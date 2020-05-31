open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Basics

module eBPF where

-- definition of registers

REG-SIZE : Nat
REG-SIZE = 13


reg : Set
reg = Fin REG-SIZE

r0 : reg
r0 = fromNat< (≤-dec {m = 1})

r1 : reg
r1 = fromNat< (≤-dec {m = 2})

r2 : reg
r2 = fromNat< (≤-dec {m = 3})

r3 : reg
r3 = fromNat< (≤-dec {m = 4})

r4 : reg
r4 = fromNat< (≤-dec {m = 5})

r5 : reg
r5 = fromNat< (≤-dec {m = 6})

r6 : reg
r6 = fromNat< (≤-dec {m = 7})

r7 : reg
r7 = fromNat< (≤-dec {m = 8})

r8 : reg
r8 = fromNat< (≤-dec {m = 9})

r9 : reg
r9 = fromNat< (≤-dec {m = 10})

r10 : reg
r10 = fromNat< (≤-dec {m = 11})

data-start : reg
data-start = fromNat< (≤-dec {m = 12})

data-end : reg
data-end = fromNat< (≤-dec {m = 13})

-- tags for registers

data R : Set where
  Shared : Nat → R
  ctx stk pkt num inv : R

invalid : R → Bool
invalid inv = false
invalid _   = true

-- environment entry

tagged-value : Set
tagged-value = R × Nat

-- environment

Env : Set
Env = Vec tagged-value REG-SIZE

non-zero-entry : Env → reg → reg → Bool
non-zero-entry env r1 r2 = is-zero (snd (lookup r1 env)) ∧
                           is-zero (snd (lookup r2 env))
  where
   is-zero : Nat → Bool
   is-zero 0 = true
   is-zero _ = false 


 -- register access

data _[_]p=_ : Env → reg → R → Set where
  acc : ∀ {env r p t n}
          {_ : p ≡ (t , n)} → 
          {{ So (invalid t)}} →
          [ env ] r ~ p →
          env [ r ]p= t

infix 0 _[_]p=_

-- arithmetic expressions, by construction no invalid register is read.

data E (env : Env) : tagged-value → Set where
   K   : (n : Nat) → E env (num , n) 
   #_  : ∀ {r t} → (env [ r ] ~ t) → E env t
   _⊕₁_ : ∀ {r1 r2 t} → env [ r1 ]p= num →
                        env [ r2 ]p= t →
                        E env num
   _⊕₂_ : ∀ {r1 r2 t} → env [ r1 ]p= t →
                        env [ r2 ]p= num →
                        E env num
   _⊝₁_ :  ∀ {r1 r2 t} → env [ r1 ]p= t →
                         env [ r2 ]p= t →
                         E env t
   _⊝₂_ : ∀ {r1 r2 t} → env [ r1 ]p= t →
                        env [ r2 ]p= num →
                        E env num

-- boolean expressions

data B (env : Env) : Set where
   _≈₁_ : ∀ {r1 r2 t} → env [ r1 ]p= t →
                        env [ r2 ]p= t →
                        B env 
   _≈₂_ : ∀ (r1 r2 : reg) → {{ So (non-zero-entry env r1 r2) }} → B env
   _≤'_ : ∀ {r1 r2 t} → env [ r1 ]p= t →
                        env [ r2 ]p= t →
                        B env 

-- size of map

data dom : R → Set where
  Shared : ∀ {n} → dom (Shared n)
  ctx : dom ctx
  stk : dom stk
  pkt : dom pkt

in-dom-dec : ∀ r → Dec (dom r)
in-dom-dec (Shared x) = yes Shared
in-dom-dec ctx = yes ctx
in-dom-dec stk = yes stk
in-dom-dec pkt = yes pkt
in-dom-dec num = no (λ ())
in-dom-dec inv = no (λ ())

postulate size-of' : ∀ {r} → dom r → Nat

size-of : ∀ {r} → dom r → Nat
size-of stk = 512
size-of r   = size-of' r

-- bound information

in-bounds : Env → Nat → reg → Set
in-bounds env sz r with lookup r env
...| (pkt , n) = n ≤ (snd (lookup data-end env) - sz)
...| (t   , n) with in-dom-dec t
... | yes x = n ≤ ((size-of x) - sz)
... | no x = ⊥

-- commands

data cmd (env : Env) : Env → Set where
  _:=_ : ∀ {t : R}(w : reg)(e : E env t) → cmd env env
  assume : B env → cmd env env
  load : ∀ {p t} (w : reg)(sz : Nat) →
                   in-bounds env sz p →
                   env [ p ]p= t →
                   t ≢ num →
                   cmd env env
  store : ∀ {p x t1 t2}(sz : Nat) →
            in-bounds env sz p →
            env [ p ]p= t1 →
            env [ x ]p= t2 →
            t1 ≢ num →
            t2 ≢ num →
            t1 ≡ stk → 
            cmd env env 


-- state definition

MEM-SIZE : Nat
MEM-SIZE = 512

Address : Set
Address = Fin MEM-SIZE

μ : Set
μ = Vec entry MEM-SIZE

ξ : Set
ξ = List Address

σ : Set
σ = Env × μ × ξ

-- program definition

data prog : σ → σ → Set where
  []  : ∀ {s} → prog s s
  _∷_ : ∀ {s s' s''} →
        cmd (fst s) (fst s') →
        prog s' s'' →
        prog s s''
