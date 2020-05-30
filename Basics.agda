module Basics where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat public
open import Agda.Builtin.Equality


variable
  A C : Set
  x y z : A
  k l m n : Nat

-- return stuff from the current instance argument

it : {{ A }} → A
it {{ x }} = x 


_∧_ : Bool → Bool → Bool
true ∧ b = b
false ∧ _ = false

-- products

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst


infixr 5 _×_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

open Σ public

-- co-products

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B


-- unit and empty types

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

-- equality

_≢_ : (x y : A) → Set
x ≢ y = ¬ (x ≡ y)

_ : x ≡ x
_ = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : (f : A → C) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : (P : A → Set) → x ≡ y → P x → P y
subst P refl prf = prf

-- ordering

module Nat-≤ where

  data _≤_ : Nat → Nat → Set where
    ≤-zero : 0 ≤ n
    ≤-suc  : m ≤ n → (suc m) ≤ (suc n)


  ≤-refl : n ≤ n
  ≤-refl {n = zero}  = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero      l≤m         = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) =
    ≤-suc (≤-trans k≤l l≤m)

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym ≤-zero      ≤-zero      = refl
  ≤-antisym (≤-suc m≤n) (≤-suc n≤m) =
    cong suc (≤-antisym m≤n n≤m)

  ≤-pred : (suc m) ≤ (suc n) → m ≤ n
  ≤-pred (≤-suc m≤n) = m≤n

  So : Bool → Set
  So false = ⊥
  So true  = ⊤

  instance
    ≤-dec : {p : So (m < (suc n))} → m ≤ n
    ≤-dec {m = zero}{n} = ≤-zero
    ≤-dec {m = suc m}{n = suc n}{p = p}
      = ≤-suc (≤-dec {p = p})

open Nat-≤ public

-- fin data type

_<'_ : Nat → Nat → Set
n <' m = suc n ≤ m

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)


fromNat< : ∀ {m n} → m <' n → Fin n
fromNat< {zero} {suc n} m<n = zero
fromNat< {suc m} {suc n} m<n = suc (fromNat< (≤-pred m<n))

-- decidability

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P


postulate 
  _≟_ : ∀ {n}(p1 p2 : Fin n) → Dec (p1 ≡ p2)

-- vector and its lookup

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data [_]_~_ : Vec A n → Fin n → A → Set where
  zero : ∀ {x : A}{xs : Vec A n} → [ x ∷ xs ] zero ~ x
  suc  : ∀ {x : A}{xs : Vec A n}{i : Fin n} → [ xs ] i ~ x → [ x ∷ xs ] (suc i) ~ x

lookup : ∀ {n} → Fin n → Vec A n → A
lookup zero (x ∷ _) = x
lookup (suc n) (_ ∷ xs) = lookup n xs

-- vector update

update : Vec A n → Fin n → A → Vec A n
update (y ∷ ys) zero  y' = (y' ∷ ys)
update (y ∷ ys) (suc i) y' = y ∷ update ys i y'


-- list

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
