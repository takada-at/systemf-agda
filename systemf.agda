module systemf where
open import Data.Nat

data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_

data Kind : Set where
  * : Kind
  _⇒_ : Kind -> Kind -> Kind

infix 20 _⇒_

data Variable : Set where
  -- variables. st. (v 0) (v 1) (v 2)
  v : ℕ → Variable

data _≢_ : (x : Variable) → (y : Variable) → Set where
  zero₁ : ∀ {n : ℕ} → v zero ≢ v (suc n)
  zero₂ : ∀ {n : ℕ} → v (suc n) ≢ v zero
  suc : ∀ {n m : ℕ} → v n ≢ v m → v (suc n) ≢ v (suc m)


data Type : Set where
  top : Type
  var : Variable → Type
  _⟶_ : Type → Type → Type
  ∀T_<:_,_ : Variable → Type → Type → Type
  λT_::_,_ : Variable → Kind → Type → Type
  _←_ : Type → Type → Type


-- substitution
data [_:=_]_≡_ : Variable → Type → Type → Type → Set where
  subst-top : ∀ {x : Variable } {s : Type} →
    [ x := s ] top ≡ top
  subst-arrow : ∀ {x : Variable} {s t₁ t₂ u₁ u₂ : Type} →
    [ x := s ] t₁ ≡ u₁ → [ x := s ] t₂ ≡ u₂
      → [ x := s ] (t₁ ⟶ t₂) ≡ (u₁ ⟶ u₂)
  subst-all : ∀ {x y : Variable} {s t₁ t₂ u₁ u₂ : Type} →
    [ x := s ] t₁ ≡ u₁ → [ x := s ] t₂ ≡ u₂
      → [ x := s ] (∀T y <: t₁ , t₂) ≡ (∀T y <: u₁ , u₂)
  subst-abs : ∀ {x y : Variable} {s t u : Type} {k : Kind} →
    [ x := s ] t ≡ u
      → [ x := s ] (λT y :: k , t) ≡ (λT y :: k , u)
  subst-app : ∀ {x : Variable} {s t₁ t₂ u₁ u₂ : Type} →
     [ x := s ] t₁ ≡ u₁ → [ x := s ] t₂ ≡ u₂
       → [ x := s ] (t₁ ← t₂) ≡ (u₁ ← u₂)
  subst-var : ∀ {x y : Variable} {s t₁ t₂ u₁ u₂ : Type} →
     x ≡ y → [ x := s ] (var y) ≡ s
  subst-var2 : ∀ {x y : Variable} {s t₁ t₂ u₁ u₂ : Type} →
     x ≢ y → [ x := s ] (var y) ≡ (var y)


data _≡'_ : Type → Type → Set where
  q-refl : ∀ {t : Type} →
    t ≡' t
  q-symm : ∀ {t s : Type} →
    t ≡' s → s ≡' t
  q-trans : ∀ {s u t : Type} →
    s ≡' u → u ≡' t → s ≡' t
  q-arrow : ∀ {s₁ s₂ t₁ t₂ : Type} →
    s₁ ≡' t₁ → s₂ ≡' t₂
      → (s₁ ⟶ s₂) ≡' (t₁ ⟶ t₂)
  q-all : ∀ {x : Variable} {s₁ s₂ t₁ t₂ : Type} →
    s₁ ≡' t₁ → s₂ ≡' t₂ → (∀T x <: s₁ , s₂) ≡' (∀T x <: t₁ , t₂)
  q-abs : ∀ {x : Variable} {s₂ t₂ : Type} {k : Kind} →
    s₂ ≡' t₂ → (λT x :: k , s₂) ≡' (λT x :: k , t₂)
  q-app : ∀ {s₁ s₂ t₁ t₂ : Type} → 
    s₁ ≡' t₁ → s₂ ≡' t₂ → (s₁ ← s₂) ≡' (t₁ ← t₂)
  q-appabs : ∀ {x : Variable} {s t u : Type} {k : Kind} →
    ([ x := s ] t ≡ u) → ((λT x :: k , t) ← s) ≡' u


data Binding : Set where
  _<:_ : Variable → Type → Binding

infix 35 _<:_

data Context : Set where
  empty : Context
  _,_ : Context → Binding → Context

infixl 30 _,_


data _∈_ : Binding → Context → Set where
  in1 : ∀ {x : Variable} {t : Type} {Γ : Context} →
      x <: t ∈ Γ , x <: t
  in2 : ∀ {x : Variable} {t : Type} {b : Binding} {Γ : Context} →
      x <: t ∈ Γ
        → x <: t ∈ Γ , b

Top : Kind → Type
Top * = top
Top (k₁ ⇒ k₂) = λT (v 0) :: k₁ , (Top k₂)

data _⊢_::_ : Context → Type → Kind → Set where
  k-top : ∀ {Γ : Context} →
    Γ ⊢ top :: *
  k-tvar : ∀ {Γ : Context} {t : Type} {x : Variable} {k : Kind} →
    x <: t ∈ Γ → Γ ⊢ t :: k
      → Γ ⊢ (var x) :: k
  k-abs : ∀ {Γ : Context} {t₁ t₂ : Type} {x : Variable} {k₁ k₂ : Kind} →
    Γ , x <: Top k₁ ⊢ t₂ :: k₂
      → Γ ⊢ (λT x :: k₁ , t₂) :: (k₁ ⇒ k₂)
  k-app : ∀ {Γ : Context} {t₁ t₂ : Type} {k₁ k₂ : Kind} →
    Γ ⊢ t₁ :: (k₁ ⇒ k₂) → Γ ⊢ t₂ :: k₂
      → Γ ⊢ t₁ ← t₂ :: k₂
  k-arrow : ∀ {Γ : Context} {t₁ t₂ : Type} →
    Γ ⊢ t₁ :: * → Γ ⊢ t₂ :: *
      → Γ ⊢ t₁ ⟶ t₂ :: *
  k-all : ∀ {Γ : Context} {t₁ t₂ : Type} {x : Variable}→
    Γ , x <: t₁ ⊢ t₂ :: *
      → Γ ⊢ (∀T x <: t₁ , t₂) :: *

data _⊢_<:_ : Context → Type → Type → Set where
  s-trans : ∀ {s t u : Type} {Γ : Context} →
    Γ ⊢ s <: t → Γ ⊢ t <: u → Γ ⊢ s <: u
  s-top :  ∀ {s t u : Type} {Γ : Context} →
    Γ ⊢ s :: * → Γ ⊢ s <: top
  s-arrow :  ∀ {s₁ s₂ t₁ t₂ : Type} {Γ : Context} →
    Γ ⊢ t₁ <: s₁ → Γ ⊢ t₂ <: s₂
      → Γ ⊢ (t₁ ⟶ t₂) <: (s₁ ⟶ s₂)
  s-tvar : ∀ {x : Variable} {t : Type} {Γ : Context} →
    x <: t ∈ Γ → Γ ⊢ var x <: t
  s-all : ∀ {x : Variable} {u₁ s₂ t₁ t₂ : Type} {Γ : Context} {k₁ : Kind} →
    Γ ⊢ u₁ :: k₁ → Γ , x <: u₁ ⊢ s₂ <: t₂
    → Γ ⊢ (∀T x <: u₁ , s₂) <: (∀T x <: u₁ , t₂)
  s-abs : ∀ {x : Variable} {u₁ s₂ t₂ : Type} {Γ : Context} {k₁ : Kind} →
    Γ , x <: Top k₁ ⊢ s₂ <: t₂
      → Γ ⊢ (λT x :: k₁ , s₂) <: (λT x :: k₁ , t₂)
  s-app : ∀ {u s₁ t₁ : Type} {Γ : Context} →
    Γ ⊢ s₁ <: t₁
      → Γ ⊢ s₁ ← u <: t₁ ← u
  s-eq : ∀ {s t : Type} {Γ : Context} {k : Kind} →
    Γ ⊢ s :: k → Γ ⊢ t :: k → s ≡' t
      → Γ ⊢ s <: t

infix 15 _⊢_<:_


-- example
-- TaPL p.372, 31.2.1
A = v 0
B = v 1
F = v 2
X = v 3
Id = λT X :: * , var X
Γ = empty , B <: top , A <: var B , F <: Id


b<top∈Γ    : B <: top ∈ Γ
b<top∈Γ = in2 (in2 in1)
a<b∈Γ      : A <: var B ∈ Γ
a<b∈Γ = in2 in1

bkind      : Γ ⊢ var B :: *
bkind = k-tvar b<top∈Γ k-top
akind      : Γ ⊢ var A :: *
akind = k-tvar a<b∈Γ bkind
idkind     : Γ ⊢ Id :: (* ⇒ *)
idkind = k-abs (k-tvar in1 k-top)
idxkind    : ∀ {t : Type} → Γ ⊢ t :: * → Γ ⊢ Id ← t :: *
idxkind = λ x → k-app (k-abs (k-tvar in1 k-top)) x


p1 : Γ ⊢ var A <: Id ← (var B)
p1 = s-trans a<b b<idb
  where
    subst      : [ X := (var B) ] var X ≡ var B
    subst = subst-var refl
    id[b]≡b    : (Id ← (var B)) ≡' var B
    id[b]≡b = q-appabs subst
    b≡idb      : var B ≡' (Id ← (var B))
    b≡idb = q-symm id[b]≡b
    b<idb      : Γ ⊢ var B <: Id ← (var B)
    b<idb = s-eq bkind (idxkind bkind) b≡idb
    a<b        : Γ ⊢ var A <: var B
    a<b = s-tvar a<b∈Γ
