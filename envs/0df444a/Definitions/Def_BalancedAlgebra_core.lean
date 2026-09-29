-- Prove2me | Definitions.Def_BalancedAlgebra_core
-- name    : BalancedAlgebra_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T00:25:05.85999+00:00
-- url     : https://prove2.me/theorems/f7a6ec61-db98-4c93-a38a-6645e9969a85
-- title:
--   Balanced algebras: partial algebras, ideals, units, associating and gregarious elements
-- statement:
--   This file fixes the vocabulary of A. Winkler's *Ideals in Balanced Algebras and the Genesis of Mathematics* (§1, §4, §4.2).
--
--   An **algebra** on a type $A$ is a partial binary operation on $A$: a rule that assigns a value $a\cdot b\in A$ to some, not necessarily all, pairs $(a,b)$. It is represented by a total function $A\to A\to\mathrm{Option}\,A$, the value $\mathrm{none}$ recording that the product is undefined; $a\cdot b\downarrow$ abbreviates "$a\cdot b$ is defined". Two derived operations name the bracketings of a triple product, $(a\cdot b)\cdot c$ and $a\cdot(b\cdot c)$, each undefined as soon as either of its two steps is.
--
--   On top of this the file defines, for a subset $B\subseteq A$ and elements of $A$:
--
--   1. **left ideal** ($a\cdot b\in B$ whenever $b\in B$ and the product is defined), **right ideal** (dually), and **subalgebra**;
--   2. the **right orbit** $aA$ and the **left orbit** $Aa$;
--   3. **balance**: $(a\cdot b)\cdot c$ is defined if and only if $a\cdot(b\cdot c)$ is, for all $a,b,c$;
--   4. **left unit** ($u\cdot a=a$ whenever defined), **right unit**, **source** (a left unit $u$ with $a\cdot u$ defined only for $a=u$), **sink** (dual);
--   5. **associating element** ($(ab)c$ defined $\iff$ $a(bc)$ defined, with equal values when both are defined), and **association** (all elements associating);
--   6. **gregarious element** ($a\cdot b\downarrow$ and $b\cdot c\downarrow$ together imply that at least one of the two bracketings of $abc$ is defined);
--   7. **left cancellable element** ($b\cdot x=b\cdot y$, both defined, forces $x=y$).
--
--   Two structural lemmas unfold the triple products: a bracketed product equals $\mathrm{some}\ q$ exactly when its two steps are defined and compose to $q$.
--
--   This is the model on which the mission's goal theorem and all its milestones are stated; it is reusable for any development about partial magmas, where definedness rather than equality carries the content.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §1 (pp. 1–3), §4 (p. 6), §4.2 (pp. 6–7)

import Mathlib

/-!
# Balanced algebras: the basic vocabulary

Formalization of the basic notions of

  Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*,
  manuscript, March 20, 2020, §1 (Algebras), §4 (Associators and Associations),
  §4.1 (Principal Ideals), §4.2 (The Gregarious Ideal).

An *algebra* on a type `A` is a partial binary operation on `A`: an arrow with codomain
`A` whose domain is a subobject of `A × A`.  Here it is modelled by a function
`op : A → A → Option A`, where `op a b = none` means that `a · b` is not defined.
-/

namespace BalancedAlgebra

universe u

/-- An *algebra* on `A` (a partial magma): a binary operation defined on a subset of
`A × A`.  `op a b = none` means the product `a · b` is undefined. -/
structure PartialAlgebra (A : Type u) where
  /-- The partial product. -/
  op : A → A → Option A

namespace PartialAlgebra

variable {A : Type u}

/-- A value of `Option A` is *defined* when it is of the form `some x`. -/
def IsDef (o : Option A) : Prop := ∃ x : A, o = some x

/-- `a · b` is defined. -/
def IsDefined (P : PartialAlgebra A) (a b : A) : Prop := IsDef (P.op a b)

/-- The left-bracketed triple product `(a · b) · c`, undefined if either step is. -/
def lprod (P : PartialAlgebra A) (a b c : A) : Option A :=
  (P.op a b).bind fun x => P.op x c

/-- The right-bracketed triple product `a · (b · c)`, undefined if either step is. -/
def rprod (P : PartialAlgebra A) (a b c : A) : Option A :=
  (P.op b c).bind fun y => P.op a y

@[simp] theorem lprod_eq_some {P : PartialAlgebra A} {a b c q : A} :
    P.lprod a b c = some q ↔ ∃ x, P.op a b = some x ∧ P.op x c = some q := by
  unfold lprod
  cases h : P.op a b with
  | none => simp
  | some x => simp

@[simp] theorem rprod_eq_some {P : PartialAlgebra A} {a b c q : A} :
    P.rprod a b c = some q ↔ ∃ y, P.op b c = some y ∧ P.op a y = some q := by
  unfold rprod
  cases h : P.op b c with
  | none => simp
  | some y => simp

/-- `B` is a *left ideal*: `A · B ⊆ B`. -/
def LeftIdeal (P : PartialAlgebra A) (B : Set A) : Prop :=
  ∀ a b c : A, b ∈ B → P.op a b = some c → c ∈ B

/-- `B` is a *right ideal*: `B · A ⊆ B`. -/
def RightIdeal (P : PartialAlgebra A) (B : Set A) : Prop :=
  ∀ a b c : A, a ∈ B → P.op a b = some c → c ∈ B

/-- `B` is a *subalgebra*: `B · B ⊆ B`. -/
def IsSubalgebra (P : PartialAlgebra A) (B : Set A) : Prop :=
  ∀ a b c : A, a ∈ B → b ∈ B → P.op a b = some c → c ∈ B

/-- The *right orbit* `a · A` of `a`. -/
def rightOrbit (P : PartialAlgebra A) (a : A) : Set A := {c | ∃ b : A, P.op a b = some c}

/-- The *left orbit* `A · a` of `a`. -/
def leftOrbit (P : PartialAlgebra A) (a : A) : Set A := {c | ∃ b : A, P.op b a = some c}

/-- `P` is *balanced*: `(a · b) · c` is defined if and only if `a · (b · c)` is. -/
def Balanced (P : PartialAlgebra A) : Prop :=
  ∀ a b c : A, IsDef (P.lprod a b c) ↔ IsDef (P.rprod a b c)

/-- `u` is a *left unit*: whenever `u · a` is defined it equals `a`. -/
def IsLeftUnit (P : PartialAlgebra A) (u : A) : Prop :=
  ∀ a c : A, P.op u a = some c → c = a

/-- `v` is a *right unit*: whenever `a · v` is defined it equals `a`. -/
def IsRightUnit (P : PartialAlgebra A) (v : A) : Prop :=
  ∀ a c : A, P.op a v = some c → c = a

/-- `u` is a *source*: a left unit such that `a · u` is defined only for `a = u`. -/
def IsSource (P : PartialAlgebra A) (u : A) : Prop :=
  P.IsLeftUnit u ∧ ∀ a : A, P.IsDefined a u → a = u

/-- `v` is a *sink*: a right unit such that `v · b` is defined only for `b = v`. -/
def IsSink (P : PartialAlgebra A) (v : A) : Prop :=
  P.IsRightUnit v ∧ ∀ b : A, P.IsDefined v b → b = v

/-- `b` is *associating*: for all `a`, `c`, the product `(a · b) · c` is defined iff
`a · (b · c)` is, and whenever both are defined they are equal. -/
def Associating (P : PartialAlgebra A) (b : A) : Prop :=
  ∀ a c : A,
    (IsDef (P.lprod a b c) ↔ IsDef (P.rprod a b c)) ∧
      ∀ x y : A, P.lprod a b c = some x → P.rprod a b c = some y → x = y

/-- `P` is an *association*: every element is associating. -/
def IsAssociation (P : PartialAlgebra A) : Prop := ∀ b : A, P.Associating b

/-- `b` is *gregarious*: whenever `a · b` and `b · c` are both defined, at least one of
`(a · b) · c` and `a · (b · c)` is defined. -/
def Gregarious (P : PartialAlgebra A) (b : A) : Prop :=
  ∀ a c : A, P.IsDefined a b → P.IsDefined b c →
    IsDef (P.lprod a b c) ∨ IsDef (P.rprod a b c)

/-- `b` is *left cancellable*: `b · x = b · y` (both defined) forces `x = y`. -/
def LeftCancellable (P : PartialAlgebra A) (b : A) : Prop :=
  ∀ x y c : A, P.op b x = some c → P.op b y = some c → x = y

end PartialAlgebra

end BalancedAlgebra


