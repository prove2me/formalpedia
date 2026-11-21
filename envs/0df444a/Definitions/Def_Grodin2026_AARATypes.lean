-- Prove2me | Definitions.Def_Grodin2026_AARATypes
-- name    : Grodin2026_AARATypes
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-20T19:13:28.286267+00:00
-- url     : https://prove2.me/theorems/1c1ea2cd-3eef-4c6e-b546-9286a3528b50
-- title:
--   The Calf interpretation of positive AARA types
-- statement:
--   The positive AARA grammar, its value types, and the potential function of Figure 2. The two-world Calf interpretation takes the tensor of free cost algebras and builds the linear-credit list by applying the list connective to credited elements. In the quadratic list family the linear coefficient increases by the quadratic coefficient at each tail.
-- source:
--   Grodin, Chu, Li, Hoffmann, and Harper (2026), Potential Functions as Types, §4.2 and §5.2, Figure 2. https://arxiv.org/abs/2607.08547v2

import Definitions.Def_Grodin2026_Banker

/-!
# Positive AARA computation types

The positive Calf connectives are interpreted in the paper's two-world model with natural
number costs. Both phase algebras of a positive AARA type are free. In particular, its
tensor uses the free algebra on pairs and combines costs additively. The list constructions
apply the abstraction map element by element, using the credit operator on each cons cell.

The interpretation is defined from these connectives. Theorem 5.7 identifies its result
with the separate potential interpretation of Figure 2.
-/

namespace Grodin2026.Revised

/-- Extend a function on generators to a homomorphism from a free cost algebra. -/
def extendFree {X : Type} {B : CostAlg} (f : X → B.carrier) : CostHom (FreeCostAlg X) B where
  fn := fun (c, x) ↦ B.charge c (f x)
  map_charge := fun p (c, x) ↦ B.charge_add p c (f x)
  mono := by
    intro a b h
    rcases a with ⟨c, x⟩
    rcases b with ⟨d, y⟩
    change c ≤ d ∧ x = y at h
    obtain ⟨hcd, rfl⟩ := h
    exact B.charge_mono_cost (f x) hcd

/-- The universal property of the tensor on two free cost algebras. Its pairing sends
`((c,x),(d,y))` to `(c+d,(x,y))`. A separately cost-preserving map on the two factors
extends uniquely to an ordinary cost homomorphism out of the tensor. -/
theorem freeTensor_universal {X Y : Type} {B : CostAlg}
    (f : (FreeCostAlg X).carrier → (FreeCostAlg Y).carrier → B.carrier)
    (hleft : ∀ (p : Nat) (x : (FreeCostAlg X).carrier) (y : (FreeCostAlg Y).carrier),
      f ((FreeCostAlg X).charge p x) y = B.charge p (f x y))
    (hright : ∀ (p : Nat) (x : (FreeCostAlg X).carrier) (y : (FreeCostAlg Y).carrier),
      f x ((FreeCostAlg Y).charge p y) = B.charge p (f x y)) :
    ∃! g : CostHom (FreeCostAlg (X × Y)) B,
      ∀ (c d : Nat) (x : X) (y : Y), g.fn (c + d, (x, y)) = f (c, x) (d, y) := by
  refine ⟨extendFree (fun xy ↦ f (0, xy.1) (0, xy.2)), ?_, ?_⟩
  · intro c d x y
    change B.charge (c + d) (f (0, x) (0, y)) = f (c, x) (d, y)
    rw [B.charge_add]
    have hl := hleft c (0, x) (d, y)
    have hr := hright d (0, x) (0, y)
    simp only [FreeCostAlg, Nat.add_zero] at hl hr
    rw [hl, hr]
  · intro g hg
    apply CostHom.ext
    funext xy
    obtain ⟨c, x, y⟩ := xy
    simpa only [Nat.add_zero, extendFree] using hg c 0 x y |>.trans
      (by
        have h := hleft c (0, x) (0, y)
        simpa only [FreeCostAlg, Nat.add_zero] using h)

/-- A two-world computation type whose algebras at both worlds are free. -/
structure FreePhase (X Y : Type) where
  alpha : CostHom (FreeCostAlg X) (FreeCostAlg Y)

/-- View a two-world map of free algebras as a Calf computation type. -/
def FreePhase.toComp {X Y : Type} (A : FreePhase X Y) : CompType :=
  AbstractionComp (FreeCostAlg X) (FreeCostAlg Y) A.alpha

/-- The constant free computation type. -/
def FreePhase.free (X : Type) : FreePhase X X :=
  ⟨CostHom.id (FreeCostAlg X)⟩

/-- The Calf tensor restricted to free algebras at both phases. On generators its
transition is obtained by applying the two input transitions and combining their
results by the tensor pairing from `freeTensor_universal`. -/
def FreePhase.tensor {X₁ X₂ Y₁ Y₂ : Type} (A : FreePhase X₁ Y₁) (B : FreePhase X₂ Y₂) :
    FreePhase (X₁ × X₂) (Y₁ × Y₂) :=
  ⟨extendFree fun (x, y) ↦
    let a : Nat × Y₁ := A.alpha.fn (0, x)
    let b : Nat × Y₂ := B.alpha.fn (0, y)
    (a.1 + b.1, (a.2, b.2))⟩

/-- The Calf coproduct of types whose phase algebras are free. -/
def FreePhase.sum {X₁ X₂ Y₁ Y₂ : Type} (A : FreePhase X₁ Y₁) (B : FreePhase X₂ Y₂) :
    FreePhase (Sum X₁ X₂) (Sum Y₁ Y₂) :=
  ⟨extendFree fun s ↦ match s with
    | .inl x =>
        let a : Nat × Y₁ := A.alpha.fn (0, x)
        (a.1, .inl a.2)
    | .inr x =>
        let b : Nat × Y₂ := B.alpha.fn (0, x)
        (b.1, .inr b.2)⟩

/-- Restrict the original Calf credit operator to free phase algebras. -/
def FreePhase.credit {X Y : Type} (p : Nat) (A : FreePhase X Y) : FreePhase X Y :=
  ⟨(CreditComp p A.toComp).alpha⟩

/-- The generator action of the inductive list connective. The empty list has no
incoming cost, and the cons constructor uses the tensor pairing on the translated
head and tail. -/
def FreePhase.listGenerator {X Y : Type} (A : FreePhase X Y) : List X → Nat × List Y
  | [] => (0, [])
  | x :: xs =>
      let a : Nat × Y := A.alpha.fn (0, x)
      let b := A.listGenerator xs
      (a.1 + b.1, a.2 :: b.2)

/-- The free phase interpretation of Calf's inductive list connective. -/
def FreePhase.list {X Y : Type} (A : FreePhase X Y) : FreePhase (List X) (List Y) :=
  ⟨extendFree A.listGenerator⟩

/-- Interpret `CList1` by applying the inductive list connective to the credited
element type. -/
def FreePhase.clist1 {X Y : Type} (p : Nat) (A : FreePhase X Y) :
    FreePhase (List X) (List Y) :=
  (A.credit p).list

/-- The generator action of the indexed quadratic-credit list connective, on the
ordinary list normal forms of its nil and cons constructors. The tail belongs to
the family at shifted index `p₂ + p₁`. -/
def FreePhase.clist2Generator {X Y : Type} (A : FreePhase X Y) (p₂ : Nat) :
    Nat → List X → Nat × List Y
  | _, [] => (0, [])
  | p₁, x :: xs =>
      let a : Nat × Y := (A.credit p₁).alpha.fn (0, x)
      let b := A.clist2Generator p₂ (p₂ + p₁) xs
      (a.1 + b.1, a.2 :: b.2)

/-- The free phase interpretation of the indexed quadratic-credit list family. -/
def FreePhase.clist2 {X Y : Type} (p₁ p₂ : Nat) (A : FreePhase X Y) :
    FreePhase (List X) (List Y) :=
  ⟨extendFree (A.clist2Generator p₂ p₁)⟩

/-- The positive AARA type grammar given in §5.2. -/
inductive AARAType : Type 1 where
  | free (X : Type) : AARAType
  | top : AARAType
  | tensor (A B : AARAType) : AARAType
  | sum (A B : AARAType) : AARAType
  | credit (p : Nat) (A : AARAType) : AARAType
  | clist1 (p : Nat) (A : AARAType) : AARAType
  | clist2 (p₁ p₂ : Nat) (A : AARAType) : AARAType

/-- The value interpretation of positive types in Figure 2. -/
def aaraValues : AARAType → Type
  | .free X => X
  | .top => PUnit
  | .tensor A B => aaraValues A × aaraValues B
  | .sum A B => Sum (aaraValues A) (aaraValues B)
  | .credit _ A => aaraValues A
  | .clist1 _ A => List (aaraValues A)
  | .clist2 _ _ A => List (aaraValues A)

/-- Sum the potentials of the elements of a list, counting every occurrence. -/
def listPotentialSum {X : Type} (φ : X → Nat) : List X → Nat
  | [] => 0
  | x :: xs => φ x + listPotentialSum φ xs

/-- The independently defined potential function of Figure 2. -/
def aaraPotential : (A : AARAType) → aaraValues A → Nat
  | .free _, _ => 0
  | .top, _ => 0
  | .tensor A B, (a, b) => aaraPotential A a + aaraPotential B b
  | .sum A _, .inl a => aaraPotential A a
  | .sum _ B, .inr b => aaraPotential B b
  | .credit p A, a => p + aaraPotential A a
  | .clist1 p A, l => l.length * p + listPotentialSum (aaraPotential A) l
  | .clist2 p₁ p₂ A, l =>
      l.length * p₁ + binom2 l.length * p₂ + listPotentialSum (aaraPotential A) l

/-- Interpret each grammar constructor by its Calf connective, in the subcollection
of computation types with free algebras at both worlds. -/
def interpPositiveFree : (A : AARAType) → FreePhase (aaraValues A) (aaraValues A)
  | .free X => .free X
  | .top => .free PUnit
  | .tensor A B => (interpPositiveFree A).tensor (interpPositiveFree B)
  | .sum A B => (interpPositiveFree A).sum (interpPositiveFree B)
  | .credit p A => (interpPositiveFree A).credit p
  | .clist1 p A => (interpPositiveFree A).clist1 p
  | .clist2 p₁ p₂ A => (interpPositiveFree A).clist2 p₁ p₂

/-- The compositional Calf interpretation of positive AARA types for Theorem 5.7. -/
def interpPositiveAARA (A : AARAType) : CompType :=
  (interpPositiveFree A).toComp

/-- The potential on a linear-credit cons is its head and tail potentials plus
one cell's credit. -/
theorem aaraPotential_clist1_cons (p : Nat) (A : AARAType) (x : aaraValues A)
    (xs : List (aaraValues A)) :
    aaraPotential (.clist1 p A) (x :: xs) =
      p + aaraPotential A x + aaraPotential (.clist1 p A) xs := by
  simp only [aaraPotential, List.length_cons, listPotentialSum, Nat.succ_mul]
  ac_rfl

/-- The potential on a quadratic-credit cons is its head and indexed tail
potentials plus the current index's credit. -/
theorem aaraPotential_clist2_cons (p₁ p₂ : Nat) (A : AARAType) (x : aaraValues A)
    (xs : List (aaraValues A)) :
    aaraPotential (.clist2 p₁ p₂ A) (x :: xs) =
      p₁ + aaraPotential A x + aaraPotential (.clist2 (p₂ + p₁) p₂ A) xs := by
  simp only [aaraPotential, List.length_cons, listPotentialSum, binom2, Nat.succ_mul,
    Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem FreePhase.credit_alpha {X Y : Type} (p : Nat) (A : FreePhase X Y)
    (x : Nat × X) :
    (A.credit p).alpha.fn x = (p + (A.alpha.fn x).1, (A.alpha.fn x).2) :=
  rfl

private theorem linear_generator_eq (A : AARAType)
    (h : ∀ x : aaraValues A,
      (interpPositiveFree A).alpha.fn (0, x) = (aaraPotential A x, x))
    (p : Nat) (xs : List (aaraValues A)) :
    ((interpPositiveFree A).credit p).listGenerator xs =
      (aaraPotential (.clist1 p A) xs, xs) := by
  induction xs with
  | nil => simp [FreePhase.listGenerator, aaraPotential, listPotentialSum]
  | cons x xs ih =>
      simp only [FreePhase.listGenerator, FreePhase.credit_alpha, h, ih,
        aaraPotential_clist1_cons]

private theorem quadratic_generator_eq (A : AARAType)
    (h : ∀ x : aaraValues A,
      (interpPositiveFree A).alpha.fn (0, x) = (aaraPotential A x, x))
    (p₁ p₂ : Nat) (xs : List (aaraValues A)) :
    (interpPositiveFree A).clist2Generator p₂ p₁ xs =
      (aaraPotential (.clist2 p₁ p₂ A) xs, xs) := by
  induction xs generalizing p₁ with
  | nil => simp [FreePhase.clist2Generator, aaraPotential, listPotentialSum, binom2]
  | cons x xs ih =>
      simp only [FreePhase.clist2Generator, FreePhase.credit_alpha, h, ih,
        aaraPotential_clist2_cons]

private theorem interpPositiveFree_generator (A : AARAType) (x : aaraValues A) :
    (interpPositiveFree A).alpha.fn (0, x) = (aaraPotential A x, x) := by
  induction A with
  | free => rfl
  | top => rfl
  | tensor A B ihA ihB =>
      obtain ⟨a, b⟩ : aaraValues A × aaraValues B := x
      simp only [interpPositiveFree, FreePhase.tensor, extendFree, FreeCostAlg,
        ihA, ihB, Nat.zero_add, aaraPotential] <;> rfl
  | sum A B ihA ihB =>
      change Sum (aaraValues A) (aaraValues B) at x
      cases x <;> simp only [interpPositiveFree, FreePhase.sum, extendFree, FreeCostAlg,
        ihA, ihB, Nat.zero_add, aaraPotential] <;> rfl
  | credit p A ih =>
      change aaraValues A at x
      change ((interpPositiveFree A).credit p).alpha.fn (0, x) =
        (p + aaraPotential A x, x)
      rw [FreePhase.credit_alpha, ih]
  | clist1 p A ih =>
      simp only [interpPositiveFree, FreePhase.clist1, FreePhase.list, extendFree, FreeCostAlg,
        Nat.zero_add, linear_generator_eq A ih p x] <;> rfl
  | clist2 p₁ p₂ A ih =>
      simp only [interpPositiveFree, FreePhase.clist2, extendFree, FreeCostAlg,
        Nat.zero_add, quadratic_generator_eq A ih p₁ p₂ x] <;> rfl

/-- The transition computed from the Calf connectives agrees with Figure 2. -/
theorem interpPositiveAARA_alpha (A : AARAType) (x : Nat × aaraValues A) :
    (interpPositiveAARA A).alpha.fn x = (x.1 + aaraPotential A x.2, x.2) := by
  obtain ⟨c, x⟩ := x
  change (interpPositiveFree A).alpha.fn (c, x) = (c + aaraPotential A x, x)
  have h := (interpPositiveFree A).alpha.map_charge c (0, x)
  rw [interpPositiveFree_generator] at h
  simpa only [FreeCostAlg, Nat.add_zero] using h

/-- Theorem 5.7 in the two-world natural-cost model. The equivalence is the
identity on both free algebras, with commutation proved from the grammar. -/
def aaraCalfEquiv (A : AARAType) :
    CompEquiv (interpPositiveAARA A) (PotentialType (aaraValues A) (aaraPotential A)) where
  toHom :=
    { hom_top := CostHom.id _
      hom_abs := CostHom.id _
      comm := fun x ↦ (interpPositiveAARA_alpha A x).symm }
  invHom :=
    { hom_top := CostHom.id _
      hom_abs := CostHom.id _
      comm := interpPositiveAARA_alpha A }
  left_inv := rfl
  right_inv := rfl

end Grodin2026.Revised


