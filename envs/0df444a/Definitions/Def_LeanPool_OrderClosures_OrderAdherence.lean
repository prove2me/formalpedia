-- Prove2me | Definitions.Def_LeanPool_OrderClosures_OrderAdherence
-- name    : LeanPool_OrderClosures_OrderAdherence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:54:35.854568+00:00
-- url     : https://prove2.me/theorems/6309f3e9-b349-4b9e-beea-90cf0b0eb5f4
-- title:
--   Order Adherence
-- statement:
--   Definitions and structural lemmas for Order Adherence, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_smul

set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace OrderClosures
universe u v
section Convergence
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def UOConvergesTo {ι : Type v} [Preorder ι] (f : ι → X) (x : X) : Prop :=
  ∀ a : X, 0 ≤ a → OrderConvergesTo (fun i ↦ |f i - x| ⊓ a) 0
def orderAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ OrderConvergesTo f x}
def uoAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ UOConvergesTo f x}
def IsOrderClosed (A : Set X) : Prop := orderAdherence A ⊆ A
def IsUOClosed (A : Set X) : Prop := uoAdherence A ⊆ A
def orderClosure (A : Set X) : Set X :=
  ⋂₀ {B : Set X | A ⊆ B ∧ IsOrderClosed B}
def directedPositiveAdherence (A : Set X) : Set X :=
  {x | 0 ≤ x ∧ ∃ B : Set X,
    B ⊆ A ∩ {y | 0 ≤ y} ∧ B.Nonempty ∧ DirectedOn (· ≤ ·) B ∧ IsLUB B x}
def solidOrderAdherence (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure (directedPositiveAdherence A)
def iteratedOrderAdherence (A : Set X) : ℕ → Set X
  | 0 => A
  | n + 1 => orderAdherence (iteratedOrderAdherence A n)
structure OrderAdherenceTower (A : Set X) where
  /-- The set reached at each ordinal stage. -/
  stage : Ordinal.{u} → Set X
  stage_zero : stage 0 = A
  stage_succ : ∀ ξ, stage (Order.succ ξ) = orderAdherence (stage ξ)
  stage_limit : ∀ ξ, Order.IsSuccLimit ξ →
    stage ξ = ⋃ η : Set.Iio ξ, stage η.1
def NeedsOrderAdherenceIterations (A : Set X) (ξ : Ordinal.{u}) : Prop :=
  ∃ T : OrderAdherenceTower A,
    ∀ η < ξ, T.stage η ⊂ T.stage (Order.succ η)
end Convergence
section Solidity
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
abbrev solidHull (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure A
noncomputable def solidGeneratorNumber (S : Set X) : Cardinal :=
  sInf {κ : Cardinal | ∃ A : Set X, Cardinal.mk A = κ ∧ solidHull A = S}
def scaleSet (a : ℝ) (A : Set X) [SMul ℝ X] : Set X :=
  (fun x ↦ a • x) '' A
def unitBallFor (p : X → ℝ) : Set X := {x | p x ≤ 1}
end Solidity
section CompletenessAndNorms
def IsOrderComplete (X : Type u) [Preorder X] : Prop :=
  ∀ A : Set X, A.Nonempty → BddAbove A → ∃ x, IsLUB A x
@[reducible]
noncomputable def conditionallyCompleteLatticeOfIsOrderComplete
    (X : Type u) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (hX : IsOrderComplete X) : ConditionallyCompleteLattice X :=
  conditionallyCompleteLatticeOfPosSet X fun _ hne hbdd => hX _ hne hbdd
noncomputable def densityCharacter (X : Type u) [TopologicalSpace X] : Cardinal :=
  sInf {κ : Cardinal | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [Module ℝ X]
structure PaperLatticeNorm (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [Module ℝ X] where
  /-- The real-valued lattice norm. -/
  toFun : X → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  eq_zero_iff : ∀ x, toFun x = 0 ↔ x = 0
  add_le : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
  smul : ∀ (a : ℝ) x, toFun (a • x) = |a| * toFun x
  solid : ∀ {x y}, |x| ≤ |y| → toFun x ≤ toFun y
instance : CoeFun (PaperLatticeNorm X) (fun _ ↦ X → ℝ) := ⟨PaperLatticeNorm.toFun⟩
def IsCompleteFor (p : X → ℝ) : Prop :=
  ∀ f : ℕ → X,
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, p (f m - f n) < ε) →
      ∃ x, ∀ ε > 0, ∃ N, ∀ n ≥ N, p (f n - x) < ε
def HasFatouProperty (p : X → ℝ) : Prop :=
  ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → IsLUB (p '' Set.range f) (p x)
def HasWeakFatouProperty (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → ∀ c, (∀ i, p (f i) ≤ c) → p x ≤ K * c
def EquivalentNorms (p q : X → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * p x ≤ q x ∧ q x ≤ C * p x
noncomputable def ambientLatticeNorm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] : PaperLatticeNorm Y where
  toFun := norm
  nonneg := norm_nonneg
  eq_zero_iff := fun _ ↦ norm_eq_zero
  add_le := norm_add_le
  smul := norm_smul
  solid := fun h ↦ HasSolidNorm.solid h
end CompletenessAndNorms
end OrderClosures


