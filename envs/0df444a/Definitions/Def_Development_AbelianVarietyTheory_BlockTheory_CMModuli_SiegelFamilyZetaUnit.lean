-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SiegelFamilyZetaUnit
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_SiegelFamilyZetaUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:34.868796+00:00
-- url     : https://prove2.me/theorems/6d2e0079-7b48-43f2-91af-f9733477d462
-- title:
--   Siegel Family Zeta Unit
-- statement:
--   Definitions and structural lemmas for Siegel Family Zeta Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SiegelFamilyZetaUnit.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
def cycloLocal (p M : ℕ) : Subring ℂ :=
  Subring.closure ({x : ℂ | ∃ q : ℚ, ¬ p ∣ q.den ∧ x = (q : ℂ)} ∪ {zeta M})
def zetaElt (p M : ℕ) : cycloLocal p M :=
  ⟨zeta M, Subring.subset_closure (Or.inr rfl)⟩
theorem zetaElt_isPrimitiveRoot (p : ℕ) {M : ℕ} (hM : M ≠ 0) : IsPrimitiveRoot (zetaElt p M) M := by
  refine IsPrimitiveRoot.of_map_of_injective (f := (cycloLocal p M).subtype) ?_ Subtype.val_injective
  simpa [zetaElt, ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta] using Complex.isPrimitiveRoot_exp M hM
def zetaUnit (p : ℕ) {M : ℕ} (hM : M ≠ 0) : (cycloLocal p M)ˣ :=
  Units.ofPowEqOne (zetaElt p M) M (zetaElt_isPrimitiveRoot p hM).pow_eq_one hM
abbrev intRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationSubring C :=
  (NormedField.valuation (K := C)).valuationSubring
section Triple
variable {S : Scheme.{0}}
def IsTrivial {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen
def diagPull (A : Over S) (P : LB (A ⊗ A).left) : LB A.left := P.pull (lift (𝟙 A) (𝟙 A)).left
def IsSymmetricPair (h : ℕ) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension h A.hom ∧ P.IsLB ∧
    IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) ∧
    IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) ∧
    LBIso P (P.pull (lift (snd A A) (fst A A)).left)
example (A : Over S) [GrpObj A] : (1 : A ⟶ A) = toUnit A ≫ η[A] := rfl
def slice (A : Over S) (P : LB (A ⊗ A).left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  P.pull (lift (fst T A ≫ x) (snd T A)).left
def IsPrincipal (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  Out.RelAmple A (diagPull A P) ∧ ∀ (T : Over S) (x : T ⟶ A), IsTrivial (slice A P x) → x = 1
def DiagAmpleAlong (A : Over S) (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (t : S' ⟶ S) : Prop :=
  Out.RelAmple ((Over.pullback t).obj A) ((diagPull A P).pull (pullback.fst A.hom t))
def IsPrincipalAlong (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (t : S' ⟶ S) : Prop :=
  DiagAmpleAlong A P t ∧
    ∀ (T : Scheme.{0}) (τ : T ⟶ S') (x : Over.mk (τ ≫ t) ⟶ A), IsTrivial (slice A P x) → x = 1
abbrev Std (h M : ℕ) : Type := (Fin h → ZMod M) × (Fin h → ZMod M)
def stdForm {h M : ℕ} (a b : Std h M) : ZMod M := ∑ i, (a.1 i * b.2 i - a.2 i * b.1 i)
def IsLevel {h M : ℕ} (A : Over S) [GrpObj A] (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lv (a + b) = lv a * lv b) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g
def IsSymplectic {h M : ℕ} {R : Type} [CommRing R] (ζ : Rˣ) (s : S ⟶ Sp R) (A : Over S) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ a b, Out.WeilIs A (diagPull A P) (M : ℤ) (lv a) (lv b)
    (Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val)))
def IsPullbackTriple {h M : ℕ} {S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lv' : Std h M → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧
    φ₂ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ φ₂ ≫ (snd A A).left = (snd A' A').left ≫ φ ∧
    LBIso P' (P.pull φ₂) ∧
    ∀ a, (lv' a).left ≫ φ = f ≫ (lv a).left
end Triple
def IsSiegelFamily (h p : ℕ) {M : ℕ} (hM : M ≠ 0) (X : Scheme.{0}) (s : X ⟶ Sp (cycloLocal p M))
    (A : Over X) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over X) ⟶ A)) : Prop :=

  SmoothOfRelativeDimension (h * (h + 1) / 2) s ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧

  IsSymmetricPair h A P ∧ IsPrincipal A P ∧ IsLevel A lv ∧ IsSymplectic (zetaUnit p hM) s A P lv ∧

  (∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(p : C)‖ < 1 →
    ∀ (β : cycloLocal p M →+* intRing C)
      (B : Over (Sp (intRing C))) [GrpObj B] (P' : LB (B ⊗ B).left)
      (lv' : Std h M → (𝟙_ (Over (Sp (intRing C))) ⟶ B)),
      IsSymmetricPair h B P' → IsLevel B lv' → IsSymplectic (zetaUnit p hM) (spMap β) B P' lv' →
      IsPrincipalAlong B P' (spMap (intRing C).subtype) →
      DiagAmpleAlong B P' (spMap (IsLocalRing.residue (intRing C))) →
      ∃ y : Sp (intRing C) ⟶ X, y ≫ s = spMap β ∧ IsPullbackTriple B P' lv' A P lv y) ∧

  (∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X)
      (B : Over (Sp (DualNumber k))) [GrpObj B] (P' : LB (B ⊗ B).left)
      (lv' : Std h M → (𝟙_ (Over (Sp (DualNumber k))) ⟶ B)),
      P'.IsLB → IsPullbackTriple B P' lv' A P lv x → IsPullbackTriple B P' lv' A P lv (constPt x) → x = constPt x)
def SiegelFamilyExists : Prop :=
  ∀ (h p n : ℕ), 1 ≤ h → p.Prime → n.Prime → Odd n → n ≠ p →
    ∃ (M : ℕ) (hM : 3 ≤ M), (∃ j : ℕ, M = n ^ j) ∧
      ∃ (X : Scheme.{0}) (s : X ⟶ Sp (cycloLocal p M)) (A : Over X) (_ : GrpObj A) (P : LB (A ⊗ A).left)
        (lv : Std h M → (𝟙_ (Over X) ⟶ A)), IsSiegelFamily h p (M := M) (by omega) X s A P lv
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit


