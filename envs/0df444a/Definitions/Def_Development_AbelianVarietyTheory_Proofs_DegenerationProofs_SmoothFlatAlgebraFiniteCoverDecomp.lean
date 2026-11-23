-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:46.400873+00:00
-- url     : https://prove2.me/theorems/c3e69675-15cc-41ca-a4b5-dea2c801717f
-- title:
--   Smooth Flat Algebra Finite Cover Decomp
-- statement:
--   Definitions and structural lemmas for Smooth Flat Algebra Finite Cover Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmoothFlatAlgebraFiniteCoverDecomp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.Smoothening
def GenOpen (K : Type) {R B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) : Prop :=
  IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom)
section
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
theorem GenOpen.comp {φ : B →ₐ[R] C} {ψ : C →ₐ[R] D} (h : GenOpen K φ) (h' : GenOpen K ψ) : GenOpen K (ψ.comp φ) := by
  unfold GenOpen at *
  have e : spMap (Algebra.TensorProduct.map (AlgHom.id K K) (ψ.comp φ)).toRingHom =
      spMap (Algebra.TensorProduct.map (AlgHom.id K K) ψ).toRingHom ≫
        spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x <;> simp
  rw [e]; infer_instance
def kaehlerAway (R : Type) {B : Type} [CommRing R] [CommRing B] [Algebra R B] (f : B) (D : Type) [CommRing D] [Algebra B D]
    [Algebra (Localization.Away f) D] [IsScalarTower B (Localization.Away f) D] :
    D ⊗[Localization.Away f] KaehlerDifferential R (Localization.Away f) ≃ₗ[D] D ⊗[B] KaehlerDifferential R B :=
  haveI : Algebra.FormallyEtale B (Localization.Away f) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  (LinearEquiv.baseChange (Localization.Away f) D _ _
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.Away f)).symm) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away f) D D _
end
abbrev Pts (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : Type 1 :=
  ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop
def Cov (K : Type) {R B : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] (E : Pts R B) : Prop :=
  ∃ l : List (Σ C : CommAlgCat.{0} R, B →ₐ[R] C), (∀ x ∈ l, Algebra.Smooth R x.1 ∧ GenOpen K x.2) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ x ∈ l, ∃ a' : x.1 →ₐ[R] R', a'.comp x.2 = a
section
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
def vanish (π : R) (E : Pts R B) : Ideal B where
  carrier := {b | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b}
  add_mem' hx hy R' _ _ a ha := by rw [map_add]; exact dvd_add (hx R' a ha) (hy R' a ha)
  zero_mem' R' _ _ a _ := by rw [map_zero]; exact dvd_zero _
  smul_mem' c x hx R' _ _ a ha := by rw [smul_eq_mul, map_mul]; exact (hx R' a ha).mul_left _
end
section
variable {R : Type} (K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)
include hπ
end
end GlobalTheory.SS.Smoothening
end


