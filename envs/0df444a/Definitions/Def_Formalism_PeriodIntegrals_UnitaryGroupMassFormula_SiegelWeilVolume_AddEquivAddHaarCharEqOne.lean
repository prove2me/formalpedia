-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:45.112839+00:00
-- url     : https://prove2.me/theorems/66d70c08-d99c-5f68-bb3f-e0d14d2def69
-- title:
--   Add Equiv Add Haar Char Eq One
-- statement:
--   Definitions and structural lemmas for Add Equiv Add Haar Char Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/AddEquivAddHaarCharEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_coe
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_mul
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_one
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_add
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_mul
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix
section Equiv
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n M : ℕ}
theorem continuous_mulTup (D : Matrix (Fin n) (Fin n) K) : Continuous (mulTup (M := M) D) := by
  first
  | (unfold mulTup; fun_prop)
  | (simp only [mulTup]; fun_prop)
  | (unfold mulTup; continuity)
  | fun_prop
def tupEquiv (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Fin n → Fin M → K) ≃ₜ+ (Fin n → Fin M → K) where
  toFun := mulTup (D : Matrix (Fin n) (Fin n) K)
  invFun := mulTup (↑D⁻¹ : Matrix (Fin n) (Fin n) K)
  left_inv X := by rw [mulTup_mul, D.mul_inv, mulTup_one]
  right_inv X := by rw [mulTup_mul, D.inv_mul, mulTup_one]
  map_add' := mulTup_add _
  continuous_toFun := continuous_mulTup _
  continuous_invFun := continuous_mulTup _
end Equiv
section HermEquiv
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
theorem continuous_hermMap [IsTopologicalRing (R ⊗[F] E)] (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (hermMap R σ hσ D) := by
  first
  | (unfold hermMap; fun_prop)
  | (simp only [hermMap]; fun_prop)
  | (unfold hermMap; exact Continuous.subtype_mk (by fun_prop) _)
  | (unfold hermMap; continuity)
def hermEquiv [IsTopologicalRing (R ⊗[F] E)] (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) :
    HermR R σ n ≃ₜ+ HermR R σ n where
  toFun := hermMap R σ hσ D
  invFun := hermMap R σ hσ ↑D⁻¹
  left_inv S := by rw [hermMap_mul, D.mul_inv, hermMap_one]
  right_inv S := by rw [hermMap_mul, D.inv_mul, hermMap_one]
  map_add' S T := Subtype.ext (by simp [hermMap_coe, Matrix.mul_add, Matrix.add_mul])
  continuous_toFun := continuous_hermMap R σ hσ _
  continuous_invFun := continuous_hermMap R σ hσ _
end HermEquiv
section Haar
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
end Haar
section Cov
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]
def cTup (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  (addEquivAddHaarChar (tupEquiv (M := M) D))⁻¹
def cHerm (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  addEquivAddHaarChar (hermEquiv R σ hσ (n := n) D)
end Cov
end PI.DegenerateSiegelWeil.Scale


