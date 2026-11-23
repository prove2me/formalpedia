-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:20.803112+00:00
-- url     : https://prove2.me/theorems/511ce6d6-507c-42dd-909b-71c0dd7e343d
-- title:
--   Continuous On Fderiv Phi M
-- statement:
--   Definitions and structural lemmas for Continuous On Fderiv Phi M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiM.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace InfKA
def entryCLM (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
@[simp] lemma entryCLM_apply (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) : entryCLM a b M = M a b := rfl
def DkL (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) where
  toFun Y := fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) • (T.op k * projW T * T.op k⁻¹) +
      PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)
  map_add' Y Y' := by
    simp only [Matrix.mul_add, Matrix.add_mul, map_add, map_sub, add_mul, mul_add, sub_mul, mul_sub,
      add_smul, sub_smul, smul_add, smul_sub]
    abel
  map_smul' c Y := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, map_sub, smul_mul_assoc, mul_smul_comm,
      mul_sub, sub_mul, smul_sub, smul_eq_mul, RingHom.id_apply, smul_add]
    module
def Ek (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A M : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  φ (toMK k⁻¹ * A * toMK k) • DkL T μ x k M +
    φ (toMK k⁻¹ * A * toMK k * M - M * (toMK k⁻¹ * A * toMK k)) • Gint T μ x k
end InfKA
end ReciprocityTheory.ChartRestriction.DS.S7


