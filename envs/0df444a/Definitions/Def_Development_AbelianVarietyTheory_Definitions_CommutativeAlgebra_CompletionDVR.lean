-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_CompletionDVR
-- name    : Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_CompletionDVR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:27.651397+00:00
-- url     : https://prove2.me/theorems/c2c9a02f-94a2-4361-8701-7b20e493f29f
-- title:
--   Completion DVR
-- statement:
--   Definitions and structural lemmas for Completion DVR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/CompletionDVR.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA.Pt
open IsLocalRing
theorem completionDVR (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    (∃ _ : IsDomain (AdicCompletion (maximalIdeal W) W),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal W) W)) ∧
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal W) W)) (AdicCompletion (maximalIdeal W) W) ∧
    Function.Injective (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) ∧
    maximalIdeal (AdicCompletion (maximalIdeal W) W) =
      (maximalIdeal W).map (algebraMap W (AdicCompletion (maximalIdeal W) W)) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W, inferInstance,
    AdicCompletion.maximalIdeal_eq_map⟩
example : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2]))
      (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2]) ∧
    Function.Injective (algebraMap ℤ_[2] (AdicCompletion (maximalIdeal ℤ_[2]) ℤ_[2])) :=
  ⟨(completionDVR ℤ_[2]).2.1, (completionDVR ℤ_[2]).2.2.1⟩
example : ¬ IsUnit (algebraMap (PowerSeries ℚ)
    (AdicCompletion (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ)) PowerSeries.X) := fun h =>
  PowerSeries.X_irreducible.not_isUnit ((completionDVR (PowerSeries ℚ)).2.2.2.1.map_nonunit _ h)
end ReciprocityTheory.CA.Pt


