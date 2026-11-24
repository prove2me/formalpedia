-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:47.47945+00:00
-- url     : https://prove2.me/theorems/c57bbdd3-7798-4717-9eb4-ab92d036d5a0
-- title:
--   PChange Of Variables Degree Piola
-- statement:
--   Definitions and structural lemmas for PChange Of Variables Degree Piola, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegreePiola.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ChangeOfVariablesDegree
variable {n : ℕ}
noncomputable def jacobian (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun k l => fderiv ℝ H x (Pi.single l 1) k
noncomputable def detCML : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }
noncomputable def entriesCLM : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l =>
    (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1))
noncomputable def killRow (i : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => if k = i then 0 else ContinuousLinearMap.proj k
noncomputable def cofactorFn (H : (Fin n → ℝ) → Fin n → ℝ) (i j : Fin n) (y : Fin n → ℝ) : ℝ :=
  Matrix.det (Matrix.of (Function.update (jacobian H y) i (Pi.single j 1)))
end ChangeOfVariablesDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


