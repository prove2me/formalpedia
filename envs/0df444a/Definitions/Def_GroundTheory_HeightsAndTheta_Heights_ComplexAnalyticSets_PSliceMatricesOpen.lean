-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:48.20465+00:00
-- url     : https://prove2.me/theorems/0c935e45-4509-4f5e-a8e8-7540c86004f3
-- title:
--   PSlice Matrices Open
-- statement:
--   Definitions and structural lemmas for PSlice Matrices Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMatricesOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
def sliceDeriv {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin (k + 1) → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
  (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ) : _ →L[ℂ] _) ∘L
    ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L D))
end
end GroundTheory.Heights₂.Heights


