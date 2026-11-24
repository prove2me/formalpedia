-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:46.014491+00:00
-- url     : https://prove2.me/theorems/99e5f988-ab17-4a4b-9318-d69bf346b3d2
-- title:
--   Good Point Branch Slice
-- statement:
--   Definitions and structural lemmas for Good Point Branch Slice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
namespace GoodPointBranch
def consZero (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (Fin d → ℂ) →L[ℂ] ℂ) 0
    fun j => ContinuousLinearMap.proj j)
def consCLM (d : ℕ) : (ℂ × (Fin d → ℂ)) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (ℂ × (Fin d → ℂ)) →L[ℂ] ℂ)
    (ContinuousLinearMap.fst ℂ ℂ (Fin d → ℂ))
    fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin d → ℂ)))
end GoodPointBranch
end
end GroundTheory.Heights₂.Heights


