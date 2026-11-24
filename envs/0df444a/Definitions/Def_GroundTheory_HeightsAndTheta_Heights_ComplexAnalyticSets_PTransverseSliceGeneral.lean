-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:46.635435+00:00
-- url     : https://prove2.me/theorems/3fb6ad14-aa51-440a-82c7-a151cafbb471
-- title:
--   PTransverse Slice General
-- statement:
--   Definitions and structural lemmas for PTransverse Slice General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
namespace TransverseSliceGeneral
variable {n d : ℕ}
def gradAt (q : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun j => (aeval q).toLinearMap ∘ₗ (pderiv j).toLinearMap
def gradSpace (W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  (Submodule.restrictScalars ℂ W).map (gradAt q)
end TransverseSliceGeneral
end
end GroundTheory.Heights₂.Heights


