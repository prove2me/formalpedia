-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:31.750164+00:00
-- url     : https://prove2.me/theorems/707893b8-317c-459a-861d-a7658a8f7cc7
-- title:
--   PPoint Ideal Multi Proj
-- statement:
--   Definitions and structural lemmas for PPoint Ideal Multi Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPointIdealMultiProj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace PointIdealMultiProj
variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}
def coneWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1
end PointIdealMultiProj
end
end GroundTheory.Heights₂.Heights.NumbersDVR


