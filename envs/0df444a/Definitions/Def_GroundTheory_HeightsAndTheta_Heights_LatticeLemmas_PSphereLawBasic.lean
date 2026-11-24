-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:07.815564+00:00
-- url     : https://prove2.me/theorems/f2727c09-43a2-4147-8648-31693571cf9e
-- title:
--   PSphere Law Basic
-- statement:
--   Definitions and structural lemmas for PSphere Law Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
namespace SphereLawBasic
def firstRow (N : ℕ) : (Fin 1 × Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun u j := u (0, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end SphereLawBasic
end
end GroundTheory.Heights₂.Heights


