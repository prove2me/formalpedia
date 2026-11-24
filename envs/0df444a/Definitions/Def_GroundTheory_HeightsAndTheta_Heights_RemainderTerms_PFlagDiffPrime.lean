-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:36.930746+00:00
-- url     : https://prove2.me/theorems/0c4c6555-d520-4477-b72d-bb2fcdd46ac5
-- title:
--   PFlag Diff Prime
-- statement:
--   Definitions and structural lemmas for PFlag Diff Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
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
namespace RestTerms
open MvPolynomial
noncomputable section
namespace FlagDiffPrime
variable {σ : Type} [DecidableEq σ]
def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i
end FlagDiffPrime
end
end RestTerms
end GroundTheory.Heights₂.Heights


