-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
-- name    : Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:44.199937+00:00
-- url     : https://prove2.me/theorems/0df8b11d-b723-494f-9bf8-fc25762eb049
-- title:
--   Sum Interlaced Bound Fails
-- statement:
--   Definitions and structural lemmas for Sum Interlaced Bound Fails, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SumInterlacedBoundFails.lean

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeIndexTer
open Finset
def phm (x : ℝ) : ℝ := ph (max x 1)
def chi (n : ℕ) : ℝ := if n = 0 then -1 else 0
end Formalism.LatticeIndexTer


