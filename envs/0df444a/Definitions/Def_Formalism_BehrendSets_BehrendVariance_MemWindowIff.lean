-- Prove2me | Definitions.Def_Formalism_BehrendSets_BehrendVariance_MemWindowIff
-- name    : Formalism_BehrendSets_BehrendVariance_MemWindowIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:20.826689+00:00
-- url     : https://prove2.me/theorems/7c312563-2499-411e-81a1-92af93426ce9
-- title:
--   Mem Window Iff
-- statement:
--   Definitions and structural lemmas for Mem Window Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/MemWindowIff.lean

import Mathlib
import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.BehrendSets.E4
open Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
end Formalism.BehrendSets.E4
namespace Formalism.BehrendSets
open Formalism.BehrendSets.Rand Formalism.BehrendSets.E4
end Formalism.BehrendSets


