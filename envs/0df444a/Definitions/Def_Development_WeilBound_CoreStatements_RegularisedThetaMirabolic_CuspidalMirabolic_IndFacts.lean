-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndFacts
-- name    : Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndFacts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:45.68808+00:00
-- url     : https://prove2.me/theorems/803bb9a1-cf11-4eab-9a61-9318bd015229
-- title:
--   Ind Facts
-- statement:
--   Definitions and structural lemmas for Ind Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndFacts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
namespace PositivityTheory.Mirab
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
end PositivityTheory.Mirab


