-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndFacts
-- name    : CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndFacts
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:10.825967+00:00
-- url     : https://prove2.me/theorems/4c32b3d8-8815-54a7-98e0-69665b52df3b
-- title:
--   Ind Facts
-- statement:
--   Definitions and structural lemmas for Ind Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndFacts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
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
namespace CompanionTheory.Mirab
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
end CompanionTheory.Mirab


