-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_GreedySplittingPrincipalTorusExists
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_GreedySplittingPrincipalTorusExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:39.805041+00:00
-- url     : https://prove2.me/theorems/2fc341ce-033f-4f71-bd97-d89f9ddb03a8
-- title:
--   Greedy Splitting Principal Torus Exists
-- statement:
--   Definitions and structural lemmas for Greedy Splitting Principal Torus Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/GreedySplittingPrincipalTorusExists.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIntegersSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ThickSplitRealSpanBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_DivSqLeOfForallDivAddSqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory
end GlobalTheory


