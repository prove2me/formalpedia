-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:13:41.370529+00:00
-- url     : https://prove2.me/theorems/80a905a4-657c-459c-84d6-cba8bb0babcf
-- title:
--   TernaryArenaInitialSeedHeader
-- statement:
--   Definitions and structural lemmas for TernaryArenaInitialSeedHeader, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaInitialSeedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
def replace (xs : List ℤ) (dB dC dP tB tC tP : ℕ) : List ℤ :=
  (((((xs.set 41 dB).set 42 dC).set 43 dP).set 44 tB).set 45 tC).set 46 tP
def patch (μ : ℕ→ℤ) (seed dB dC dP tB tC tP : ℕ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update μ (seed+41) dB) (seed+42) dC) (seed+43) dP) (seed+44) tB) (seed+45) tC) (seed+46) tP
end ThreeSum.WeightedGlobalArenaInitialSeedHeader
end
end WeightedCache3SUMRefinement_e1ae71d


