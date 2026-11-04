-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
-- name    : Submission_Weighted_Global_TernaryNativeCoverWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:33:17.474549+00:00
-- url     : https://prove2.me/theorems/603a1e2c-921b-43b8-916a-6d80c73029b1
-- title:
--   Ternary Native Cover Witness
-- statement:
--   Definitions and structural lemmas for Ternary Native Cover Witness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000
def leftRecord (i : I) (e : ActualEdge m) : SourceRecord (fixedLength m) (fixedAlpha m) I :=
  (i,⟨left e,left_mem_vertices e⟩)
def rightRecord (i : I) (e : ActualEdge m) : SourceRecord (fixedLength m) (fixedAlpha m) I :=
  (i,⟨right e,right_mem_vertices e⟩)
open WeightedGlobalOversizePrime
def nativeMaps (K m k : ℕ) (i : Fin (nativeFamily K m k).length) :
    Weight m (nativePrime K m) := (nativeFamily K m k)[i.val]
end ThreeSum.WeightedGlobalNativeCoverWitness


