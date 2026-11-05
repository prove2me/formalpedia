-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:26:52.552357+00:00
-- url     : https://prove2.me/theorems/03f8f652-29e8-4299-8ac6-e1ce00714d25
-- title:
--   TernaryNativeCoverWitness
-- statement:
--   Definitions and structural lemmas for TernaryNativeCoverWitness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCoverWitness.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


