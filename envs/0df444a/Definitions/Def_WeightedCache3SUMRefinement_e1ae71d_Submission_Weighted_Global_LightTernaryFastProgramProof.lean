-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:44:44.269785+00:00
-- url     : https://prove2.me/theorems/4e80d1a0-e310-4f1e-bfc9-02241ae2453a
-- title:
--   LightTernaryFastProgramProof
-- statement:
--   Definitions and structural lemmas for LightTernaryFastProgramProof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryFastProgramProof.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeTime
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalFastProgramProof
open Light LightWeightedGlobalFastProgram LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def scanFree (M b p K κ n free : ℕ) : ℕ :=
  finish free (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
    (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))
def Receipt (M b p K κ n free c : ℕ) [Fact p.Prime] (μ ν : ℕ→ℤ) : Prop :=
  Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p)
    (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) c) ∧
  Seg ν free (header n (n^κ) (LightWeightedGlobalDimensions.r M n)
    (LightWeightedGlobalDimensions.J M b n (n^κ)) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
    (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) free c) ∧
  Seg ν (params free) (LightScales.values n) ∧
  LightWeightedGlobalGlobalPreludeProof.Menu ν (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
    (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ)) c ∧
  Kept μ ν free
def time (M b p K κ colorTime n : ℕ) : ℕ :=
  WeightedGlobalGlobalPreludeTime.uniformTime M b p K κ n+LightColorScanHost.time colorTime n+1000
end ThreeSum.LightWeightedGlobalFastProgramProof
end
end WeightedCache3SUMRefinement_e1ae71d


