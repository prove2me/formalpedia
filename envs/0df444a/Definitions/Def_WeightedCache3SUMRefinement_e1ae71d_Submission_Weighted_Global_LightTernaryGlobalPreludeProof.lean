-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:34:48.018682+00:00
-- url     : https://prove2.me/theorems/159701a4-335e-4d84-80b9-57dbf7dba905
-- title:
--   LightTernaryGlobalPreludeProof
-- statement:
--   Definitions and structural lemmas for LightTernaryGlobalPreludeProof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryGlobalPreludeProof.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalGlobalPreludeProof
open Light LightWeightedGlobalGlobalPrelude
open LightExtensionBackendLayout hiding params
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
def time (M b p K κ n free : ℕ) : ℕ :=
  let U:=n^κ
  let J:=LightWeightedGlobalDimensions.J M b n U
  let d:=LightWeightedGlobalDimensions.dim M b p K n U
  let q:=p^d
  LightNatPower.time κ+LightScales.time n+LightWeightedGlobalDimensions.time M b p K n U+
    LightWeightedGlobalExtensionBackendSetup.time (backend free) d p q J+LightNatPower.time 6+5000
def Menu (ν : ℕ→ℤ) (base d p q J c : ℕ) [Fact p.Prime] : Prop :=
  ∀s<q*q, ∀i<J+2, ν (physical base d q J+s*(J+2)+i)=
    (LightExtensionSeedMatrix.value
      (TernaryExtensionEncoding.encodedMul
        (LightExtensionBackend.modulusMonic (factor base d p q J) c)) q p s
      (TernarySignedLayout.offset J i):ℤ)
end ThreeSum.LightWeightedGlobalGlobalPreludeProof
end
end WeightedCache3SUMRefinement_e1ae71d


