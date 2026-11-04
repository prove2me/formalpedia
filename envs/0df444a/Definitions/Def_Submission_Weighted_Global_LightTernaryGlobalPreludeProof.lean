-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
-- name    : Submission_Weighted_Global_LightTernaryGlobalPreludeProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:42:46.269628+00:00
-- url     : https://prove2.me/theorems/03926c12-a036-4b5a-a645-5c1cde59f515
-- title:
--   Light Ternary Global Prelude Proof
-- statement:
--   Definitions and structural lemmas for Light Ternary Global Prelude Proof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryGlobalPreludeProof.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
set_option autoImplicit false
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


