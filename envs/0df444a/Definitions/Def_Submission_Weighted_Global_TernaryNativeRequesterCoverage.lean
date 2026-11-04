-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
-- name    : Submission_Weighted_Global_TernaryNativeRequesterCoverage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:22:37.403885+00:00
-- url     : https://prove2.me/theorems/65f9f2bd-9906-4233-bf7e-584eda226fb6
-- title:
--   Ternary Native Requester Coverage
-- statement:
--   Definitions and structural lemmas for Ternary Native Requester Coverage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeRequesterCoverage
open TernarySignedReduction TernarySignedDigits TernaryExtensionEncoding
set_option maxHeartbeats 2500000
variable {p : ℕ} [Fact p.Prime]
def field {J : ℕ} (v : Coordinate J→ℤ) : Coordinate J→ZMod p := fun k => (v k : ZMod p)
def sourceLeft {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (b : ℤ) : Fin r→ZMod p := H (field (leftRaw U radix J b))
def sourceRight {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (c : ℤ) : Fin r→ZMod p := H (field (rightRaw U radix J c))
def position (J t : ℕ) : ℕ := t/(2^J)
def target {J r : ℕ} (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (U radix : ℕ) (A : ℕ→ℤ) (t : ℕ) : ℤ :=
  (coefficientCode (H (field (requesterRaw U radix J (A (position J t))
    (TernaryCarryCode.carryFromCode J (t%(2^J)))))) : ℕ)
end ThreeSum.WeightedGlobalNativeRequesterCoverage


