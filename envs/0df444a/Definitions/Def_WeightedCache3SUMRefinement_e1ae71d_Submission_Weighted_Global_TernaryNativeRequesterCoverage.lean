-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:36:30.535289+00:00
-- url     : https://prove2.me/theorems/d3ca906a-3721-4c9a-8805-b531e5b6871a
-- title:
--   TernaryNativeRequesterCoverage
-- statement:
--   Definitions and structural lemmas for TernaryNativeRequesterCoverage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


