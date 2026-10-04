-- Prove2me | Definitions.Def_Yukon_ce524b49ffe83175501954a1
-- name    : Yukon_ce524b49ffe83175501954a1
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T00:19:02.968903+00:00
-- url     : https://prove2.me/theorems/ad191c9e-da3b-4f53-aaa2-01e34c61555d
-- title:
--   ProximityPrize.Benchmark.TargetLower
-- statement:
--   Source module ProximityPrize.Benchmark.TargetLower from a verified submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/207eb2212d947e27871c25e60dd3c1ad927955a1/ProximityPrize/Benchmark/TargetLower.lean
--
--   yukon-proof-operation:816ab128-5fb7-4db2-9901-482d5e3bf835; Yukon contributor: anonymous
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjhjOGE3YTk5NzgzZmIwOTA3NzZkZmQ3MWNjMDY1N2JhYjlkY2Y5NDhiMjE3N2JkNDI1YWU5OWYxNjQzMGY5YSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjgxNmFiMTI4LTVmYjctNGRiMi05OTAxLTQ4MmQ1ZTNiZjgzNTsgWXVrb24gY29udHJpYnV0b3I6IGFub255bW91cyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2NlNTI0YjQ5ZmZlODMxNzU1MDE5NTRhMSIsInYiOjJ9]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Definitions.Def_Yukon_03910bd6c65b3e776cef1c0b

/-!
# Lower challenge certificate for the ABF26 reduction threshold

The fixed extractor-error target is `2^(-128)`. The interface certifies one
admissible radius at which the executable IRS straight-line extractor's
combination-round error bound is at most that target, then scores the induced
spot-check error `(1 - δ)^t`, where `t = IRSProfile.repetitions = 128`.

This extractor certificate is the MCA-plus-list term from ABF26 Lemma 6.10. It
upper-bounds Definition 6.11's winning-set soundness, so the certificate also
establishes a conservative safe point for the exact combinatorial reduction
error; equality is not assumed.
-/

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

/-- Exact radius encoded in the trusted theorem type. -/
noncomputable def claimedRadius (numerator denominator : Nat) : ℝ≥0 :=
  (numerator : ℝ≥0) / (denominator : ℝ≥0)

/-- Error corresponding to a score in hundredths of a bit. -/
noncomputable def claimedError (centiBits : Nat) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100))

/-- The fixed ABF26 extractor-error target `2^(-128)`. -/
noncomputable def reductionTarget : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

/-- A lower certificate for the ABF26 reduction threshold.

`reduction` bounds the executable IRS extractor's certified combination-round
error at one safe radius. This implies the corresponding Definition 6.11
winning-set bound. `score` converts that radius to the spot-check term
`(1 - δ)^t`. A larger `centiBits` value is stronger. -/
structure ProtocolClaim
    (centiBits radiusNumerator radiusDenominator : Nat) : Prop where
  admissible : claimedRadius radiusNumerator radiusDenominator ∈
    Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance
  reduction :
    ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension
        IRSProfile.interleaving IRSProfile.domain
        (claimedRadius radiusNumerator radiusDenominator) ≤
      reductionTarget
  score :
    (1 - claimedRadius radiusNumerator radiusDenominator) ^
        IRSProfile.repetitions ≤
      claimedError centiBits

end ProximityPrize.Benchmark


