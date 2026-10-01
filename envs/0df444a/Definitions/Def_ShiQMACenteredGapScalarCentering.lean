-- Prove2me | Definitions.Def_ShiQMACenteredGapScalarCentering
-- name    : ShiQMACenteredGapScalarCentering
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-01T09:06:06.9718+00:00
-- url     : https://prove2.me/theorems/0ac95129-ff50-41cf-b6c9-2ff55d4a2c1d
-- title:
--   Scalar coin and affine-centering definitions for QMA amplification
-- statement:
--   Defines the ideal affine-centering coin probability, the corresponding centered acceptance map, and the logarithmic number of fair bits used for a dyadic approximation.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-affine-centering.lean#L7-L12; https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-dyadic-centering.lean#L27-L28

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace ShiQMACenteredGap

/-- The probability of the auxiliary coin used in affine acceptance centering. -/
noncomputable def centeringCoin (a b : ℝ) : ℝ := 1 - (a + b) / 2

/-- Run the verifier with probability one half, otherwise use the auxiliary coin.
This definition is scalar arithmetic, not yet a circuit implementation. -/
noncomputable def centeredAcceptance (u t : ℝ) : ℝ := (t + u) / 2

/-- Only logarithmically many fair bits are needed at inverse-polynomial gap. -/
def coinBits (q : Nat) : Nat := Nat.log 2 (4 * q) + 1

end ShiQMACenteredGap


