-- Prove2me | Definitions.Def_RotationLadder_Protocol_ladderProb
-- name    : RotationLadder_Protocol_ladderProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:33.066825+00:00
-- url     : https://prove2.me/theorems/a69d7db9-a181-4681-9bad-c201862c093b
-- title:
--   Upward probability $p_{0,i}$ of the ladder
-- statement:
--   For a level $i\ge0$, the probability that the circuit of Fig. 2 applied to $|H_0\rangle|H_i\rangle$ gives outcome 0 is
--
--   $$p_{0,i}=\cos^2\theta_i\cos^2\theta_0+\sin^2\theta_i\sin^2\theta_0 .$$
--
--   It is the probability of moving one level up the ladder.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_theta

namespace RotationLadder.Protocol

/-- **The upward probability `p_(0,i)`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 3: "`p_(0,i) = cos² θ_i cos² θ_0 + sin² θ_i sin² θ_0`". -/
noncomputable def ladderProb (i : ℕ) : ℝ :=
  Real.cos (theta i) ^ 2 * Real.cos (theta 0) ^ 2 +
    Real.sin (theta i) ^ 2 * Real.sin (theta 0) ^ 2

end RotationLadder.Protocol


