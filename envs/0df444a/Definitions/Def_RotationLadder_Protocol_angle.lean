-- Prove2me | Definitions.Def_RotationLadder_Protocol_angle
-- name    : RotationLadder_Protocol_angle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:33.750334+00:00
-- url     : https://prove2.me/theorems/27b815a7-be3d-4c35-90ce-5cd5973603e9
-- title:
--   Rotation angle $2\theta_i$ of a level
-- statement:
--   The state $|H_i\rangle$ implements a rotation by $2\theta_i$, the angle listed in Table I of the paper. Level 0 gives $\pi/4$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3, Table I

import Mathlib
import Definitions.Def_RotationLadder_Protocol_theta

namespace RotationLadder.Protocol

/-- **The rotation angle of a level.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, p. 3, Table I: "Rotation by angle `2θ_i` implementable using an `|H_i⟩` state". -/
noncomputable def angle (i : ℕ) : ℝ := 2 * theta i

end RotationLadder.Protocol


