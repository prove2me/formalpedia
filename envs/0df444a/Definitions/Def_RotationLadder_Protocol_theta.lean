-- Prove2me | Definitions.Def_RotationLadder_Protocol_theta
-- name    : RotationLadder_Protocol_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:45.15796+00:00
-- url     : https://prove2.me/theorems/3e6dfe71-dcea-482b-baa3-d1f3d50b3388
-- title:
--   Ladder angles $\theta_i$ with $\cot\theta_i=\cot^{i+1}(\pi/8)$
-- statement:
--   For an integer $i$, the ladder angle $\theta_i\in(0,\pi/2)$ is
--
--   $$\theta_i=\arctan\bigl(\tan^{\,i+1}(\pi/8)\bigr),\qquad\text{so that}\qquad \cot\theta_i=\cot^{\,i+1}\theta_0,\quad \theta_0=\frac{\pi}{8}.$$
--
--   These are the angles of the non-stabilizer states of the ladder. They shrink roughly geometrically as $i$ grows.
--
--   **Formalization Note** The index is an integer because the measurement outcome 1 at level 0 produces $\theta_{-1}=\pi/4$, the stabilizer state that the paper discards.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 2

import Mathlib

namespace RotationLadder.Protocol

/-- **The ladder angles `θ_i`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 2: "`|H_i⟩ = cos θ_i |0⟩ + sin θ_i |1⟩`, `cot θ_i = cot^(i+1) θ_0`",
with `θ_0 = π/8`.

`theta i = arctan (tan(π/8)^(i+1))`, the unique angle in `(0, π/2)` with
`cot θ_i = cot^(i+1)(π/8)`.

**Formalization Note.** The index is an integer because outcome 1 at `i = 0` produces
`θ_-1 = π/4`, the discarded stabilizer state of p. 2. The power is a `zpow`. -/
noncomputable def theta (i : ℤ) : ℝ :=
  Real.arctan (Real.tan (Real.pi / 8) ^ (i + 1))

end RotationLadder.Protocol


