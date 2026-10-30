-- Prove2me | Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory
-- name    : StrictCompatLB_FullInhomogeneous_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:28.943154+00:00
-- url     : https://prove2.me/theorems/f3285d3c-3467-4a43-b1c3-38232a1817ed
-- title:
--   Continuous summable occupancy solutions of the JSQ(d) ODE
-- statement:
--   For load $\lambda$ and sample size $d$, an occupancy trajectory $q:[0,\infty)\to\mathcal Y$ starts at a specified $q^0$, is continuous in the full $\ell_1$ distance, and satisfies
--
--   $$
--   \dot q_i(t)=\lambda(q_{i-1}(t)^d-q_i(t)^d)-(q_i(t)-q_{i+1}(t)),\qquad i\ge1.
--   $$
--
--   Here $\mathcal Y$ is the published space of nonnegative, nonincreasing summable occupancy tails, with coordinate $q_0=1$ appended. Derivatives are within the nonnegative time axis, hence right derivatives at zero. Time is represented by nonnegative reals, so equality of trajectories imposes no condition on artificial negative-time extensions. Existence and uniqueness are not built into this predicate: they are assertions of the theorem for every $q^0\in\mathcal Y$, including states of infinite support.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, https://arxiv.org/abs/2008.07562v2, §2 p. 9 (Y), Theorem 3.4 p. 12, equation (3.3), and Remark 9 p. 16.

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Occupancy

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

/-- A continuous, summable occupancy solution of (3.3), arXiv:2008.07562v2 p. 12.
Time is nonnegative, so uniqueness does not constrain irrelevant negative-time extensions.
The reused trajectory predicate supplies the coordinate ODE and right derivative at zero.
Continuity here is in the full ell-one distance, not merely coordinatewise.
This predicate does not assert existence or uniqueness; both are theorem conclusions. -/
def IsSolution (lam : ℝ) (d : ℕ) (q₀ : ℕ → ℝ) (s : ℝ≥0 → ℕ → ℝ) : Prop :=
  s 0 = q₀ ∧
  (∀ t, MeanField.InY (s t)) ∧
  (∀ t, Tendsto (fun u : ℝ≥0 => PowerOfDUniversality.Fluid.l1dist (s u) (s t))
    (𝓝 t) (𝓝 0)) ∧
  PowerTwoChoices.Limit.IsTrajectory lam d (fun t => s (Real.toNNReal t))

end StrictCompatLB.FullInhomogeneous


