-- Prove2me | Definitions.Def_GaussDiffSVP_coolPairWeight
-- name    : GaussDiffSVP_coolPairWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:53.742289+00:00
-- url     : https://prove2.me/theorems/0e165b11-eaf2-481a-957b-8b7f69184ba2
-- title:
--   Cooling pair weight with eligibility, $K(x,y)$
-- statement:
--   $$K(x,y) = \mathbf 1[x,y\in S_r(a_0)]\ \mathbf 1[E_r(x-y)\in a_1(1\pm w_n)]\ \omega_r(x-y),$$
--   the weight of a pair before the common thinning factor: both endpoints in the input shell, the difference eligible (42), reweighted by $\omega_r$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (42), (45), p.28

import Mathlib
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_coolWeight

open scoped ENNReal

namespace GaussDiffSVP

/-- The cooling pair weight before the common thinning factor (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §5.1–5.2, pp.27–28, (42) and
(45)): `K(x, y) = 1[x, y ∈ S_r(a₀)] 1[E_r(x − y) ∈ a₁(1 ± w_n)] ω_r(x − y)`, with `a₀ = 1/(1 + u)`,
`a₁ = 4a₀ − 2` and `ω_r` the reweighting `coolWeight`. The activation probability (45) is
`q_j = (2^{−h_n}/D_j^+) K`.

**Formalization Note.** Values in `ℝ≥0∞`; "`E_r(x − y) ∈ a₁(1 ± w_n)`" is `x − y ∈ S_r(a₁)`. -/
noncomputable def coolPairWeight {n : ℕ} (w u r : ℝ) (x y : SuperlatSVP.E n) : ℝ≥0∞ := by
  classical
  exact if x ∈ shell r w (1 / (1 + u)) ∧ y ∈ shell r w (1 / (1 + u)) ∧
      x - y ∈ shell r w (4 / (1 + u) - 2) then
    ENNReal.ofReal (coolWeight w u r (x - y)) else 0

end GaussDiffSVP


