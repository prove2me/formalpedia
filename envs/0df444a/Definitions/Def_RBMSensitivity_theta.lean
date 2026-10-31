-- Prove2me | Definitions.Def_RBMSensitivity_theta
-- name    : RBMSensitivity_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:45.51729+00:00
-- url     : https://prove2.me/theorems/98c22b5b-bdd6-40c0-8a74-e93688c0080e
-- title:
--   The time averages $\theta_t$
-- statement:
--   For $x\in G$ and $t>0$,
--   $$\theta_t(\alpha):=\frac 1t\int_0^t\mathbb E[f(Z^{\alpha,x}(s))]\,ds,\qquad\alpha\in U.$$
--
--   The proof of the goal theorem passes from finite-horizon derivatives to the stationary one through these averages.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §9, p.35

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `θ_t(α) := (1/t) ∫_0^t E[f(Z^{α,x}(s))] ds`: arXiv:1907.00472v2, §9, p.35.

**Formalization Note.** Defined for `t > 0` in the paper. Here the time index `t` is real, and it is
used only with `0 < t`. Inside the integral, `s` is in `[0, t]`, so `s.toNNReal` is `s`. -/
noncomputable def theta {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → E J → ℝ≥0 → Ω → E J) (f : E J → ℝ) (x : E J) (t α : ℝ) : ℝ :=
  (1 / t) * ∫ s in (0 : ℝ)..t, ∫ ω, f (Z α x s.toNNReal ω) ∂P

end RBMSensitivity


