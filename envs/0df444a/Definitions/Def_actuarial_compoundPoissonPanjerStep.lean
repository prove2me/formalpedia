-- Prove2me | Definitions.Def_actuarial_compoundPoissonPanjerStep
-- name    : actuarial_compoundPoissonPanjerStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:47.825756+00:00
-- url     : https://prove2.me/theorems/6314a380-c1b1-4152-bb9e-15b98b7c5515
-- title:
--   Poisson frequency recursion from lower aggregate-loss coefficients
-- statement:
--   For a strictly positive aggregate amount s, the Poisson Panjer update uses the previous aggregate coefficients g(s-j), weighted by claim sizes j, severity masses f(j) and the rate-to-size factor λ/s. The j=0 summand vanishes algebraically and no recurrence requires the current value g(s) on its right side.
--
--   **Mathematical statement**
--
--   $$
--   P_\lambda(f,g;s)=\frac{\lambda}{s}\sum_{j=1}^{s}jf_jg_{s-j}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def compoundPoissonPanjerStep (rate : ℝ)
  (f g : ℕ → ℝ) (s : ℕ) : ℝ :=
  rate / (s : ℝ) *
    (∑ j ∈ Finset.range (s + 1), (j : ℝ) * f j * g (s - j))

end ActuarialValuation


