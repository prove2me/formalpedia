-- Prove2me | Definitions.Def_CPDETrial_idxP
-- name    : CPDETrial_idxP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:18.79504+00:00
-- url     : https://prove2.me/theorems/7eb95075-16d1-4d7c-a822-4965d5277bad
-- title:
--   Canonical Gaussian space of the lookahead index
-- statement:
--   $\mathbb P_{\mathrm{idx}}$ is the law of an i.i.d. sequence $(\omega_0,\omega_1,\omega_2,\dots)$ of standard normal variables. In the cPDE index, $\omega_0$ plays the standardized prior uncertainty $(\theta_i-\mu^t_i)/\sqrt{\Sigma^t_{i,i}}$ of the sampled arm, and $\omega_r$ ($r\ge 1$) the standardized noise of the $r$-th lookahead observation from it. Expectations in the index (eq. (EC.8)) are taken under this measure.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 10, eqs. (9)–(10), and p. ec3, eq. (EC.8)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The canonical probability space of the lookahead index.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.1–3.2, eqs. (9)–(10) (p. 10) and (EC.8) (p. ec3).

`idxP` is the law of an i.i.d. sequence of standard normal variables `(ω 0, ω 1, ω 2, …)` on
`ℕ → ℝ`. In the definition of the cPDE index, coordinate `0` is the standardized prior
uncertainty `(θ_i − µ^t_i)/√(Σ^t_{i,i})` of the sampled arm, and coordinate `r ≥ 1` is the
standardized sampling noise of the `r`-th lookahead observation from that arm. -/
noncomputable def idxP : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

end CPDETrial


