-- Prove2me | Definitions.Def_GaussDiffSVP_singleBudget
-- name    : GaussDiffSVP_singleBudget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:46.492455+00:00
-- url     : https://prove2.me/theorems/9c879530-f556-4ad4-8344-9c201c5674d4
-- title:
--   The single-sample schedule (166)
-- statement:
--   For a rational $0<\delta\le 1$, with $L_{\log} = \lceil\log_2(n+2)\rceil$,
--   $$w_n = \frac{1}{\lceil L_{\log}^{1+\delta/2}\rceil},\qquad h_n = \Big\lceil \frac{n}{L_{\log}^{1+\delta/3}}\Big\rceil,\qquad b_n = \Big\lceil \frac{n}{L_{\log}^{\delta/6}}\Big\rceil,$$
--   and $\ell_n = n w_n + L_{\log}$. This is the wider-shell schedule of the single-sample sampler; Theorem 5.2 covers it as well as the default schedule.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (166), App. C.3.2, p.86

import Mathlib
import Definitions.Def_GaussDiffSVP_Budget

namespace GaussDiffSVP

/-- The single-sample schedule (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (166), App. C.3.2, p.86), for the rational parameter
`0 < δ ≤ 1`: with `L_log = ⌈log₂(n + 2)⌉`,
`w_n = 1 / ⌈L_log^{1+δ/2}⌉`, `h_n = ⌈n / L_log^{1+δ/3}⌉`, `b_n = ⌈n / L_log^{δ/6}⌉`
(and `ℓ_n = n w_n + L_log`, see `Budget.ell`).

**Formalization Note.** Real powers are `Real.rpow` of the positive base `L_log ≥ 1`; the
ceilings are `Nat.ceil`, cast to `ℝ`. -/
noncomputable def singleBudget (δ : ℝ) : Budget where
  w n := 1 / (⌈(Llog n : ℝ) ^ (1 + δ / 2)⌉₊ : ℝ)
  h n := (⌈(n : ℝ) / (Llog n : ℝ) ^ (1 + δ / 3)⌉₊ : ℝ)
  b n := (⌈(n : ℝ) / (Llog n : ℝ) ^ (δ / 6)⌉₊ : ℝ)

end GaussDiffSVP


