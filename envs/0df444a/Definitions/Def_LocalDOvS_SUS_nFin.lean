-- Prove2me | Definitions.Def_LocalDOvS_SUS_nFin
-- name    : LocalDOvS_SUS_nFin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:20.042708+00:00
-- url     : https://prove2.me/theorems/97e6793c-4023-46d3-9161-3325c39afae8
-- title:
--   Final sample size $n_{\mathrm{fin}}$
-- statement:
--   The per-point sample size of the final comparison:
--
--   $$
--   n_{\mathrm{fin}}:=\Big\lfloor\frac{32\,\sigma^2\log(2/\alpha)}{\epsilon^2}\Big\rfloor+1 ,
--   $$
--
--   the least $n$ with $h(n,\sigma,\alpha)<\epsilon/4$ (Algorithm 2, line 22: "until the confidence half-widths are smaller than $\epsilon/4$").
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, line 22, p.16

import Mathlib
import Definitions.Def_LocalDOvS_SUS_alphaSUS

open scoped NNReal

namespace LocalDOvS.SUS

/-- The per-point sample size of the final sub-problem (Zhang–Zheng–Lavaei, arXiv:2012.02427v2,
Algorithm 2, line 22, p.16: "until the `1 − δ/(2T_max)` confidence half-widths are smaller than
`ε/4`"): `n_fin := ⌊32 σ² log(2/α) / ε²⌋ + 1`, the least `n` with `h(n, σ, α) < ε/4`.

**Formalization Note.** `α = alphaSUS N δ`; natural-number floor `⌊·⌋₊`. The inequality is
strict, as printed ("smaller than `ε/4`"), unlike the `≤ |S| · ε/80` of lines 7 and 17. -/
noncomputable def nFin (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) : ℕ :=
  ⌊32 * (σ : ℝ) ^ 2 * Real.log (2 / alphaSUS N δ) / ε ^ 2⌋₊ + 1

end LocalDOvS.SUS


