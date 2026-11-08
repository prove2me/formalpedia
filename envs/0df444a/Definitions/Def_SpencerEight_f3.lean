-- Prove2me | Definitions.Def_SpencerEight_f3
-- name    : SpencerEight_f3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:15.901703+00:00
-- url     : https://prove2.me/theorems/4b7d2832-809b-424c-9cc2-79b2b678d5a6
-- title:
--   Shared statistic $f_3$
-- statement:
--   $$f_3(u):=\frac{u^6}{1-u^2}\quad(|u|<1),\qquad f_3(u):=+\infty\quad(|u|\ge1).$$
--
--   **Formalization Note** Valued in $[0,\infty]$, so that $+\infty$ is a genuine value. A real-valued version would change the sublevel sets in Lemma 8.65.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.19, p.118 (PDF p.118)

import Mathlib
open scoped ENNReal

namespace SpencerEight

/-- The shared statistic of the first row (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.19, p.118 (PDF p.118)): `f₃(u) := u⁶/(1 − u²)` for `|u| < 1` and `f₃(u) := +∞` for `|u| ≥ 1`.

**Formalization Note** Valued in `ℝ≥0∞`, so that `+∞` is really `+∞`: on `|u| < 1` the value is nonnegative and `ENNReal.ofReal` is exact. -/
noncomputable def f3 (u : ℝ) : ℝ≥0∞ :=
  if |u| < 1 then ENNReal.ofReal (u ^ 6 / (1 - u ^ 2)) else ⊤

end SpencerEight


