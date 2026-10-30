-- Prove2me | Definitions.Def_AnalystRanking_Revelation_fprob
-- name    : AnalystRanking_Revelation_fprob
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:31:16.048065+00:00
-- url     : https://prove2.me/theorems/8cc95051-a910-43d1-99aa-f90e2214f69f
-- title:
--   Forecast law $\Pr(m\mid s)$ under a strategy $(\sigma^h,\sigma^l)$
-- statement:
--   A (symmetric, possibly mixed) forecasting strategy is a pair $\sigma=(\sigma^h,\sigma^l)$ with $\sigma^h=\Pr(m=\hat h\mid s=h)$ and $\sigma^l=\Pr(m=\hat l\mid s=l)$ (p. 7). The induced law of the forecast $m\in\{\hat h,\hat l\}$ given the signal is
--   $$\Pr(\hat h\mid h)=\sigma^h,\quad \Pr(\hat l\mid h)=1-\sigma^h,\quad \Pr(\hat l\mid l)=\sigma^l,\quad \Pr(\hat h\mid l)=1-\sigma^l.$$
--
--   **Formalization Note** $\sigma$ is a pair of reals; statements restrict it to $[0,1]^2$. Signals and forecasts are `Bool` with `true` the high value.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 7

import Mathlib

namespace AnalystRanking.Revelation

/-- **Law of a forecast given the signal, under a strategy `σ = (σʰ, σˡ)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 7: "`σʰ_i = Pr(m_i = ĥ | s_i = h)` and `σˡ_i = (m_i = l̂ | s_i = l)`"; a symmetric
strategy is `σ_i = σ_j = σ`.

`fprob σ s m` is `Pr(m | s)`: `(h, ĥ) ↦ σʰ`, `(h, l̂) ↦ 1 − σʰ`, `(l, l̂) ↦ σˡ`, `(l, ĥ) ↦ 1 − σˡ`.

**Formalization Note.** A strategy is a pair `σ : ℝ × ℝ` with `σ.1 = σʰ`, `σ.2 = σˡ`; signals and
forecasts `{ĥ, l̂}` are `Bool` (`true = h`, `true = ĥ`). Statements restrict `σ` to `[0, 1]²`. -/
noncomputable def fprob (σ : ℝ × ℝ) (s m : Bool) : ℝ :=
  match s, m with
  | true, true => σ.1
  | true, false => 1 - σ.1
  | false, false => σ.2
  | false, true => 1 - σ.2

end AnalystRanking.Revelation


