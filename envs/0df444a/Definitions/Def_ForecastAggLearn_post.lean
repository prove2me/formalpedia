-- Prove2me | Definitions.Def_ForecastAggLearn_post
-- name    : ForecastAggLearn_post
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:19.111235+00:00
-- url     : https://prove2.me/theorems/46304e32-2c20-4ff9-b1b1-f132fc8ada0b
-- title:
--   Posterior of $\omega=1$ given the signals in $B$
-- statement:
--   Let $p_j^b=dC_j^b/d(C_j^0+C_j^1)$ be the density of the conditional law $C_j^b$ with respect to $C_j^0+C_j^1$ (it exists on every measurable space). For a set $B\subseteq[m]$ of signals and a signal profile $s$, put
--
--   $$
--   \operatorname{post}_B(s)=\frac{\mu\prod_{j\in B}p_j^1(s_j)}{\mu\prod_{j\in B}p_j^1(s_j)+(1-\mu)\prod_{j\in B}p_j^0(s_j)} .
--   $$
--
--   This is the posterior $\mathbb P(\omega=1\mid (s_j)_{j\in B})$. In the paper's notation, $r^*(s)=\operatorname{post}_{[m]}(s)$ is the Bayes-optimal forecast aggregating all signals (eq. (1)), $F_i(s)=\operatorname{post}_{A_i}(s)$ is the forecast of expert $i$ (eq. (2)), and $x_j(s_j)=\operatorname{post}_{\{j\}}(s)$ is the posterior after one signal.
--
--   **Formalization Note** The densities are Mathlib's `rnDeriv`. The quotient is computed in $[0,\infty]$ and converted to a real number; where the denominator is $0$ or $\infty$ (a null event) the value is $0$. The value always lies in $[0,1]$. Unlike the printed formulas (1)–(2) in terms of $x_j$, this is defined also for $\mu\in\{0,1\}$; it agrees with (1)–(2) whenever $0<\mu<1$ and every $x_j(s_j)\in(0,1)$.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, eqs. (1)–(2), p.9

import Mathlib

namespace ForecastAggLearn

open MeasureTheory

/-- **Posterior of ω = 1 given the signals in a set `B`.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.9, eqs. (1)–(2): `r*(s) = P(ω = 1 | s_1, …, s_m)`
and `F_i(s) = P(ω = 1 | (s_j)_{j∈A_i})`.

With the densities `p_j^b = dC_j^b / d(C_j^0 + C_j^1)`, the posterior given `(s_j)_{j∈B}` is

  `μ Π_{j∈B} p_j^1(s_j) / (μ Π_{j∈B} p_j^1(s_j) + (1 − μ) Π_{j∈B} p_j^0(s_j))`.

Then `r* = post μ P Finset.univ`, the expert forecast is `F_i = post μ P (A_i)` and the
single-signal posterior is `x_j = post μ P {j}`.

**Formalization Note.** The densities are `Measure.rnDeriv` (a fixed measurable version) against
`C_j^0 + C_j^1`, which dominates both conditional laws on every measurable signal space; no
finiteness or reference measure is assumed. The quotient is computed in `ℝ≥0∞` and converted with
`toReal`; on the null event where the denominator is `0` or `∞` the value is `0`. The value always
lies in `[0, 1]`. This is the formula (1)–(2) rewritten with likelihoods: it agrees with (1)–(2)
whenever `0 < μ < 1` and every `x_j(s_j) ∈ (0, 1)`, and is also defined for `μ ∈ {0, 1}`, where
(1)–(2) are `0/0`. -/
noncomputable def post {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m))
    (s : (j : Fin m) → S j) : ℝ :=
  let num : ENNReal :=
    ENNReal.ofReal μ * ∏ j ∈ B, (P j true).rnDeriv (P j false + P j true) (s j)
  let den : ENNReal := num +
    ENNReal.ofReal (1 - μ) * ∏ j ∈ B, (P j false).rnDeriv (P j false + P j true) (s j)
  (num / den).toReal

end ForecastAggLearn


