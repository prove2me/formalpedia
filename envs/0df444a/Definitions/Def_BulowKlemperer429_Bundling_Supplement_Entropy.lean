-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Supplement_Entropy
-- name    : BulowKlemperer429_Bundling_Supplement_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:27.083191+00:00
-- url     : https://prove2.me/theorems/9e58efea-14f1-42d3-b10a-13739b2d4e95
-- title:
--   Functional entropy, cumulative entropy $L$ and the tail statistic $J$
-- statement:
--   For a law $\mu$ and a function $f$, the functional entropy is
--   $$\mathrm{Ent}_\mu(f)=\mathbb E_\mu[f\log f]-\mathbb E_\mu[f]\log\mathbb E_\mu[f],$$
--   with natural logarithm and $0\log0=0$; it is used for bounded nonnegative $f$. For a law of a real random variable $X$ with distribution function $F(t)=\Pr[X\le t]$, the cumulative entropy is $L(X)=\int_0^\infty-F(t)\log F(t)\,dt$. With $\varphi(q)=q+(1-q)\log(1-q)$ on $[0,1]$ and $\varphi(1)=1$, the tail statistic of a nonnegative $X$ is
--   $$J(X)=\int_0^\infty\varphi\big(\Pr[X>t]\big)\,dt .$$
--
--   These are the variation statistics of Section 4: $L$ tensorizes over independent coordinates, and $J=\mathbb E[X]-L(X)$ for bounded $X$ is the bundle term of Theorem 4.3.
--
--   **Formalization Note** $\mathrm{Ent}$ is a real number built from Bochner integrals, meaningful for bounded $f$. $L$ and $J$ are integrals of nonnegative integrands valued in $[0,\infty]$, so they need no integrability condition and $J$ applies to unbounded $X$, as the paper's definition does. $\varphi(1)=1$ is what the formula gives under Lean's convention $\log0=0$.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 12, §4, functional entropy; §4.1 p. 13 cumulative entropy L; §4.2 pp. 13–14 φ and J (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

/-- Section 4, p. 12: functional entropy `Ent(f) = E[f log f] − E[f] log E[f]` of a function `f`
under a law `μ`, natural logarithm, with `0 log 0 = 0` (Mathlib's `Real.log 0 = 0`).
Real (Bochner) integrals: every use has `f` bounded and nonnegative. -/
noncomputable def functionalEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂μ - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

/-- Section 4.1, p. 13: cumulative entropy `L(X) = ∫_0^∞ −F(t) log F(t) dt` of a law `μ` on `ℝ`,
with `F(t) = μ((−∞, t])`, as an extended nonnegative real (the integrand is nonnegative). -/
noncomputable def cumulativeEntropy (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.negMulLog (μ (Set.Iic t)).toReal)

/-- Section 4.2, p. 13: `φ(q) = q + (1 − q) log(1 − q)` on `[0, 1]`; at `q = 1` the formula gives
`1` because `Real.log 0 = 0`, which is the paper's convention `φ(1) := 1`. -/
noncomputable def phiTail (q : ℝ) : ℝ :=
  q + (1 - q) * Real.log (1 - q)

/-- Section 4.2, pp. 13–14: the tail statistic `J(X) = ∫_0^∞ φ(Pr[X > t]) dt` of a law `μ` on
`[0, ∞)`, the paper's definition for unbounded `X`, as an extended nonnegative real. -/
noncomputable def tailJ (μ : Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (phiTail (μ {x | t < (x : ℝ)}).toReal)

end BulowKlemperer429.Bundling.Supplement


