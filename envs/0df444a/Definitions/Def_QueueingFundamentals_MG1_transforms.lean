-- Prove2me | Definitions.Def_QueueingFundamentals_MG1_transforms
-- name    : QueueingFundamentals_MG1_transforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:24:28.513197+00:00
-- url     : https://prove2.me/theorems/e154e1d0-9da3-49a6-b950-7d3f5fc4fb68
-- title:
--   Laplace–Stieltjes transforms, convolution powers and the M/G/1 busy-period equation
-- statement:
--   For a probability distribution $F$ on $[0,\infty)$ and complex $s$ the **Laplace–Stieltjes transform** is
--
--   $$
--   F^*(s) = \int_0^\infty e^{-st}\,dF(t).
--   $$
--
--   The same formula with the integral over the whole real line defines the two-sided transform of a distribution on $\mathbb R$; the book uses it in §6.2 for the law of $U = S - T$ in the G/G/1 queue.
--
--   The $n$-fold convolution $G^{(n)}$ of a distribution $G$ with itself is defined by $G^{(0)} = $ the unit mass at $0$ and $G^{(n+1)} = G^{(n)} * G$.
--
--   For an M/G/1 queue with arrival rate $\lambda$ and service distribution $B$, a distribution $G$ on $[0,\infty)$ satisfies the **busy-period equation** if for every $x$
--
--   $$
--   G(x) = \int_0^x \sum_{n=0}^{\infty} \frac{e^{-\lambda t}(\lambda t)^n}{n!}\, G^{(n)}(x-t)\,dB(t),
--   $$
--
--   where $G(x)$ denotes the distribution function. The equation expresses that the busy period is the first service time plus one independent busy period for each arrival during that service.
--
--   **Formalization Note** `lst μ s` is `∫ exp(-s t) dμ(t)` for complex `s`, integrated over all of `ℝ`; for a measure concentrated on `[0,∞)` this is the book's $\int_0^\infty$. It is a Bochner integral and returns `0` where the integrand is not integrable. `convPow` uses Mathlib's additive convolution `Measure.conv`. In `IsBusyPeriodEquation` the distribution functions are `(G (Iic x)).toReal` and the integral is over `t ≤ x`, which is the book's `∫_0^x` when `B` lives on `[0,∞)`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.236–239, LSTs B*(s), W*(s), G*(s) and Eq. (5.36); p.285, two-sided LST U*(s)

import Mathlib

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- The Laplace–Stieltjes transform `F*(s) = ∫ e^{-st} dF(t)` of a measure `μ` on `ℝ`, at a complex
argument `s`, integrated over all of `ℝ` (a Bochner integral: `0` where the integrand is not
integrable). For a distribution on `[0, ∞)` it is the book's `∫_0^∞ e^{-st} dF(t)`, used for `B*`,
`W*`, `W_q*`, `G*` in §§5.1.5–5.1.6 (pp.236–240) and for `A*` in §6.1; for the law of
`U = S − T` it is the two-sided LST `U*(s)` of §6.2 (p.285). -/
noncomputable def lst (μ : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ t, Complex.exp (-(s * (t : ℂ))) ∂μ

/-- The `n`-fold convolution `G^{(n)}` of a measure `G` on `ℝ` with itself; `G^{(0)}` is the unit
mass at `0` (p.239). -/
noncomputable def convPow (G : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convPow G n).conv G

/-- The busy-period equation (5.36) (p.239) for a candidate busy-period distribution `G`, in the
book's CDF form: for every `x`,
`G(x) = ∫_0^x ∑_{n ≥ 0} (e^{-λt}(λt)^n / n!) G^{(n)}(x - t) dB(t)`,
with `G(x) = G((-∞, x])` and the integral over `t ≤ x` (the service distribution `B` lives on
`[0, ∞)`). -/
def IsBusyPeriodEquation (lam : ℝ) (B G : Measure ℝ) : Prop :=
  ∀ x : ℝ, (G (Set.Iic x)).toReal =
    ∫ t in Set.Iic x,
      ∑' n : ℕ, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) *
        ((convPow G n) (Set.Iic (x - t))).toReal ∂B

end QueueingFundamentals.MG1


