-- Prove2me | Definitions.Def_AddLogReg_ExpCrit_Setting
-- name    : AddLogReg_ExpCrit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:05.274031+00:00
-- url     : https://prove2.me/theorems/287b2c7c-5953-47a4-9345-6ab8586998bc
-- title:
--   §4.1, pp. 345–348 — labels y = ±1, P(y=b|x), the exponential criterion J(F) = E(e^{−yF(x)}) (11), E(e^{−yF(x)}|x), E_w (p. 347), the half log-odds (12), the Real AdaBoost step (23)
-- statement:
--   This file fixes the population setting of §4.1 of Friedman, Hastie and Tibshirani (2000) for two-class classification.
--
--   Let $X$ be a measurable space of features. The label $y$ takes the values $-1$ and $1$; in Lean it lives on `Bool`, with $\mathrm{sgn}(\mathrm{true}) = 1$ and $\mathrm{sgn}(\mathrm{false}) = -1$. Let $\nu$ be a probability measure on $X \times \{-1, 1\}$, the joint law of $(x, y)$, and let $\nu_X$ be its marginal on $X$. Disintegrating $\nu$ gives the conditional law of $y$ given $x$, and with it
--
--   1. the **conditional class probability** $P(y = b \mid x)$, for $b \in \{-1, 1\}$;
--   2. the **exponential criterion** (11), the expectation under the joint law
--   $$J(F) = E\big(e^{-yF(x)}\big) = \int e^{-yF(x)} \, d\nu(x, y) \in [0, \infty],$$
--   for a function $F : X \to \mathbb R$;
--   3. the **conditional criterion** at $F(x) = t$, $E(e^{-yt} \mid x)$, the integral of $e^{-yt}$ against the conditional law of $y$ given $x$;
--   4. the **weighted conditional expectation** of p. 347, with weight $w(x, y) = e^{-yF(x)}$,
--   $$E_w[g(x, y) \mid x] = \frac{E[w(x, y) g(x, y) \mid x]}{E[w(x, y) \mid x]};$$
--   5. the **half log-odds** (12),
--   $$F^\star(x) = \tfrac12 \log \frac{P(y = 1 \mid x)}{P(y = -1 \mid x)};$$
--   6. the **Real AdaBoost step** (23) for a current estimate $F$,
--   $$f(x) = \tfrac12 \log \frac{E_w[1_{[y=1]} \mid x]}{E_w[1_{[y=-1]} \mid x]}, \qquad w(x, y) = e^{-yF(x)}.$$
--
--   These are the objects of Lemma 1, Corollary 3 and Result 2: Lemma 1 says that $F^\star$ minimizes $J$, and Result 2 that one Real AdaBoost step from any $F$ lands on $F^\star$.
--
--   **Formalization Note** $P(y = b \mid x)$ is `(ν.condKernel x {b}).toReal`, read off Mathlib's conditional kernel of $\nu$; it is determined only for $\nu_X$-almost every $x$, so statements comparing it with joint expectations hold almost everywhere. $J$ is a lower Lebesgue integral with values in $[0, \infty]$, so a competitor $F$ with non-integrable $e^{-yF(x)}$ has $J(F) = \infty$ instead of the junk value $0$ of a Bochner integral. The conditional criterion and $E_w$ are integrals over the two-point label set and therefore always finite; the denominator of $E_w$ is strictly positive. $P(y = -1 \mid x)$ is kept as its own quantity, as printed, rather than replaced by $1 - P(y = 1 \mid x)$. In the half log-odds and in the step $f$, `Real.log` returns $0$ at $0$, so these formulas carry meaning only where the class probabilities are strictly between $0$ and $1$; the theorems that use them assume that.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 345, §4.1 (11), (12); p. 347, definition of E_w; p. 348, (23); p. 338, y = ±1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- The label `y ∈ {−1, 1}` of the paper, encoded on `Bool`: `true ↦ 1`, `false ↦ −1`. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

variable {X : Type*} [MeasurableSpace X]

/-- `P(y = b | x)`: the conditional law of the label given the feature `x`, read off the
disintegration `ν.condKernel` of the joint law `ν` of `(x, y)`. -/
noncomputable def condProb (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (b : Bool) (x : X) : ℝ :=
  (ν.condKernel x {b}).toReal

/-- The exponential criterion (11): `J(F) = E(e^{−yF(x)})`, the expectation under the joint
law `ν` of `(x, y)`, taken as a lower Lebesgue integral in `ℝ≥0∞` (so that a competitor with
non-integrable `e^{−yF(x)}` has `J = ⊤`). -/
noncomputable def J (ν : Measure (X × Bool)) (F : X → ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(sgn z.2 * F z.1))) ∂ν

/-- The conditional criterion `E(e^{−yF(x)} | x)` evaluated at `F(x) = t`: the integral of
`e^{−yt}` against the conditional law of `y` given `x`. -/
noncomputable def condCrit (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (x : X) (t : ℝ) : ℝ :=
  ∫ b, Real.exp (-(sgn b * t)) ∂(ν.condKernel x)

/-- The weighted conditional expectation of p. 347 with weight `w(x, y) = e^{−yF(x)}`:
`E_w[g(x, y) | x] = E[w(x, y) g(x, y) | x] / E[w(x, y) | x]`. -/
noncomputable def wCondExp (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ)
    (g : X → Bool → ℝ) (x : X) : ℝ :=
  (∫ b, Real.exp (-(sgn b * F x)) * g x b ∂(ν.condKernel x)) /
    ∫ b, Real.exp (-(sgn b * F x)) ∂(ν.condKernel x)

/-- The half log-odds (12): `F(x) = ½ log [P(y = 1 | x) / P(y = −1 | x)]`. -/
noncomputable def halfLogit (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (x : X) : ℝ :=
  (1 / 2) * Real.log (condProb ν true x / condProb ν false x)

/-- The Real AdaBoost stagewise step (23):
`f(x) = ½ log (E_w[1_{[y=1]} | x] / E_w[1_{[y=−1]} | x])`, with `w(x, y) = e^{−yF(x)}` for the
current estimate `F`. -/
noncomputable def realStep (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ) (x : X) : ℝ :=
  (1 / 2) * Real.log (wCondExp ν F (fun _ b => if b = true then 1 else 0) x /
    wCondExp ν F (fun _ b => if b = false then 1 else 0) x)

end AddLogReg.ExpCrit


