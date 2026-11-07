-- Prove2me | Definitions.Def_MeanOnlyProphet_rateOf
-- name    : MeanOnlyProphet_rateOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:05.073202+00:00
-- url     : https://prove2.me/theorems/4bde4262-d274-4615-a4ea-a81a58f1b2e4
-- title:
--   Input rate $r(t)=-n\log F(\theta(t))$
-- statement:
--   Let $F(x)=\mu((-\infty,x])$ be the common CDF of the values and $\theta$ a threshold function. The **input rate** is
--   $$
--   r(t)=-n\cdot\log F(\theta(t)),\qquad \log 0=-\infty .
--   $$
--   It is the expected number of the $n$ values exceeding $\theta(t)$ in the $n\to\infty$ scaling, and it is how the unknown distribution enters the finite-$n$ analysis. It is nonnegative and, for decreasing $\theta$, nondecreasing; it equals $+\infty$ where $F(\theta(t))=0$.
--
--   **Formalization Note** The rate takes values in $[0,\infty]$ (`ℝ≥0∞`): it is $+\infty$ exactly where $F(\theta(t))=0$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.2, p.28 (PDF p.29)

import Mathlib

open MeasureTheory

namespace MeanOnlyProphet

/-- **The common CDF `F`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711
(held version, sha256 c68bfec4…), App. A.2, p.28 (PDF p.29): "Let F be the common CDF of the n i.i.d.
variables". `cdfF μ x = μ((−∞, x])` as a real number. -/
noncomputable def cdfF (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Set.Iic x)).toReal

/-- **The input rate `r(t) = −n · log F(θ(t))`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2, p.28 (PDF p.29): "let
r(t) = −n · log F (θ(t)), with log 0 = −∞."

**Formalization Note.** The rate takes values in `ℝ≥0∞`: it is `+∞` exactly where `F(θ(t)) = 0`
(the paper's `log 0 = −∞`), and `ENNReal.ofReal (−n · log F(θ(t)))` otherwise (`log F ≤ 0` there). -/
noncomputable def rateOf (μ : Measure ℝ) (n : ℕ) (θ : ℝ → ℝ) (t : ℝ) : ENNReal :=
  if cdfF μ (θ t) = 0 then ⊤ else ENNReal.ofReal (-(n : ℝ) * Real.log (cdfF μ (θ t)))

end MeanOnlyProphet


