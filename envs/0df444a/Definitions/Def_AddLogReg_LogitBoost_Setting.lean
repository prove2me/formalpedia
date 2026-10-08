-- Prove2me | Definitions.Def_AddLogReg_LogitBoost_Setting
-- name    : AddLogReg_LogitBoost_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:08.831502+00:00
-- url     : https://prove2.me/theorems/c3247580-9209-4fac-a633-d65ce72b0ade
-- title:
--   §4.3, pp. 351–352 — symmetric logistic (30), conditional log-likelihood (31), E_w with weight p(1−p), population LogitBoost step (Algorithm 3)
-- statement:
--   This file fixes the objects of §4.3 (LogitBoost, two classes, population version).
--
--   Let $X$ be a measurable space of features and let $\nu$ be a finite (in the theorems: probability) measure on $X\times\{0,1\}$, the joint law of the feature $x$ and the label. The label is encoded on the Booleans, and the **0/1 response** is
--   $$y^* = \begin{cases}1 & \text{label} = \texttt{true},\\ 0 & \text{label} = \texttt{false}.\end{cases}$$
--   Conditional expectations given $x$ are integrals against the regular conditional distribution $\nu(\cdot\mid x)$ of the label given $x$ (the disintegration of $\nu$).
--
--   1. The **symmetric logistic** (30): for a real number $t$,
--   $$p(t) = \frac{e^{t}}{e^{t}+e^{-t}},$$
--   and for a current additive fit $F : X\to\mathbb R$ one writes $p(x) = p(F(x))$.
--   2. The **conditional expected log-likelihood** at the update $F(x)+f(x)$ with $f(x)=t$, the conditional form of (31):
--   $$E\big[l(F+f)\mid x\big]\Big|_{f(x)=t} = E\Big[\,2y^*(F(x)+t) - \log\big(1+e^{2(F(x)+t)}\big)\ \Big|\ x\Big].$$
--   3. The **weighted conditional expectation** with a general weight $w(x,y)$ (p. 347):
--   $$E_w\big[g(x,y)\mid x\big] = \frac{E[w(x,y)\,g(x,y)\mid x]}{E[w(x,y)\mid x]}.$$
--   4. The **working response** and **weight** of Algorithm 3, step 2(a):
--   $$z = \frac{y^*-p(x)}{p(x)(1-p(x))},\qquad w(x) = p(x)(1-p(x)).$$
--   5. The **population LogitBoost step** (Algorithm 3, steps 2(b)–(c)): the weighted least-squares fit of $z$ on $x$ is, in the population, the weighted conditional mean $f(x) = E_w(z\mid x)$ with $w(x) = p(x)(1-p(x))$, and the update is
--   $$F(x) \leftarrow F(x) + \tfrac12 E_w(z\mid x).$$
--
--   These are the objects about which Result 3 asserts that LogitBoost takes Newton steps on the expected Bernoulli log-likelihood.
--
--   **Formalization Note** Labels are `Bool`. The conditional law of the label given $x$ is Mathlib's `ν.condKernel x`. The symmetric logistic is written with the exact expression of (30), not as $1/(1+e^{-t})$, which differs by a factor 2 in $t$. The weight in $E_w$ is an explicit argument; in this mission it is always $p(x)(1-p(x))$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 351, §4.3 (30) and Algorithm 3; p. 352, (31) and the paragraph after (36); p. 347 (weighted conditional expectation)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

/-- The 0/1 response `y* = (y + 1)/2` of §4.3, encoded on `Bool`: `true ↦ 1`, `false ↦ 0`. -/
def ystar : Bool → ℝ
  | true => 1
  | false => 0

/-- The symmetric logistic (30): `p = e^{t} / (e^{t} + e^{−t})`, evaluated at `t = F(x)`. -/
noncomputable def symLogistic (t : ℝ) : ℝ :=
  Real.exp t / (Real.exp t + Real.exp (-t))

variable {X : Type*} [MeasurableSpace X]

/-- The conditional form of the expected log-likelihood (31) at the update `F(x) + f(x)` with
`f(x) = t`: `E[2y*(F(x) + t) − log(1 + e^{2(F(x)+t)}) | x]`, the integral against the conditional
law `ν.condKernel x` of the label given `x` under the joint law `ν` of `(x, y)`. -/
noncomputable def condLogLik (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ) (x : X)
    (t : ℝ) : ℝ :=
  ∫ b, (2 * ystar b * (F x + t) - Real.log (1 + Real.exp (2 * (F x + t)))) ∂(ν.condKernel x)

/-- The weighted conditional expectation of p. 347 with a general weight `w(x, y)`:
`E_w[g(x, y) | x] = E[w(x, y) g(x, y) | x] / E[w(x, y) | x]`. -/
noncomputable def wCondExpBy (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (w : X → Bool → ℝ)
    (g : X → Bool → ℝ) (x : X) : ℝ :=
  (∫ b, w x b * g x b ∂(ν.condKernel x)) / ∫ b, w x b ∂(ν.condKernel x)

/-- The working response of Algorithm 3, step 2(a): `z = (y* − p(x)) / (p(x)(1 − p(x)))`, with
`p(x)` given by (30) from the current `F`. -/
noncomputable def workingResponse (F : X → ℝ) (x : X) (b : Bool) : ℝ :=
  (ystar b - symLogistic (F x)) / (symLogistic (F x) * (1 - symLogistic (F x)))

/-- The weight of Algorithm 3, step 2(a): `w(x) = p(x)(1 − p(x))`, a function of `x` only. -/
noncomputable def logitWeight (F : X → ℝ) (x : X) (_ : Bool) : ℝ :=
  symLogistic (F x) * (1 - symLogistic (F x))

/-- One step of LogitBoost (Algorithm 3, steps 2(b)–(c)), population version: the weighted
least-squares fit of `z` on `x` is the weighted conditional mean `f(x) = E_w(z | x)` with
`w(x) = p(x)(1 − p(x))`, and the update is `F(x) ← F(x) + ½ f(x)`. -/
noncomputable def logitBoostStep (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ)
    (x : X) : ℝ :=
  F x + (1 / 2) * wCondExpBy ν (logitWeight F) (workingResponse F) x

end AddLogReg.LogitBoost


