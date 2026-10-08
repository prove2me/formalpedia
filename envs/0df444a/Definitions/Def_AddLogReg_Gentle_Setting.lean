-- Prove2me | Definitions.Def_AddLogReg_Gentle_Setting
-- name    : AddLogReg_Gentle_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:03.137659+00:00
-- url     : https://prove2.me/theorems/8ea598b2-f756-443f-a957-274bdfc17c79
-- title:
--   §4.4, pp. 353–354 — conditional criterion E(e^{−y(F(x)+f(x))}|x), E_w with w = e^{−yF(x)} (p. 347), P_w, population Gentle AdaBoost step (Algorithm 4), symmetric logistic
-- statement:
--   This file fixes the objects of §4.4 (Gentle AdaBoost, two classes, population version).
--
--   Let $X$ be a measurable space of features and let $\nu$ be a finite (in the theorems: probability) measure on $X\times\{-1,1\}$, the joint law of the feature $x$ and the label $y$. The label is encoded on the Booleans: $y = 1$ for `true` and $y = -1$ for `false`; the 0/1 response is $y^* = (y+1)/2$. Conditional expectations given $x$ are integrals against the regular conditional distribution $\nu(\cdot\mid x)$ of the label given $x$ (the disintegration of $\nu$), and $P(y = 1\mid x) = \nu(\{1\}\mid x)$.
--
--   Fix a current additive fit $F : X\to\mathbb R$.
--
--   1. The **conditional exponential criterion** at the update $F(x)+f(x)$ with $f(x) = t$:
--   $$J(F(x)+f(x))\Big|_{f(x)=t} = E\big(e^{-y(F(x)+t)}\,\big|\,x\big).$$
--   2. The **weighted conditional expectation** (p. 347), with weight $w(x,y) = e^{-yF(x)}$:
--   $$E_w\big[g(x,y)\mid x\big] = \frac{E[w(x,y)\,g(x,y)\mid x]}{E[w(x,y)\mid x]},$$
--   and the **weighted class probabilities** $P_w(y = b\mid x) = E_w[1_{[y=b]}\mid x]$.
--   3. The **population Gentle AdaBoost step** (Algorithm 4, steps 2(a)–(b)): in the population, the weighted least-squares fit of $y$ on $x$ with weights $w(x,y) = e^{-yF(x)}$ is the weighted conditional mean, so
--   $$F(x) \leftarrow F(x) + E_w(y\mid x).$$
--   4. The **symmetric logistic** of (37): for a real $t$,
--   $$p(t) = \frac{e^{t}}{e^{t}+e^{-t}},$$
--   and $p(x) = p(F(x))$.
--
--   These are the objects about which Result 4 asserts that Gentle AdaBoost takes Newton steps on $E e^{-yF(x)}$.
--
--   **Formalization Note** Labels are `Bool`. The conditional law of the label given $x$ is Mathlib's `ν.condKernel x`. The criterion is the conditional one, an integral against that kernel, because the Derivation of Result 4 differentiates conditionally on $x$; it is not a closed form with a free probability parameter. The symmetric logistic is written with the exact expression of (37), not as $1/(1+e^{-t})$, which differs by a factor 2 in $t$. The weights after step 2(c) are $e^{-yF(x)}$ up to the renormalization, which the ratio defining $E_w$ absorbs.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 353, §4.4, Algorithm 4 and Derivation of Result 4; p. 354, (37); p. 347 (weighted conditional expectation); p. 349 (y*)

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

variable {X : Type*} [MeasurableSpace X]

/-- The conditional exponential criterion at the update `F(x) + f(x)` with `f(x) = t`:
`E(e^{−y(F(x)+t)} | x)`, the integral against the conditional law `ν.condKernel x` of the label
given `x`. The Derivation of Result 4 writes it `J(F(x) + f(x))`. -/
noncomputable def condCritAt (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ) (x : X)
    (t : ℝ) : ℝ :=
  ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) ∂(ν.condKernel x)

/-- The weighted class probability `P_w(y = b | x) = E_w[1_{[y = b]} | x]`, with
`w(x, y) = e^{−yF(x)}`. -/
noncomputable def wProb (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ) (b : Bool)
    (x : X) : ℝ :=
  AddLogReg.ExpCrit.wCondExp ν F (fun _ b' => if b' = b then 1 else 0) x

/-- One step of Gentle AdaBoost (Algorithm 4, steps 2(a)–(b)), population version: the weighted
least-squares fit of `y` on `x` with weights `w(x, y) = e^{−yF(x)}` is the weighted conditional
mean `f(x) = E_w(y | x)`, and the update is `F(x) ← F(x) + f(x)`. -/
noncomputable def gentleStep (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ) (x : X) : ℝ :=
  F x + AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x

end AddLogReg.Gentle


