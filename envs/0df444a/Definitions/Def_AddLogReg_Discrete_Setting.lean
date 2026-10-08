-- Prove2me | Definitions.Def_AddLogReg_Discrete_Setting
-- name    : AddLogReg_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:52.916777+00:00
-- url     : https://prove2.me/theorems/98632b29-7dab-443f-a025-654b6d836265
-- title:
--   §4.1, pp. 345–347 and Algorithm 1 — J(F) = E e^{−yF(x)}, weighted expectations E_w(·|x), E_w, the classifier (18), err and the line-search coefficient (20)
-- statement:
--   The two-class population setting of Results 1 and 2 of Friedman, Hastie and Tibshirani (2000), with the objects of the population version of Discrete AdaBoost.
--
--   Let $X$ be a measurable space of features and let $\nu$ be a probability law of the pair $(x, y)$ on $X \times \{-1, 1\}$. Labels are encoded as Booleans, with $\operatorname{sgn}(\mathrm{true}) = 1$ and $\operatorname{sgn}(\mathrm{false}) = -1$; the paper's $y$ is $\operatorname{sgn}(b)$. The conditional law of $y$ given $x$ is the disintegration kernel $\nu(\cdot \mid x)$ of $\nu$. For a function $F : X \to \mathbb R$:
--
--   1. the **exponential criterion** (11) is
--   $$J(F) = E\big(e^{-yF(x)}\big) \in [0, \infty],$$
--   a lower Lebesgue integral, so that $J(F) = \infty$ when $e^{-yF(x)}$ is not integrable;
--   2. with weight $w(x, y) = e^{-yF(x)}$, the **weighted conditional expectation** (p. 347) of $g(x, y)$ is
--   $$E_w[g(x, y) \mid x] = \frac{E[w(x, y)\, g(x, y) \mid x]}{E[w(x, y) \mid x]},$$
--   and the **weighted expectation** is $E_w[g(x, y)] = E[w(x, y) g(x, y)] / E[w(x, y)]$;
--   3. a classifier $f : X \to \mathbb R$ is **$\pm 1$-valued** if $f(x) \in \{-1, 1\}$ for every $x$;
--   4. the **Newton-like classifier** (18) is $f(x) = 1$ if $E_w(y \mid x) > 0$ and $f(x) = -1$ otherwise;
--   5. the **weighted misclassification error** of $f$ is $\mathrm{err} = E_w[1_{[y \neq f(x)]}]$;
--   6. the **line-search coefficient** (20) is $c = \tfrac12 \log\big((1 - \mathrm{err})/\mathrm{err}\big)$.
--
--   These are the objects in terms of which the paper shows that population Discrete AdaBoost takes Newton-like steps on $J$ followed by an exact line search.
--
--   **Formalization Note** $J$ takes values in $[0, \infty]$. $E_w$ and $E_w(\cdot \mid x)$ are ratios of Bochner integrals. The conditional one is a finite sum over the two labels and is well defined at every $x$; the unconditional one carries its intended meaning only when $F$ is measurable and $J(F) < \infty$, and every theorem that uses it assumes this. The conditional expectation given $x$ is the integral against `ν.condKernel x`. `lineSearchCoeff` is the bare formula; the theorems assume $0 < \mathrm{err} < 1$ wherever it is used for a minimization claim.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 338, Algorithm 1; p. 345, §4.1 (11); p. 347, weighted conditional expectation, (17), (18), (20)

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

variable {X : Type*} [MeasurableSpace X]

/-- The (unconditional) weighted expectation with weight `w(x, y) = e^{−yF(x)}`:
`E_w[g(x, y)] = E[w(x, y) g(x, y)] / E[w(x, y)]`, expectations under the joint law `ν`. -/
noncomputable def wExp (ν : Measure (X × Bool)) (F : X → ℝ) (g : X → Bool → ℝ) : ℝ :=
  (∫ z, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * F z.1)) * g z.1 z.2 ∂ν) /
    ∫ z, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * F z.1)) ∂ν

/-- A classifier with values in `{−1, 1}`: `f(x) ∈ {−1, 1}` for every `x`. -/
def IsPMOne (f : X → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

/-- The Newton-like choice (18) of the classifier:
`f(x) = 1` if `E_w(y | x) > 0`, and `f(x) = −1` otherwise. -/
noncomputable def newtonClassifier (ν : Measure (X × Bool)) [IsFiniteMeasure ν] (F : X → ℝ)
    (x : X) : ℝ :=
  if 0 < AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x then 1 else -1

/-- The weighted misclassification error `err = E_w[1_{[y ≠ f(x)]}]` of a classifier `f`. -/
noncomputable def err (ν : Measure (X × Bool)) (F : X → ℝ) (f : X → ℝ) : ℝ :=
  wExp ν F (fun x b => if AddLogReg.ExpCrit.sgn b ≠ f x then 1 else 0)

/-- The line-search coefficient (20): `c = ½ log ((1 − err) / err)`. -/
noncomputable def lineSearchCoeff (e : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 - e) / e)

end AddLogReg.Discrete


