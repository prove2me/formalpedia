-- Prove2me | Definitions.Def_AddLogReg_Multiclass_Setting
-- name    : AddLogReg_Multiclass_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:03.092795+00:00
-- url     : https://prove2.me/theorems/c2ad24b7-f0f9-44db-8430-9414d87cbe8b
-- title:
--   §5, pp. 354–357 — J-class setting: y*_j, softmax (40), symmetric multiple logistic (39), multilogit log-likelihood, score/Hessian, LogitBoost (J classes) step, AdaBoost.MH criterion
-- statement:
--   This file fixes the objects of §5 (multiclass procedures, population version).
--
--   Let $J\ge 1$ be the number of classes, labelled $1,\dots,J$ (in Lean `Fin J`), and let $X$ be a measurable space of features. Let $\nu$ be a finite (in the theorems: probability) measure on $X\times\{1,\dots,J\}$, the joint law of the feature $x$ and the class. The classes are mutually exclusive, so the observed class is a single label $y$, and the **indicator responses** and the **$\{-1,1\}$ responses** are
--   $$y^*_j = \mathbf 1_{[y=j]},\qquad y_j = 2y^*_j-1 .$$
--   Conditional expectations given $x$ are integrals against the regular conditional distribution $\nu(\cdot\mid x)$ of the class given $x$ (the disintegration of $\nu$), and $p_j(x)=P(y_j=1\mid x)=\nu(\{j\}\mid x)$.
--
--   1. **Definition 1.** For a vector $p=(p_1,\dots,p_J)$ the **symmetric multiple logistic transformation** (39) is $F_j = \log p_j - \frac1J\sum_{k=1}^J \log p_k$, and for a vector $F$ the probabilities (40) are
--   $$p_j = \frac{e^{F_j}}{\sum_{k=1}^J e^{F_k}} .$$
--   For a current fit $F(x) = (F_1(x),\dots,F_J(x))$ the **model probabilities** are $p_j(x) = e^{F_j(x)}/\sum_k e^{F_k(x)}$.
--   2. **Multilogit log-likelihood with base class $b$.** For a vector $G$ with $G_b=0$, the log-likelihood of one observation is
--   $$l(G) = \sum_{j\ne b} y^*_j G_j - \log\Big(1+\sum_{k\ne b} e^{G_k}\Big),$$
--   and the **expected conditional log-likelihood** at the update $G+g$, with $G_j(x)=F_j(x)-F_b(x)$ the multilogit coordinates of the current fit, is $E\big(l(G+g)\mid x\big)$. The coordinate $g_b$ plays no role.
--   3. The explicit **partial derivative** $E(y^*_j\mid x) - e^{G_j(x)+g_j}/\big(1+\sum_{k\ne b}e^{G_k(x)+g_k}\big)$, the **score** $s_j(x)=E(y^*_j-p_j(x)\mid x)$ and the **Hessian** $H_{j,k}(x) = -p_j(x)(\delta_{jk}-p_k(x))$.
--   4. The **diagonal quasi-Newton step** in base-$b$ coordinates: $g_j = -s_j(x)/H_{j,j}(x)$ for $j\ne b$ and $g_b=0$; and the **symmetrization** $f_j = g_j - \frac1J\sum_{k=1}^J g_k$.
--   5. The **weighted conditional expectation** (p. 347) $E_w[g\mid x] = E[wg\mid x]/E[w\mid x]$, the **working response** $z_j = (y^*_j-p_j(x))/(p_j(x)(1-p_j(x)))$ and the **weight** $w_j = p_j(x)(1-p_j(x))$ of Algorithm 6, step 2(a).
--   6. The **population LogitBoost step (J classes)**, Algorithm 6, steps 2(a)–(b): with $f_j(x) = E_{w_j}(z_j\mid x)$,
--   $$F_j(x)\ \leftarrow\ F_j(x) + \frac{J-1}{J}\Big(f_j(x) - \frac1J\sum_{k=1}^J f_k(x)\Big).$$
--   7. The **AdaBoost.MH criterion** (§5, observation 1): $\sum_{j=1}^J E\,e^{-y_jG_j(x)}$, with each term $E\,e^{-y_jG_j(x)}$ the criterion of class $j$ against the rest.
--
--   These are the objects of Definition 1, Result 5 and Result 6.
--
--   **Formalization Note** Classes are `Fin J` with `[NeZero J]`; the conditional law of the class given $x$ is Mathlib's `ν.condKernel x`. The constants $1/J$ and $(J-1)/J$ are computed in $\mathbb R$. The criteria are lower Lebesgue integrals with values in $[0,\infty]$, so a non-integrable $e^{-y_jG_j}$ gives $+\infty$, not a junk $0$. The fixed base class $J$ of the page is a parameter $b$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, §5 and Definition 1 (39)–(40); p. 355, observation 1 and Algorithm 5; p. 356, Algorithm 6; p. 357, Derivation of Result 6, steps 1–3; p. 347 (weighted conditional expectation)

import Mathlib

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

variable {J : ℕ}

/-- The indicator response `y*_j = 1_{[class = j]}` of §5 for mutually exclusive classes: the
observed class is one label `y : Fin J`. -/
def ystar (y j : Fin J) : ℝ := if y = j then 1 else 0

/-- The `{−1, 1}` response `y_j = 2 y*_j − 1` of class `j` (Schapire and Singer, Algorithm 5). -/
def ypm (y j : Fin J) : ℝ := 2 * ystar y j - 1

/-- The probabilities of (40) from a vector `F = (F_1, …, F_J)`:
`p_j = e^{F_j} / Σ_{k=1}^J e^{F_k}`. -/
noncomputable def softmax (F : Fin J → ℝ) (j : Fin J) : ℝ :=
  Real.exp (F j) / ∑ k, Real.exp (F k)

/-- The symmetric multiple logistic transformation (39):
`F_j = log p_j − (1/J) Σ_{k=1}^J log p_k`. -/
noncomputable def symMultiLogit (p : Fin J → ℝ) (j : Fin J) : ℝ :=
  Real.log (p j) - (1 / (J : ℝ)) * ∑ k, Real.log (p k)

/-- Step 3 of the Derivation of Result 6: conversion of an update `g` to the symmetric
parametrization, `f_j = g_j − (1/J) Σ_{k=1}^J g_k`. -/
noncomputable def symmetrize (g : Fin J → ℝ) (j : Fin J) : ℝ :=
  g j - (1 / (J : ℝ)) * ∑ k, g k

/-- The multinomial log-likelihood of one observation with class `y` in the multilogit
parametrization with base class `b` (Derivation of Result 6, step 1):
`l(G) = Σ_{j ≠ b} y*_j G_j − log(1 + Σ_{k ≠ b} e^{G_k})`. The coordinate `G b` is not used
(the base coordinate is pinned at `0`). -/
noncomputable def logLik (b : Fin J) (G : Fin J → ℝ) (y : Fin J) : ℝ :=
  ∑ j ∈ Finset.univ.erase b, ystar y j * G j -
    Real.log (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (G k))

variable [NeZero J] {X : Type*} [MeasurableSpace X]

/-- `p_j(x) = P(y_j = 1 | x)`: the conditional probability of class `j` given `x` under the
joint law `ν` of (feature, class), via the disintegration `ν.condKernel`. -/
noncomputable def classProb (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (j : Fin J) (x : X) :
    ℝ :=
  (ν.condKernel x {j}).toReal

/-- The expected conditional log-likelihood `E(l(G + g) | x)` of step 1 of the Derivation of
Result 6, with base class `b` and with `G_j(x) = F_j(x) − F_b(x)` the multilogit coordinates of the
current symmetric fit `F` (so `G_b(x) = 0`); the update `g` has its base coordinate ignored. -/
noncomputable def baseLogLik (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ)
    (x : X) (b : Fin J) (g : Fin J → ℝ) : ℝ :=
  ∫ y, logLik b (fun j => F x j - F x b + g j) y ∂(ν.condKernel x)

/-- The partial derivative of `E(l(G + g) | x)` in `g_j` at a general `g`, written out:
`E(y*_j | x) − e^{G_j + g_j} / (1 + Σ_{k ≠ b} e^{G_k + g_k})`. -/
noncomputable def gradBase (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ)
    (x : X) (b : Fin J) (g : Fin J → ℝ) (j : Fin J) : ℝ :=
  (∫ y, ystar y j ∂(ν.condKernel x)) -
    Real.exp (F x j - F x b + g j) /
      (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F x k - F x b + g k))

/-- The score of step 1: `s_j(x) = E(y*_j − p_j(x) | x)` with `p_j(x)` the current model
probability (40). -/
noncomputable def score (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ)
    (x : X) (j : Fin J) : ℝ :=
  ∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)

/-- The Hessian of step 1: `H_{j,k}(x) = −p_j(x)(δ_{jk} − p_k(x))`. -/
noncomputable def hess (F : X → Fin J → ℝ) (x : X) (j k : Fin J) : ℝ :=
  -(softmax (F x) j * ((if j = k then 1 else 0) - softmax (F x) k))

/-- The quasi-Newton update of step 2 in base-`b` coordinates: the diagonal Newton step
`g_j = −s_j(x) / H_{j,j}(x)` for `j ≠ b`, and `g_b = 0`. -/
noncomputable def diagStep (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ)
    (x : X) (b j : Fin J) : ℝ :=
  if j = b then 0 else -(score ν F x j) / hess F x j j

/-- The weighted conditional expectation of p. 347 with a general weight `w(x, y)`:
`E_w[g(x, y) | x] = E[w(x, y) g(x, y) | x] / E[w(x, y) | x]`. -/
noncomputable def wCondExpBy (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (w : X → Fin J → ℝ)
    (g : X → Fin J → ℝ) (x : X) : ℝ :=
  (∫ y, w x y * g x y ∂(ν.condKernel x)) / ∫ y, w x y ∂(ν.condKernel x)

/-- The working response of class `j` in Algorithm 6, step 2(a)(i):
`z_j = (y*_j − p_j(x)) / (p_j(x)(1 − p_j(x)))`, with `p_j(x)` from (40). -/
noncomputable def workingResponse (F : X → Fin J → ℝ) (x : X) (y j : Fin J) : ℝ :=
  (ystar y j - softmax (F x) j) / (softmax (F x) j * (1 - softmax (F x) j))

/-- The weight of class `j` in Algorithm 6, step 2(a)(i): `w_j(x) = p_j(x)(1 − p_j(x))`, a
function of `x` only. -/
noncomputable def classWeight (F : X → Fin J → ℝ) (x : X) (j : Fin J) : ℝ :=
  softmax (F x) j * (1 - softmax (F x) j)

/-- One step of LogitBoost (J classes), Algorithm 6, steps 2(a)–(b), population version: the
weighted least-squares fit of `z_j` on `x` with weights `w_j` is the weighted conditional mean
`f_j(x) = E_{w_j}(z_j | x)`; then `f_j ← ((J − 1)/J)(f_j − (1/J) Σ_k f_k)` and
`F_j ← F_j + f_j`. -/
noncomputable def logitBoostJStep (ν : Measure (X × Fin J)) [IsFiniteMeasure ν]
    (F : X → Fin J → ℝ) (x : X) (j : Fin J) : ℝ :=
  let u : Fin J → ℝ := fun i =>
    wCondExpBy ν (fun x' _ => classWeight F x' i) (fun x' y => workingResponse F x' y i) x
  F x j + (((J : ℝ) - 1) / (J : ℝ)) * (u j - (1 / (J : ℝ)) * ∑ k, u k)

/-- The criterion of one class against the rest in AdaBoost.MH (§5, observation 1):
`E e^{−y_j g(x)}`, a lower Lebesgue integral in `[0, ∞]`. -/
noncomputable def critOne (ν : Measure (X × Fin J)) (j : Fin J) (g : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(ypm z.2 j * g z.1))) ∂ν

/-- The population criterion of AdaBoost.MH (§5, observation 1): `Σ_{j=1}^J E e^{−y_j G_j(x)}`. -/
noncomputable def critMH (ν : Measure (X × Fin J)) (G : Fin J → X → ℝ) : ℝ≥0∞ :=
  ∑ j, critOne ν j (G j)

end AddLogReg.Multiclass


