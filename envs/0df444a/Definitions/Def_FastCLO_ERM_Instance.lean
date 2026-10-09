-- Prove2me | Definitions.Def_FastCLO_ERM_Instance
-- name    : FastCLO_ERM_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:18:24.093082+00:00
-- url     : https://prove2.me/theorems/dcbe4ee4-88f3-40f8-bfdb-bbcfab6d5b04
-- title:
--   A contextual linear optimization instance: law of X, conditional law of Y given X with ‖Y‖ ≤ 1, f*(x) = E[Y | X = x], the joint law and the i.i.d. sample law
-- statement:
--   An **instance** consists of a probability measure $\mu$ on $\mathbb R^p$, the law $\mathbb P_X$ of the features $X$, and a Markov kernel $\kappa$ from $\mathbb R^p$ to $\mathbb R^d$, the conditional law of the cost vector $Y$ given $X = x$. The costs are bounded: for every $x$, $\kappa(x)$ gives probability $0$ to $\{y : \|y\| > 1\}$, so $Y \in \mathcal Y = \{y : \|y\| \le 1\}$ almost surely.
--
--   From these the definition builds:
--
--   1. the regression function $f^*(x) = \mathbb E[Y \mid X = x] = \int y \, \kappa(x)(dy)$;
--   2. the joint law $\mathbb P_{X,Y} = \mu \otimes \kappa$ of $(X, Y)$ on $\mathbb R^p \times \mathbb R^d$;
--   3. the law $\mathbb P^n$ of the data $\mathcal D = ((X_1, Y_1), \dots, (X_n, Y_n))$, $n$ independent draws of $(X, Y)$.
--
--   These are the probabilistic ingredients of every regret statement of the mission.
--
--   **Formalization Note** The paper speaks of a joint law of $(X, Y)$; it is given here through its disintegration $(\mu, \kappa)$, and every joint law on $\mathbb R^p \times \mathbb R^d$ arises this way.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, §1, pp. 1–2

import Mathlib
import Definitions.Def_FastCLO_ERM_Polytope
open MeasureTheory ProbabilityTheory

namespace FastCLO.ERM

/-- A contextual linear optimization instance (arXiv:2011.03030v3, §1, pp. 1–2): the law `μ` of the
features `X ∈ ℝ^p` and the conditional law `κ x` of the cost vector `Y ∈ ℝ^d` given `X = x`, with
`Y` bounded, `‖Y‖ ≤ 1` (p. 2: "Y ∈ 𝒴 = {y : ‖y‖ ≤ 1}").

Formalization Note: the joint law of `(X, Y)` is given through its disintegration `(μ, κ)`; every
joint law on `ℝ^p × ℝ^d` disintegrates this way. -/
structure Instance (p d : ℕ) where
  /-- the law `P_X` of `X` -/
  μ : Measure (Vec p)
  /-- the conditional law of `Y` given `X = x` -/
  κ : Kernel (Vec p) (Vec d)
  [isProb : IsProbabilityMeasure μ]
  [isMarkov : IsMarkovKernel κ]
  /-- `‖Y‖ ≤ 1` almost surely given every `X = x` -/
  boundedY : ∀ x, κ x {y | 1 < ‖y‖} = 0

attribute [instance] Instance.isProb Instance.isMarkov

/-- The regression function `f*(x) = E[Y | X = x]`, the mean of the conditional law
(arXiv:2011.03030v3, p. 1). -/
noncomputable def Instance.fstar {p d : ℕ} (I : Instance p d) (x : Vec p) : Vec d :=
  ∫ y, y ∂(I.κ x)

/-- The joint law of `(X, Y)`: `μ ⊗ κ`. -/
noncomputable def Instance.joint {p d : ℕ} (I : Instance p d) : Measure (Vec p × Vec d) :=
  I.μ ⊗ₘ I.κ

/-- The law of the data `D = ((X_1, Y_1), …, (X_n, Y_n))`: `n` independent draws of `(X, Y)`
(arXiv:2011.03030v3, p. 2). -/
noncomputable def Instance.sample {p d : ℕ} (I : Instance p d) (n : ℕ) :
    Measure (Fin n → Vec p × Vec d) :=
  Measure.pi fun _ => I.joint

end FastCLO.ERM


