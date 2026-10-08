-- Prove2me | Definitions.Def_KendallBD_MinVar_Setting
-- name    : KendallBD_MinVar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:18.601078+00:00
-- url     : https://prove2.me/theorems/5fdfe488-d93c-47f7-82ac-46322e916f3b
-- title:
--   §2, (11), (13), (14c), p. 4; §6, (55)–(56), pp. 11–12 — rates, mean, variance, and minimizing rates
-- statement:
--   Let $\lambda(t)$ and $\mu(t)$ be the per-individual birth and death rates of Kendall's process, which starts from one ancestor. Define
--
--   $$
--   \rho(t)=\int_0^t(\mu(\tau)-\lambda(\tau))\,d\tau,\qquad
--   \bar n_t=e^{-\rho(t)},\qquad
--   V_{\lambda,\mu}(t)=e^{-2\rho(t)}\int_0^t e^{\rho(\tau)}(\lambda(\tau)+\mu(\tau))\,d\tau.
--   $$
--
--   Here $V_{\lambda,\mu}(t)$ is the variance formula (14c). An admissible rate pair is continuous and nonnegative for $t\ge0$, and it has prescribed mean $\bar n$ when the displayed mean identity holds for every $t\ge0$. For a positive differentiable prescribed mean, put $g(t)=\bar n_t'/\bar n_t$ and define $\lambda_*(t)=\max\{g(t),0\}$ and $\mu_*(t)=\max\{-g(t),0\}$. The file also defines the logistic mean $\bar n_t=a/(1+(a-1)e^{-bt})$.
--
--   These shared definitions fix the objects compared in Kendall's minimum-variance result. The identity between (14c) and the variance of the population law belongs to the geometric-solution mission.
--
--   **Formalization Note** The integral is an oriented interval integral. The functions are defined on all real times, but the stochastic claims use $t\ge0$. The later theorems assume $C^1$ regularity and strict positivity before using the derivative and quotient in $g$.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (11), (13), (14c), p. 4; §6, (55)–(56), pp. 11–12; (58), p. 12

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (14c), p. 4: the variance of the population size in its
integral form, for the process starting from one ancestor. -/
noncomputable def fluct (lam mu : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-2 * KendallBD.Sol.rho lam mu t) *
    ∫ τ in (0 : ℝ)..t, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)

/-- Continuous, nonnegative birth and death rates on nonnegative time. Continuity
is the stated regularity convention used to read Kendall's differential formulas. -/
def Admissible (lam mu : ℝ → ℝ) : Prop :=
  Continuous lam ∧ Continuous mu ∧
    ∀ t : ℝ, 0 ≤ t → 0 ≤ lam t ∧ 0 ≤ mu t

/-- Kendall (1948), (13), p. 4: the mean population size of a process with
rates `lam`, `mu`, restricted to nonnegative time. -/
def HasMean (lam mu nbar : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → Real.exp (-KendallBD.Sol.rho lam mu t) = nbar t

/-- The logarithmic derivative of the prescribed positive mean, (55), p. 11.
Statements using this definition assume `ContDiff ℝ 1 nbar` and `0 < nbar t`. -/
noncomputable def growth (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv nbar t / nbar t

/-- The nonnegative birth rate in Kendall's minimum-fluctuation choice (56), p. 12. -/
noncomputable def lamStar (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (growth nbar t) 0

/-- The nonnegative death rate in Kendall's minimum-fluctuation choice (56), p. 12. -/
noncomputable def muStar (nbar : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (-growth nbar t) 0

/-- Kendall's logistic mean (58), p. 12, with parameters `a = α`, `b = β`. -/
noncomputable def logisticMean (a b : ℝ) (t : ℝ) : ℝ :=
  a / (1 + (a - 1) * Real.exp (-b * t))

end KendallBD.MinVar


