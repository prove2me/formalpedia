-- Prove2me | Definitions.Def_FTPLLinBandit_actMean
-- name    : FTPLLinBandit_actMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:41.50682+00:00
-- url     : https://prove2.me/theorems/1c1adea4-c6aa-4b6a-8c26-167431c49bb6
-- title:
--   Action mean $\mu=\mathbb E_{Z\sim\rho}[x(\Theta+Z)]$
-- statement:
--   For an argmax selection $x$ of $A$, a perturbation density $\rho$ and a point $\Theta$, the **action mean** is
--   $$\mu=\mathbb E_{Z\sim\rho}\big[x(\Theta+Z)\big]=\int_{\mathbb R^d}\rho(z)\,x(\Theta+z)\,dz ,$$
--   the mean of the FTPL action law $p$, the law of $x(\Theta+Z)$. With $\rho=\rho_t$ and $\Theta=\hat\Theta_t$ it is the paper's $\mu_t=\mu(p_t)$; by Lemma 18 it is $\nabla\Psi(\Theta)$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §5, p.10

import Mathlib

open MeasureTheory

namespace FTPLLinBandit

/-- **The action mean `µ_t = E_{Z∼ρ}[x(Θ + Z)]`.** Wei, arXiv:2610.17818, §5, p.10: "Let p_t be
the law of x(Θ̂_t + Z) for Z ∼ ρ_t. Define the action mean … µ_t = µ(p_t) = E_{Z∼ρ_t}[x(Θ̂_t + Z)]".

`actMean x ρ Θ = ∫ ρ(z) x(Θ + z) dz` for an argmax selection `x` and a perturbation density `ρ`.

**Formalization Note.** The point `Θ` is a free argument (the paper's `Θ̂_t`). The Bochner integral
is the true mean whenever `z ↦ ρ(z) x(Θ+z)` is integrable, e.g. for a probability density and a
measurable `x` with values in a bounded `A`. -/
noncomputable def actMean {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (Θ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ∫ z, ρ z • x (Θ + z)

end FTPLLinBandit


