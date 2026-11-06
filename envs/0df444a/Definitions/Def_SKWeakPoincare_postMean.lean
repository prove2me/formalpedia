-- Prove2me | Definitions.Def_SKWeakPoincare_postMean
-- name    : SKWeakPoincare_postMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:41.206474+00:00
-- url     : https://prove2.me/theorems/4e25d0cb-4c26-4f58-9443-2b9598acc9bc
-- title:
--   Posterior mean $m(y)$ of the exponential tilt, full-support laws, and KL divergence on $\{\pm1\}^n$
-- statement:
--   Let $\mu$ be a law on $\{\pm1\}^n$. It has **full support** if $\mu(x)>0$ for every $x$. For a field $y\in\mathbb R^n$ its exponential tilt is
--   $$
--   \mu_y(x)=\frac{\mu(x)\exp\langle y,x\rangle}{E_{\sigma\sim\mu}[\exp\langle y,\sigma\rangle]},
--   $$
--   and the **posterior mean** is $m(y)=E_{\sigma\sim\mu_y}[\sigma]\in\mathbb R^n$. For $\mu=\mu_{\beta,A}$ this is the magnetization $m(A,y)$ of the SK model with external field $y$. The **Kullback–Leibler divergence** of two laws is $D(p\|q)=\sum_xp(x)\log\big(p(x)/q(x)\big)$ (natural logarithm).
--
--   The posterior mean is the drift of the stochastic-localization paths, and the symmetric KL divergence compares two tilts in Lemma 6.3.
--
--   **Formalization Note** Fields and means are vectors of `EuclideanSpace ℝ (Fin n)`, so their norm is the Euclidean norm $\|\cdot\|_2$ (Mathlib's norm on `Fin n → ℝ` is the sup norm). The tilt is the published `SKAnnealing.Sampling.tilt` and the mean vector is `tapMean`. The KL divergence is used only for full-support laws, where each term is finite.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Section 3.1, p.14 (m(A,y)); Section 6, p.37 (μ_y, m(y), full support); Lemma 6.3, p.38 (D(·‖·))

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_tapHessian

open OAI.CriticalSK SKAnnealing.Sampling

namespace SKWeakPoincare

/-- `μ` is a **full-support distribution** on `{±1}^n`: every configuration has positive mass and the
masses sum to one. Hou–Liu–Yu, arXiv:2610.09882, Section 6, p. 37 ("a full-support distribution `μ`
on `{±1}^n`"). -/
def IsFullSupportLaw {n : ℕ} (μ : Spin n → ℝ) : Prop :=
  (∀ x, 0 < μ x) ∧ ∑ x, μ x = 1

/-- The **posterior mean** `m(y) = E_{σ∼μ_y}[σ]` of the exponential tilt
`μ_y(x) = μ(x) exp⟨y, x⟩ / E_{σ∼μ}[exp⟨y, σ⟩]`, as a vector of Euclidean space `ℝ^n`.
Hou–Liu–Yu, arXiv:2610.09882, Section 6, p. 37; for `μ = μ_{β,A}` it is `m(A, y)` of Section 3.1, p. 14.

**Formalization Note.** `tilt μ y` is the published exponential tilt (DHMR26 bundle) and `tapMean`
its vector of spin means. The field and the mean live in `EuclideanSpace ℝ (Fin n)`, whose norm is
the Euclidean norm `‖·‖₂` of the paper (the norm of `Fin n → ℝ` in Mathlib is the sup norm). -/
noncomputable def postMean {n : ℕ} (μ : Spin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (tapMean (tilt μ (WithLp.ofLp y)))

/-- Kullback–Leibler divergence `D(p ‖ q) = Σ_x p(x) log(p(x)/q(x))` between two laws on `{±1}^n`
(natural logarithm, p. 14). Used for full-support laws, where every term is finite. -/
noncomputable def lawKL {n : ℕ} (p q : Spin n → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

end SKWeakPoincare


