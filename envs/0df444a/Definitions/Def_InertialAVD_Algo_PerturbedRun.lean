-- Prove2me | Definitions.Def_InertialAVD_Algo_PerturbedRun
-- name    : InertialAVD_Algo_PerturbedRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:49.849272+00:00
-- url     : https://prove2.me/theorems/c58af571-fb67-40ac-9c0d-bb846d105caa
-- title:
--   Algorithm (55) with perturbations $g_k$, the sequence $z_k$ (59), the energy $\mathcal G(k)$ and the series $\sum_j (j+\alpha-1)\|g_j\|$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R\cup\{+\infty\}$, $\Psi:\mathcal H\to\mathbb R$, $\Theta=\Phi+\Psi$, $\alpha,s\in\mathbb R$, and let $P$ stand for $\operatorname{prox}_{s\Phi}$. This file defines four objects.
--
--   1. **The perturbed inertial forward-backward algorithm (55).** Sequences $(x_k)_{k\ge0}$, $(y_k)_{k\ge0}$ in $\mathcal H$ form a run with perturbations $(g_k)_{k\ge0}$ if
--   $$y_k = x_k + \frac{k-1}{k+\alpha-1}(x_k-x_{k-1})\quad(k\ge1),\qquad x_{k+1}=P\big(y_k-s(\nabla\Psi(y_k)-g_k)\big)\quad(k\ge0).$$
--   2. **The sequence (59).** $z_k=\frac{k+\alpha-1}{\alpha-1}\,y_k-\frac{k}{\alpha-1}\,x_k$ for every $k\ge0$; in particular $z_0=y_0$.
--   3. **The energy** (p. 20). For a point $x^*$,
--   $$\mathcal G(k)=\frac{2s}{\alpha-1}(k+\alpha-2)^2\big(\Theta(x_k)-\Theta(x^*)\big)+(\alpha-1)\|z_k-x^*\|^2,$$
--   an extended real, since $\Theta(x_0)$ may be $+\infty$.
--   4. **The perturbation series** $\sum_{j=0}^\infty (j+\alpha-1)\|g_j\|$ of (68) and Theorem 5.1, as a real series sum.
--
--   These are the objects in terms of which the estimates (66), (68), (69), (72), (80) and Theorems 5.1 and 5.3 are stated.
--
--   **Formalization Note.** $y_0$ is left free: the page's $k=0$ step involves an unspecified $x_{-1}$, and for $\alpha>1$ every $y_0$ arises from some $x_{-1}$, so every run the page allows is covered. $\Theta$ is the published `NesterovFB.Rates.theta Φ Ψ`. The series is a `tsum`; every statement using it assumes $\sum_k k\|g_k\|<\infty$, which makes it convergent.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), pp. 18–20, (55), (59), definition of 𝒢(k) before (66), (68)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

namespace InertialAVD.Algo

/-- `(x, y)` is a run of the perturbed inertial forward-backward algorithm (55), with `P` playing
the role of `prox_{sΦ}`, smooth part `Ψ` and perturbations `g k`:
* `y k = x k + (k − 1)/(k + α − 1) · (x k − x (k − 1))` for every `k ≥ 1`;
* `x (k + 1) = P (y k − s (∇Ψ(y k) − g k))` for every `k ≥ 0`.

`y 0` is left free: the page's `k = 0` extrapolation uses an unspecified `x_{−1}`, and for `α > 1`
every `y 0 ∈ H` arises from some `x_{−1}`. -/
def IsPerturbedRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → ℝ) (P : H → H) (α s : ℝ) (g : ℕ → H) (x y : ℕ → H) : Prop :=
  (∀ k : ℕ, 1 ≤ k →
      y k = x k + (((k : ℝ) - 1) / ((k : ℝ) + α - 1)) • (x k - x (k - 1))) ∧
    (∀ k : ℕ, x (k + 1) = P (y k - s • (gradient Ψ (y k) - g k)))

/-- The auxiliary sequence (59): `z k = (k + α − 1)/(α − 1) · y k − k/(α − 1) · x k`, for every
`k ≥ 0` (so `z 0 = y 0`). -/
noncomputable def zSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x y : ℕ → H) (k : ℕ) : H :=
  (((k : ℝ) + α - 1) / (α - 1)) • y k - ((k : ℝ) / (α - 1)) • x k

/-- The energy `𝒢(k) = 2s/(α − 1) · (k + α − 2)² · (Θ(x k) − Θ(x*)) + (α − 1)‖z k − x*‖²`
(p. 20), where `Θ = Φ + Ψ` is `NesterovFB.Rates.theta Φ Ψ`. Valued in `EReal`, since `Θ(x 0)` may
be `+∞`. -/
noncomputable def energyG {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (Ψ : H → ℝ) (α s : ℝ) (x y : ℕ → H) (xstar : H) (k : ℕ) : EReal :=
  ((2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2 : ℝ) : EReal)
      * (NesterovFB.Rates.theta Φ Ψ (x k) - NesterovFB.Rates.theta Φ Ψ xstar)
    + (((α - 1) * ‖zSeq α x y k - xstar‖ ^ 2 : ℝ) : EReal)

/-- The perturbation series `∑_{j=0}^∞ (j + α − 1)‖g j‖` appearing in (68) and in the constant of
Theorem 5.1 (a real `tsum`; it is used only under the hypothesis that `∑ k‖g k‖` converges, which
makes this series convergent). -/
noncomputable def pertSum {H : Type*} [NormedAddCommGroup H] (α : ℝ) (g : ℕ → H) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) + α - 1) * ‖g j‖

end InertialAVD.Algo


