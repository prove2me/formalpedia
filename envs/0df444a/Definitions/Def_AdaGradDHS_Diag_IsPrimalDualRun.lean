-- Prove2me | Definitions.Def_AdaGradDHS_Diag_IsPrimalDualRun
-- name    : AdaGradDHS_Diag_IsPrimalDualRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:01.041403+00:00
-- url     : https://prove2.me/theorems/a68f47e7-e24e-406d-a5a0-51de15a4a06c
-- title:
--   A run of the primal-dual subgradient update (3)
-- statement:
--   Let $X \subseteq \mathbb{R}^d$, $\varphi : \mathbb{R}^d \to \mathbb{R}$, proximal functions $\psi_1, \psi_2, \dots$, a step size $\eta$, feedback vectors $g_1, g_2, \dots$ and $T \in \mathbb{N}$. A sequence $x_1, \dots, x_{T+1}$ is a **run of the primal-dual subgradient update (3)** if $x_1 \in X$ and, for every $t \in \{1, \dots, T\}$, $x_{t+1} \in X$ and
--   $$x_{t+1} \in \operatorname*{argmin}_{x \in X}\Big\{ \eta\,\langle \bar g_t, x\rangle + \eta\,\varphi(x) + \tfrac1t\,\psi_t(x) \Big\}, \qquad \bar g_t = \frac1t \sum_{\tau=1}^t g_\tau .$$
--
--   This is Nesterov's primal-dual subgradient method in Xiao's regularized dual averaging form, with a proximal term $\psi_t$ that may change from round to round; Algorithm 1 (diagonal AdaGrad) is the case $\psi_t(x) = \tfrac12\langle x, (\delta I + \operatorname{diag}(s_t))x\rangle$.
--
--   **Formalization Note** The argmin is a predicate: $x_{t+1}$ is some minimizer of the objective over $X$. Its existence is carried by this hypothesis rather than by a closedness assumption on $X$ or $\varphi$; where the minimizer is not unique, any minimizer is allowed. The initial point is not fixed here; each theorem states its own condition on $x_1$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §1.1, p. 2123, eq. (3); Figure 1 (Algorithm 1), p. 2130

import Mathlib

namespace AdaGradDHS.Diag

/-- **A run of the primal-dual subgradient update (3), rounds `t = 1, …, T`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §1.1, p. 2123, eq. (3): "xt+1 = argmin_{x∈X} {η⟨ḡt, x⟩ + ηϕ(x) + (1/t)ψt(x)}", with
"ḡt = (1/t) Σ_{τ=1}^t gτ" (p. 2123); Figure 1, p. 2130 (the loop "FOR t = 1 to T").

`IsPrimalDualRun X φ ψ η g x T` says: `x 1 ∈ X`, and for every `t ∈ {1, …, T}`, `x (t+1) ∈ X` and
for every `y ∈ X`
`η⟨ḡ_t, x_{t+1}⟩ + ηφ(x_{t+1}) + (1/t)ψ_t(x_{t+1}) ≤ η⟨ḡ_t, y⟩ + ηφ(y) + (1/t)ψ_t(y)`,
where `ḡ_t = (1/t) Σ_{τ=1}^t g_τ`.

**Formalization Note.** The `argmin` is a predicate: `x_{t+1}` is *a* minimizer of the update's
objective over `X`. Its existence is the paper's presupposition ("the sequence {xt} defined by
the update (3)"), carried by this hypothesis rather than by a closedness assumption; where the
minimizer is not unique any minimizer is allowed. The initial point is not fixed here: each
theorem states its own condition on `x 1`. The divisor `t` is at least `1`. -/
def IsPrimalDualRun {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (g x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  x 1 ∈ X ∧ ∀ t ∈ Finset.Icc 1 T, x (t + 1) ∈ X ∧ ∀ y ∈ X,
    η * inner ℝ ((1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, g τ) (x (t + 1)) + η * φ (x (t + 1))
        + 1 / (t : ℝ) * ψ t (x (t + 1)) ≤
      η * inner ℝ ((1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, g τ) y + η * φ y + 1 / (t : ℝ) * ψ t y

end AdaGradDHS.Diag


