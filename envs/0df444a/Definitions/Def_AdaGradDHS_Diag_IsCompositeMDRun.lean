-- Prove2me | Definitions.Def_AdaGradDHS_Diag_IsCompositeMDRun
-- name    : AdaGradDHS_Diag_IsCompositeMDRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:37.680476+00:00
-- url     : https://prove2.me/theorems/37692caf-b854-4253-a9a3-0cd30ca554a7
-- title:
--   A run of the composite mirror-descent update (4)
-- statement:
--   Let $X \subseteq \mathbb{R}^d$, $\varphi : \mathbb{R}^d \to \mathbb{R}$, proximal functions $\psi_1, \psi_2, \dots$, a step size $\eta$, feedback vectors $g_1, g_2, \dots$ and $T \in \mathbb{N}$. A sequence $x_1, \dots, x_{T+1}$ is a **run of the composite mirror-descent update (4)** if $x_1 \in X$ and, for every $t \in \{1, \dots, T\}$, $x_{t+1} \in X$ and
--   $$x_{t+1} \in \operatorname*{argmin}_{x \in X}\Big\{ \eta\,\langle g_t, x\rangle + \eta\,\varphi(x) + B_{\psi_t}(x, x_t) \Big\},$$
--   where $B_{\psi_t}$ is the Bregman divergence of $\psi_t$.
--
--   This is the composite mirror-descent (proximal gradient, forward-backward splitting) method with a time-varying proximal function; Algorithm 1 (diagonal AdaGrad) is the case $\psi_t(x) = \tfrac12\langle x, (\delta I + \operatorname{diag}(s_t))x\rangle$.
--
--   **Formalization Note** The argmin is a predicate: $x_{t+1}$ is some minimizer over $X$; its existence is carried by this hypothesis, not by a closedness assumption. The initial point is not fixed here; each theorem states its own condition on $x_1$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §1.1, p. 2123, eq. (4); Figure 1 (Algorithm 1), p. 2130

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman

namespace AdaGradDHS.Diag

/-- **A run of the composite mirror-descent update (4), rounds `t = 1, …, T`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §1.1, p. 2123, eq. (4): "xt+1 = argmin_{x∈X} {η⟨gt, x⟩ + ηϕ(x) + Bψt(x, xt)}"; Figure 1,
p. 2130 (the loop "FOR t = 1 to T").

`IsCompositeMDRun X φ ψ η g x T` says: `x 1 ∈ X`, and for every `t ∈ {1, …, T}`, `x (t+1) ∈ X`
and for every `y ∈ X`
`η⟨g_t, x_{t+1}⟩ + ηφ(x_{t+1}) + B_{ψ_t}(x_{t+1}, x_t) ≤ η⟨g_t, y⟩ + ηφ(y) + B_{ψ_t}(y, x_t)`.

**Formalization Note.** The `argmin` is a predicate: `x_{t+1}` is *a* minimizer over `X`; its
existence is carried by this hypothesis (the paper's "the sequence {xt} defined by the update
(4)"), not by a closedness assumption. The initial point is not fixed here: each theorem states
its own condition on `x 1`. -/
def IsCompositeMDRun {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (η : ℝ)
    (g x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  x 1 ∈ X ∧ ∀ t ∈ Finset.Icc 1 T, x (t + 1) ∈ X ∧ ∀ y ∈ X,
    η * inner ℝ (g t) (x (t + 1)) + η * φ (x (t + 1)) + bregman (ψ t) (x (t + 1)) (x t) ≤
      η * inner ℝ (g t) y + η * φ y + bregman (ψ t) y (x t)

end AdaGradDHS.Diag


