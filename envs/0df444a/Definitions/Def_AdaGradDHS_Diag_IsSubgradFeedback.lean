-- Prove2me | Definitions.Def_AdaGradDHS_Diag_IsSubgradFeedback
-- name    : AdaGradDHS_Diag_IsSubgradFeedback
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:46.043009+00:00
-- url     : https://prove2.me/theorems/ea51ea09-b53f-4490-a10a-728a728e3c61
-- title:
--   Subgradient feedback $g_t \in \partial f_t(x_t)$ on $X$
-- statement:
--   Let $X \subseteq \mathbb{R}^d$, let $f_1, f_2, \dots : \mathbb{R}^d \to \mathbb{R}$ be the losses, $x_1, x_2, \dots$ the predictions and $g_1, g_2, \dots$ the feedback vectors, and $T \in \mathbb{N}$. The feedback is a **subgradient feedback on rounds $1, \dots, T$** if for every $t \in \{1, \dots, T\}$ and every $y \in X$
--   $$f_t(x_t) + \langle g_t,\, y - x_t\rangle \le f_t(y).$$
--
--   In Algorithm 1 the learner suffers $f_t(x_t)$ and receives $g_t \in \partial f_t(x_t)$; for a convex $f_t$ this is exactly the condition above on all of $\mathbb{R}^d$.
--
--   **Formalization Note** Only the subgradient inequality on $X$ is required and $f_t$ is not assumed convex, so theorems assuming this predicate cover the paper's setting. Sequences are indexed by $\mathbb{N}$ with the paper's indices; index $0$ is unused. The vectors $g_t$ may depend on the iterates.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130 ("Receive subgradient gt ∈ ∂ft(xt) of ft at xt"); §1.1, p. 2122

import Mathlib

namespace AdaGradDHS.Diag

/-- **Subgradient feedback `g_t ∈ ∂f_t(x_t)`, rounds `t = 1, …, T`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130: "Receive subgradient gt ∈ ∂ft(xt) of ft at xt"; §1.1,
p. 2122: "At every timestep t, the learner receives the (sub)gradient information gt ∈ ∂ft(xt)".

`IsSubgradFeedback X f g x T` says: for every round `t ∈ {1, …, T}` and every `y ∈ X`,
`f_t(x_t) + ⟨g_t, y − x_t⟩ ≤ f_t(y)`.

**Formalization Note.** Only the subgradient inequality on `X` is required, and `f_t` is not
assumed convex: a convex `f_t` with `g_t ∈ ∂f_t(x_t)` satisfies the predicate, so theorems
assuming it are at least as general as the paper's. Sequences are indexed by `ℕ` with the
paper's indices; index `0` is unused. The vectors `g_t` may depend on the iterates (adaptive
feedback). -/
def IsSubgradFeedback {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ X, f t (x t) + inner ℝ (g t) (y - x t) ≤ f t y

end AdaGradDHS.Diag


