-- Prove2me | Definitions.Def_OnlineConvexOpt_BanditConvex_FirstOrderAlgorithm
-- name    : OnlineConvexOpt_BanditConvex_FirstOrderAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:37:50.922433+00:00
-- url     : https://prove2.me/theorems/3bf9c5ef-f21d-45a8-a34b-0858be4adb5d
-- title:
--   First order online algorithm (Definition 6.4)
-- statement:
--   Definition 6.4 (p. 107, PDF p. 129) singles out the online algorithms Lemma 6.5's
--   reduction applies to: an algorithm `A` mapping a full cost-function sequence to a play
--   sequence (`x_1 ← A(∅)`, `x_t ← A(f_1, ..., f_{t-1})`) is a **first order online
--   algorithm** if (1) it is non-anticipating — round `t`'s decision depends only on
--   `f_1, ..., f_{t-1}`, which the definition's opening sentence presupposes of every OCO
--   algorithm — and (2) it treats every cost function only through its gradient at the point
--   it actually plays. Formally, writing $\hat f_\tau(x) = \nabla f_\tau(x_\tau)^\top x$ for the
--   linearization of $f_\tau$ at the point $A$ itself played on round $\tau$, the book
--   requires $A(f_1,\dots,f_{t-1}) = A(\hat f_1,\dots,\hat f_{t-1})$ for every $t$.
--
--   `IsFirstOrderOnlineAlgorithm A` formalizes this as a conjunction: a non-anticipation
--   clause (`∀ f f' t, (∀ s < t, f s = f' s) → A f t = A f' t`, mirroring
--   `OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm`'s clause for the same function type, with
--   no decision-set membership clause since Definition 6.4 states none) together with the
--   substitution property: for every cost sequence `f` and every sequence `g` of linear
--   functionals built from gradients of `f` at the points `A f τ` that `A` itself plays on
--   `f` (`g τ y = ⟪∇f_τ(x_τ), y⟫`), `A` produces the same decision at every round on `g` as
--   it does on `f`.
--
--   **Formalization Note.** The book's first bullet ("the family of loss functions is closed
--   under addition of linear functions") is a technical closure condition on the admissible
--   domain of `A`, not a mathematical property to verify of a candidate `A`; it is not
--   formalized as part of the predicate, since Lemma 6.5 and Theorem 6.9's proofs use only
--   the substitution property stated here (see `MODERATION_NOTES.md`).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 107, Definition 6.4 (PDF p. 129)

import Mathlib

namespace OnlineConvexOpt.BanditConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Definition 6.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 107, PDF p. 129). `A`, an algorithm mapping a full sequence of
differentiable cost functions to a play sequence (`x_1 ← A(∅)`, `x_t ← A(f_1, ..., f_{t-1})`,
here `A f t` for round `t`), is a *first order online algorithm* if (1) it is non-anticipating —
round `t`'s decision depends only on `f_1, ..., f_{t-1}`, which Definition 6.4's opening sentence
presupposes of every OCO algorithm before stating the "first order" bullets — and (2) it treats
every cost function only through its gradient at the point it actually plays: for every cost
sequence `f` and every sequence `g` of linear functionals `g τ = fun y => ⟪∇f_τ(x_τ), y⟫` built
from the gradients of `f` at the points `x_τ = A f τ` that `A` itself plays on `f`, `A` produces
the same decision at every round on `g` as it does on `f` (`A(f_1, ..., f_{t-1}) = A(f̂_1, ...,
f̂_{t-1})` in the book's notation, `f̂_τ(x) = ∇f_τ(x_τ)^⊤x`). Clause (1) mirrors
`OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm`'s non-anticipation conjunct for the same function
type, without a decision-set membership clause since Definition 6.4 states none. -/
def IsFirstOrderOnlineAlgorithm (A : (ℕ → E → ℝ) → ℕ → E) : Prop :=
  (∀ (f f' : ℕ → E → ℝ) (t : ℕ), (∀ s < t, f s = f' s) → A f t = A f' t) ∧
  ∀ f g : ℕ → E → ℝ,
    (∀ τ : ℕ, ∃ gradfτ : E, HasGradientAt (f τ) gradfτ (A f τ) ∧ ∀ y : E, g τ y = inner ℝ gradfτ y) →
    ∀ t : ℕ, A f t = A g t

end OnlineConvexOpt.BanditConvex


