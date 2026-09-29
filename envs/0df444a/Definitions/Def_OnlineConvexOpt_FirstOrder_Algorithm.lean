-- Prove2me | Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
-- name    : OnlineConvexOpt_FirstOrder_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:18:03.304678+00:00
-- url     : https://prove2.me/theorems/ce775614-e79c-4360-a77c-26096781430a
-- title:
--   Non-anticipating online algorithm for OCO
-- statement:
--   `IsOnlineAlgorithm K A` formalizes "an algorithm for online convex optimization" for the lower bound of Theorem 3.2: a map $A$ from a full cost-function sequence $f : \mathbb{N} \to E \to \mathbb{R}$ (unknown to the algorithm in advance) to a play sequence $A\,f : \mathbb{N} \to E$, required to
--
--   - always play inside $K$: $A\,f\,0 \in K$ and $A\,f\,(t+1) \in K$ for every $t$;
--   - be *non-anticipating*: if two cost sequences $f, f'$ agree on every round strictly before $t$, the algorithm's round-$t$ play agrees too, $A\,f\,t = A\,f'\,t$ — matching the OCO protocol, where round $t$'s decision is chosen after observing $f_0(x_0), \dots, f_{t-1}(x_{t-1})$ but before $f_t$ itself is revealed.
--
--   **Formalization Note.** This is the standard "non-anticipating map from the full input to the output sequence" idiom for an online algorithm/prediction strategy, chosen so that "any algorithm" in Theorem 3.2 can be quantified over directly as a function, without introducing an explicit internal-state or history-indexed representation.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 45, Theorem 3.2's statement ("any algorithm for online convex optimization"), PDF p. 67

import Mathlib

namespace OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An online algorithm for OCO on decision set `K`: a map from a full cost-function sequence
(unknown to the algorithm in advance) to a play sequence, required to be non-anticipating
(`A f t` depends only on `f 0, ..., f (t - 1)`, matching the protocol of chapter 1/3: round `t`'s
decision is chosen after observing `f_0(x_0), ..., f_{t-1}(x_{t-1})` but before `f_t` is revealed)
and to always play inside `K`. This is the "any algorithm for online convex optimization" the
lower bound of Theorem 3.2 quantifies over. -/
def IsOnlineAlgorithm (K : Set E) (A : (ℕ → E → ℝ) → ℕ → E) : Prop :=
  (∀ f, A f 0 ∈ K) ∧ (∀ f t, A f (t + 1) ∈ K) ∧
    ∀ (f f' : ℕ → E → ℝ) (t : ℕ), (∀ s < t, f s = f' s) → A f t = A f' t

end OnlineConvexOpt.FirstOrder


