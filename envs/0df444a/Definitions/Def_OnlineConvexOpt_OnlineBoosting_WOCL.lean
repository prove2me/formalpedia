-- Prove2me | Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL
-- name    : OnlineConvexOpt_OnlineBoosting_WOCL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:48:16.584574+00:00
-- url     : https://prove2.me/theorems/788f0bbe-e298-41e5-8829-5a1085096341
-- title:
--   γ-weak OCO learner (WOCL), shifted form
-- statement:
--   Definition 12.1 (p. 197), in its shifted form Eq. (12.2) (p. 198, after assuming loss
--   functions are shifted so $f_t(\bar x)=0$, the book's own simplification adopted throughout
--   the rest of the chapter): `W`, a round-by-round prediction sequence, is a `γ`-weak OCO
--   learner for hypothesis class `H` and context sequence `a` if, for every **linear** loss
--   sequence `flin` whose range over the decision set `K` is at most 1 (Definition 12.1's own
--   precondition, "$\max_{x\in K} f_t(x) - \min_{y\in K} f_t(y) \le 1$", p. 197) it is run
--   against, $\sum_{t=1}^T \mathrm{flin}_t(W_t) \le \gamma\min_{h\in H}
--   \sum_{t=1}^T \mathrm{flin}_t(h(a_t)) + \mathrm{Regret}_T(W)$.
--
--   **Formalization Note.** The range-bound precondition is an implication's antecedent, not
--   part of the conclusion: Definition 12.1 only *claims* the inequality when the range
--   condition holds, and asserts nothing about `W` against a loss sequence that violates it.
--   Rendered as a plain bounded hypothesis (`∀ x ∈ K, ∀ y ∈ K, flin t x - flin t y ≤ 1`) rather
--   than a fresh `⨆`/`⨅`-on-`K` expression, matching this chunk's own convention for the
--   diameter bound `D`. A moderator change request (2026-09-19) caught that the first draft
--   dropped this precondition entirely, making the definition strictly weaker (easier to
--   satisfy) than Definition 12.1 actually states.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 197-198, Definition 12.1/Eq. (12.2) (PDF p. 219-220)

import Mathlib

namespace OnlineConvexOpt.OnlineBoosting

variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 12.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 197, PDF p. 219), in its shifted form Eq. (12.2) (p. 198, PDF p. 220,
"it is convenient to henceforth assume that the loss functions are shifted such that
`f_t(x̄)=0`... we can rephrase `γ`-WOCL as [12.2]"): `W`, a sequence of round-by-round
predictions, is a `γ`-weak OCO learner (WOCL) for hypothesis class `H` and context sequence `a`
if, for every **linear** loss sequence `flin` whose range over the decision set `K` is at most 1
(`max_{x∈K} f_t(x) − min_{y∈K} f_t(y) ≤ 1`, Definition 12.1's own precondition, p. 197 — rendered
here as a plain bounded hypothesis over `K`, matching this chunk's own convention for the
diameter bound `D`, rather than a fresh `⨆`/`⨅`-on-`K`), it is run against,
`∑_{t=1}^T flin_t(W_t) ≤ γ·min_{h∈H}∑_{t=1}^T flin_t(h(a_t)) + Regret_T(W)`. The range-bound
premise is an implication, not a further conjunct of the conclusion, since Definition 12.1 only
*claims* the inequality when the range condition holds — it asserts nothing about `W` against a
loss sequence that violates it. -/
def IsGammaWOCL (K : Set E) (γ : ℝ) (T : ℕ) (a : ℕ → A) (H : Set (A → E)) (W : ℕ → E)
    (flin : ℕ → E → ℝ) (RegretBoundW : ℝ) : Prop :=
  (∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ x ∈ K, ∀ y ∈ K, flin t x - flin t y ≤ 1) →
  (∑ t ∈ Finset.Icc 1 T, flin t (W t)) ≤
    γ * (⨅ h ∈ H, ∑ t ∈ Finset.Icc 1 T, flin t (h (a t))) + RegretBoundW

end OnlineConvexOpt.OnlineBoosting


