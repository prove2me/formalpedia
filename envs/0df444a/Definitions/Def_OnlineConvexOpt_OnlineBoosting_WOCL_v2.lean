-- Prove2me | Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL_v2
-- name    : OnlineConvexOpt_OnlineBoosting_WOCL_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:53.321358+00:00
-- url     : https://prove2.me/theorems/4388f5a7-c35f-4c7a-bcde-986dbb690457
-- title:
--   γ-weak OCO learner (Definition 12.1, shifted form (12.2)) with a genuine comparator over H
-- statement:
--   $W$ is a $\gamma$-weak OCO learner for the hypothesis class $H$ and contexts $a$ on a linear loss sequence of range at most $1$ over $K$ if $\sum_{t=1}^Tf_t(W_t)\le\gamma\inf_{h\in H}\sum_{t=1}^Tf_t(h(a_t))+\mathrm{Regret}_T(W)$ (Eq. (12.2)). Corrected version of `OnlineConvexOpt_OnlineBoosting_WOCL`: the comparator is the real infimum of the image of $H$ (genuine when $H$ is nonempty and maps into the bounded set $K$) instead of the binder `⨅ h ∈ H, …`, which returns the junk value $0$ outside $H$. The range-bound premise remains an implication.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 197, Definition 12.1 and p. 198, Eq. (12.2) (PDF pp. 219–220)

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
here as a plain bounded hypothesis over `K`), it is run against,
`∑_{t=1}^T flin_t(W_t) ≤ γ·min_{h∈H}∑_{t=1}^T flin_t(h(a_t)) + Regret_T(W)`. The comparator
`min_{h∈H}` is the real infimum of the image of `H` under the cumulative loss (genuine when `H`
is nonempty and every `h ∈ H` maps contexts into the bounded set `K`; the retired version used
the binder `⨅ h ∈ H, …`, whose inner infimum is the junk value `sInf ∅ = 0` at every `h ∉ H`).
The range-bound premise is an implication, not a further conjunct of the conclusion, since
Definition 12.1 only *claims* the inequality when the range condition holds — it asserts
nothing about `W` against a loss sequence that violates it. -/
def IsGammaWOCL (K : Set E) (γ : ℝ) (T : ℕ) (a : ℕ → A) (H : Set (A → E)) (W : ℕ → E)
    (flin : ℕ → E → ℝ) (RegretBoundW : ℝ) : Prop :=
  (∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ x ∈ K, ∀ y ∈ K, flin t x - flin t y ≤ 1) →
  (∑ t ∈ Finset.Icc 1 T, flin t (W t)) ≤
    γ * sInf ((fun h => ∑ t ∈ Finset.Icc 1 T, flin t (h (a t))) '' H) + RegretBoundW

end OnlineConvexOpt.OnlineBoosting


