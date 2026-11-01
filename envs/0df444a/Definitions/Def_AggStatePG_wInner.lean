-- Prove2me | Definitions.Def_AggStatePG_wInner
-- name    : AggStatePG_wInner
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:50.009762+00:00
-- url     : https://prove2.me/theorems/6690464b-8438-4de5-9de8-a6fa61ab2301
-- title:
--   Weighted inner product $\langle Q,Q'\rangle_{w\times1}$, display (6)
-- statement:
--   For state-relevance weights $w\in\mathbb R^{|\mathcal S|}$, the **weighted inner product** on $\mathbb R^{|\mathcal S|\times|\mathcal A|}$ is
--   $$\langle Q,Q'\rangle_{w\times1}=\sum_{s\in\mathcal S}\sum_{a\in\mathcal A}w(s)Q(s,a)Q'(s,a).\qquad(6)$$
--   Lemma 5 writes the directional derivative of $J$ as $\langle Q_\pi,\pi'-\pi\rangle_{\eta_\pi\times1}$.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, display (6), p.9

import Mathlib

namespace AggStatePG

/-- The **weighted inner product** (6) (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, display (6), p.9): for state-relevance weights
`w ∈ ℝ^{|S|}`, `⟨Q, Q'⟩_{w×1} = ∑_{s ∈ S} ∑_{a ∈ A} w(s) Q(s,a) Q'(s,a)` on `ℝ^{|S|×|A|}`.

**Formalization Note.** State-action vectors are tables `S → A → ℝ`. -/
def wInner {S A : Type*} [Fintype S] [Fintype A]
    (w : S → ℝ) (Q Q' : S → A → ℝ) : ℝ :=
  ∑ s : S, ∑ a : A, w s * Q s a * Q' s a

end AggStatePG


