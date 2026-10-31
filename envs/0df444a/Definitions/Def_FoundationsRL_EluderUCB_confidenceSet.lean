-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_confidenceSet
-- name    : FoundationsRL_EluderUCB_confidenceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:39.761983+00:00
-- url     : https://prove2.me/theorems/1992ea2b-46e0-4e71-bf44-56c5c5c90803
-- title:
--   (4.5): the confidence set $\mathcal F^t$
-- statement:
--   Given $\beta$ and the empirical minimizer $\hat f^t$, the confidence set of round $t$ is
--
--   $$
--   \mathcal F^t=\Bigl\{f\in\mathcal F:\ \sum_{i=1}^{t-1}\bigl(f(\pi^i)-r^i\bigr)^2\le\sum_{i=1}^{t-1}\bigl(\hat f^t(\pi^i)-r^i\bigr)^2+\beta\Bigr\}.
--   $$
--
--   It collects the functions whose empirical squared error is close to that of $\hat f^t$.
--
--   **Formalization Note** The source sets $\mathcal F^1=\mathcal F$ separately. Both sums are empty at $t=1$, so the single formula gives this whenever $\beta\ge0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.5), p. 58

import Mathlib

namespace FoundationsRL.EluderUCB

/-- **The confidence set of round `t`.** Foster & Rakhlin, arXiv:2312.16730v1, (4.5), p. 58:
`Fᵗ = {f ∈ F : ∑_{i=1}^{t-1} (f(πⁱ) - rⁱ)² ≤ ∑_{i=1}^{t-1} (f̂ᵗ(πⁱ) - rⁱ)² + β}`, with `F¹ = F`.

**Formalization Note.** At `t = 1` both sums are empty, so `F¹ = F` holds whenever `β ≥ 0`, which is
the case for the source's `β = 8 log(|F|/δ)`; the source's separate clause is not needed. -/
def confidenceSet {Act : Type*} (F : Set (Act → ℝ)) (β : ℝ) (π : ℕ → Act) (r : ℕ → ℝ) (t : ℕ)
    (fhat : Act → ℝ) : Set (Act → ℝ) :=
  {f ∈ F | ∑ i ∈ Finset.Ico 1 t, (f (π i) - r i) ^ 2 ≤
    ∑ i ∈ Finset.Ico 1 t, (fhat (π i) - r i) ^ 2 + β}

end FoundationsRL.EluderUCB


