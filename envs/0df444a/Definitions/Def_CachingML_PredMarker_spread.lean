-- Prove2me | Definitions.Def_CachingML_PredMarker_spread
-- name    : CachingML_PredMarker_spread
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:59:45.672256+00:00
-- url     : https://prove2.me/theorems/8625e93d-8947-4fcf-aa51-34f32497228f
-- title:
--   Definition 7 — the spread $S_\ell$ of a loss function
-- statement:
--   Let $\ell : \mathbb R \times \mathbb R \to \mathbb R_{\ge 0}$ be a loss function. For a length $T \ge 1$, let $\mathcal A_T$ be the set of strictly increasing integer sequences $a_1 < a_2 < \dots < a_T$ and $\mathcal B_T$ the set of non-increasing real sequences $b_1 \ge b_2 \ge \dots \ge b_T$, and write $\ell(A_T, B_T) = \sum_{i=1}^T \ell(a_i, b_i)$. The **spread** of $\ell$ at $m$ is
--
--   $$S_\ell(m) = \min\{T \ge 1 : \ell(A_T, B_T) \ge m \text{ for all } A_T \in \mathcal A_T,\ B_T \in \mathcal B_T\}.$$
--
--   It is the length of a sequence of true arrival times that can be predicted in completely reversed order while keeping the total loss below $m$, plus one. A loss with a slowly growing spread lets a predictor with small error get only short stretches of the order wrong.
--
--   **Formalization Note** The argument $m$ is a real number (the paper writes $S_\ell : \mathbb N^+ \to \mathbb R^+$ but applies $S_\ell$ at the real arguments $\epsilon$ and $\eta_{r,c}$ in Theorem 3.3 and Lemmas 3.3–3.4). The value lies in `ℕ∞`: it is `⊤` when no length $T$ works. Lengths range over $T \ge 1$, so $S_\ell(m) \ge 1$ for every $m$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 14, Definition 7

import Mathlib

namespace CachingML.PredMarker

/-- The spread of a loss function `ℓ` (Lykouris–Vassilvitskii, arXiv:1802.05399v4, Definition 7,
p. 14): `S_ℓ(m)` is the least length `T ≥ 1` such that for every strictly increasing sequence of
integers `a_1 < ⋯ < a_T` and every non-increasing sequence of reals `b_1 ≥ ⋯ ≥ b_T`,
`∑_i ℓ(a_i, b_i) ≥ m`. The argument `m` is real; the value is `⊤` when no such `T` exists. -/
noncomputable def spread (ℓ : ℝ → ℝ → ℝ) (m : ℝ) : ℕ∞ :=
  sInf {T : ℕ∞ | ∃ t : ℕ, T = t ∧ 1 ≤ t ∧
    ∀ a : Fin t → ℤ, StrictMono a → ∀ b : Fin t → ℝ, Antitone b →
      m ≤ ∑ i, ℓ (a i) (b i)}

end CachingML.PredMarker


