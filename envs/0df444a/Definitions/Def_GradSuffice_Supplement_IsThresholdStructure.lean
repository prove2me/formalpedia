-- Prove2me | Definitions.Def_GradSuffice_Supplement_IsThresholdStructure
-- name    : GradSuffice_Supplement_IsThresholdStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:26:06.185231+00:00
-- url     : https://prove2.me/theorems/70d70b8f-cdf9-4027-9bb2-1ae6822f34bb
-- title:
--   Threshold structure of margin $\theta$ and size $N$
-- statement:
--   Let $V$ be a real normed space with closed unit ball $B_V$ and dual unit ball $B_V^\star$. Pairs $(w_1,\xi_1),\dots,(w_N,\xi_N)\in B_V\times B_V^\star$ form a **threshold structure of margin $\theta$ and size $N$** if
--   $$w_i\cdot\xi_j\ \begin{cases}\le 0, & i\le j,\\ \ge\theta, & i>j.\end{cases}$$
--
--   Threshold structures are a one-dimensional analogue of shattered trees; exchanging the roles of $w_i$ and $\xi_i$ and reversing the order turns a threshold structure in $B$ into one in $B^\star$, which is what Theorem 7 exploits.
--
--   **Formalization Note** The definition is stated for an arbitrary real normed space $V$, so that the $(B,B^\star)$-structures of Theorem 7 are the case $V=X$ and the $(B^\star,(B^\star)^\star)$-structures the case $V=X^\star$ (pairs in $B^\star\times B^{\star\star}$, pairing $\Psi_j(\xi_i)$). Indices run over $\{0,\dots,N-1\}$; only their order matters.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §6.2, p.17

import Mathlib

namespace GradSuffice.Supplement

/-- **Threshold structure of margin `θ` and size `N`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §6.2, p.17: "We say that `B` admits a
threshold structure of margin `θ` of size `N` if there exist pairs `{(wᵢ, ξᵢ)}_{i=1}^N ⊆ B × B⋆`
such that `wᵢ · ξⱼ ≤ 0` for `i ≤ j` and `wᵢ · ξⱼ ≥ θ` for `i > j`."

**Formalization Note.** Stated for an arbitrary real normed space `V` with unit ball
`closedBall (0 : V) 1` and dual unit ball `closedBall (0 : StrongDual ℝ V) 1` (operator norm), so
that the `(B, B⋆)`-structures of Theorem 7 are the instance `V = X` and the `(B⋆, (B⋆)⋆)`-structures
are the instance `V = StrongDual ℝ X` (pairs `(ξᵢ, Ψᵢ) ∈ B⋆ × B⋆⋆`, pairing `Ψⱼ(ξᵢ)`). Indices are
`Fin N` (0-based; only their order matters). This is §6.2's convention, not the variants of
Eq. (44) or Eq. (47). -/
def IsThresholdStructure {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (θ : ℝ) {N : ℕ}
    (w : Fin N → V) (ξ : Fin N → StrongDual ℝ V) : Prop :=
  (∀ i, ‖w i‖ ≤ 1) ∧ (∀ j, ‖ξ j‖ ≤ 1) ∧
    ∀ i j : Fin N, (i ≤ j → ξ j (w i) ≤ 0) ∧ (j < i → θ ≤ ξ j (w i))

end GradSuffice.Supplement


