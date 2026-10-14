-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_Rank
-- name    : RankBasedSDI_LoadBalancing_Rank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:27:54.36153+00:00
-- url     : https://prove2.me/theorems/0066f703-2839-426b-997f-aa12849c817c
-- title:
--   Rank function (2.3), order-compatible permutations $\mathfrak P(x)$ (2.16) and drift sets $\mathrm{conv}\{b_\pi\}$
-- statement:
--   Fix $N \ge 1$ and write $[N]=\{1,\dots,N\}$. For $x\in\mathbb R^N$ and $i\in[N]$ the **rank** of $x_i$ among the coordinates of $x$ is
--
--   $$
--   \mathrm{rank}(i;x) = \#\{j\in[N] : x_j < x_i\} + \#\{j\le i : x_j = x_i\} \in [N],
--   $$
--
--   so that ties are broken in favour of the smaller index. For example $x=(1,1,2,2,3)$ has ranks $(1,2,3,4,5)$ and $x=(1,1,3,2,2)$ has ranks $(1,2,5,3,4)$.
--
--   Let $\Pi$ be the set of permutations of $[N]$. For $x\in\mathbb R^N$ the set of **order-compatible permutations** is
--
--   $$
--   \mathfrak P(x)=\{\pi\in\Pi : x_i<x_j \text{ implies } \pi(i)<\pi(j) \text{ for every } i,j\in[N]\}.
--   $$
--
--   For $b\in\mathbb R^N$ and $\pi\in\Pi$ write $b_\pi=(b_{\pi(1)},\dots,b_{\pi(N)})$. The **drift set** at $x$ is the convex hull $\mathrm{conv}\{b_\pi:\pi\in\mathfrak P(x)\}\subset\mathbb R^N$, and the **rank-based drift** at $x$ is the vector $(b_{\mathrm{rank}(1;x)},\dots,b_{\mathrm{rank}(N;x)})$.
--
--   These objects define the drift of the rank-based equations (SDE)/(SDER) and the set-valued drift of the inclusions (SDI)/(SDIR), and the routing rule of the load-balancing model.
--
--   **Formalization Note** Servers and ranks are indexed by `Fin N`: the paper's index $i$ is Lean's $i-1$ and the paper's rank $r$ is Lean's $r-1$; `rankCount` is the paper's count (values in $\{1,\dots,N\}$) and `rank` subtracts one, with a structural lemma `rankCount_mem` showing the value lies in $[1,N]$. $b_\pi$ is `b ∘ π` and the convex hull is Mathlib's `convexHull ℝ`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 4, eq. (2.3); p. 7, eq. (2.16)

import Mathlib

namespace RankBasedSDI.LoadBalancing

/-!
Atar & Ichiba, arXiv:2409.15121v1, (2.3) p. 4 and (2.16) p. 7: the rank function, the
order-compatible permutations `𝔓(x)` and the drift sets `conv{b_π : π ∈ 𝔓(x)}`.
Servers and ranks are indexed by `Fin N`: the paper's index `i ∈ [N]` is Lean's `i - 1`, and
the paper's rank `r ∈ [N]` is Lean's `r - 1`.
-/

/-- The paper's rank (2.3), with the paper's values in `{1, …, N}`:
`rank(i; x) = #{j ∈ [N] : x_j < x_i} + #{j ≤ i : x_j = x_i}`. -/
noncomputable def rankCount {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j => x j < x i)).card +
    (Finset.univ.filter (fun j => j ≤ i ∧ x j = x i)).card

/-- The rank count lies in `{1, …, N}` (structural lemma needed to land in `Fin N`). -/
theorem rankCount_mem {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    1 ≤ rankCount x i ∧ rankCount x i ≤ N := by
  classical
  constructor
  · have : 0 < (Finset.univ.filter (fun j => j ≤ i ∧ x j = x i)).card :=
      Finset.card_pos.mpr ⟨i, by simp⟩
    unfold rankCount; omega
  · unfold rankCount
    rw [← Finset.card_union_of_disjoint]
    · simpa using Finset.card_le_univ
        (Finset.univ.filter (fun j => x j < x i) ∪
          Finset.univ.filter (fun j => j ≤ i ∧ x j = x i))
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact absurd h2.2 (ne_of_lt h1)

/-- `rank x i : Fin N` is the paper's `rank(i; x) − 1` (rank `1` is Lean's `0`): the position of
`x_i` among the `x_j` in increasing order, ties broken in favour of the smaller index. -/
noncomputable def rank {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : Fin N :=
  ⟨rankCount x i - 1, by have := rankCount_mem x i; omega⟩

/-- (2.16): `𝔓(x) = {π ∈ Π : x_i < x_j implies π(i) < π(j) for every i, j ∈ [N]}`. -/
def permSet {N : ℕ} (x : Fin N → ℝ) : Set (Equiv.Perm (Fin N)) :=
  {π | ∀ i j : Fin N, x i < x j → π i < π j}

/-- The drift set `conv{b_π : π ∈ 𝔓(x)}` of (SDI)/(SDIR), where
`b_π = (b_{π(1)}, …, b_{π(N)})`, i.e. `b ∘ π`. -/
def driftSet {N : ℕ} (b : Fin N → ℝ) (x : Fin N → ℝ) : Set (Fin N → ℝ) :=
  convexHull ℝ ((fun π : Equiv.Perm (Fin N) => b ∘ π) '' permSet x)

/-- The rank-based drift of (SDE)/(SDER): the vector `(b_{ℛ_1}, …, b_{ℛ_N})` with
`ℛ_i = rank(i; x)`. -/
noncomputable def rankDrift {N : ℕ} (b : Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => b (rank x i)

end RankBasedSDI.LoadBalancing


