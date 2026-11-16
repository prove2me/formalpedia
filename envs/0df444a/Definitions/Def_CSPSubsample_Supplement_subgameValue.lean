-- Prove2me | Definitions.Def_CSPSubsample_Supplement_subgameValue
-- name    : CSPSubsample_Supplement_subgameValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:53.037303+00:00
-- url     : https://prove2.me/theorems/1f2c8b7a-091c-401d-92e3-679eafc300ac
-- title:
--   Sampled subgame value $\omega(G_S)$ and its expectation $\mathbb E_S[\omega(G_S)]$ under sampling with replacement
-- statement:
--   Let $G$ be a $k$-player free game and $N$ a natural number. For each player $i$ let $S_i=(y_{i,1},\dots,y_{i,N})\in Y_i^N$ be a tuple of $N$ questions, and $S=S_1\times\cdots\times S_k$. The **subgame $G_S$** is the free game in which the question of the $i$-th player is sampled uniformly from $S_i$: a position $j_i\in[N]$ is drawn uniformly, independently for each player, and player $i$ is asked $y_{i,j_i}$. A strategy of player $i$ assigns an answer to each element of $S_i$, the same answer to equal elements. Its value is
--   $$
--   \omega(G_S)=\max_{(b_i)_{i\in[k]}}\ \frac1{N^k}\sum_{j\in[N]^k}V\big(y_{1,j_1},\dots,y_{k,j_k},b_1(y_{1,j_1}),\dots,b_k(y_{k,j_k})\big).
--   $$
--   When each $S_i$ is obtained by sampling $N$ elements of $Y_i$ uniformly at random **with replacement**, independently across players, $S$ is uniform over $Y_1^N\times\cdots\times Y_k^N$, and
--   $$
--   \mathbb E_S[\omega(G_S)]=\frac{1}{(|Y_1|\cdots|Y_k|)^N}\sum_{S\in Y_1^N\times\cdots\times Y_k^N}\omega(G_S).
--   $$
--
--   These are the two quantities compared in the subsampling theorem for free games (Theorem 6.1).
--
--   **Formalization Note** An element repeated in $S_i$ is asked with its multiplicity (the paper's proof compares the question law of $G_S$ with $\otimes_i\mathrm{Unif}(S_i)$, pp. 24–25). A strategy is written $b_i:Y_i\to B_i$; only its values on the elements of $S_i$ enter, so the maximum is the paper's maximum over $b_i:S_i\to B_i$ (footnote 2, p. 24). For $N=0$ and $k\ge1$ the sum is empty and Lean returns $0$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Theorem 6.1, p.23 (PDF p.25), and footnote 2 of its proof, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_CSPSubsample_Supplement_FreeGame

set_option autoImplicit false

namespace CSPSubsample.Supplement

namespace FreeGame

variable {k : ℕ}

/-- The value `ω(G_S)` of the **subgame `G_S`** of a free game `G` determined by tuples
`S_i = (y_{i,1}, …, y_{i,N}) ∈ Y_i^N`, `i ∈ [k]`, in which the questions of the `i`-th player
are uniformly sampled from `S_i` (arXiv:2608.00203 (PDF sha256 fd9ae011…), Theorem 6.1, p.23 =
PDF p.25, and footnote 2, p.24 = PDF p.26):
`ω(G_S) = max_{(b_i)} (1/N^k) ∑_{j ∈ [N]^k} V(y_{1,j_1}, …, y_{k,j_k}, b_1(y_{1,j_1}), …, b_k(y_{k,j_k}))`.

**Formalization Note** `S i : Fin N → Y i` is the tuple `S_i`. Player `i`'s question is
`y_{i,j_i}` with the position `j_i` uniform in `[N]`, independently across players, so an
element repeated in `S_i` is asked with its multiplicity (the paper's proof compares the
subgame's question law with `⊗_i Unif(S_i)`, pp.24–25). A strategy is a function of the
question, not of its position (footnote 2: a valid strategy assigns the same value to the
same elements of `S_i`); it is written `b_i : Y_i → B_i`, of which only the values on the
elements of `S_i` enter, so the maximum is the paper's maximum over `b_i : S_i → B_i`. For
`N = 0` and `k ≥ 1` the sum is empty and Lean returns `0/0 = 0`. -/
noncomputable def subgameValue (G : FreeGame k) (N : ℕ) (S : (i : Fin k) → Fin N → G.Y i) : ℝ :=
  ⨆ b : (i : Fin k) → G.Y i → G.B i,
    (∑ j : Fin k → Fin N, G.V (fun i => S i (j i)) (fun i => b i (S i (j i)))) /
      (N : ℝ) ^ k

/-- The expectation `E_S[ω(G_S)]` when, for each `i ∈ [k]`, the tuple `S_i` of size `N` is
chosen by sampling `N` elements of `Y_i` uniformly at random **with replacement**, independently
across players (arXiv:2608.00203 (PDF sha256 fd9ae011…), Theorem 6.1, p.23 = PDF p.25).

**Formalization Note** The `N` draws for player `i` are i.i.d. uniform on `Y_i` and the players'
tuples are independent, so `S = (S_i)_i` is uniform on `(i : Fin k) → Fin N → Y i`, a set of
`(|Y_1|⋯|Y_k|)^N` elements; the expectation is the finite average over it. -/
noncomputable def expSubgameValue (G : FreeGame k) (N : ℕ) : ℝ :=
  (∑ S : (i : Fin k) → Fin N → G.Y i, G.subgameValue N S) /
    (Fintype.card ((i : Fin k) → Fin N → G.Y i) : ℝ)

end FreeGame

end CSPSubsample.Supplement


