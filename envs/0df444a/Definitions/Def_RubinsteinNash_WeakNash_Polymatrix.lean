-- Prove2me | Definitions.Def_RubinsteinNash_WeakNash_Polymatrix
-- name    : RubinsteinNash_WeakNash_Polymatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:33.13082+00:00
-- url     : https://prove2.me/theorems/da19f519-e572-4797-8b75-f1068d29620c
-- title:
--   Def. 2.9, p. 11, and §8.1, p. 50 — polymatrix games and the complete bipartite polymatrix game
-- statement:
--   Let $\mathcal I$ be a finite set of players, and let each player $i$ have a finite action set $A_i$.
--
--   1. A **polymatrix game** (Definition 2.9) is given by a two-player *subgame* for every ordered pair of distinct players $i\neq j$, in which player $i$ receives $v^j_i(a_i,a_j)$ when $i$ plays $a_i$ and $j$ plays $a_j$. Every player plays the same action in all of its subgames, and its utility is the sum of its subgame utilities:
--   $$u_i(a_i,a_{-i})=\sum_{j\neq i} v^j_i(a_i,a_j).$$
--   2. A **complete bipartite polymatrix game** has its players split into two sides $V_A$ and $V_B$. Every $v\in V_A$ and every $w\in V_B$ play a bimatrix subgame, in which $v$ receives $U^{v,w}(s,t)$ and $w$ receives $U^{w,v}(t,s)$ when $v$ plays $s\in S^v$ and $w$ plays $t\in S^w$; two vertices on the same side play no subgame. Hence
--   $$U^v(a)=\sum_{w\in V_B}U^{v,w}(a_v,a_w)\quad(v\in V_A),\qquad U^w(a)=\sum_{v\in V_A}U^{w,v}(a_w,a_v)\quad(w\in V_B).$$
--
--   These are the games of Section 8.1, whose WeakNash equilibria are trimmed into well-supported ones in Lemma 8.1.
--
--   **Formalization Note.** The player type is the disjoint union `VA ⊕ VB`; `PA v w` is the matrix $U^{v,w}$ of $v\in V_A$ against $w\in V_B$ and `PB w v` the matrix $U^{w,v}$ of $w\in V_B$ against $v\in V_A$. The general polymatrix payoff sums over $j\neq i$; in the bipartite instance the same-side subgames are the zero matrix, so the sum for $v\in V_A$ is over $V_B$ only.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), Definition 2.9, p. 11, and proof of Lemma 8.1, §8.1, p. 50 (first display)

import Mathlib

namespace RubinsteinNash.WeakNash

open Finset

/-- **Polymatrix game** (Definition 2.9, p. 11): each pair of distinct players `i ≠ j` plays a
two-player subgame, in which `i` receives `G i j (s i) (s j)`; every player plays the same
strategy in all its subgames, and its utility is the sum of its subgame utilities,
`u_i(a_i, a_{-i}) = Σ_{j ≠ i} v^j_i(a_i, a_j)`. -/
def polymatrixPayoff {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (G : (i j : ι) → S i → S j → ℝ) : ι → (∀ i, S i) → ℝ :=
  fun i s => ∑ j ∈ univ.erase i, G i j (s i) (s j)

/-- The subgame payoffs of a **complete bipartite** polymatrix game with sides `VA` and `VB`
(§8.1, p. 50): a vertex `v ∈ VA` and a vertex `w ∈ VB` play a bimatrix subgame in which `v`
receives `PA v w (s v) (s w)` and `w` receives `PB w v (s w) (s v)`; two vertices on the same
side play no subgame (payoff `0`). -/
def bipartiteSubgames {VA VB : Type*} {S : VA ⊕ VB → Type*}
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ) :
    (i j : VA ⊕ VB) → S i → S j → ℝ
  | Sum.inl v, Sum.inr w => fun a b => PA v w a b
  | Sum.inr w, Sum.inl v => fun b a => PB w v b a
  | Sum.inl _, Sum.inl _ => fun _ _ => 0
  | Sum.inr _, Sum.inr _ => fun _ _ => 0

/-- The utilities of the complete bipartite polymatrix game with subgame payoffs `PA`, `PB`:
`U^v = Σ_{w ∈ VB} U^{v,w}` for `v ∈ VA` and `U^w = Σ_{v ∈ VA} U^{w,v}` for `w ∈ VB`
(proof of Lemma 8.1, p. 50). -/
def bipartitePolymatrixPayoff {VA VB : Type*} [Fintype VA] [DecidableEq VA]
    [Fintype VB] [DecidableEq VB] {S : VA ⊕ VB → Type*}
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ) :
    VA ⊕ VB → (∀ i, S i) → ℝ :=
  polymatrixPayoff (bipartiteSubgames PA PB)

end RubinsteinNash.WeakNash


