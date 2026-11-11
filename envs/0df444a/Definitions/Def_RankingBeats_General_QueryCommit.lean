-- Prove2me | Definitions.Def_RankingBeats_General_QueryCommit
-- name    : RankingBeats_General_QueryCommit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:28.022613+00:00
-- url     : https://prove2.me/theorems/444017d1-a92e-43db-a7b8-c3d4e4e31ddf
-- title:
--   Query-commit view of Ranking: query times t_uv, R_t, A_t, and the alternating path AltPath^t(x, x_{-v})
-- statement:
--   Fix a rank vector $\vec x$ with distinct ranks. Times are pairs $t\in[0,1)\times[0,1)$ ordered lexicographically. The pair $\{u,v\}$ is first queried at time
--   $$t_{uv}=\min\{(x_u,x_v),(x_v,x_u)\},$$
--   and an edge $(u,v)$ of $R(\vec x)$ is matched exactly at time $t_{uv}$. For a removed set $S$, $R^t(\vec x_{-S})$ is the partial matching formed right before time $t$ — the edges of $R(\vec x_{-S})$ with $t_{uv}<t$ — and $A^t(\vec x_{-S})$ is the set of vertices not in $S$ that are not covered by $R^t(\vec x_{-S})$. The **alternating path** is the symmetric difference
--   $$\mathrm{AltPath}^t(\vec x,\vec x_{-v})=\big(R^t(\vec x)\setminus R^t(\vec x_{-v})\big)\cup\big(R^t(\vec x_{-v})\setminus R^t(\vec x)\big),$$
--   and $\mathrm{AltPath}(\vec x,\vec x_{-v})$ is the same for the full matchings. An edge set $E'$ **is the path $(u_0,\dots,u_k)$ from $v$** when the $u_i$ are pairwise distinct, $u_0=v$, and the edges of $E'$ are exactly the pairs $\{u_i,u_{i+1}\}$ ($k=0$ when $E'=\emptyset$).
--
--   These objects state Fact 3.3 and the Alternating Path Lemma 4.1, and the facts about backups and blockers that rest on it.
--
--   **Formalization Note** Times are `ℝ ×ₗ ℝ` (lexicographic). `partialRanking G S x t` filters the final matching by query time; this equals the paper's partial matching because an edge of $R$ is committed at its query time (p. 12). A path is a `List V`; `IsPathFrom E v p` is `p.Nodup ∧ p.head? = some v ∧ E = pathEdges p`, and $u_i$ is `p.getD i v`, $k$ is `p.length - 1` (the list is nonempty).
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 12 (query-commit view, t_uv, R_t, A_t); p. 13 (AltPath^t, Lemma 4.1)

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking

open Classical

namespace RankingBeats.General

/-!
# The query-commit view of Ranking: query times, `R_t`, `A_t`, and the alternating path

Derakhshan, Yu, *Ranking Beats 1-1/e on General Graphs*, STOC 2027 submission (manuscript sha256
6715d477…), p. 12 (query-commit view), p. 13 (Lemma 4.1, `AltPath^t`).

* Times are pairs in `ℝ ×ₗ ℝ`, ordered lexicographically; the paper's times lie in
  `[0, 1) × [0, 1)`.
* `queryTime x u v = t_uv = min{(x_u, x_v), (x_v, x_u)}`, the first time the pair `(u, v)` is
  queried. It is symmetric, so it is a function of the unordered edge `s(u, v)`.
* `partialRanking G S x t = R_t(x_{-S})`: the partial matching formed right before time `t`, i.e.
  the edges of `R(x_{-S})` whose query time is `< t` (an edge `(u, v)` of `R` is matched exactly at
  time `t_uv`, p. 12).
* `availableAt G S x t = A_t(x_{-S})`: the vertices not removed (`∉ S`) and not covered by
  `R_t(x_{-S})`.
* `altPathAt G x v t = AltPath^t(x, x_{-v}) = (R_t(x) \ R_t(x_{-v})) ∪ (R_t(x_{-v}) \ R_t(x))`;
  `altPath G x v` is the same for the full matchings (`AltPath(x, x_{-v})`).
* A path `p = (u_0, …, u_k)` is a list of pairwise distinct vertices; `IsPathFrom E v p` says it
  starts at `u_0 = v` and its consecutive pairs are exactly the edges of `E` (so `p = [v]`,
  `k = 0`, when `E = ∅`). Its length is `k = p.length - 1` and `u_i = p.getD i v`.
-/

variable {V : Type*}

/-- `t_uv = min{(x_u, x_v), (x_v, x_u)}` in the lexicographic order. -/
noncomputable def queryTime (x : V → ℝ) (u v : V) : ℝ ×ₗ ℝ :=
  min (toLex (x u, x v)) (toLex (x v, x u))

/-- The query time of an unordered edge. -/
noncomputable def edgeTime (x : V → ℝ) : Sym2 V → ℝ ×ₗ ℝ :=
  Sym2.lift ⟨queryTime x, fun _ _ => min_comm _ _⟩

/-- `R_t(x_{-S})`: the edges of `R(x_{-S})` queried (hence matched) strictly before time `t`. -/
noncomputable def partialRanking [Fintype V] [LinearOrder V] (G : SimpleGraph V) (S : Finset V)
    (x : V → ℝ) (t : ℝ ×ₗ ℝ) : Finset (Sym2 V) :=
  (ranking G S x).filter fun e => edgeTime x e < t

/-- `A_t(x_{-S})`: the vertices that are not removed and are still available right before
time `t`. -/
noncomputable def availableAt [Fintype V] [LinearOrder V] (G : SimpleGraph V) (S : Finset V)
    (x : V → ℝ) (t : ℝ ×ₗ ℝ) : Finset V :=
  (Finset.univ \ S).filter fun u => ¬ IsMatched (partialRanking G S x t) u

/-- `AltPath^t(x, x_{-v}) = (R_t(x) \ R_t(x_{-v})) ∪ (R_t(x_{-v}) \ R_t(x))`. -/
noncomputable def altPathAt [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ) (v : V)
    (t : ℝ ×ₗ ℝ) : Finset (Sym2 V) :=
  (partialRanking G ∅ x t \ partialRanking G {v} x t) ∪
    (partialRanking G {v} x t \ partialRanking G ∅ x t)

/-- `AltPath(x, x_{-v}) = (R(x) \ R(x_{-v})) ∪ (R(x_{-v}) \ R(x))`. -/
noncomputable def altPath [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ) (v : V) :
    Finset (Sym2 V) :=
  (ranking G ∅ x \ ranking G {v} x) ∪ (ranking G {v} x \ ranking G ∅ x)

/-- The edges `(u_i, u_{i+1})` of the vertex list `p = (u_0, …, u_k)`. -/
noncomputable def pathEdges (p : List V) : Finset (Sym2 V) :=
  ((p.zip p.tail).map fun q => s(q.1, q.2)).toFinset

/-- The edge set `E` is the path `p = (u_0, …, u_k)` starting at `u_0 = v`: the vertices of `p`
are pairwise distinct, `p` starts at `v`, and the edges of `E` are exactly the consecutive pairs of
`p`. -/
def IsPathFrom (E : Finset (Sym2 V)) (v : V) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some v ∧ E = pathEdges p

end RankingBeats.General


