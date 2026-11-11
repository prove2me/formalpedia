-- Prove2me | Definitions.Def_NonMarkovColorings_Main_GraphNotions
-- name    : NonMarkovColorings_Main_GraphNotions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:41.716771+00:00
-- url     : https://prove2.me/theorems/629d84ec-9e28-4d81-b8f8-69f026d1cfb0
-- title:
--   Balls by walk length, induced-subgraph neighbourhoods $N_S$, $N^r_S$, $N_{\le D}(v)$, and fixed total orders on $V$ (§1.3, §3.3, §5)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. For $r\in\mathbb N$ and $T\subseteq V$, the **ball** $B_r(T)$ is the set of vertices that can be reached from some vertex of $T$ by a walk of $G$ with at most $r$ edges (§1.3); for a real radius $R$, $B_R(v)$ is the set of $u$ joined to $v$ by a walk of length at most $R$. For $U\subseteq V$, $G[U]$ is the induced subgraph (kept on the vertex type $V$). For $S\subseteq V$ and $v\in V$,
--   $$N_S(v)=N(v)\setminus S,\qquad N^r_S(T)=B_r(T\setminus S)\setminus (T\setminus S)\ \text{ computed in } G[V\setminus S],$$
--   so $N_S(v)$ is the neighbourhood of $v$ in $G[(V\setminus S)\cup\{v\}]$ (§3.3, p. 15). For $D\in\mathbb N$, $N_{\le D}(v)=\{w\in N(v): d(w)\le D\}$ (§5, p. 33). A **fixed total order** on $V$ is a duplicate-free list of all vertices; the first element of a set in that order is used wherever the paper chooses an element "according to some fixed, but otherwise arbitrary, total order".
--
--   **Formalization Note.** Balls use walk lengths (`SimpleGraph.Walk.length`), so a vertex in another component is never in a ball (Mathlib's `SimpleGraph.dist` would be $0$ there). `ball G r T`, `ballReal G R v`, `restrictGraph G U`, `nbrOut G S v`, `sphereOut G r S T`, `lowDegNbrs G D v`; `VertexOrder V` with `first S` (`none` iff $S=\emptyset$) and `listOf S`.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 6 §1.3; p. 15 §3.3; p. 33 §5

import Mathlib

/-!
# Graph notions: balls by walk length, punctured neighbourhoods, fixed vertex orders

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), §1.3 p. 6,
§3.3 p. 15, §5 p. 33, §3.2–3.4 pp. 14–19.

* `ball G r T` is `B_r(T)`: the vertices reachable from a vertex of `T` by a walk of `G` with at
  most `r` edges (§1.3). Distances are walk lengths, so unreachable vertices are never in a ball.
* `ballReal G R v` is the ball of a real radius `R` (used for `Δ^{1/10}`): walk length `≤ R`.
* `restrictGraph G U` is the induced graph `G[U]`, kept on the vertex type `V` (edges of `G` with
  both ends in `U`).
* `nbrOut G S v` is `N_S(v) = N(v) \ S`, the neighbourhood of `v` in `G[(V \ S) ∪ {v}]` (§3.3).
* `sphereOut G r S T` is `N^r_S(T) = N^r(T \ S)` computed in `G[V \ S]`, where
  `N^r(T') = B_r(T') \ T'` (§1.3, §3.3).
* `lowDegNbrs G D v` is `N_{≤D}(v) = {w ∈ N(v) : d(w) ≤ D}` (§5, p. 33).
* A `VertexOrder V` is a fixed total order on `V`, presented as a duplicate-free list of all
  vertices; `first S` is the first element of `S` in it (`none` iff `S = ∅`), and `listOf S`
  lists `S` in that order. The paper's "fixed, but otherwise arbitrary, total order" choices are
  parameters of type `VertexOrder V`.
-/

namespace NonMarkovColorings.Main

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `B_r(T)`: vertices reachable from some vertex of `T` by a walk with at most `r` edges. -/
def ball (G : SimpleGraph V) (r : ℕ) (T : Finset V) : Finset V :=
  Finset.univ.filter fun u => ∃ x ∈ T, ∃ p : G.Walk x u, p.length ≤ r

/-- The ball of real radius `R` around `v`: vertices joined to `v` by a walk of length `≤ R`. -/
def ballReal (G : SimpleGraph V) (R : ℝ) (v : V) : Finset V :=
  Finset.univ.filter fun u => ∃ p : G.Walk v u, (p.length : ℝ) ≤ R

/-- The induced graph `G[U]`, on the vertex type `V`: `a ~ b` iff `a ~ b` in `G` and
`a, b ∈ U`. -/
def restrictGraph (G : SimpleGraph V) (U : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => G.Adj a b ∧ a ∈ U ∧ b ∈ U

/-- `N_S(v) = N(v) \ S`, the neighbourhood of `v` in `G[(V \ S) ∪ {v}]`. -/
def nbrOut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  G.neighborFinset v \ S

/-- `N^r_S(T)`: `N^r(T \ S) = B_r(T \ S) \ (T \ S)` computed in the graph `G[V \ S]`. -/
def sphereOut (G : SimpleGraph V) (r : ℕ) (S T : Finset V) : Finset V :=
  ball (restrictGraph G (Finset.univ \ S)) r (T \ S) \ (T \ S)

/-- `N_{≤D}(v) = {w ∈ N(v) : d(w) ≤ D}`. -/
def lowDegNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => G.degree w ≤ D

/-- A fixed total order on the vertex set: a duplicate-free list containing every vertex. -/
structure VertexOrder (V : Type*) where
  /-- The vertices, listed in increasing order. -/
  toList : List V
  /-- No vertex is listed twice. -/
  nodup : toList.Nodup
  /-- Every vertex is listed. -/
  complete : ∀ v, v ∈ toList

/-- The first element of `S` in the order (`none` iff `S` is empty). -/
def VertexOrder.first (o : VertexOrder V) (S : Finset V) : Option V :=
  o.toList.find? fun v => decide (v ∈ S)

/-- The elements of `S`, listed in the order. -/
def VertexOrder.listOf (o : VertexOrder V) (S : Finset V) : List V :=
  o.toList.filter fun v => decide (v ∈ S)

end

end NonMarkovColorings.Main


