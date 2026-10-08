-- Prove2me | Definitions.Def_SpectralSparsify_Pullback_Contraction
-- name    : SpectralSparsify_Pullback_Contraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:33.720076+00:00
-- url     : https://prove2.me/theorems/3a29f875-d3e9-4a73-b085-43b3fc2dfa2f
-- title:
--   Contraction and pullback under a partition map π; the graphs G₀, G₁, the E₁-graph and the lift of a graph on {1,…,k} to representatives (§10.2)
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph and $V_1,\dots,V_k$ a partition of $V$, with **map** $\pi:V\to\{1,\dots,k\}$, $\pi(u)=i$ for $u\in V_i$.
--
--   1. The **contraction** of $G$ under $\pi$ is the weighted graph $H=(\{1,\dots,k\},F,z)$ with
--   $$z(i,j)=\sum_{(u,v):\,\pi(u)=i,\ \pi(v)=j} w(u,v)\qquad (i\neq j),$$
--   and no self-loops: edges inside a part do not appear in the contraction.
--   2. Given a weighted graph $\widetilde H=(\{1,\dots,k\},\widetilde F,\tilde z)$, a weighted graph $\widetilde G=(V,\widetilde E,\tilde w)$ is a **pullback** of $\widetilde H$ under $\pi$ if (0) every edge of $\widetilde G$ joins two different parts, (1) $\widetilde H$ is the contraction of $\widetilde G$ under $\pi$, and (2) for every edge $(i,j)\in\widetilde F$, $\widetilde E$ contains exactly one edge $(u,v)$ with $\pi(u)=i$ and $\pi(v)=j$.
--   3. $E_0=\partial(V_1,\dots,V_k)$ is the set of edges between different parts, $G_0=(V,E_0,w)$, $E_1=E-E_0$ and $G_1=(V,E_1,w)$. The **$E_1$-graph** is the unweighted graph on $V$ whose edges are those of $E_1$; "$V_i$ is connected by edges in $E_1$" means any two vertices of $V_i$ are joined by a path in it.
--   4. Given representatives $v_i\in V_i$, the **lift** of a weighted graph $H$ on $\{1,\dots,k\}$ is the weighted graph on $V$ supported on $\{v_1,\dots,v_k\}$ that is isomorphic to $H$ under $i\mapsto v_i$. In the proof of Lemma 10.2, $F$ and $\widetilde F$ are the lifts of $H$ and $\widetilde H$.
--
--   These are the objects of §10.2, where contraction lets a sparsifier for the light edges between heavily connected parts be built on the much smaller contracted graph.
--
--   **Formalization Note** The partition is `π : V → Fin k` (parts $V_i=\pi^{-1}(i)$; Lemma 10.2 assumes `π` surjective, so that the parts are nonempty). `contraction w π i j` sums `w u v` over ordered pairs with `π u = i`, `π v = j` and is $0$ for $i=j$; as $i\neq j$ fixes the orientation, each undirected edge between $V_i$ and $V_j$ is counted once. Condition (0) of `IsPullback` is left implicit in the paper ($\widetilde E$ consists of the pulled-back edges, and in the proof of part (c) the sum runs over "all edges in $\widetilde E_0$"); it is required, since contraction cannot see an edge inside a part and without it Lemma 10.2 is false. Condition (2) is stated for $i\neq j$ with $\tilde z(i,j)\neq 0$, as a unique ordered pair `(u, v)` with `π u = i`, `π v = j`, `wt u v ≠ 0`. `crossPart w π` is $G_0$, `intraPart w π` is $G_1$, `intraGraph w π` is the $E_1$-graph (built with `SimpleGraph.fromRel`), and `liftAlong r z` is the lift along representatives `r : Fin k → V`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 36, §10.2 (map of a partition, contraction, pullback; statement of Lemma 10.2); p. 37, proof of Lemma 10.2 (F, F̃)

import Mathlib

namespace SpectralSparsify.Pullback

/-- The contraction of a weighted graph `w` on `V` under the map `π : V → Fin k` of a partition
`V₁, …, V_k` (`Vᵢ = π⁻¹(i)`), arXiv:0808.4134v3, §10.2, p. 36: the weighted graph on `Fin k` with
`z(i, j) = ∑_{(u,v) : π(u) = i, π(v) = j} w(u, v)` for `i ≠ j`, and no self-loops (`z(i, i) = 0`). -/
def contraction {V : Type*} [Fintype V] {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) :
    Fin k → Fin k → ℝ :=
  fun i j => if i = j then 0 else
    ∑ u ∈ Finset.univ.filter (fun u => π u = i), ∑ v ∈ Finset.univ.filter (fun v => π v = j), w u v

/-- `w̃` is a pullback of the weighted graph `z̃` on `Fin k` under `π` (§10.2, p. 36):
(0) every edge of `w̃` joins two different parts (the paper's `Ẽ` consists of the pulled-back edges,
left implicit there); (1) `z̃` is the contraction of `w̃` under `π`; and (2) for every edge `(i, j)` of
`z̃` there is exactly one edge `(u, v)` of `w̃` with `π u = i` and `π v = j`. -/
def IsPullback {V : Type*} [Fintype V] {k : ℕ} (wt : V → V → ℝ) (zt : Fin k → Fin k → ℝ)
    (π : V → Fin k) : Prop :=
  (∀ u v, π u = π v → wt u v = 0) ∧
  contraction wt π = zt ∧
  ∀ i j, i ≠ j → zt i j ≠ 0 → ∃! p : V × V, π p.1 = i ∧ π p.2 = j ∧ wt p.1 p.2 ≠ 0

/-- `G₀ = (V, E₀, w)` with `E₀ = ∂(V₁, …, V_k)` the edges between different parts (p. 36). -/
def crossPart {V : Type*} {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) : V → V → ℝ :=
  fun u v => if π u = π v then 0 else w u v

/-- `G₁ = (V, E₁, w)` with `E₁ = E − E₀` the edges inside the parts (p. 36). -/
def intraPart {V : Type*} {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) : V → V → ℝ :=
  fun u v => if π u = π v then w u v else 0

/-- The (unweighted) graph of the edges in `E₁`: `u ~ v` iff `u ≠ v`, `π u = π v` and `w u v ≠ 0`
(symmetrized). Hypothesis 1 of Lemma 10.2, "each `Vᵢ` is connected by edges in `E₁`", is reachability
in this graph between any two vertices of the same part. -/
def intraGraph {V : Type*} {k : ℕ} (w : V → V → ℝ) (π : V → Fin k) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => π u = π v ∧ w u v ≠ 0)

/-- Given representatives `r i ∈ Vᵢ`, the weighted graph on `V` supported on `{r 1, …, r k}` that is
isomorphic to the graph `z` on `Fin k` under `i ↦ r i` (proof of Lemma 10.2, p. 37: `F` from `H`,
`F̃` from `H̃`): weight `z(i, j)` between `r i` and `r j`, `0` elsewhere. -/
def liftAlong {V : Type*} [DecidableEq V] {k : ℕ} (r : Fin k → V) (z : Fin k → Fin k → ℝ) :
    V → V → ℝ :=
  fun u v => ∑ i, ∑ j, if r i = u ∧ r j = v then z i j else 0

end SpectralSparsify.Pullback


