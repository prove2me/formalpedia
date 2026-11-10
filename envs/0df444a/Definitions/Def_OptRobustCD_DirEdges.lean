-- Prove2me | Definitions.Def_OptRobustCD_DirEdges
-- name    : OptRobustCD_DirEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:49:58.067031+00:00
-- url     : https://prove2.me/theorems/42adba1b-9378-4f0e-b635-c22b731d1b53
-- title:
--   Vectors on directed edges, Euclidean norms, edit distance $|E(G)\triangle E(G')|$ and balls $|B_G(v,s)|$
-- statement:
--   Basic notation of §3.2 and §4.
--
--   **Vectors on directed edges.** For a graph $G$ on $[n]$, $\vec E(G)$ is its set of directed edges, both orientations $u\to v$, $v\to u$ of every edge. As on p.15, $\mathbb R^{\vec E(G)}$ is viewed as the subspace of $\mathbb R^{n^2-n}$ of vectors indexed by ordered pairs of distinct vertices that vanish off $\vec E(G)$, so vectors on the directed edges of different graphs on $[n]$ are compared in one space. The restriction $y|_{\vec E(G)}$ sets the entries off $\vec E(G)$ to $0$.
--
--   **Norms.** $\|x\|=(\sum_i x_i^2)^{1/2}$, $\langle x,y\rangle=\sum_i x_iy_i$ and $\|x\|_4^4=\sum_i x_i^4$, for vectors indexed by any finite set.
--
--   **Edits and balls.** $|E(G)\triangle E(G')|$ is the number of edges in exactly one of $G,G'$; the endpoints of these edges form the set $A$ of Lemma 4.12. $|B_G(v,s)|$ is the number of vertices of $G$ within graph distance $s$ of $v$ (p.21). $|\vec E(G)|=2|E(G)|$.
--
--   **Formalization Note** Vectors on ordered pairs are functions on `Fin n × Fin n`; the diagonal is never an edge. Norms are written out because Lean's default norm on functions is the sup norm. Distances are extended (`edist`, infinite between components), so unreachable vertices are not in any ball.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §3.2 p.13 (pdf p.15); §4 p.15 (pdf p.17); Lemma 4.10 p.21 (pdf p.23); Lemma 4.12 p.23 (pdf p.25)

import Mathlib

namespace OptRobustCD

/-!
# Vectors on directed edges, Euclidean norms, edit distance and graph balls

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §3.2 (p.13, pdf p.15), the
opening of §4 (p.15, pdf p.17), Theorem 1.1 (p.2, pdf p.4) and §4.3 (p.21, pdf p.23).

"We view `R^{E⃗(G)}`, for every graph `G` on `[n]`, as the subspace of `R^{n²−n}` consisting of the
vectors indexed by ordered pairs of distinct vertices that vanish off `E⃗(G)`." (p.15)

**Formalization Note.**
* A vector on directed edges is `EVec n := Fin n × Fin n → ℝ`; a vector "in `R^{E⃗(G)}`" is one
  that vanishes off `G.Adj` (`SupportedOn G`). The diagonal is never an edge, so for supported
  vectors the norms below are those of `R^{n²−n}`.
* Norms are Euclidean, written out (`l2`): Lean's default norm on a function type is the sup norm.
* `|E(G) △ E(G′)|` is the number of unordered edges in the symmetric difference (`editDist`).
* `|B_G(v, s)|` is the number of vertices within graph distance `s` of `v` (`ballCard`), using the
  extended distance `edist` (`⊤` between different components), so unreachable vertices are not
  counted.
-/

open Finset
open scoped Classical

/-- Vectors indexed by ordered pairs of vertices. -/
abbrev EVec (n : ℕ) := Fin n × Fin n → ℝ

/-- The Euclidean norm `(∑ᵢ xᵢ²)^{1/2}`. -/
noncomputable def l2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean inner product `∑ᵢ xᵢ yᵢ`. -/
def ip {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

/-- `‖x‖₄⁴ = ∑ᵢ xᵢ⁴`. -/
def l4pow4 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 4

/-- `y ∈ R^{E⃗(G)}`: `y` vanishes off the directed edges of `G`. -/
def SupportedOn {n : ℕ} (G : SimpleGraph (Fin n)) (y : EVec n) : Prop :=
  ∀ p : Fin n × Fin n, ¬ G.Adj p.1 p.2 → y p = 0

/-- The restriction `y|_{E⃗(G)}`: the entries off `E⃗(G)` set to `0`. -/
noncomputable def restrictTo {n : ℕ} (G : SimpleGraph (Fin n)) (y : EVec n) : EVec n :=
  fun p => if G.Adj p.1 p.2 then y p else 0

/-- `|E⃗(G)|`, the number of directed edges (twice the number of edges). -/
noncomputable def numArcs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2).card

/-- `|E(G)|`, the number of (undirected) edges. -/
noncomputable def numEdges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := G.edgeFinset.card

/-- `|E(G) △ E(G′)|`, the number of edges in exactly one of the two graphs. -/
noncomputable def editDist {n : ℕ} (G G' : SimpleGraph (Fin n)) : ℕ :=
  (symmDiff G.edgeFinset G'.edgeFinset).card

/-- The endpoints of the edges in `E(G) △ E(G′)`. -/
noncomputable def editEndpoints {n : ℕ} (G G' : SimpleGraph (Fin n)) : Finset (Fin n) :=
  univ.filter fun a => ∃ v, ¬ (G.Adj a v ↔ G'.Adj a v)

/-- `|B_G(v, s)|`, the number of vertices of `G` within graph distance `s` of `v`. -/
noncomputable def ballCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℕ) : ℕ :=
  (univ.filter fun u => G.edist v u ≤ (s : ℕ∞)).card

end OptRobustCD


