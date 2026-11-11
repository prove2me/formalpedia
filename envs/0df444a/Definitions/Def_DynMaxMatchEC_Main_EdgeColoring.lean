-- Prove2me | Definitions.Def_DynMaxMatchEC_Main_EdgeColoring
-- name    : DynMaxMatchEC_Main_EdgeColoring
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:02:31.353074+00:00
-- url     : https://prove2.me/theorems/1fada5f9-2982-41af-8a2a-f123c50bd683
-- title:
--   Degree-bounded edge updates, edge-list input, the reported edge coloring and proper k-edge-colorings
-- statement:
--   A **$k$-edge-coloring** of a graph $G$ assigns to every edge a color in $\{1,\dots,k\}$ so that two distinct edges sharing an endpoint get different colors (§2.1). Here colors are natural numbers and $k$ is a real number (so that $\Delta+n^{f(n)}$ or $(1+\varepsilon)\Delta$ colors can be stated): $\chi$ is a proper $k$-edge-coloring of $G$ if $1\le\chi(e)\le k$ for every edge $e$ of $G$ and $\chi(e)\ne\chi(f)$ for distinct edges $e,f$ of $G$ with a common endpoint.
--
--   For the dynamic coloring theorems, an update is legal for the degree bound $\Delta$ if it is an edge update and afterwards every vertex has degree at most $\Delta$ (`IsDegLegal`). The initial graph $G_0$ is given in preprocessing, after the parameters, by its number of edges $m_0$ and its edges, each as two vertex words, in an arbitrary order and orientation (`edgeWords`, `IsEdgeList`).
--
--   The **reported coloring** after preprocessing or a completed update is the all-uncolored assignment ($0$) with every output triple $u,v,c$ ("edge $uv$ now has color $c$") written so far applied in order; triples that do not name two distinct vertices are ignored. `ColoringOK k G out` says that the reported coloring of the output `out` is a proper $k$-edge-coloring of $G$. `MaxDegLE Δ G` says every degree is at most $\Delta$, and `maxDeg G` is the maximum degree.
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 3, §1.2; p. 4, Theorem 1.2; p. 11, §2.1; p. 59, Theorem 5.1; p. 78, Theorem C.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model

namespace DynMaxMatchEC.Main

open DynBrooks

/-!
# Degree-bounded updates, edge-list input, and the reported edge coloring

Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring* (manuscript, Nov. 1,
2026; PDF sha256 2c277528…4ca5), §1.2 p. 3, Theorem 1.2 p. 4, §2.1 p. 11, Theorem 5.1 p. 59,
Theorem C.1 p. 78.

* A **k-edge-coloring** of `G` assigns to every edge of `G` a color in `{1, …, k}` so that two
  distinct edges with a common endpoint get different colors (§2.1). Colors are natural numbers; the
  bound `k` is a real number so that `Δ + n^{f(n)}` colors can be stated.
* The dynamic coloring algorithms receive the initial graph `G₀` in preprocessing as its number of
  edges `m₀` followed by its edges, each as two vertex words, in an arbitrary order and orientation
  (`edgeWords`); the parameters precede them.
* An update is legal for the degree bound `Δ` when it is an edge update (`IsEdgeUpdate`) and every
  vertex has degree at most `Δ` afterwards.
* **Reported coloring.** The output is read as triples `u, v, c`, each meaning "the edge `uv` now has
  color `c`". The coloring `χ` after preprocessing or after a completed update is the all-`0`
  (uncolored) assignment with every triple written so far applied in order; a triple whose vertex
  words are not two distinct vertices `< n` is ignored. Correctness is checked on the edges of the
  current graph only.
-/

open Classical in
/-- Every vertex of `G` has degree at most `Δ`. -/
def MaxDegLE {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v : Fin n, G.degree v ≤ Δ

open Classical in
/-- The maximum vertex degree `Δ(G)` of `G` (`0` for the graph without vertices). -/
noncomputable def maxDeg {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.maxDegree

/-- A legal update for the degree bound `Δ`: an edge update after which every degree is at
most `Δ`. -/
def IsDegLegal {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) (x : Update n) : Prop :=
  IsEdgeUpdate G x ∧ MaxDegLE Δ (x.apply G)

/-- `es` lists every edge of `G` exactly once, in any order and orientation. -/
def IsEdgeList {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun e => s(e.1, e.2)).Nodup ∧
    ∀ e : Sym2 (Fin n), e ∈ G.edgeSet ↔ e ∈ es.map fun e => s(e.1, e.2)

/-- The words describing an edge list: its length `m₀`, then the two endpoints of every edge. -/
def edgeWords {n : ℕ} (es : List (Fin n × Fin n)) : List ℕ :=
  es.length :: es.flatMap fun e => [e.1.val, e.2.val]

/-- Apply one color record `u, v, c`: the edge `uv` gets color `c`. -/
def applyColorRecord {n : ℕ} (χ : Sym2 (Fin n) → ℕ) : ℕ × ℕ × ℕ → (Sym2 (Fin n) → ℕ)
  | (u, v, c) =>
      match toEdge n u v with
      | some e => Function.update χ e c
      | none => χ

/-- The reported edge coloring: every edge uncolored (`0`), with every record of the output applied
in order. -/
def reportedColoring (n : ℕ) (out : List ℕ) : Sym2 (Fin n) → ℕ :=
  (triples out).foldl applyColorRecord fun _ => 0

/-- `χ` is a proper edge coloring of `G` with colors in `{1, …, ⌊k⌋}`: every edge of `G` gets a
color `c` with `1 ≤ c ≤ k`, and two distinct edges of `G` with a common endpoint get different
colors. -/
def IsProperEdgeColoring {n : ℕ} (k : ℝ) (G : SimpleGraph (Fin n)) (χ : Sym2 (Fin n) → ℕ) :
    Prop :=
  (∀ e ∈ G.edgeSet, 1 ≤ χ e ∧ (χ e : ℝ) ≤ k) ∧
    ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f → (∃ v : Fin n, v ∈ e ∧ v ∈ f) → χ e ≠ χ f

/-- The dynamic coloring guarantee: the reported coloring of the output so far is a proper edge
coloring of the current graph with at most `k` colors. -/
def ColoringOK {n : ℕ} (k : ℝ) (G : SimpleGraph (Fin n)) (out : List ℕ) : Prop :=
  IsProperEdgeColoring k G (reportedColoring n out)

end DynMaxMatchEC.Main


