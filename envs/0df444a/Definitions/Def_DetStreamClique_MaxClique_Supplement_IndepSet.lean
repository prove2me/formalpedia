-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_Supplement_IndepSet
-- name    : DetStreamClique_MaxClique_Supplement_IndepSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:18:17.180736+00:00
-- url     : https://prove2.me/theorems/9e3eb87c-1582-434d-ad96-5878ef1dc5ea
-- title:
--   β-approximate Maximum Independent Set and insertion-only streaming correctness
-- statement:
--   Vertices are $V=\operatorname{Fin}(n)$ and graphs are simple, undirected and unweighted. Write $\alpha(G)$ for the independence number of $G$, the largest size of a set of vertices no two of which are adjacent. For a real approximation ratio $\beta$, a finite vertex set $U$ is a **$\beta$-approximate Maximum Independent Set** of $G$ when
--   $$U\text{ is an independent set of }G,\qquad |U|\ge\alpha(G)/\beta.$$
--   Both clauses are part of the definition: the output must be a valid independent set, not only a large set.
--
--   A deterministic streaming machine that reads an insertion-only edge stream is **correct** for this problem at ratio $\beta$ when, on every legal insertion-only stream (distinct, non-loop, unordered edges in any order), its output is a $\beta$-approximate Maximum Independent Set of the graph formed by the streamed edges.
--
--   This is the independent-set mirror of the published approximate-clique predicate, built on the same stream model and machine interface, and is used by the deterministic space lower bound for independent sets.
--
--   **Formalization Note** The independence number is Mathlib's `SimpleGraph.indepNum`; the approximation guarantee uses real division, so non-integer $\beta$ is allowed.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, §1 (definition of β-approximation and of the edge-arrival streaming setting), p. 2

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Graphs

open scoped Classical

namespace DetStreamClique.MaxClique.Supplement

open DetStreamClique.MaxClique

/-- β-approximate Maximum Independent Set (p. 2): an independent set of `G`
of size at least `α(G)/β`. Both clauses are required. -/
def ApproxIndep {n : ℕ} (β : ℝ) (G : Graph n) (out : Finset (Fin n)) : Prop :=
  G.IsIndepSet (out : Set (Fin n)) ∧ (G.indepNum : ℝ) / β ≤ (out.card : ℝ)

/-- Correctness of an insertion-only streaming machine for β-approximate
Maximum Independent Set: on every legal insertion-only stream. -/
def StreamCorrectIndep {n : ℕ} {S : Type}
    (a : StreamingMachine (Edge n) (Finset (Fin n)) S) (β : ℝ) : Prop :=
  ∀ xs, ValidStream xs → ApproxIndep β (streamGraph xs) (a.run xs)

end DetStreamClique.MaxClique.Supplement


