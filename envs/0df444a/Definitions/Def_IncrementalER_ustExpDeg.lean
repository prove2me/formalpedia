-- Prove2me | Definitions.Def_IncrementalER_ustExpDeg
-- name    : IncrementalER_ustExpDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:33.435558+00:00
-- url     : https://prove2.me/theorems/973ecc59-e95e-42ba-9e47-93fc75303f67
-- title:
--   Expected vertex degree in a capacity-weighted random spanning tree
-- statement:
--   A spanning tree of $G$ is a set $F$ of unordered pairs $\{x,y\}$, $x\neq y$, forming a tree on $V$; its capacity is $c(F)=\prod_{e\in F}c(e)$. For $v\in V$,
--
--   $$\mathbb E[\deg_T(v)]=\frac{\sum_F c(F)\,\deg_F(v)}{\sum_F c(F)},$$
--
--   the expected degree of $v$ in a spanning tree $T$ sampled with probability proportional to its capacity (Fact 3.6, item 1).
--
--   **Formalization Note** Trees through a pair of conductance $0$ have capacity $0$. For a multigraph the law of the vertex degrees of the tree is the same as for the merged conductances.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.6, item 1, p.12

import Mathlib
import Definitions.Def_IncrementalER_lap

namespace IncrementalER

/-!
# The expected degree of a vertex in a random spanning tree

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Fact 3.6, item 1, p.12:
"a random uniform spanning tree of G sampled proportional to its capacity c(T) = ∏_{e∈T} c(e)".

**Formalization Note.** A spanning tree is a finite set `F` of unordered pairs `{x, y}` with
`x ≠ y` whose simple graph on `V` is a tree. Its capacity is `∏_{e ∈ F} c(e)`, so a tree using a
pair of conductance `0` has capacity `0` and never occurs. For a multigraph, whose spanning trees
pick one of the parallel edges, the law of the vertex degrees of the tree is the same as for this
collapsed form, because the collapsed conductance is the sum of the parallel capacities. The
expectation is the capacity-weighted average over all spanning trees.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The conductance of an unordered pair, `c({x, y}) = (c(x, y) + c(y, x)) / 2` (`= c(x, y)` for a
symmetric `c`). -/
noncomputable def pairCond (c : V → V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => (c x y + c y x) / 2, fun x y => by dsimp only; ring⟩

/-- `F` is a spanning tree of the complete graph on `V`: no loops, and its graph is a tree. -/
def IsSpanningTree (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, ¬ e.IsDiag) ∧ (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsTree

/-- The capacity `c(F) = ∏_{e ∈ F} c(e)` of a spanning tree. -/
noncomputable def treeCap (c : V → V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∏ e ∈ F, pairCond c e

open Classical in
/-- `E[deg_T(v)]` for a spanning tree `T` drawn with probability proportional to `c(T)`. -/
noncomputable def ustExpDeg (c : V → V → ℝ) (v : V) : ℝ :=
  (∑ F ∈ Finset.univ.filter (fun F : Finset (Sym2 V) => IsSpanningTree F),
      treeCap c F * ((F.filter fun e => v ∈ e).card : ℝ)) /
    ∑ F ∈ Finset.univ.filter (fun F : Finset (Sym2 V) => IsSpanningTree F), treeCap c F

end IncrementalER


