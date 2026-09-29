-- Prove2me | Definitions.Def_StochasticProg_MultistageBounds_Tree
-- name    : StochasticProg_MultistageBounds_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:15:01.638989+00:00
-- url     : https://prove2.me/theorems/8cee261b-a82a-48e3-9c10-db1687aa1be8
-- title:
--   Finite scenario tree with H stages
-- statement:
--   A **finite scenario tree** formalizes the multistage event structure Birge & Louveaux build
--   throughout §10.1 (p. 418): the support `Ω = Ω₁ × ⋯ × Ω_H` of a multistage random process,
--   with `Ωᵗ = Ω₁ × ⋯ × Ωₜ` partitioned at every stage `t` into finitely many blocks
--   `Ωᵗ = S^t_1 ∪ ⋯ ∪ S^t_{νₜ}`, consistently from one period to the next (each `S^t_i` is the
--   union of its period-`(t+1)` children's projections).
--
--   A `Tree H` (parameters: a stage count $H\in\mathbb N$) packages this as
--   - a finite type `Node` of tree nodes (one node per block `S^t_i`, at every stage `t`);
--   - `stage : Node → Fin H`, reporting which stage a node belongs to (the book's stage
--     $t=1,\dots,H$ is `stage = 0,\dots,H-1$ here);
--   - `anc : Node → Node`, the ancestor map, required only to raise `stage` by exactly one when
--     applied to any node of positive stage;
--   - a distinguished `root : Node` at stage `0`, the unique node there.
--
--   The derived operation `Tree.children j` collects the period-`(stage j + 1)` nodes whose
--   ancestor is `j`, the book's $D^{t+1}(j)$.
--
--   **Formalization Note** This is the same representation Chunk 06's `Multistage.Tree` uses for
--   the book's exact scenario tree; it is restated in this chunk's own namespace rather than
--   imported, since a draft item cannot import another chunk's draft item. This chunk instantiates
--   it twice: once for the exact tree of (1.1) and once, more coarsely, for the aggregated tree of
--   (1.2) — the pair Chapter 10, Theorem 1 relates.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 418, Chapter 10, Section 10.1

import Mathlib

namespace StochasticProg.MultistageBounds

/-- A finite scenario tree with `H` stages (Birge & Louveaux Ch. 10, §10.1, p. 418: `Ωt` is
partitioned as `Ωt = St1 ∪ ⋯ ∪ Stνt`, consistently from one period to the next). Stages are
`Fin H` (the book's `t = 1` is `stage = 0` here). `Node` collects every scenario/aggregated
node at every stage into one finite type, `stage` reports which stage a node belongs to, and
`anc` is the ancestor map implicit in the book's consistency condition `Sti = ⋃_{j∈Dt+1(i)}
{ωt | (ωt,ωt+1) ∈ St+1j}` (p. 418), required only to raise `stage` by one when applied to a
non-root node. A single distinguished `root` realizes the unique node at stage `t = 1`. This is
the same representation Chunk 06's `Multistage.Tree` uses for the exact (unaggregated) scenario
tree (restated here, not imported: a draft cannot import another chunk's draft, per
`CAPTAIN_BRIEF.md` Addendum 2 rule 5); this chunk uses one instance of it for the exact tree of
(1.1) and a second, coarser instance for the aggregated tree of (1.2). -/
structure Tree (H : ℕ) where
  Node : Type
  fintypeNode : Fintype Node
  decEqNode : DecidableEq Node
  stage : Node → Fin H
  anc : Node → Node
  anc_stage : ∀ j : Node, (stage j).val ≠ 0 → (stage (anc j)).val + 1 = (stage j).val
  root : Node
  root_stage : (stage root).val = 0
  root_unique : ∀ j : Node, (stage j).val = 0 → j = root

variable {H : ℕ} (T : Tree H)

instance : Fintype T.Node := T.fintypeNode
instance : DecidableEq T.Node := T.decEqNode

/-- The period-`t+1` descendants of a node `j` at period `t`, `Dt+1(j)` (p. 289, reused from
Ch. 6's notation). -/
def Tree.children (j : T.Node) : Finset T.Node :=
  Finset.univ.filter (fun k => (T.stage k).val = (T.stage j).val + 1 ∧ T.anc k = j)

end StochasticProg.MultistageBounds


