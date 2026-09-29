-- Prove2me | Definitions.Def_StochasticProg_Multistage_Tree
-- name    : StochasticProg_Multistage_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:07:19.785327+00:00
-- url     : https://prove2.me/theorems/277c7134-86c9-4a84-a984-622f251d4161
-- title:
--   Finite scenario tree for a multistage stochastic program
-- statement:
--   A **finite scenario tree** with $H$ stages, formalizing Birge & Louveaux's scenario
--   structure for a multistage stochastic linear program (Ch. 6, p. 267: "for every stage
--   $t=1,\dots,H$ and each scenario at that stage, $k=1,\dots,K^t$").
--
--   `Tree H` bundles a type `Node` of all scenarios at every stage together with a function
--   `stage : Node -> Fin H` reporting which stage a node belongs to, an ancestor map
--   `anc : Node -> Node` that raises `stage` by exactly one on every non-root node (the book's
--   $a(k)$, p. 288: "$a(k)$ is the ancestor scenario of $k$ at stage $t-1$"), and a
--   distinguished `root` that is the unique node at stage $0$ (the book's single scenario
--   $j = K^1 = 1$ at $t=1$, p. 289). `Tree.children T j` is the Finset of period-$(t+1)$
--   descendants of a scenario $j$ at period $t$, the book's $D^{t+1}(j)$ (p. 288).
--
--   **Formalization Note.** Stage comparisons are stated on `.val : ℕ` (e.g. `(stage j).val =
--   0`) rather than as equalities in `Fin H`, so that the definition needs no assumption that
--   `H ≠ 0` merely to write the numeral `0` or the successor `+1` in `Fin H`.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 267-268, 288-289, Chapter 6, Section 6.1

import Mathlib

namespace StochasticProg.Multistage

/-- A finite scenario tree with `H` stages (Birge & Louveaux Ch. 6, p. 267: "for every stage
`t = 1,...,H` and each scenario at that stage, `k = 1,...,K^t`"). Stages are `Fin H`
(book's `t = 1` is `stage = 0` here). `Node` collects every scenario at every stage into one
finite type, `stage` reports which stage a node belongs to, and `anc` is the book's ancestor
map `a(k)` (p. 288: "`a(k)` is the ancestor scenario of `k` at stage `t-1`"), required only to
raise `stage` by one when applied to a non-root node; its value at the root is never used. A
single distinguished `root` realizes the book's "`j = K^1 = 1`" (p. 289: at `t = 2` there is
exactly one scenario at `t - 1 = 1`). Stage comparisons are stated on `.val : ℕ` throughout to
avoid needing a `Fin H` literal/successor instance that would otherwise require `H ≠ 0`. -/
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

/-- The period-`t+1` descendants of a scenario `j` at period `t`, `D^{t+1}(j)` (p. 288). -/
def Tree.children (j : T.Node) : Finset T.Node :=
  Finset.univ.filter (fun k => (T.stage k).val = (T.stage j).val + 1 ∧ T.anc k = j)

end StochasticProg.Multistage


