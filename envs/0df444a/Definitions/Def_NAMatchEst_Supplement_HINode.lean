-- Prove2me | Definitions.Def_NAMatchEst_Supplement_HINode
-- name    : NAMatchEst_Supplement_HINode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:36:06.400894+00:00
-- url     : https://prove2.me/theorems/cdfb1214-62e0-4c2a-b371-716c2384b461
-- title:
--   Template nodes $A$, $B_i$, $C_j$ of the §7 hard instance
-- statement:
--   The **template nodes** of one side of the hard instance of §7.1: a node $A$, nodes $B_1,\dots,B_\alpha$ and auxiliary nodes $C_1,\dots,C_{r-1}$. In the construction each node $X$ on side $S\in\{L,R\}$ stands for a vertex set $X^S$ of $t$ vertices; the dummy sets $D^S$ are not template nodes.
--
--   These nodes index the templates (`templateMult`), the lifts (`TemplateLift`) and the core vertex set $U^L\sqcup U^R$ used in Theorem 10.
--
--   **Formalization Note** Indices are 0-based: `B i` is $B_{i+1}$ and `C j` is $C_{j+1}$, introduced at stage $j+1$. The side is carried separately as a Boolean (`false` = $L$).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.92 (PDF 96)

import Mathlib

namespace NAMatchEst.Supplement

/-- The **template nodes** of one side of the §7.1 hard instance: the node `A`, the nodes
`B i` for `i ∈ [α]`, and the auxiliary nodes `C j` for `j ∈ [r − 1]`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.92 (PDF 96):
"For each S ∈ {L, R}, fix pairwise disjoint vertex sets A^S, B^S_i for i ∈ [α], C^S_j for
j ∈ [r − 1], and D^S, each of cardinality t."

**Formalization Note** Indices are 0-based: `B i` with `i : Fin α` is the paper's `B_{i+1}`, and
`C j` with `j : Fin (r - 1)` is the paper's `C_{j+1}`, introduced at stage `j + 1`. The side
`S ∈ {L, R}` is carried separately (a `Bool`, `false` = `L`). The dummy sets `D^S` are not
template nodes. -/
inductive HINode (α r : ℕ) where
  /-- The node `A`. -/
  | A
  /-- The node `B_{i+1}`. -/
  | B (i : Fin α)
  /-- The auxiliary node `C_{j+1}`. -/
  | C (j : Fin (r - 1))
  deriving DecidableEq, Fintype

end NAMatchEst.Supplement


