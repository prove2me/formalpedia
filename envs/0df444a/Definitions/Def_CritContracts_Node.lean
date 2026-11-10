-- Prove2me | Definitions.Def_CritContracts_Node
-- name    : CritContracts_Node
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:35.572721+00:00
-- url     : https://prove2.me/theorems/7794b9bb-57a4-491c-bfaa-8765604c1e6d
-- title:
--   The vertices of the reduction's bipartite graph
-- statement:
--   The vertex set of the bipartite graph built in Appendix B.1.1 for a Subset Sum instance with $k$ items:
--
--   1. the zero-cost **anchors** $u_0\in U$ and $v_0\in V$;
--   2. the **state vertices** $p_i\in V$ and $q_i\in U$ for every item $i$;
--   3. the **verification vertices** $r_0\in U$ and $r_1\in V$;
--   4. the **amplification vertices** $a\in U$ and $b\in V$;
--   5. the two internal vertices $z$ and $y$ of every **three-edge path** $s-z-y-t$; $z$ lies on the side of $t$ and $y$ on the side of $s$.
--
--   The three-edge paths are, for every pair of items $j<i$, one path from $q_j$ to $p_i$ and one from $p_j$ to $q_i$, and the two final paths from $r_1$ to $a$ and from $r_0$ to $b$. Each path has a source $s$ and a target $t$ on opposite sides.
--
--   **Formalization Note** Items are $0,\dots,k-1$ in Lean (the paper's item $i+1$). The paths are indexed by the type `PathIx k` (the pairs $j<i$ twice, plus the two final paths), and `Node.side` gives the side (`0` for $U$, owned by agent 1; `1` for $V$, owned by agent 2).
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Appendix B.1.1, pp.33–36 (PDF pp.34–37), Figures 5 and 6

import Mathlib

set_option autoImplicit false

namespace CritContracts

/-- The pairs `j < i` of items, indexing the state paths of Appendix B.1.1 (Ezra–Feldman–Molina–Schlesinger,
*Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript sha256
430be35c…), p.35, PDF p.36). `e.1.1` is the earlier item `j`, `e.1.2` the later item `i`. -/
abbrev ItemPair (k : ℕ) := {x : Fin k × Fin k // x.1 < x.2}

/-- The three-edge paths of the construction (pp.34–36): for every pair `j < i` a path from `q_j` to `p_i`
(`qp`) and one from `p_j` to `q_i` (`pq`); the final paths from `r₁` to `a` (`ra`) and from `r₀` to `b` (`rb`).

**Formalization Note** Items are `0, …, k − 1` here and `1, …, k` in the paper: item `i` here is the paper's item
`i + 1`. -/
inductive PathIx (k : ℕ) where
  /-- The path of value `2·3^{−j}` from `q_j` to `p_i`, `j < i`. -/
  | qp (e : ItemPair k)
  /-- The path of value `2·3^{−j}` from `p_j` to `q_i`, `j < i`. -/
  | pq (e : ItemPair k)
  /-- The path of value `12ΔD` from `r₁` to `a`. -/
  | ra
  /-- The path of value `12ΔD` from `r₀` to `b`. -/
  | rb
  deriving DecidableEq, Fintype

/-- The vertices of the bipartite graph of Appendix B.1.1 (pp.33–36) for `k` items:
`anchor 0 = u₀ ∈ U`, `anchor 1 = v₀ ∈ V` (p.33); the state vertices `p i ∈ V` and `q i ∈ U` (p.35);
`ver 0 = r₀ ∈ U`, `ver 1 = r₁ ∈ V` (p.36); `amp 0 = a ∈ U`, `amp 1 = b ∈ V` (p.36); and the two internal
vertices `z π` (on the side of the path's target) and `y π` (on the side of its source) of every three-edge path
`π` (p.34). -/
inductive Node (k : ℕ) where
  /-- The zero-cost anchors `u₀` (`s = 0`) and `v₀` (`s = 1`). -/
  | anchor (s : Fin 2)
  /-- The state vertex `p_i ∈ V`. -/
  | p (i : Fin k)
  /-- The state vertex `q_i ∈ U`. -/
  | q (i : Fin k)
  /-- The verification vertices `r₀ ∈ U` (`s = 0`) and `r₁ ∈ V` (`s = 1`). -/
  | ver (s : Fin 2)
  /-- The amplification vertices `a ∈ U` (`s = 0`) and `b ∈ V` (`s = 1`). -/
  | amp (s : Fin 2)
  /-- The internal vertex `z` of a three-edge path, adjacent to its source. -/
  | z (pth : PathIx k)
  /-- The internal vertex `y` of a three-edge path, adjacent to its target. -/
  | y (pth : PathIx k)
  deriving DecidableEq, Fintype

namespace PathIx

variable {k : ℕ}

/-- The source `s` of a three-edge path. -/
def src : PathIx k → Node k
  | qp e => Node.q e.1.1
  | pq e => Node.p e.1.1
  | ra => Node.ver 1
  | rb => Node.ver 0

/-- The target `t` of a three-edge path. -/
def tgt : PathIx k → Node k
  | qp e => Node.p e.1.2
  | pq e => Node.q e.1.2
  | ra => Node.amp 0
  | rb => Node.amp 1

/-- The side of the source of a three-edge path (`0` for `U`, `1` for `V`). -/
def srcSide : PathIx k → Fin 2
  | qp _ => 0
  | pq _ => 1
  | ra => 1
  | rb => 0

end PathIx

/-- The side of a vertex: `0` for `U` (agent 1), `1` for `V` (agent 2). The internal vertex `z` of a path lies on
the side of its target and `y` on the side of its source (p.34). -/
def Node.side {k : ℕ} : Node k → Fin 2
  | anchor s => s
  | p _ => 1
  | q _ => 0
  | ver s => s
  | amp s => s
  | z pth => 1 - pth.srcSide
  | y pth => pth.srcSide

end CritContracts


