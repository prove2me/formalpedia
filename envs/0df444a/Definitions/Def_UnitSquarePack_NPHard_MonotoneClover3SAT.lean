-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_MonotoneClover3SAT
-- name    : UnitSquarePack_NPHard_MonotoneClover3SAT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:20.447453+00:00
-- url     : https://prove2.me/theorems/635b19e8-4286-4dde-a96a-2a0b9eb026fc
-- title:
--   The language Monotone-Clover-3SAT
-- statement:
--   An instance of **Clover-3SAT** is a 3SAT formula with variables $x_0, \dots, x_{n-1}$ (the paper's $x_1, \dots, x_n$) and two lists of clauses $c_0, \dots, c_{p-1}$ and $d_0, \dots, d_{q-1}$, with $p, q \ge 1$, together with a planar embedding of the **clover graph** $G$ whose vertices are the $x_i$, $c_j$, $d_j$ and whose edges are
--
--   - $x_i c_j$ whenever $x_i$ or $\neg x_i$ appears in $c_j$, and $x_i d_j$ likewise;
--   - the paths $x_0x_1\cdots x_{n-1}$, $c_0 c_1 \cdots c_{p-1}$ and $d_0 d_1 \cdots d_{q-1}$;
--   - the four edges $x_0c_0$, $c_0x_{n-1}$, $x_{n-1}d_0$, $d_0x_0$.
--
--   The instance is **monotone** if every $c_j$ is a positive clause and every $d_j$ a negative clause.
--
--   The language **Monotone-Clover-3SAT** is the set of binary codes of $(n, (c_j), (d_j))$ with $p, q \ge 1$, all clauses well formed (one to three literals on $x_0, \dots, x_{n-1}$), the instance monotone, the clover graph planar (it has a crossing-free drawing, published `WilliamsonShmoys.HasPlanarDrawingOn`), and the formula $c_0 \wedge \cdots \wedge c_{p-1} \wedge d_0 \wedge \cdots \wedge d_{q-1}$ satisfiable.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 18, §4.2, definition of Clover-3SAT

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_UnitSquarePack_NPHard_Formula

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open OptimalQueuingComplexity.Restless

/-- An instance of Clover-3SAT: the variables `x_0, …, x_{n-1}` (the paper's `x_1, …, x_n`) and
the two clause lists `c_0, …, c_{p-1}` (`cs`) and `d_0, …, d_{q-1}` (`ds`). -/
structure CloverInstance where
  n : ℕ
  cs : CookPvsNP.CNF
  ds : CookPvsNP.CNF

namespace CloverInstance

variable (Φ : CloverInstance)

/-- The number of vertices of the clover graph: `n + p + q`. -/
def size : ℕ := Φ.n + Φ.cs.length + Φ.ds.length

/-- The edge relation of the clover graph `G` on `Fin (n + p + q)`: vertex `i < n` is `x_i`,
vertex `n + j` is `c_j`, vertex `n + p + j` is `d_j`. Edges: `x_i c_j` (resp. `x_i d_j`) whenever
`x_i` or `¬x_i` occurs in `c_j` (resp. `d_j`); the paths `x_0 x_1 ⋯ x_{n-1}`, `c_0 ⋯ c_{p-1}`,
`d_0 ⋯ d_{q-1}`; and the four edges `x_0 c_0`, `c_0 x_{n-1}`, `x_{n-1} d_0`, `d_0 x_0`
(the paper's `(x_1, c_1), (c_1, x_n), (x_n, d_1), (d_1, x_1)`). -/
def rel (u v : Fin Φ.size) : Prop :=
  (u.val < Φ.n ∧ Φ.n ≤ v.val ∧ v.val < Φ.n + Φ.cs.length ∧
      Occurs u.val (Φ.cs.getD (v.val - Φ.n) [])) ∨
  (u.val < Φ.n ∧ Φ.n + Φ.cs.length ≤ v.val ∧
      Occurs u.val (Φ.ds.getD (v.val - Φ.n - Φ.cs.length) [])) ∨
  (v.val = u.val + 1 ∧ v.val < Φ.n) ∨
  (Φ.n ≤ u.val ∧ v.val = u.val + 1 ∧ v.val < Φ.n + Φ.cs.length) ∨
  (Φ.n + Φ.cs.length ≤ u.val ∧ v.val = u.val + 1) ∨
  (u.val = 0 ∧ v.val = Φ.n) ∨
  (u.val = Φ.n ∧ v.val + 1 = Φ.n) ∨
  (u.val + 1 = Φ.n ∧ v.val = Φ.n + Φ.cs.length) ∨
  (u.val = Φ.n + Φ.cs.length ∧ v.val = 0)

/-- The clover graph `G` (symmetric, loopless closure of `rel`). -/
def graph : SimpleGraph (Fin Φ.size) := SimpleGraph.fromRel Φ.rel

/-- Binary code: `n`, then the clauses `c_j`, then the clauses `d_j`. -/
def code : List Bool := encNat Φ.n ++ encClauses Φ.cs ++ encClauses Φ.ds

end CloverInstance

/-- The language Monotone-Clover-3SAT: codes of instances with at least one clause `c` and at
least one clause `d` (the paper names `c_1` and `d_1`), every clause having one to three
literals on `x_0, …, x_{n-1}`, every `c_j` positive and every `d_j` negative, the clover graph
planar (it has a crossing-free drawing in the plane), and the formula
`c_0 ∧ ⋯ ∧ c_{p-1} ∧ d_0 ∧ ⋯ ∧ d_{q-1}` satisfiable. -/
def monotoneClover3SAT : CookPvsNP.Lang Bool :=
  {w | ∃ Φ : CloverInstance, w = Φ.code ∧ 1 ≤ Φ.cs.length ∧ 1 ≤ Φ.ds.length ∧
      (∀ C ∈ Φ.cs ++ Φ.ds, ClauseOK Φ.n C) ∧
      (∀ C ∈ Φ.cs, IsPositiveClause C) ∧ (∀ C ∈ Φ.ds, IsNegativeClause C) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Φ.graph ∧
      CookPvsNP.CNF.Satisfiable (Φ.cs ++ Φ.ds)}

end UnitSquarePack.NPHard


