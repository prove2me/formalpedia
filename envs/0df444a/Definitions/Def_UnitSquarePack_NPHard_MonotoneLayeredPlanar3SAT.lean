-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_MonotoneLayeredPlanar3SAT
-- name    : UnitSquarePack_NPHard_MonotoneLayeredPlanar3SAT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:25.993669+00:00
-- url     : https://prove2.me/theorems/7c11b39a-9087-4c9c-b026-f4fecfb1d3b2
-- title:
--   The language Monotone-Layered-Planar-3SAT
-- statement:
--   An instance of **Layered-Planar-3SAT** is a 3SAT formula $\Phi$ with variables $x_0, \dots, x_{n-1}$ and clauses $c_0, \dots, c_{m-1}$ together with a planar, integer-coordinate, straight-line embedding of its incidence graph (edges $x_i c_j$ whenever $x_i$ or $\neg x_i$ occurs in $c_j$) in which every variable vertex has an even $y$-coordinate, every clause vertex an odd $y$-coordinate, and every edge joins two vertices whose $y$-coordinates differ by $1$. The embedding is part of the input. It is planar when distinct vertices get distinct points, no edge segment contains a vertex other than its endpoints, and two distinct edge segments meet only in a common endpoint.
--
--   The instance is **monotone** if every clause vertex with $y$-coordinate of the form $4k+1$ is a positive clause and every clause vertex with $y$-coordinate of the form $4k-1$ (that is, $y \equiv 3 \pmod 4$) is a negative clause.
--
--   The language **Monotone-Layered-Planar-3SAT** is the set of binary codes (the number $n$, the clauses, then all vertex coordinates as binary integers) of monotone instances with well-formed clauses and a layered planar embedding whose formula is satisfiable.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 18, §4.2, definition of Layered-Planar-3SAT (pp. 18–19)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_UnitSquarePack_NPHard_GridPolygon
import Definitions.Def_UnitSquarePack_NPHard_Formula

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Set OptimalQueuingComplexity.Restless

/-- An instance of Layered-Planar-3SAT: `n` variables `x_0, …, x_{n-1}`, the clauses `F`, and an
integer-coordinate drawing of the incidence graph: `varPos i` is the point of `x_i` and
`clausePos j` the point of the `j`-th clause. -/
structure LayeredInstance where
  n : ℕ
  F : CookPvsNP.CNF
  varPos : List (ℤ × ℤ)
  clausePos : List (ℤ × ℤ)

namespace LayeredInstance

variable (I : LayeredInstance)

/-- The point of the variable `x_i`. -/
def varPt (i : ℕ) : ℤ × ℤ := I.varPos.getD i (0, 0)

/-- The point of the `j`-th clause. -/
def clausePt (j : ℕ) : ℤ × ℤ := I.clausePos.getD j (0, 0)

/-- `x_i c_j` is an edge of the incidence graph: `x_i` or `¬x_i` occurs in `c_j`. -/
def IsEdge (i j : ℕ) : Prop := i < I.n ∧ j < I.F.length ∧ Occurs i (I.F.getD j [])

/-- The straight-line drawing of the edge `x_i c_j`. -/
def edgeSeg (i j : ℕ) : Set (ℝ × ℝ) := segment ℝ (toPlane (I.varPt i)) (toPlane (I.clausePt j))

/-- The drawing is a planar, integer-coordinate, straight-line embedding of the incidence graph
with variable vertices at even `y`, clause vertices at odd `y`, and every edge joining two
vertices whose `y`-coordinates differ by `1`. Planarity: distinct vertices get distinct points,
no edge passes through a vertex other than its two endpoints, and two distinct edges meet only in
a common endpoint. -/
def IsLayeredEmbedding : Prop :=
  I.varPos.length = I.n ∧ I.clausePos.length = I.F.length ∧
  (∀ i < I.n, Even (I.varPt i).2) ∧
  (∀ j < I.F.length, Odd (I.clausePt j).2) ∧
  (∀ i j, I.IsEdge i j → |(I.varPt i).2 - (I.clausePt j).2| = 1) ∧
  (∀ i < I.n, ∀ i' < I.n, I.varPt i = I.varPt i' → i = i') ∧
  (∀ j < I.F.length, ∀ j' < I.F.length, I.clausePt j = I.clausePt j' → j = j') ∧
  (∀ i < I.n, ∀ j < I.F.length, I.varPt i ≠ I.clausePt j) ∧
  (∀ i j, I.IsEdge i j →
    (∀ i' < I.n, i' ≠ i → toPlane (I.varPt i') ∉ I.edgeSeg i j) ∧
    (∀ j' < I.F.length, j' ≠ j → toPlane (I.clausePt j') ∉ I.edgeSeg i j)) ∧
  (∀ i j i' j', I.IsEdge i j → I.IsEdge i' j' → (i, j) ≠ (i', j') →
    ∀ z ∈ I.edgeSeg i j ∩ I.edgeSeg i' j',
      (i = i' ∧ z = toPlane (I.varPt i)) ∨ (j = j' ∧ z = toPlane (I.clausePt j)))

/-- Monotone: a clause whose vertex has `y`-coordinate `4k + 1` is positive, one whose vertex has
`y`-coordinate `4k - 1` (that is, `≡ 3 (mod 4)`) is negative. -/
def IsMonotone : Prop :=
  ∀ j < I.F.length,
    ((I.clausePt j).2 % 4 = 1 → IsPositiveClause (I.F.getD j [])) ∧
    ((I.clausePt j).2 % 4 = 3 → IsNegativeClause (I.F.getD j []))

/-- Binary code: `n`, the clauses, then all vertex coordinates (integers in binary). -/
def code : List Bool :=
  encNat I.n ++ encClauses I.F ++ I.varPos.flatMap (fun v => encInt v.1 ++ encInt v.2) ++
    I.clausePos.flatMap (fun v => encInt v.1 ++ encInt v.2)

end LayeredInstance

/-- The language Monotone-Layered-Planar-3SAT: codes of instances (formula together with the
embedding) where every clause has one to three literals on `x_0, …, x_{n-1}`, the embedding is
a layered planar embedding, the instance is monotone, and the formula is satisfiable. -/
def monotoneLayeredPlanar3SAT : CookPvsNP.Lang Bool :=
  {w | ∃ I : LayeredInstance, w = I.code ∧ (∀ C ∈ I.F, ClauseOK I.n C) ∧
      I.IsLayeredEmbedding ∧ I.IsMonotone ∧ CookPvsNP.CNF.Satisfiable I.F}

end UnitSquarePack.NPHard


