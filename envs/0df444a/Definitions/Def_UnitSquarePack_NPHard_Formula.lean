-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_Formula
-- name    : UnitSquarePack_NPHard_Formula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:18:34.268049+00:00
-- url     : https://prove2.me/theorems/d674c8b0-f936-45fe-9fc7-fe85a5f5fce2
-- title:
--   3SAT clauses with at most three literals, positive and negative clauses, and their binary code
-- statement:
--   Formulas are in conjunctive normal form over the published `CookPvsNP.CNF`: a list of clauses, each a list of literals $(\mathrm{true}, i)$ for $x_i$ and $(\mathrm{false}, i)$ for $\neg x_i$. With $n$ variables $x_0, \dots, x_{n-1}$ (the paper's $x_1, \dots, x_n$), a clause is **well formed** if it has one, two or three literals, each on a variable of index $< n$ ("a 3SAT instance has at most 3 vertices per clause", p. 20). A clause is **positive** if all its literals are positive and **negative** if all are negative; an instance is **monotone** when every clause is positive or negative. The variable $x_i$ **occurs** in a clause if $x_i$ or $\neg x_i$ is one of its literals.
--
--   A list of clauses is written in binary as the number of clauses followed, for each clause, by its length and its literals (a sign bit and the variable index in binary).
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 4, §2.1 (monotone 3SAT); p. 20, caption of Figure 23

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open OptimalQueuingComplexity.Restless

/-- A 3SAT clause over the variables `x_0, …, x_{n-1}` (the paper's `x_1, …, x_n`): one to three
literals, each on a variable of index `< n`. A literal is `(true, i)` for `x_i` and `(false, i)`
for `¬x_i`, as in `CookPvsNP.Literal`. -/
def ClauseOK (n : ℕ) (C : List CookPvsNP.Literal) : Prop :=
  1 ≤ C.length ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.2 < n

/-- A positive clause: all its literals are positive. -/
def IsPositiveClause (C : List CookPvsNP.Literal) : Prop := ∀ l ∈ C, l.1 = true

/-- A negative clause: all its literals are negative. -/
def IsNegativeClause (C : List CookPvsNP.Literal) : Prop := ∀ l ∈ C, l.1 = false

/-- The variable `x_i` occurs in the clause `C` (as `x_i` or as `¬x_i`). -/
def Occurs (i : ℕ) (C : List CookPvsNP.Literal) : Prop := ∃ l ∈ C, l.2 = i

/-- Binary code of a list of clauses: the number of clauses, then for each clause its length and
its literals (a sign bit followed by the variable index in binary). -/
def encClauses (F : CookPvsNP.CNF) : List Bool :=
  encNat F.length ++ F.flatMap (fun C => encNat C.length ++ C.flatMap (fun l => l.1 :: encNat l.2))

end UnitSquarePack.NPHard


