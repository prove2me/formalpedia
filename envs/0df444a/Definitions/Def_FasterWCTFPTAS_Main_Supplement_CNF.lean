-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNF
-- name    : FasterWCTFPTAS_Main_Supplement_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:06:37.3884+00:00
-- url     : https://prove2.me/theorems/1476905a-353f-43b3-b38e-2a96b00d2947
-- title:
--   CNF formulas with canonical finite-set clauses
-- statement:
--   A Boolean formula has $N$ variables and a list of $M$ clauses. Each clause is a finite set of signed variables $(j,b)$, with $b=1$ denoting the positive literal. The formula is satisfiable precisely when
--
--   $$\exists a\in\{0,1\}^N\quad\forall C\in F\quad\exists(j,b)\in C:\ a_j=b.$$
--
--   Empty clauses and repeated clauses are permitted; an empty formula is true. The input consists of $N,M$, then each clause's length and its variable-index/polarity pairs in increasing index order, negative before positive. Its length is at most $2+M(1+4N)$ real cells. This is a general CNF object, separate from the machine and hardness assumption, supporting the conditional lower bounds.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), pp.6,19 (PDF pp.7,20), CNF-SETH.

import Mathlib

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- A general Boolean CNF. Clauses are sets of signed variables, the clause list may repeat
clauses, and both the empty clause and empty formula are allowed. A true polarity is positive.
Source: CNF-SETH, printed pp. 6 and 19 (PDF 7 and 20). -/
structure CNF where
  numVars : ℕ
  clauses : List (Finset (Fin numVars × Bool))

/-- One assignment makes at least one literal of every clause true. -/
def CNF.Satisfiable (F : CNF) : Prop :=
  ∃ a : Fin F.numVars → Bool,
    ∀ c ∈ F.clauses, ∃ literal ∈ c, a literal.1 = literal.2

/-- Canonical clause enumeration: increasing variable index, negative before positive. -/
def clauseLiterals {N : ℕ} (c : Finset (Fin N × Bool)) : List (Fin N × Bool) :=
  ((List.finRange N).flatMap fun j => [(j, false), (j, true)]).filter
    (fun literal => decide (literal ∈ c))

/-- Clause length followed by its variable-index/polarity pairs. -/
def clauseCode {N : ℕ} (c : Finset (Fin N × Bool)) : List ℕ :=
  c.card :: (clauseLiterals c).flatMap
    (fun literal => [literal.1.val, if literal.2 then 1 else 0])

/-- `[N,M]` followed by the canonical clauses, one natural per real input cell.
Length is at most `2 + M * (1 + 4*N)`; unrestricted repeated literals are not encoded. -/
def CNF.encode (F : CNF) : List ℝ :=
  ((F.numVars :: F.clauses.length :: F.clauses.flatMap clauseCode).map
    fun x => (x : ℝ))

end FasterWCTFPTAS.Main.Supplement


