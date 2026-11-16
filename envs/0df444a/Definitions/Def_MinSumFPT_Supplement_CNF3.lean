-- Prove2me | Definitions.Def_MinSumFPT_Supplement_CNF3
-- name    : MinSumFPT_Supplement_CNF3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:17:49.876833+00:00
-- url     : https://prove2.me/theorems/70314f4c-008e-4b58-a73a-2197114a7417
-- title:
--   3-CNF formulas and their integer encoding
-- statement:
--   A CNF formula on $N$ variables is a list of clauses, each a finite set of literals $x_v$ or $\neg x_v$ ($v<N$); it is satisfiable if some assignment makes a literal of every clause true. A **3-CNF formula** has at most three literals per clause; the empty clause and repeated clauses are allowed.
--
--   The formula is given to a program as the integer list $[N,M]$ ($M$ the number of clauses) followed by each clause as its length and its literals (variable index, then polarity bit $1$ for positive and $0$ for negative).
--
--   This is the input of the 3-SAT decision procedure of Theorem 40.
--
--   **Formalization Note** Formulas, satisfiability and the clause code are the published `FasterWCTFPTAS.Main.Supplement` definitions `CNF`, `CNF.Satisfiable` and `clauseCode`.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 40, p.48 (3-CNF formulas on N variables and O(N) clauses)

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNF
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-!
# 3-CNF formulas and their integer encoding (Theorem 40)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Theorem 40, p.48: "the satisfiability of 3-CNF formulas on N variables and O(N)
clauses".

This module bundles `Is3CNF` and `encodeCNF`.

**Formalization Note.** Formulas are the published `FasterWCTFPTAS.Main.Supplement.CNF` (a number
of variables `N` and a list of clauses, each a finite set of signed variables `Fin N × Bool`) with
its `Satisfiable`. A 3-CNF formula has at most three literals per clause (the empty clause and
repeated clauses are allowed). The integer input is `[N, M]` followed by each clause as its length
and its literals (variable index, polarity bit `1` for positive), through the published
`clauseCode`. -/

open FasterWCTFPTAS.Main.Supplement

/-- Every clause has at most three literals. -/
def Is3CNF (F : CNF) : Prop := ∀ c ∈ F.clauses, c.card ≤ 3

/-- The integer encoding `[N, M, clause codes…]` of a CNF formula. -/
def encodeCNF (F : CNF) : List ℤ :=
  ((F.numVars :: F.clauses.length :: F.clauses.flatMap clauseCode).map fun x : ℕ => (x : ℤ))

end MinSumFPT.Supplement


