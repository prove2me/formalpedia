-- Prove2me | Definitions.Def_ExactOneHS_Counting_Output
-- name    : ExactOneHS_Counting_Output
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:26.419785+00:00
-- url     : https://prove2.me/theorems/c8f947e4-a241-485a-8391-b40919dbe8a7
-- title:
--   The output of the Exact-One Hitting Set procedure: a number, or two CNF queries on one set of declared variables
-- statement:
--   A **query pair** consists of a number $N$ of declared variables and two ordinary unweighted CNF formulas $Q_0, Q_1$ over the same variables $x_1, \dots, x_N$ (CNFs in the sense of `SubexponentialSAT`: finite sets of clauses, each a finite set of literals). Every one of the $N$ variables is declared, including those that occur in no clause, so $\#\mathrm{SAT}(Q_\beta)$ counts assignments in $\{0,1\}^N$.
--
--   An **output** of the Exact-One Hitting Set procedure is either a number $z$ (an answer computed directly) or a query pair. Both queries are part of one output and are therefore fixed before either count is known; this is what "nonadaptively" means.
--
--   Outputs are coded as bit strings: a tag bit, followed for a number by its binary representation (least significant bit first, the `countWord` of `SubexponentialSAT`), and for a query pair by the codes `encodeCNF` of $Q_0$ and of $Q_1$ (each starts with $N$ in unary and lists the clauses as increasing lists of literal codes $2v + [\text{positive}]$).
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 5, Theorem 1.2 ("two ordinary unweighted 3-CNFs Q0, Q1, nonadaptively"); p. 10, §3 Conventions (#SAT over all declared variables)

import Mathlib
import Definitions.Def_SubexponentialSAT

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- Two ordinary unweighted CNF queries `Q₀, Q₁` over one common set `Fin N` of declared
variables (every variable of `Fin N` is declared, also those occurring in no clause). -/
structure QueryPair where
  /-- the common number of declared variables -/
  N : ℕ
  /-- the query `Q₀` -/
  Q0 : SAT.CNF (Fin N)
  /-- the query `Q₁` -/
  Q1 : SAT.CNF (Fin N)

/-- Code of a query pair: `encodeCNF Q₀` followed by `encodeCNF Q₁` (each starts with `N` in
unary). Both queries are written out together, before any count is known. -/
def encodeQueryPair (q : QueryPair) : List Bool :=
  Encoding.encodeCNF q.Q0 ++ Encoding.encodeCNF q.Q1

/-- The output of the Exact-One Hitting Set procedure: either a directly computed number or a
pair of counting queries. -/
inductive Output
  | direct (z : ℕ)
  | queries (q : QueryPair)

/-- Code of an output: a tag bit, then the number in binary (least significant bit first,
`countWord`) or the two queries. -/
def encodeOutput : Output → List Bool
  | .direct z => true :: SqrtLogSpace.countWord z
  | .queries q => false :: encodeQueryPair q

end ExactOneHS.Counting


