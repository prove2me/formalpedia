-- Prove2me | Definitions.Def_SubmodOrder_OracleProg
-- name    : SubmodOrder_OracleProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:13.182427+00:00
-- url     : https://prove2.me/theorems/c66b2ea7-9bb0-4cae-8e15-c9a01367e074
-- title:
--   Value-oracle programs and their query count
-- statement:
--   A **value-oracle program** for set functions on a ground set $N$ is an adaptive procedure that may repeatedly ask for the value $f(S)$ of a set $S$ of its choice, choosing each next step from the answers received so far, and finally returns a result. Formally a program is either a result, or a query of a set $S$ together with a continuation: a program for each possible answer $f(S)\in\mathbb R$.
--
--   Running a program against a set function $f$ answers every query $S$ by $f(S)$. Its **number of oracle queries** on $f$ is the number of queries along this run.
--
--   This is the cost model of Theorem 2 of the paper, which counts oracle queries.
--
--   **Formalization Note** A program never receives $f$ itself and can learn about $f$ only through queries, so a query count cannot be circumvented. Computation inside the continuations (arithmetic, comparisons, logarithms, maxima) is free, as in the paper.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Theorem 2, p.5, "O(n/ε log k) oracle queries"; proof of Theorem 2, p.20

import Mathlib

namespace SubmodOrder

/-- A value-oracle program over the ground set `α` returning a value of type `β` (the query model
of Udwani, arXiv:2107.02743v5, Theorem 2, p.5: "O(n/ε log k) oracle queries").

A program either stops with a result (`pure b`) or asks the oracle for the value of a set `S`
and continues with a program that depends on the answer (`query S cont`).

**Formalization Note.** A program is a term of this type and never receives the set function
`f` itself: it learns about `f` only through the answers to its queries. All other computation
(arithmetic, comparisons, `⌈log⌉`, maxima) happens inside the continuations and is free, as in
the paper, which counts oracle queries only. -/
inductive OracleProg (α β : Type*) where
  | pure : β → OracleProg α β
  | query : Finset α → (ℝ → OracleProg α β) → OracleProg α β

namespace OracleProg

variable {α β γ : Type*}

/-- Sequential composition of oracle programs: run `p`, then `g` on its result. -/
def bind : OracleProg α β → (β → OracleProg α γ) → OracleProg α γ
  | pure b, g => g b
  | query S cont, g => query S fun v => bind (cont v) g

/-- The result of running the program `p` against the value oracle of `f`: every query `S` is
answered with `f S`. -/
def run (f : Finset α → ℝ) : OracleProg α β → β
  | pure b => b
  | query S cont => run f (cont (f S))

/-- The number of oracle queries the program makes when run against the value oracle of `f`
(each `query` costs one, along the execution path that the answers of `f` select). -/
def queries (f : Finset α → ℝ) : OracleProg α β → ℕ
  | pure _ => 0
  | query S cont => queries f (cont (f S)) + 1

end OracleProg

end SubmodOrder


