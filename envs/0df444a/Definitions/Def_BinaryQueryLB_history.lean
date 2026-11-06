-- Prove2me | Definitions.Def_BinaryQueryLB_history
-- name    : BinaryQueryLB_history
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:18.300928+00:00
-- url     : https://prove2.me/theorems/4b6b724d-9d51-4e98-a532-3f050a751225
-- title:
--   Answer history of the run of an algorithm on $(f,G)$
-- statement:
--   The **run** of an algorithm $A$ on $(f,G)$ is the sequence of queries and answers it produces when every answer is computed from $f$ and $G$. The answer history after $t$ steps is defined recursively: it is empty at $t=0$; at each step, if $A$ applied to the current history asks a query, its answer under $G$ on $f$ is appended, and if $A$ stops, the history stays unchanged.
--
--   While the algorithm has not stopped, the history after $t$ steps has exactly $t$ answers.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_Algorithm
import Definitions.Def_BinaryQueryLB_answer

namespace BinaryQueryLB

/-- **Answer history of a run.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.12: "For a function `f` and a chart `G`, the run of
the algorithm on `(f, G)` is the sequence of queries and answers that it produces when every answer
is computed from `f` and `G`."

`history A G f t` is the list of answers after `t` steps of the run of `A` on `(f, G)`: at each step
the algorithm, applied to the current history, either asks a query, whose answer is appended, or
stops, after which the history no longer changes.

**Formalization Note.** Steps are counted from `0`; while the algorithm has not stopped,
`history A G f t` has length `t`. -/
def history {d : ℕ} (A : Algorithm d) (G : Chart d) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ℕ → List Bool
  | 0 => []
  | t + 1 =>
    match A (history A G f t) with
    | Sum.inl qr => history A G f t ++ [answer G f qr]
    | Sum.inr _ => history A G f t

end BinaryQueryLB


