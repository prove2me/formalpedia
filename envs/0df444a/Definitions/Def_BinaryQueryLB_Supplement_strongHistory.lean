-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_strongHistory
-- name    : BinaryQueryLB_Supplement_strongHistory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:50:32.800771+00:00
-- url     : https://prove2.me/theorems/ee806869-fb2b-409a-880f-c0e4f3aa96b1
-- title:
--   Answer history of a run with $O^*$
-- statement:
--   For an algorithm $A$ with $O^*$, a chart $G$ and a function $f$, the **run** of $A$ on $(f,G)$ is the sequence of queries and answers it produces when every answer is computed from $f$ and $G$. The history after $t$ steps is the list of answer pairs received so far: at each step $A$, applied to the current history, either asks a query $(y,v)$, whose answer $\big(f(y),\langle v,G(f,y)\rangle\big)$ is appended, or stops, after which the history no longer changes.
--
--   **Formalization Note** Steps are counted from $0$; while $A$ has not stopped, the history after $t$ steps has length $t$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_Supplement_StrongAlgorithm
import Definitions.Def_BinaryQueryLB_Supplement_strongAnswer

namespace BinaryQueryLB.Supplement

/-- **Answer history of a run with O\*.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.12: "For a function `f` and a chart `G`, the run of the algorithm on `(f, G)` is the sequence of
queries and answers that it produces when every answer is computed from `f` and `G`"; with `O∗` the
answers are the exact pairs `(f(y), ⟨v, g_f(y)⟩)`.

`strongHistory A G f t` is the list of answer pairs after `t` steps of the run of `A` on `(f, G)`:
at each step the algorithm, applied to the current history, either asks a query `(y, v)`, whose
answer `strongAnswer G f (y, v)` is appended, or stops, after which the history no longer changes.

**Formalization Note.** Steps are counted from `0`; while the algorithm has not stopped,
`strongHistory A G f t` has length `t`. -/
noncomputable def strongHistory {d : ℕ} (A : StrongAlgorithm d) (G : BinaryQueryLB.Chart d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => []
  | t + 1 =>
    match A (strongHistory A G f t) with
    | Sum.inl q => strongHistory A G f t ++ [strongAnswer G f q]
    | Sum.inr _ => strongHistory A G f t

end BinaryQueryLB.Supplement


