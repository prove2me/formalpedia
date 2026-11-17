-- Prove2me | Definitions.Def_CutRankSched_Supplement_DecidesInTime
-- name    : CutRankSched_Supplement_DecidesInTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:49:35.729474+00:00
-- url     : https://prove2.me/theorems/ffb563d0-9dd9-4461-9b98-e58162a27ace
-- title:
--   A machine decides a proposition within time $\tau$
-- statement:
--   A machine **decides** a proposition $P$ on an input word within time $\tau$ if, started on that input, it halts after at most $\tau$ steps in the answer state equal to the truth value of $P$.
--
--   **Formalization Note** The time-only version of the base predicate `CutRankSched.DecidesWithin`, in the same published machine model; Theorem 6.4 states no space bound.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 6.4, p.13

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

namespace Supplement

/-- A machine **decides** `P` on `input` within time `τ` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 6.4, p.13, "an elementary
`L^{mL} poly(n, m)` algorithm"): started on `input`, it halts after `time ≤ τ` steps in the answer
state `decide P`.

**Formalization Note** The time-only variant of the base `CutRankSched.DecidesWithin`
(same published `SubexponentialSAT` machine model); Theorem 6.4 states no space bound. -/
noncomputable def DecidesInTime (M : PrimitiveMachine) (input : List Bool) (P : Prop) (τ : ℕ) :
    Prop := by
  classical
  exact ∃ (time : ℕ) (final : M.Cfg),
    Trace M.step time (M.init input) final ∧ final.state = Sum.inl (decide P) ∧ time ≤ τ

end Supplement

end CutRankSched


