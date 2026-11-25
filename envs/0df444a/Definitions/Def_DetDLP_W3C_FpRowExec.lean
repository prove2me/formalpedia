-- Prove2me | Definitions.Def_DetDLP_W3C_FpRowExec
-- name    : DetDLP_W3C_FpRowExec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:33:03.995803+00:00
-- url     : https://prove2.me/theorems/5f4585de-197b-41f3-831c-d09e2cc3972f
-- title:
--   FP row execution
-- statement:
--   Certified single-call LoopRuns constructors for finite-field row execution
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpTraceStep

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpRowExec

open NineOracleLoop

/-- Extend a certified trace by one controller call.  This is the reusable
    `LoopRuns` constructor needed when a row-search/update round has been
    identified by the controller equations. -/
theorem call_round {step : List Bool → List Bool} {R : List Bool → List Bool → Prop}
    {rounds cap : ℕ} {state answer output nextState query nextAnswer : List Bool}
    (hstep : step (pairWord state answer) = false :: pairWord nextState query)
    (h0 : (pairWord state answer).length ≤ cap)
    (h1 : (pairWord nextState query).length ≤ cap)
    (h2 : nextAnswer.length ≤ cap)
    (hcall : R query nextAnswer)
    (tail : LoopRuns step R rounds nextState nextAnswer output cap) :
    LoopRuns step R (rounds + 1) state answer output cap := by
  exact Or.inr ⟨nextState, query, nextAnswer, hstep, h0, h1, h2, hcall, tail⟩

/-- A one-round terminal observation is a complete bounded trace. -/
theorem halt_round {step : List Bool → List Bool} {R : List Bool → List Bool → Prop}
    {cap : ℕ} {state answer output : List Bool}
    (hstep : step (pairWord state answer) = true :: output)
    (h0 : (pairWord state answer).length ≤ cap)
    (h1 : output.length ≤ cap) :
    LoopRuns step R 1 state answer output cap := Or.inl ⟨hstep, h0, h1⟩

end DetDLP.W3C.FpRowExec


