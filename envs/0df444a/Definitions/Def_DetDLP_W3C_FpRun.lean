-- Prove2me | Definitions.Def_DetDLP_W3C_FpRun
-- name    : DetDLP_W3C_FpRun
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:52:17.016298+00:00
-- url     : https://prove2.me/theorems/f9446f84-3922-4429-a2b9-c43566c3d7b7
-- title:
--   Finite-field Stage-II controller run
-- statement:
--   Compiles the finite-field Stage-II trace controller as a bounded nine-oracle loop.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpTraceStep

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpRun

open Groundwork NineOracleLoop FpStep FpTraceStep
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The nine Stage-II query machines, in the fixed order used by the trace controller. -/
abbrev OracleFamily := Fin 9 → PrimitiveMachine

/-- Compile the finite-field controller as a bounded nine-oracle loop. The remaining
    Stage-II correctness arguments are kept separate from this generic machine-composition
    result: this theorem only packages the already-verified polynomial-time controller and
    the uniform oracle mux. -/
theorem compileOracleLoop (A : OracleFamily) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ), 1 ≤ C ∧
      ∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ → ∀ (rounds maxLen : ℕ) (input output : Word), 1 ≤ rounds →
      LoopRuns (FpStep.step FpTraceStep.resume) (NineCall A o τ σ) rounds input [] output maxLen →
      RunsWithin D out input output
        ((rounds : ℝ) * (polyBound C maxLen + (C : ℝ)*(τ+σ+1)))
        (polyBound C maxLen + (C : ℝ)*(σ+1)) := by
  exact nine_oracle_polyT_loop (FpStep.step FpTraceStep.resume) FpTraceStep.step_poly A o

end DetDLP.W3C.FpRun


