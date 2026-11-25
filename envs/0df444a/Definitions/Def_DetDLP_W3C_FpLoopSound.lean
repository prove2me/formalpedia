-- Prove2me | Definitions.Def_DetDLP_W3C_FpLoopSound
-- name    : DetDLP_W3C_FpLoopSound
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:35:27.138805+00:00
-- url     : https://prove2.me/theorems/4e58616d-ad0d-4b1b-b76b-643f78a71531
-- title:
--   Finite-field Stage-II loop trace compilation
-- statement:
--   Compiles a bounded nine-oracle finite-field controller trace from a certified oracle kit into one machine with uniform polynomial time and space bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpOracles
import Definitions.Def_DetDLP_W3C_FpRun

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpLoopSound

open Groundwork NineOracleLoop FpStep FpTraceStep
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The nine machines certified by an oracle kit, in the order expected by the trace. -/
def family {en de : FpOracles.Port} (K : FpOracles.Kit en de) : Fin 9 → PrimitiveMachine :=
  fun j => (K.ports j).1

/-- The corresponding designated output tape for each oracle machine. -/
def outputs {en de : FpOracles.Port} (K : FpOracles.Kit en de) :
    ∀ j, Fin ((family K j).tapeCount) := fun j => (K.ports j).2

/-- Bounded trace simulation for the finite-field controller. Every intermediate
state, query, and answer word in `LoopRuns` is subject to `maxLen`; compilation
therefore yields a single machine with uniform time and space bounds. -/
theorem compileKitTrace {en de : FpOracles.Port} (K : FpOracles.Kit en de) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ), 1 ≤ C ∧
      ∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
        ∀ (rounds maxLen : ℕ) (input output : Word), 1 ≤ rounds →
        LoopRuns (FpStep.step FpTraceStep.resume)
          (NineCall (family K) (outputs K) τ σ) rounds input [] output maxLen →
        RunsWithin D out input output
          ((rounds : ℝ) * (polyBound C maxLen + (C : ℝ) * (τ + σ + 1)))
          (polyBound C maxLen + (C : ℝ) * (σ + 1)) := by
  exact FpRun.compileOracleLoop (family K) (outputs K)

/-- Construct an oracle kit from the explicit count-oracle parameter and compile its
trace. This keeps the preprocessing dependency explicit and avoids requiring the
unproved global count-oracle existence theorem. -/
theorem compileFromCounts (en de : FpOracles.Port)
    (counts : DetDLP.M89S1.CountOracle)
    (net : DetDLP.w3_terminalOps DetDLP.w3_fpQueries)
    (update : DetDLP.w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ), 1 ≤ C ∧
      ∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
        ∀ (rounds maxLen : ℕ) (input output : Word), 1 ≤ rounds →
        ∀ (K : FpOracles.Kit en de),
          K = Classical.choice (FpOracles.available counts en de net update) →
          LoopRuns (FpStep.step FpTraceStep.resume)
            (NineCall (family K) (outputs K) τ σ) rounds input [] output maxLen →
          RunsWithin D out input output
            ((rounds : ℝ) * (polyBound C maxLen + (C : ℝ) * (τ + σ + 1)))
            (polyBound C maxLen + (C : ℝ) * (σ + 1)) := by
  let K : FpOracles.Kit en de := Classical.choice (FpOracles.available counts en de net update)
  obtain ⟨D,out,C,hC,hbound⟩ := compileKitTrace K
  refine ⟨D,out,C,hC,?_⟩
  intro τ σ ht hs rounds maxLen input output hr K' hK trace
  subst K'
  exact hbound τ σ ht hs rounds maxLen input output hr trace

end DetDLP.W3C.FpLoopSound


