-- Prove2me | Definitions.Def_DetDLP_W3C_FpDecompOne
-- name    : DetDLP_W3C_FpDecompOne
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T04:24:49.984704+00:00
-- url     : https://prove2.me/theorems/d5d4c904-086d-5a4a-bf69-ecf5bfb47389
-- title:
--   Finite-field decomposition coordinate cycle
-- statement:
--   Defines a bounded single phase-4 decomposition and phase-5 update cycle, and composes its two calls into a LoopRuns segment.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpDecompPhase
import Definitions.Def_DetDLP_W3C_FpRowExec

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpDecompOne

open FpStep FpTraceStep NineOracleLoop

/-- One bounded phase-4 decomposition call followed by its phase-5 update call. -/
structure Cycle (R : List Bool → List Bool → Prop) (cap : ℕ)
    (s next : FpState) (a final : List Bool) where
  mid : FpState
  q : List Bool
  u : List Bool
  v : List Bool
  h4 : step resume (pairWord (packState s) a) = false :: pairWord (packState mid) q
  h5 : step resume (pairWord (packState mid) u) = false :: pairWord (packState next) v
  b0 : (pairWord (packState s) a).length ≤ cap
  b1 : (pairWord (packState mid) q).length ≤ cap
  b2 : u.length ≤ cap
  b3 : (pairWord (packState mid) u).length ≤ cap
  b4 : (pairWord (packState next) v).length ≤ cap
  b5 : final.length ≤ cap
  firstCall : R q u
  secondCall : R v final

/-- Prepend one certified coordinate cycle to any already-built tail trace. -/
theorem cycle_trace {R : List Bool → List Bool → Prop} {cap rounds : ℕ}
    {s next : FpState} {a final output : List Bool}
    (cycle : Cycle R cap s next a final)
    (tail : LoopRuns (step resume) R rounds (packState next) final output cap) :
    LoopRuns (step resume) R (rounds + 2) (packState s) a output cap := by
  apply DetDLP.W3C.FpRowExec.call_round cycle.h4 cycle.b0 cycle.b1 cycle.b2 cycle.firstCall
  exact DetDLP.W3C.FpRowExec.call_round cycle.h5 cycle.b3 cycle.b4 cycle.b5 cycle.secondCall tail

end DetDLP.W3C.FpDecompOne


