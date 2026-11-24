-- Prove2me | Definitions.Def_RHX_RunChain
-- name    : RHX_RunChain
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:44:15.000025+00:00
-- url     : https://prove2.me/theorems/73cf701d-1853-4f2e-bf2e-c1de001a8920
-- title:
--   Boolean equality of evaluator states
-- statement:
--   Boolean equalities `RHX.accBeq`, `RHX.accsBeq` and `RHX.stoBeq` on the accumulator records and states (`ArbEcon.Off.StO`) of the framework's offline Euler–Maclaurin evaluator. They let a run of a few thousand evaluator steps between two literal states be checked by one small `decide +kernel`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
/-! Checkpointed evaluator runs: a Boolean equality on evaluator states, so that a run of `k` terms
    between two literal states can be checked by one small `decide +kernel`. -/

namespace RHX

open ArbEcon.Off

/-- Field-wise equality of accumulator balls. -/
def accBeq (x y : Acc) : Bool :=
  Nat.beq x.reP y.reP && Nat.beq x.reN y.reN && Nat.beq x.reR y.reR &&
    Nat.beq x.imP y.imP && Nat.beq x.imN y.imN && Nat.beq x.imR y.imR

/-- Element-wise equality of accumulator lists. -/
def accsBeq : List Acc → List Acc → Bool
  | [], [] => true
  | x :: xs, y :: ys => accBeq x y && accsBeq xs ys
  | _, _ => false

/-- Field-wise equality of evaluator states. -/
def stoBeq (s t : StO) : Bool :=
  Nat.beq s.n t.n && Nat.beq s.llo t.llo && Nat.beq s.lhi t.lhi && Nat.beq s.g t.g &&
    accsBeq s.acc t.acc

end RHX

def RHX_RunChain : Nat := 0


