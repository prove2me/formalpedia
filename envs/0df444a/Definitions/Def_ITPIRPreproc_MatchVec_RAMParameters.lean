-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_RAMParameters
-- name    : ITPIRPreproc_MatchVec_RAMParameters
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T18:24:06.931757+00:00
-- url     : https://prove2.me/theorems/41046191-33c3-4d75-a371-123b1e4d8a11
-- title:
--   Word-RAM program computing the matching-vector word length
-- statement:
--   An explicit streaming word-RAM program first reads a self-delimiting nonnegative integer h, then computes the target 2^h by repeated doubling. It tests the candidates t=0,1,2,... in order, computing t^t by repeated multiplication, and stops at the first candidate satisfying 2^h ≤ t^t. The decoded h remains in register 0, the target in register 1, and the selected word length in register 2. The program uses only registers 0 through 7, writes no output, and leaves the suffix following the first encoded integer unread. The parser transfers control to the relocated arithmetic block instead of halting. Correctness, termination, and resource bounds are separate proof obligations.
-- source:
--   Derived implementation of the least-word-length parameter in Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters, corresponding to the indexed matching-vector construction in Appendix A of Dujmovic-Lai-Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572. The instruction sequence is supplied by this formalization.

import Definitions.Def_ITPIRPreproc_MatchVec_RAMEncoding
import Definitions.Def_ITPIRPreproc_MatchVec_RAMRelocation

namespace ITPIRPreproc.MatchVec.WordRAM

/-- Read one integer and jump to the given absolute continuation address. -/
def readNatJump (exit : ℕ) : Program :=
  readNatProgram.set 5 (.jlt 5 4 exit)

/-- On entry, register 0 holds h. Compute 2^h in register 1 and the least
ell with 2^h ≤ ell^ell in register 2. Scratch registers are 3 through 7. -/
def wordLengthCode : Program :=
  [ .const 1 1, .const 2 0, .const 3 1, .const 4 0,
    .const 5 1, .const 6 0, .const 7 2,
    .jlt 4 0 9, .jlt 6 5 12,
    .mul 1 1 7, .add 4 4 5, .jlt 6 5 7,
    .const 2 0, .const 3 1, .const 4 0,
    .jlt 4 2 17, .jlt 6 5 20,
    .mul 3 3 2, .add 4 4 5, .jlt 6 5 15,
    .jlt 3 1 22, .halt, .add 2 2 5, .jlt 6 5 13 ]

/-- Streaming input decoder followed by the parameter computation. -/
def wordLengthProgram : Program :=
  placeAfter (readNatJump 11) wordLengthCode

end ITPIRPreproc.MatchVec.WordRAM


