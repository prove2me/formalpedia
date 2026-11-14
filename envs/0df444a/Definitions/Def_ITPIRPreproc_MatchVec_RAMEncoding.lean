-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_RAMEncoding
-- name    : ITPIRPreproc_MatchVec_RAMEncoding
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T17:48:48.625082+00:00
-- url     : https://prove2.me/theorems/7397084e-0838-479e-9754-a5bc08ed0300
-- title:
--   Word-RAM routine for reading one self-delimiting integer
-- statement:
--   An explicit 11-instruction deterministic streaming word-RAM program for the integer encoding used by this mission. The encoding stores the binary digits in little-endian order, with a true continuation flag before each digit and a false terminating flag. The program accumulates the value in register 0, keeps the next power of two in register 1, and halts after reading the terminating flag. Registers 2 and 3 are temporary, register 4 holds one, and register 5 remains zero. It produces no output bits.
--
--   This is an implementation helper for the mission's formal input format, not a new definition of PIR or an assumed implementation theorem. Its correctness, termination, and costs are separate proof obligations.
-- source:
--   Derived implementation for encNat in Definitions.Def_ITPIRPreproc_MatchVec_Machine (the mission word-RAM and bit-string encoding). Used by the indexed matching-vector routines of Dujmovic-Lai-Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, Appendix A, printed pp.36-37. The instruction sequence is supplied by this formalization, not stated in the paper.

import Definitions.Def_ITPIRPreproc_MatchVec_Machine

namespace ITPIRPreproc.MatchVec.WordRAM

/-- A streaming deterministic program reading one `encNat` integer. Register 0 is
the accumulator, 1 is the current binary weight, 2 is the continuation flag,
3 is the bit/contribution temporary, 4 contains one, and 5 remains zero.
The program halts immediately after the first terminating false flag. -/
def readNatProgram : Program :=
  [ .const 0 0,
    .const 1 1,
    .const 4 1,
    .inBit 2,
    .jlt 5 2 6,
    .halt,
    .inBit 3,
    .mul 3 3 1,
    .add 0 0 3,
    .add 1 1 1,
    .jlt 5 4 3 ]

end ITPIRPreproc.MatchVec.WordRAM


