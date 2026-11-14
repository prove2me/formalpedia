-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_RAMPrimeParameters
-- name    : ITPIRPreproc_MatchVec_RAMPrimeParameters
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T19:22:56.731512+00:00
-- url     : https://prove2.me/theorems/dcabba36-b588-4862-ad3b-4c5f0b8e755f
-- title:
--   Composed word-RAM program for the matching-vector scalar parameters
-- statement:
--   A halt-to-continuation transformation replaces halt instructions in a program by a conditional jump to a relocated following block, using two designated interface registers. Its preservation properties are separate proof obligations. The new arithmetic block computes the least powers of 2 and 3 whose squares exceed the supplied word length, stores their exponents and values, and subtracts one from their maximum to obtain the degree. It preserves the decoded input h, the row count 2^h, and the word length. The complete program applies this block after the earlier word-length computation, starting from a self-delimiting encoding of h. It uses registers 0 through 12 and writes no output bits. The concrete composition uses register 6 for zero and register 5 for one; the word-length computation establishes this interface before reaching its halt.
-- source:
--   Derived implementation of the scalar parameters in Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters and the degree in Definitions.Def_ITPIRPreproc_MatchVec_PolynomialConstruction, corresponding to Appendix A of Dujmovic-Lai-Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572. The machine instructions and composition infrastructure are supplied by this formalization.

import Definitions.Def_ITPIRPreproc_MatchVec_RAMParameters

namespace ITPIRPreproc.MatchVec.WordRAM

/-- Replace halts by a branch to a continuation, using two interface registers. -/
def haltTo (target zeroReg oneReg : ℕ) : Instr → Instr
  | .halt => .jlt zeroReg oneReg target
  | op => op

/-- Continue into a relocated block when P reaches a halt instruction. -/
def continueWith (P Q : Program) (zeroReg oneReg : ℕ) : Program :=
  P.map (haltTo P.length zeroReg oneReg) ++ Q.map (relocateInstr P.length)

/-- Resume a cost-erased state at an indicated program counter. -/
def resumeState (target : ℕ) (s : State) : State :=
  {s with pc := target, halted := false, cost := 0}

/-- From the word-length output interface, compute both prime-power exponents,
powers and the polynomial degree. Registers 0,1,2 are preserved. -/
def primeParametersCode : Program :=
  [ .const 3 0, .const 4 1,
    .mul 10 4 4, .jlt 2 10 7, .mul 4 4 7, .add 3 3 5, .jlt 6 5 2,
    .const 8 0, .const 9 1, .const 11 3,
    .mul 10 9 9, .jlt 2 10 15, .mul 9 9 11, .add 8 8 5, .jlt 6 5 10,
    .jlt 4 9 18, .add 12 4 6, .jlt 6 5 19, .add 12 9 6,
    .sub 12 12 5, .halt ]

/-- Read h, compute its word length, and compute the two prime-power parameters. -/
def matchingParametersProgram : Program :=
  continueWith wordLengthProgram primeParametersCode 6 5

end ITPIRPreproc.MatchVec.WordRAM


