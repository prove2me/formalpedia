-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_RAMRelocation
-- name    : ITPIRPreproc_MatchVec_RAMRelocation
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T17:53:34.736201+00:00
-- url     : https://prove2.me/theorems/37c038b4-6600-4bb4-aab8-c7363369a85e
-- title:
--   Relocating a word-RAM code block and its program counter
-- statement:
--   For a finite code prefix of length b, relocate a program by adding b to every absolute conditional-jump target and placing the relocated instructions after the prefix. Relocate a machine state by adding b to its program counter and leaving registers, memory, input position, output, coin position, halting flag, and cost unchanged. These are syntactic operations on the mission word-RAM. They do not execute the prefix and do not assume that a program halts. Their execution-preservation property is a separate theorem.
-- source:
--   Derived implementation infrastructure for the word-RAM model Definitions.Def_ITPIRPreproc_MatchVec_Machine. Intended for composing the concrete programs required by the Dujmovic-Lai-Wichs PIR formalization; this relocation construction is not a theorem stated in the paper.

import Definitions.Def_ITPIRPreproc_MatchVec_Machine

namespace ITPIRPreproc.MatchVec.WordRAM

/-- Shift every absolute jump target by the size of a code prefix. -/
def relocateInstr (offset : ℕ) : Instr → Instr
  | .jlt a b target => .jlt a b (offset+target)
  | op => op

/-- Move the program counter while preserving registers, memory, tapes, output, and cost. -/
def relocateState (offset : ℕ) (s : State) : State :=
  {s with pc := offset+s.pc}

/-- Place a program after a code prefix, with all its jumps relocated. -/
def placeAfter (precode P : Program) : Program :=
  precode ++ P.map (relocateInstr precode.length)

end ITPIRPreproc.MatchVec.WordRAM


