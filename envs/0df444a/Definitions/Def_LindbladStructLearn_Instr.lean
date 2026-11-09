-- Prove2me | Definitions.Def_LindbladStructLearn_Instr
-- name    : LindbladStructLearn_Instr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:24.281217+00:00
-- url     : https://prove2.me/theorems/7e6c6afa-56dc-46dc-bf66-f65507f402f8
-- title:
--   Instructions of the learner's machine
-- statement:
--   The paper's "quantum algorithm" only accesses the unknown dynamics through experiments of one form: prepare a Pauli eigenstate, apply $e^{\mathcal Lt}$, measure in a Pauli eigenbasis (Theorem 1.1, item 4; Figure 1). A learner is therefore a classical program with one quantum instruction. The instructions are: the real-RAM core instructions of the public `SmaleNinth.RAMInstr` (unit-cost real arithmetic, comparisons, jumps, integer pointers, real memory); pointer addition and subtraction; integer-memory load and store; casting a pointer to a real; a fair coin writing a bit to a pointer register; `experiment`; and `halt` with an output pointer.
--
--   `experiment` reads $A \in \mathcal P_n$, $v \in \{\pm1\}^n$ and $B \in \mathcal P_n$ from $3n$ integer cells at a pointer (letters $0..3$, signs $0 = +1$, $1 = -1$) and a duration $t$ from a real register, and writes the outcome $w$ to the next $n$ cells.
--
--   **Formalization Note** The paper fixes no machine; this one follows the public pattern `LSWNewArcAudit.NewArc.OracleInstruction` (no pointer multiplication).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4; Figure 1, p.35

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Instructions of the learner's machine (the "quantum algorithm" of Theorem 1.1, Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4).

**Formalization Note** The paper fixes no machine. A learner is a classical program on the
public real RAM core `SmaleNinth.RAMInstr` (unit-cost real arithmetic, integer pointers), extended
as in the public `LSWNewArcAudit.NewArc.OracleInstruction` (pointer add/sub, an integer memory,
pointer-to-real casts, `halt` with an output pointer; no pointer multiplication), with a fair
coin and one quantum instruction, `experiment`: prepare a Pauli eigenstate `|A,v⟩`, apply the
unknown evolution for a duration `t` read from a real register, and measure in the Pauli basis
`B` (Theorem 1.1, item 4; Figure 1, p.35).

`experiment addr time` reads `A ∈ 𝒫_n`, `v ∈ {±1}ⁿ`, `B ∈ 𝒫_n` from the `3n` integer cells at
the pointer `addr` (letters `0..3`, signs `0 = +1`, `1 = −1`) and the duration from the real
register `time`; it writes the outcome `w` to the next `n` integer cells. `coin dst` writes a fair
bit to a pointer register. -/
inductive Instr : Type
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | coin (dst : ℕ)
  | experiment (address time : ℕ)
  | halt (pointer : ℕ)

end LindbladStructLearn


