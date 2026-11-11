-- Prove2me | Definitions.Def_ArbLindbladLearn_Instr
-- name    : ArbLindbladLearn_Instr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:29.781169+00:00
-- url     : https://prove2.me/theorems/f4798f87-2720-447d-82e1-620d7facb65d
-- title:
--   Instructions of the learner's machine
-- statement:
--   The paper fixes no machine; its access model is: one experiment prepares a state, applies $e^{t\mathcal L}$ once for a chosen $t\ge0$, and measures, and the classical running time is also counted. The learner is a classical program on the public real RAM core `SmaleNinth.RAMInstr`, extended with pointer arithmetic, an integer memory, a fair coin, `halt` with an output pointer, and one quantum instruction `experiment`: prepare $C_1|0^n\rangle$ with a Clifford circuit over $\{H,S,\mathrm{CNOT}\}$, apply $e^{t\mathcal L}$, apply a Clifford circuit $C_2$, and measure in the computational basis. Every experiment of Algorithms 1 and 2 has this form; it is ancilla-free and control-free.
--
--   `experiment addr time` reads the circuits at the pointer `addr` and the duration from the real register `time`; `coin dst` writes a fair bit.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34; access model, §1.1, p.2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- Instructions of the learner's machine for Corollary 4.7 (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34;
access model §1.1, p.2).

**Formalization Note** The paper fixes no machine (its access model is §1.1, p.2: one
experiment prepares a state, applies `e^{tℒ}` once for a chosen `t ≥ 0`, and measures; the
classical running time is also counted). The learner is a classical program on the public real
RAM core `SmaleNinth.RAMInstr` (unit-cost real arithmetic, integer pointers), extended with
pointer addition and subtraction, an integer memory, pointer-to-real casts, `halt` with an
output pointer (no pointer multiplication), a fair coin, and one quantum instruction,
`experiment`: prepare `C₁|0ⁿ⟩` with a Clifford circuit `C₁` over `{H, S, CNOT}`, apply `e^{tℒ}` for
a duration `t` read from a real register, apply a Clifford circuit `C₂`, and measure every qubit
in the computational basis. Every experiment of Algorithms 1 and 2 (pp.23, 31) has this form, and
it is ancilla-free and control-free (Theorem 1.1, p.3).

`experiment addr time` reads the two circuits from integer memory at the pointer `addr` (see
`parseExperiment`) and the duration from the real register `time`, and writes the outcome bits
after the circuits. `coin dst` writes a fair bit to a pointer register. -/
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

end ArbLindbladLearn


