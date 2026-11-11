-- Prove2me | Definitions.Def_ArbLindbladLearn_branches
-- name    : ArbLindbladLearn_branches
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:27.001318+00:00
-- url     : https://prove2.me/theorems/a15c26be-9a9d-4a24-b1d2-16ee75b7e57c
-- title:
--   One step of the learner's machine
-- statement:
--   The paper fixes no machine; its access model is: one experiment prepares a state, applies $e^{t\mathcal L}$ once for a chosen $t\ge0$, and measures, and the classical running time is also counted. The learner is a classical program on the public real RAM core `SmaleNinth.RAMInstr`, extended with pointer arithmetic, an integer memory, a fair coin, `halt` with an output pointer, and one quantum instruction `experiment`: prepare $C_1|0^n\rangle$ with a Clifford circuit over $\{H,S,\mathrm{CNOT}\}$, apply $e^{t\mathcal L}$, apply a Clifford circuit $C_2$, and measure in the computational basis. Every experiment of Algorithms 1 and 2 has this form; it is ancilla-free and control-free.
--
--   A step returns the list of (weight, successor) pairs: one for a deterministic instruction, two of weight $1/2$ for `coin`, and one per outcome $b\in\{0,1\}^n$ for `experiment`, with its Born weight; the experiment appends $t$ to the durations and costs $1+n+|C_1|+|C_2|$ work units. A halted state stutters. A negative duration, malformed circuits, or an invalid program counter make the run stuck forever without output. The evolution enters only through the experiment branch.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34; access model, §1.1, p.2

import Mathlib
import Definitions.Def_ArbLindbladLearn_Program
import Definitions.Def_ArbLindbladLearn_MState
import Definitions.Def_ArbLindbladLearn_parseExperiment
import Definitions.Def_ArbLindbladLearn_bornWeight

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- One step of the learner's machine on `n` qubits with evolution `evo` (Corollary 4.7,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34; access model §1.1, p.2): the list of (weight, successor)
pairs.

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

Semantics. A halted state stutters (weight `1`). Every other step costs one unit of work, except
`experiment`, which costs `1 + n + |C₁| + |C₂|`. A program counter outside the program, a core
`accept`/`reject`, an experiment with malformed circuits or with a negative duration are stuck:
the state repeats forever, charged, and never produces output. `coin` branches two ways with
weight `1/2`. `experiment` branches over every outcome `b ∈ {0,1}ⁿ` with weight
`bornWeight (evo t) C₁ C₂ b`, writes `b` (`0`/`1`) to the `n` integer cells after the circuits,
and appends `t` to `durations`. `evo` occurs only in this branch. -/
def branches (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) (s : MState) :
    List (ℝ≥0∞ × MState) := by
  classical
  exact
  if s.output.isSome then [(1, s)] else
  let t : MState := { s with work := s.work + 1, core := { s.core with pc := s.core.pc + 1 } }
  match P[s.core.pc]? with
  | none => [(1, { s with work := s.work + 1 })]
  | some (.core _) => [(1, { t with core := SmaleNinth.RAMStep (coreProgram P) s.core })]
  | some (.pointerAdd dst a b) =>
      [(1, { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.core.ptrs a + s.core.ptrs b) } })]
  | some (.pointerSub dst a b) =>
      [(1, { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.core.ptrs a - s.core.ptrs b) } })]
  | some (.integerLoad dst a) =>
      [(1, { t with core := { t.core with
        ptrs := Function.update s.core.ptrs dst (s.intMem (s.core.ptrs a)) } })]
  | some (.integerStore a b) =>
      [(1, { t with intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) })]
  | some (.pointerReal dst a) =>
      [(1, { t with core := { t.core with
        regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } })]
  | some (.coin dst) =>
      [(1 / 2, { t with core := { t.core with ptrs := Function.update s.core.ptrs dst 0 } }),
       (1 / 2, { t with core := { t.core with ptrs := Function.update s.core.ptrs dst 1 } })]
  | some (.experiment addr tm) =>
      let τ := s.core.regs tm
      match parseExperiment n s.intMem (s.core.ptrs addr) with
      | none => [(1, { s with work := s.work + 1 })]
      | some (C₁, C₂, out) =>
        if τ < 0 then [(1, { s with work := s.work + 1 })]
        else
          (Finset.univ : Finset (Qubits n)).toList.map fun b =>
            (ENNReal.ofReal (bornWeight (evo τ) C₁ C₂ b),
              { t with
                work := s.work + 1 + n + C₁.length + C₂.length
                durations := s.durations ++ [τ]
                intMem := fun z =>
                  if h : out ≤ z ∧ z < out + n then
                    (if b ⟨(z - out).toNat, by omega⟩ then 1 else 0)
                  else s.intMem z })
  | some (.halt a) => [(1, { t with output := some (s.core.ptrs a) })]

end ArbLindbladLearn


