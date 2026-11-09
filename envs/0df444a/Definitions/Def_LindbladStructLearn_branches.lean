-- Prove2me | Definitions.Def_LindbladStructLearn_branches
-- name    : LindbladStructLearn_branches
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:58:30.257417+00:00
-- url     : https://prove2.me/theorems/28df2ede-9ae0-4389-b4dd-a7e9deeca9fb
-- title:
--   One step of the learner's machine
-- statement:
--   One step of the machine on $n$ qubits whose experiments apply the evolution $\mathrm{evo}(t)$, as a list of (weight, successor) pairs. A halted configuration repeats with weight $1$. Every other step costs one unit of work, except `experiment`, which costs $n+1$. `coin` branches two ways with weight $1/2$. `experiment` with duration $t \ge 0$ and valid cells branches over all outcomes $w \in \{\pm1\}^n$ with weight $\mathrm{tr}(|B,w\rangle\langle B,w|\,\mathrm{evo}(t)(|A,v\rangle\langle A,v|))$, writes $w$, and appends $t$ to the durations. A negative duration, invalid cells, a program counter outside the program, or a core `accept`/`reject` make the machine stuck: it repeats forever, charging work, without output. The unknown dynamics enter only through the experiment branch.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4; Figure 1, p.35

import Mathlib
import Definitions.Def_LindbladStructLearn_Program
import Definitions.Def_LindbladStructLearn_coreProgram
import Definitions.Def_LindbladStructLearn_MState
import Definitions.Def_LindbladStructLearn_bornAmp

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- One step of the learner's machine on `n` qubits with evolution `evo` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1,
p.4, and Figure 1, p.35): the list of (weight, successor) pairs.

**Formalization Note** The paper fixes no machine. A learner is a classical program on the
public real RAM core `SmaleNinth.RAMInstr` (unit-cost real arithmetic, integer pointers), extended
as in the public `LSWNewArcAudit.NewArc.OracleInstruction` (pointer add/sub, an integer memory,
pointer-to-real casts, `halt` with an output pointer; no pointer multiplication), with a fair
coin and one quantum instruction, `experiment`: prepare a Pauli eigenstate `|A,v⟩`, apply the
unknown evolution for a duration `t` read from a real register, and measure in the Pauli basis
`B` (Theorem 1.1, item 4; Figure 1, p.35).

Semantics. A halted state stutters (weight `1`). Every other step costs one unit of work, except
`experiment`, which costs `n + 1` (it reads and writes `Θ(n)` cells). A program counter outside the
program, a core `accept`/`reject`, an experiment with a negative duration or with an invalid
letter or sign are stuck: the state repeats forever, charged, and never produces output. `coin`
branches two ways with weight `1/2`. `experiment` branches over every outcome `w ∈ {±1}ⁿ` with
weight `tr(|B,w⟩⟨B,w| · evo(t)(|A,v⟩⟨A,v|))`, writes `w` (`0 = +1`, `1 = −1`) to the integer
cells `base + 3n + i`, and appends `t` to `durations`. `evo` occurs only in this branch. -/
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
      let base := s.core.ptrs addr
      let τ := s.core.regs tm
      let cell : ℤ → ℤ := fun z => s.intMem (base + z)
      if τ < 0 ∨ ¬ ∀ i : Fin n, (0 ≤ cell i ∧ cell i ≤ 3) ∧
          (cell (n + i) = 0 ∨ cell (n + i) = 1) ∧ (0 ≤ cell (2 * n + i) ∧ cell (2 * n + i) ≤ 3)
      then [(1, { s with work := s.work + 1 })]
      else
        let A : Pauli n := fun i => ⟨(cell i).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
        let v : Qubits n := fun i => decide (cell (n + i) = 1)
        let B : Pauli n := fun i => ⟨(cell (2 * n + i)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
        (Finset.univ : Finset (Qubits n)).toList.map fun w =>
          (ENNReal.ofReal (bornAmp (evo τ) A v B w).re,
            { t with
              work := s.work + n + 1
              durations := s.durations ++ [τ]
              intMem := fun z =>
                if h : base + 3 * n ≤ z ∧ z < base + 4 * n then
                  (if w ⟨(z - (base + 3 * n)).toNat, by omega⟩ then 1 else 0)
                else s.intMem z })
  | some (.halt a) => [(1, { t with output := some (s.core.ptrs a) })]

end LindbladStructLearn


