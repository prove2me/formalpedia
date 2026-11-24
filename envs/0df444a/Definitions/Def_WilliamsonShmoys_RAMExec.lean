-- Prove2me | Definitions.Def_WilliamsonShmoys_RAMExec
-- name    : WilliamsonShmoys_RAMExec
-- status  : Definition
-- author  : @もち
-- created : 2026-11-24T11:38:11.16225+00:00
-- url     : https://prove2.me/theorems/0478b597-f599-4241-942a-602d22b7659b
-- title:
--   Instruction semantics and code placement for the planar RAM
-- statement:
--   Explicit single-instruction semantics and code placement for the unit-cost RAM of this mission.
--
--   `execInstr ins s` is the state obtained by executing instruction `ins` on state $s$. It does exactly what `planarRAMStep` does once it has looked up `ins` at the program counter: arithmetic and memory instructions update one cell and advance the counter by $1$, branches and jumps set the counter, and `halt` leaves the state unchanged.
--
--   `CodeAt p base code` says that the list `code` occupies positions $\mathrm{base},\mathrm{base}+1,\dots$ of the program $p$. Code fragments can then be specified and verified in isolation and placed anywhere in a larger program.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

namespace WilliamsonShmoys

open PlanarRAMInstruction

/-- The effect of one instruction on a state, exactly as in `planarRAMStep`
(the step function looks up the instruction at the program counter and applies this). -/
noncomputable def execInstr : PlanarRAMInstruction → PlanarRAMState → PlanarRAMState
  | natConst dst value, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst value }
  | natAdd dst l r, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem l + s.natMem r) }
  | natSub dst l r, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem l - s.natMem r) }
  | natLoad dst a, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem (s.natMem a)) }
  | natStore a src, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem (s.natMem a) (s.natMem src) }
  | realZero dst, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst 0 }
  | realAdd dst l r, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem l + s.realMem r) }
  | realSub dst l r, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem l - s.realMem r) }
  | realLoad dst a, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem (s.natMem a)) }
  | realStore a src, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem (s.natMem a) (s.realMem src) }
  | natBranch l r y n, s => { s with pc := if s.natMem l ≤ s.natMem r then y else n }
  | realBranch l r y n, s => { s with pc := if s.realMem l ≤ s.realMem r then y else n }
  | jump j, s => { s with pc := j }
  | halt, s => s

/-- The code fragment `code` occupies positions `base, base+1, …` of the program `p`. -/
def CodeAt (p : List PlanarRAMInstruction) (base : ℕ) (code : List PlanarRAMInstruction) : Prop :=
  ∀ i, i < code.length → p[base + i]? = code[i]?

end WilliamsonShmoys


