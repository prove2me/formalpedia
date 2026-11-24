-- Prove2me | Definitions.Def_WilliamsonShmoys_RAMSandboxOdd
-- name    : WilliamsonShmoys_RAMSandboxOdd
-- status  : Definition
-- author  : @もち
-- created : 2026-11-24T10:15:00.724892+00:00
-- url     : https://prove2.me/theorems/cfed3ec6-423a-40f4-af05-ea105a30c673
-- title:
--   Odd-cell sandboxed RAM subprograms
-- statement:
--   Relocation and odd-cell memory sandboxing of a subprogram for the unit-cost RAM of this mission.
--
--   `sandboxTriple base T ONE exit pc ins` translates the instruction at index `pc` of a subprogram $q$ into three host instructions at positions $\mathrm{base}+3\,\mathrm{pc}$, $+1$, $+2$:
--
--   1. every cell $a$ of $q$ (natural or real) is mapped to the **odd** host cell $2a+1$;
--   2. an indirect access with address value $x$ first computes $2x+1$ into an even scratch cell $T$, using an even cell `ONE` holding $1$;
--   3. jump and branch targets $j$ become $\mathrm{base}+3j$, and `halt` becomes a jump to the continuation $\mathrm{exit}$.
--
--   `SandboxedOddAt p q base T ONE exit` says the host program $p$ contains this translation. `SandboxOddRel ONE s s'` says the host's odd cells mirror the subprogram's memory and `ONE` holds $1$.
--
--   Since the subprogram only touches odd cells, all **even** cells, infinitely many, remain available to the host. This matters when the host's own data grows with the input: in the Baker shifting program the host keeps the original $n\times n$ instance and the best answer found so far while calling the solver. It supersedes `Def_WilliamsonShmoys_RAMSandbox`, whose fixed-offset scheme only leaves a bounded region to the host.
-- source:
--   Subroutine-call infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

namespace WilliamsonShmoys

open PlanarRAMInstruction

/-- Sandboxed translation of the instruction at index `pc` of a subprogram into three host
instructions, placed at `base + 3*pc`, `base + 3*pc + 1`, `base + 3*pc + 2`.
Every cell `a` of the subprogram (natural or real) is mapped to the odd cell `2*a + 1`, so all
even cells stay available to the host. An indirect access computes `2*x + 1` into the even
scratch cell `T`, using the even cell `ONE` which holds `1`. Jump targets `j` become
`base + 3*j`, and `halt` becomes a jump to `exit`. Unused slots hold `halt`. -/
def sandboxTriple (base T ONE exit pc : ℕ) :
    PlanarRAMInstruction → PlanarRAMInstruction × PlanarRAMInstruction × PlanarRAMInstruction
  | natConst d v => (natConst (2 * d + 1) v, jump (base + 3 * (pc + 1)), halt)
  | natAdd d l r => (natAdd (2 * d + 1) (2 * l + 1) (2 * r + 1), jump (base + 3 * (pc + 1)), halt)
  | natSub d l r => (natSub (2 * d + 1) (2 * l + 1) (2 * r + 1), jump (base + 3 * (pc + 1)), halt)
  | natLoad d a => (natAdd T (2 * a + 1) (2 * a + 1), natAdd T T ONE, natLoad (2 * d + 1) T)
  | natStore a src => (natAdd T (2 * a + 1) (2 * a + 1), natAdd T T ONE, natStore T (2 * src + 1))
  | realZero d => (realZero (2 * d + 1), jump (base + 3 * (pc + 1)), halt)
  | realAdd d l r => (realAdd (2 * d + 1) (2 * l + 1) (2 * r + 1), jump (base + 3 * (pc + 1)), halt)
  | realSub d l r => (realSub (2 * d + 1) (2 * l + 1) (2 * r + 1), jump (base + 3 * (pc + 1)), halt)
  | realLoad d a => (natAdd T (2 * a + 1) (2 * a + 1), natAdd T T ONE, realLoad (2 * d + 1) T)
  | realStore a src => (natAdd T (2 * a + 1) (2 * a + 1), natAdd T T ONE, realStore T (2 * src + 1))
  | natBranch l r y n => (natBranch (2 * l + 1) (2 * r + 1) (base + 3 * y) (base + 3 * n), halt, halt)
  | realBranch l r y n => (realBranch (2 * l + 1) (2 * r + 1) (base + 3 * y) (base + 3 * n), halt, halt)
  | jump j => (jump (base + 3 * j), halt, halt)
  | halt => (jump exit, halt, halt)

/-- The host program `p` contains the odd-cell sandboxed translation of `q` at offset `base`. -/
def SandboxedOddAt (p q : List PlanarRAMInstruction) (base T ONE exit : ℕ) : Prop :=
  ∀ i ins, q[i]? = some ins →
    p[base + 3 * i]? = some (sandboxTriple base T ONE exit i ins).1 ∧
    p[base + 3 * i + 1]? = some (sandboxTriple base T ONE exit i ins).2.1 ∧
    p[base + 3 * i + 2]? = some (sandboxTriple base T ONE exit i ins).2.2

/-- Memory correspondence: host odd cells `2*a + 1` mirror the subprogram's cells `a`
(natural and real), and the host cell `ONE` holds `1`. -/
def SandboxOddRel (ONE : ℕ) (s s' : PlanarRAMState) : Prop :=
  s'.natMem ONE = 1 ∧ (∀ a, s'.natMem (2 * a + 1) = s.natMem a) ∧
    (∀ a, s'.realMem (2 * a + 1) = s.realMem a)

end WilliamsonShmoys


