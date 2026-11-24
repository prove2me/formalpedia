-- Prove2me | Definitions.Def_WilliamsonShmoys_RAMSandbox
-- name    : WilliamsonShmoys_RAMSandbox
-- status  : Definition
-- author  : @もち
-- created : 2026-11-24T06:14:37.474625+00:00
-- url     : https://prove2.me/theorems/db92b465-b196-48a9-a852-b895d9045b39
-- title:
--   Relocated and memory-sandboxed RAM subprograms
-- statement:
--   Relocation and memory sandboxing of a subprogram for the unit-cost RAM of this mission.
--
--   Given a subprogram $q$, `sandboxPair base o T O exit pc ins` translates the instruction `ins` at index `pc` into a pair of host instructions, to be placed at host positions $\mathrm{base}+2\,\mathrm{pc}$ and $\mathrm{base}+2\,\mathrm{pc}+1$:
--
--   1. every memory cell $a$ of $q$ (natural or real) is relocated to $a+o$;
--   2. an indirect access first computes the relocated address $x+o$ into a scratch cell $T$, using a cell $O$ that holds $o$;
--   3. jump and branch targets $j$ become $\mathrm{base}+2j$; unused second slots are filled with a jump to the next pair;
--   4. `halt` becomes a jump to the continuation address $\mathrm{exit}$.
--
--   `SandboxedAt p q base o T O exit` says that a host program $p$ contains this translation of $q$. `SandboxRel o O s s'` is the memory correspondence: host cells $a+o$ mirror the subprogram's cells $a$, and cell $O$ holds $o$.
--
--   With cells below $o$ reserved for the host, a host program can call an arbitrary RAM subprogram, for example an exact tree-width solver, without the subprogram overwriting the host's working data.
-- source:
--   Subroutine-call infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false

namespace WilliamsonShmoys

open PlanarRAMInstruction

/-- Sandboxed translation of the instruction at index `pc` of a subprogram, as a pair of
instructions placed at `base + 2*pc` and `base + 2*pc + 1` of a host program.
Every memory cell `a` of the subprogram is relocated to `a + o`; indirect accesses first
compute the relocated address into the scratch cell `T`, using cell `O` which holds `o`.
Jump targets `j` become `base + 2*j`, and `halt` becomes a jump to `exit`. -/
def sandboxPair (base o T O exit pc : ℕ) : PlanarRAMInstruction → PlanarRAMInstruction × PlanarRAMInstruction
  | natConst d v => (natConst (d + o) v, jump (base + 2 * (pc + 1)))
  | natAdd d l r => (natAdd (d + o) (l + o) (r + o), jump (base + 2 * (pc + 1)))
  | natSub d l r => (natSub (d + o) (l + o) (r + o), jump (base + 2 * (pc + 1)))
  | natLoad d a => (natAdd T (a + o) O, natLoad (d + o) T)
  | natStore a src => (natAdd T (a + o) O, natStore T (src + o))
  | realZero d => (realZero (d + o), jump (base + 2 * (pc + 1)))
  | realAdd d l r => (realAdd (d + o) (l + o) (r + o), jump (base + 2 * (pc + 1)))
  | realSub d l r => (realSub (d + o) (l + o) (r + o), jump (base + 2 * (pc + 1)))
  | realLoad d a => (natAdd T (a + o) O, realLoad (d + o) T)
  | realStore a src => (natAdd T (a + o) O, realStore T (src + o))
  | natBranch l r y n => (natBranch (l + o) (r + o) (base + 2 * y) (base + 2 * n), halt)
  | realBranch l r y n => (realBranch (l + o) (r + o) (base + 2 * y) (base + 2 * n), halt)
  | jump j => (jump (base + 2 * j), halt)
  | halt => (jump exit, jump exit)

/-- The host program `p` contains the sandboxed translation of `q` at offset `base`. -/
def SandboxedAt (p q : List PlanarRAMInstruction) (base o T O exit : ℕ) : Prop :=
  ∀ i ins, q[i]? = some ins →
    p[base + 2 * i]? = some (sandboxPair base o T O exit i ins).1 ∧
    p[base + 2 * i + 1]? = some (sandboxPair base o T O exit i ins).2

/-- Memory correspondence: the host's cells `a + o` mirror the subprogram's cells `a`
(natural and real), and cell `O` holds the offset `o`. -/
def SandboxRel (o O : ℕ) (s s' : PlanarRAMState) : Prop :=
  s'.natMem O = o ∧ (∀ a, s'.natMem (a + o) = s.natMem a) ∧ (∀ a, s'.realMem (a + o) = s.realMem a)

end WilliamsonShmoys


