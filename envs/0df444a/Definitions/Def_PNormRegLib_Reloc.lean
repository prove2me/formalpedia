-- Prove2me | Definitions.Def_PNormRegLib_Reloc
-- name    : PNormRegLib_Reloc
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T08:35:27.907427+00:00
-- url     : https://prove2.me/theorems/fec440b0-9f4b-46d8-915a-0829431b5960
-- title:
--   Relocation of real-RAM programs
-- statement:
--   Consider programs of the real RAM `PNormReg_Machine`. Fix parameters $p=(c_0,\rho,\kappa,\beta,\tau,e)$: a code offset $c_0$, a register offset $\rho$, a pointer offset $\kappa$, a base pointer register $\beta$, a scratch pointer register $\tau$ and an exit label $e$. The **relocated copy** $\mathrm{reloc}_p(P)$ of a program $P$ replaces each instruction $\iota$ by a pair $(\mathrm{prep}\,\iota,\ \mathrm{main}\,\iota)$:
--
--   1. a memory access through pointer $q$ (real or integer, load or store) becomes $p_\tau:=p_{\kappa+q}+p_\beta$, followed by the same access through $p_\tau$;
--   2. a jump to position $t$ becomes the no-op $p_\tau:=p_\tau$, followed by the jump to $c_0+2t$;
--   3. `halt` becomes the no-op, followed by an unconditional jump to $e$;
--   4. every other instruction becomes the no-op, followed by the same instruction.
--
--   Throughout, real registers are renamed $r_i\mapsto r_{\rho+i}$ and pointer registers $p_q\mapsto p_{\kappa+q}$. Instruction $i$ of $P$ sits at positions $2i$ and $2i+1$ of $\mathrm{reloc}_p(P)$.
--
--   A program $Q$ **embeds** $B$ at offset $o$ if $Q[o+i]=B[i]$ for every position $i$ of $B$. An instruction is **within the bounds** $(n_R,n_Q)$ if its real register indices are below $n_R$ and its pointer register indices below $n_Q$, and $P$ **uses indices below** $(n_R,n_Q)$ if all its instructions are.
--
--   A relocated copy runs inside a larger program with its own registers, its own memory region (virtual address $z$ is real address $p_\beta+z$, with $p_\beta$ set at run time) and a return point. Programs that are only known to exist can therefore be composed. Every step of $P$ costs exactly two steps of the copy, so time bounds transfer exactly.
--
--   **Formalization Note.** The no-op before a jump makes the taken and the untaken branch cost two steps each. `accept` and `reject` become the no-op followed by themselves; the machine is stuck at them in both programs.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormRegLib

open PNormReg SmaleNinth

/-- Parameters of a relocated copy: code offset, register and pointer renaming offsets, the pointer
register holding the memory base, a scratch pointer register, and the exit label. -/
structure RelocParams where
  /-- Position in the host program where the relocated copy starts. -/
  cOff : ℕ
  /-- Real register `i` of the copied program becomes register `roff + i`. -/
  roff : ℕ
  /-- Pointer register `q` of the copied program becomes pointer register `qoff + q`. -/
  qoff : ℕ
  /-- Pointer register holding the memory base: virtual address `z` is real address `base + z`. -/
  base : ℕ
  /-- Scratch pointer register for computed addresses. -/
  tmp : ℕ
  /-- Position in the host program to which the copied `halt` jumps. -/
  exit : ℕ

namespace RelocParams

/-- `p[tmp] := p[tmp]`, a one-step no-op. -/
def noop (p : RelocParams) : Instr := .core (.pcopy p.tmp p.tmp)

/-- Each instruction becomes exactly two: a preparation (a no-op, or `tmp := q + base` before a
memory access) and the renamed instruction (jumps retargeted, accesses through `tmp`, `halt` turned
into a jump to `exit`). -/
def pair (p : RelocParams) : Instr → Instr × Instr
  | .core (.const d c) => (p.noop, .core (.const (p.roff + d) c))
  | .core (.add d i j) => (p.noop, .core (.add (p.roff + d) (p.roff + i) (p.roff + j)))
  | .core (.sub d i j) => (p.noop, .core (.sub (p.roff + d) (p.roff + i) (p.roff + j)))
  | .core (.mul d i j) => (p.noop, .core (.mul (p.roff + d) (p.roff + i) (p.roff + j)))
  | .core (.div d i j) => (p.noop, .core (.div (p.roff + d) (p.roff + i) (p.roff + j)))
  | .core (.load d q) => (.pointerAdd p.tmp (p.qoff + q) p.base, .core (.load (p.roff + d) p.tmp))
  | .core (.store q i) => (.pointerAdd p.tmp (p.qoff + q) p.base, .core (.store p.tmp (p.roff + i)))
  | .core (.pset q c) => (p.noop, .core (.pset (p.qoff + q) c))
  | .core (.pcopy q q') => (p.noop, .core (.pcopy (p.qoff + q) (p.qoff + q')))
  | .core (.pinc q) => (p.noop, .core (.pinc (p.qoff + q)))
  | .core (.pdec q) => (p.noop, .core (.pdec (p.qoff + q)))
  | .core (.jle i t) => (p.noop, .core (.jle (p.roff + i) (p.cOff + 2 * t)))
  | .core (.pjle q q' t) => (p.noop, .core (.pjle (p.qoff + q) (p.qoff + q') (p.cOff + 2 * t)))
  | .core .accept => (p.noop, .core .accept)
  | .core .reject => (p.noop, .core .reject)
  | .pointerAdd d a b => (p.noop, .pointerAdd (p.qoff + d) (p.qoff + a) (p.qoff + b))
  | .pointerSub d a b => (p.noop, .pointerSub (p.qoff + d) (p.qoff + a) (p.qoff + b))
  | .integerLoad d a => (.pointerAdd p.tmp (p.qoff + a) p.base, .integerLoad (p.qoff + d) p.tmp)
  | .integerStore a b => (.pointerAdd p.tmp (p.qoff + a) p.base, .integerStore p.tmp (p.qoff + b))
  | .pointerReal d a => (p.noop, .pointerReal (p.roff + d) (p.qoff + a))
  | .sqrt d a => (p.noop, .sqrt (p.roff + d) (p.roff + a))
  | .rpow d a b => (p.noop, .rpow (p.roff + d) (p.roff + a) (p.roff + b))
  | .coin d => (p.noop, .coin (p.roff + d))
  | .halt => (p.noop, .core (.pjle p.tmp p.tmp p.exit))

end RelocParams

/-- The relocated program: instruction `i` of `P` sits at positions `2i, 2i+1`. -/
def reloc (p : RelocParams) (P : Program) : Program :=
  P.flatMap fun ins => [(p.pair ins).1, (p.pair ins).2]

/-- `B` occurs in `Q` starting at position `off`. -/
def Embeds (Q B : Program) (off : ℕ) : Prop := ∀ i x, B[i]? = some x → Q[off + i]? = some x

/-- Register indices of `ins` are below `nR` and pointer indices below `nQ`. -/
def InstrOK (nR nQ : ℕ) : Instr → Prop
  | .core (.const d _) => d < nR
  | .core (.add d i j) | .core (.sub d i j) | .core (.mul d i j) | .core (.div d i j) =>
      d < nR ∧ i < nR ∧ j < nR
  | .core (.load d q) => d < nR ∧ q < nQ
  | .core (.store q i) => q < nQ ∧ i < nR
  | .core (.pset q _) => q < nQ
  | .core (.pcopy q q') => q < nQ ∧ q' < nQ
  | .core (.pinc q) | .core (.pdec q) => q < nQ
  | .core (.jle i _) => i < nR
  | .core (.pjle q q' _) => q < nQ ∧ q' < nQ
  | .core .accept | .core .reject => True
  | .pointerAdd d a b | .pointerSub d a b => d < nQ ∧ a < nQ ∧ b < nQ
  | .integerLoad d a => d < nQ ∧ a < nQ
  | .integerStore a b => a < nQ ∧ b < nQ
  | .pointerReal d a => d < nR ∧ a < nQ
  | .sqrt d a => d < nR ∧ a < nR
  | .rpow d a b => d < nR ∧ a < nR ∧ b < nR
  | .coin d => d < nR
  | .halt => True

/-- Every instruction of `P` uses register indices below `nR` and pointer indices below `nQ`. -/
def UsesBelow (P : Program) (nR nQ : ℕ) : Prop := ∀ ins ∈ P, InstrOK nR nQ ins

end PNormRegLib


