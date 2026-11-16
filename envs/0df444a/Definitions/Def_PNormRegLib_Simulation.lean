-- Prove2me | Definitions.Def_PNormRegLib_Simulation
-- name    : PNormRegLib_Simulation
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T08:36:18.217958+00:00
-- url     : https://prove2.me/theorems/0ad927aa-7567-4b34-9088-c30d19a9be81
-- title:
--   Simulation relation for relocated real-RAM programs
-- statement:
--   Let $p=(c_0,\rho,\kappa,\beta,\tau,e)$ be relocation parameters (definition `PNormRegLib_Reloc`). A **frame** is a tuple $F=(n_R,n_Q,b,R,k,c,M,I_M)$: index bounds $n_R,n_Q$, a memory base $b\in\mathbb Z$, a window radius $R$, a coin-cursor offset $k$, a work offset $c$, and a real memory $M$ and integer memory $I_M$ for the outside of the window. The pair is **valid** if $\beta\ne\tau$ and neither $\beta$ nor $\tau$ equals $\kappa+q$ for any $q<n_Q$.
--
--   A host state $r$ **represents** a virtual state $v$ if:
--
--   1. $r.\mathrm{reg}(\rho+i)=v.\mathrm{reg}(i)$ for $i<n_R$, $r.\mathrm{ptr}(\kappa+q)=v.\mathrm{ptr}(q)$ for $q<n_Q$, and $r.\mathrm{ptr}(\beta)=b$;
--   2. on the window, the memories agree:
--   $$r.\mathrm{mem}(b+z)=v.\mathrm{mem}(z)\quad\text{and}\quad r.\mathrm{int}(b+z)=v.\mathrm{int}(z)\qquad(|z|\le R);$$
--   3. outside the window, $r.\mathrm{mem}(y)=M(y)$ and $r.\mathrm{int}(y)=I_M(y)$ for $|y-b|>R$;
--   4. $r.\mathrm{cursor}=v.\mathrm{cursor}+k$ and $r.\mathrm{work}=c+2\,v.\mathrm{work}$.
--
--   The states are **in simulation** if moreover both are running and the program counter of $r$ is $c_0+2\cdot(\text{program counter of }v)$.
--
--   This is the invariant of the simulation theorem `PNormRegLib.reloc_sim`. Item 3 expresses that the relocated copy never touches memory outside its window, and item 4 that it runs at exactly half speed.
--
--   **Formalization Note.** `Frame`, `Valid p F`, `Agree p F r v` (items 1–4) and `Sim p F r v`.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc

namespace PNormRegLib

open PNormReg

/-- The frame of a relocated copy: index bounds, memory base `b` and window radius `R`, cursor
offset `k`, work offset `c`, and the memory `M`, `IM` outside the window. -/
structure Frame where
  /-- Bound on the real register indices of the copied program. -/
  nR : ℕ
  /-- Bound on the pointer register indices of the copied program. -/
  nQ : ℕ
  /-- The memory base (the value of the base pointer register). -/
  b : ℤ
  /-- The window radius: virtual addresses `z` with `|z| ≤ R` are represented. -/
  R : ℤ
  /-- Coin-cursor offset: the copy reads the host tape from position `k` on. -/
  k : ℕ
  /-- Work offset: host work is `c + 2 · (virtual work)`. -/
  c : ℕ
  /-- The real memory outside the window, which the copy must leave unchanged. -/
  M : ℤ → ℝ
  /-- The integer memory outside the window, which the copy must leave unchanged. -/
  IM : ℤ → ℤ

/-- The reserved pointer registers `base`, `tmp` are distinct and outside the renamed range. -/
def Valid (p : RelocParams) (F : Frame) : Prop :=
  p.base ≠ p.tmp ∧ ∀ q < F.nQ, p.qoff + q ≠ p.base ∧ p.qoff + q ≠ p.tmp

/-- The real state `r` represents the virtual state `v`: renamed registers and pointers agree, the
base register holds `b`, memory agrees on the window `b + [-R, R]`, memory outside the window is the
fixed `M`/`IM`, and cursor and work are offset (the work at twice the rate). -/
def Agree (p : RelocParams) (F : Frame) (r v : State) : Prop :=
  (∀ i < F.nR, r.core.regs (p.roff + i) = v.core.regs i) ∧
  (∀ q < F.nQ, r.core.ptrs (p.qoff + q) = v.core.ptrs q) ∧
  r.core.ptrs p.base = F.b ∧
  (∀ z, |z| ≤ F.R → r.core.mem (F.b + z) = v.core.mem z) ∧
  (∀ z, |z| ≤ F.R → r.integerMemory (F.b + z) = v.integerMemory z) ∧
  (∀ y, F.R < |y - F.b| → r.core.mem y = F.M y) ∧
  (∀ y, F.R < |y - F.b| → r.integerMemory y = F.IM y) ∧
  r.cursor = v.cursor + F.k ∧
  r.work = F.c + 2 * v.work

/-- `Agree`, both running, and the real program counter at the relocated position. -/
def Sim (p : RelocParams) (F : Frame) (r v : State) : Prop :=
  Agree p F r v ∧ r.halted = false ∧ v.halted = false ∧ r.core.pc = p.cOff + 2 * v.core.pc

end PNormRegLib


