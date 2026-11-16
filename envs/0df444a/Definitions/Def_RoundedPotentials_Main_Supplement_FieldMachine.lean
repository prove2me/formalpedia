-- Prove2me | Definitions.Def_RoundedPotentials_Main_Supplement_FieldMachine
-- name    : RoundedPotentials_Main_Supplement_FieldMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:03:04.868563+00:00
-- url     : https://prove2.me/theorems/9b07bf18-591b-4f90-88ba-1a3e4c9cca04
-- title:
--   A two-sorted machine counting integer comparisons, field operations and words (Lemma 4.7)
-- statement:
--   Lemma 4.7 counts three resources separately: integer comparisons, field operations and additional words. This file defines a machine in which each of them is a counter.
--
--   The machine has an integer memory and a field memory over a commutative ring $F$; in the paper $F=\mathbb F_P$. A program is a finite list of instructions:
--   1. integer constants, $+$, $-$, $\times$ (no division), and indirect load and store;
--   2. a jump, and a branch on an integer comparison $a<b$;
--   3. field constants, the cast of an integer into $F$, field $+$, $-$, $\times$, and indirect load and store of field cells;
--   4. halt, returning a field cell.
--
--   Field values can never be compared or turned back into integers. The counters are:
--   - `cmps`: the number of executed comparisons;
--   - `fops`: the number of executed constants, casts, $+$, $-$, $\times$ on the field side;
--   - `iops`: every other executed instruction;
--   - `written`: the set of cells written so far.
--
--   An integer of absolute value larger than the bound $R=M^K$ is a fault. Here $M=n+|Q_0|+\max_u|i_u|+2$, so a word has $O(K\log M)$ bits. A negative address and a program counter outside the program are also faults.
--
--   The input layout has the integer cells $n,Q_0,i_1,\dots,i_n$ and the field cells $\lambda_1,\dots,\lambda_n,\alpha_1,\dots,\alpha_n,\beta_1,\dots,\beta_n$. The target value is
--   $$E(\zeta)=\sum_{j}\bigl(\alpha_j K^+_j-\beta_j K^-_j\bigr),\qquad K^+_j=\sum_u\lambda_u\,\mathrm{clip}(i_u-i_j,0,Q_0),\quad K^-_j=\sum_u\lambda_u\,\mathrm{clip}(i_j-i_u,0,Q_0),$$
--   where the clipping is computed on integers before the cast into $F$, as in (14)–(15).
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 22, Lemma 4.7 and its proof, eqs. (14), (15), (19)

import Mathlib

namespace RoundedPotentials.Main.Supplement

/-! # A two-sorted counting machine for Lemma 4.7

Lemma 4.7 counts three resources separately: integer comparisons, field operations and
additional words. The machine below has an integer memory `mi : ℕ → ℤ` and a field memory
`mf : ℕ → F` over an arbitrary commutative ring `F` (in the paper `F = 𝔽_P`). Field values can
only be combined by the counted field instructions and can never be converted back to integers or
branched on; integers are combined by `+, −, ×` (no division) and compared only by the counted
branch `ijlt`. Every integer written must have absolute value at most a bound `R` fixed by the
statement (a word of `O(log R)` bits); a larger value, a negative address or a program counter
outside the program is a fault. -/

/-- The instruction set. `d a b s` are cell addresses fixed in the program; `iload`, `istore`,
`fload`, `fstore` are indirect (the address is the value of an integer cell). -/
inductive FInstr where
  /-- `mi[d] := k` -/
  | iconst (d : ℕ) (k : ℤ)
  /-- `mi[d] := mi[a] + mi[b]` -/
  | iadd (d a b : ℕ)
  /-- `mi[d] := mi[a] - mi[b]` -/
  | isub (d a b : ℕ)
  /-- `mi[d] := mi[a] * mi[b]` -/
  | imul (d a b : ℕ)
  /-- `mi[d] := mi[mi[a]]` -/
  | iload (d a : ℕ)
  /-- `mi[mi[a]] := mi[s]` -/
  | istore (a s : ℕ)
  /-- integer comparison: jump to `l` if `mi[a] < mi[b]` -/
  | ijlt (a b l : ℕ)
  /-- jump to `l` -/
  | jmp (l : ℕ)
  /-- `mf[d] := (k : F)` -/
  | fconst (d : ℕ) (k : ℤ)
  /-- `mf[d] := (mi[a] : F)` -/
  | fcast (d a : ℕ)
  /-- `mf[d] := mf[a] + mf[b]` -/
  | fadd (d a b : ℕ)
  /-- `mf[d] := mf[a] - mf[b]` -/
  | fsub (d a b : ℕ)
  /-- `mf[d] := mf[a] * mf[b]` -/
  | fmul (d a b : ℕ)
  /-- `mf[d] := mf[mi[a]]` -/
  | fload (d a : ℕ)
  /-- `mf[mi[a]] := mf[s]` -/
  | fstore (a s : ℕ)
  /-- halt with answer `mf[a]` -/
  | halt (a : ℕ)

/-- A configuration. `outcome = none` while running, `some none` after a fault, `some (some x)`
after halting with answer `x`. `cmps` counts executed `ijlt`; `fops` counts executed
`fconst, fcast, fadd, fsub, fmul`; `iops` counts all other executed instructions except `halt`.
`written` is the set of cells written so far (`true` = integer memory, `false` = field memory). -/
structure FConfig (F : Type) where
  pc : ℕ
  mi : ℕ → ℤ
  mf : ℕ → F
  cmps : ℕ
  fops : ℕ
  iops : ℕ
  written : Finset (Bool × ℕ)
  outcome : Option (Option F)

namespace FConfig

variable {F : Type}

def fault (c : FConfig F) : FConfig F := { c with outcome := some none }

/-- Write the integer `x` into integer cell `d` (a fault if `|x| > R`), count one integer
operation, and advance. -/
def iwrite (c : FConfig F) (R : ℤ) (d : ℕ) (x : ℤ) : FConfig F :=
  if |x| ≤ R then
    { c with pc := c.pc + 1, mi := Function.update c.mi d x, iops := c.iops + 1,
             written := insert (true, d) c.written }
  else c.fault

/-- Write `x` into field cell `d`, add `fo` field operations and `io` integer operations, and
advance. -/
def fwrite (c : FConfig F) (d : ℕ) (x : F) (fo io : ℕ) : FConfig F :=
  { c with pc := c.pc + 1, mf := Function.update c.mf d x, fops := c.fops + fo,
           iops := c.iops + io, written := insert (false, d) c.written }

end FConfig

/-- One step of program `P` with integer bound `R`; a halted or faulted configuration is left
unchanged. -/
def fstep {F : Type} [CommRing F] (P : List FInstr) (R : ℤ) (c : FConfig F) : FConfig F :=
  if c.outcome.isSome then c else
  match P[c.pc]? with
  | none => c.fault
  | some (FInstr.iconst d k) => c.iwrite R d k
  | some (FInstr.iadd d a b) => c.iwrite R d (c.mi a + c.mi b)
  | some (FInstr.isub d a b) => c.iwrite R d (c.mi a - c.mi b)
  | some (FInstr.imul d a b) => c.iwrite R d (c.mi a * c.mi b)
  | some (FInstr.iload d a) =>
      if c.mi a < 0 then c.fault else c.iwrite R d (c.mi (c.mi a).toNat)
  | some (FInstr.istore a s) =>
      if c.mi a < 0 then c.fault else c.iwrite R (c.mi a).toNat (c.mi s)
  | some (FInstr.ijlt a b l) =>
      { c with pc := if c.mi a < c.mi b then l else c.pc + 1, cmps := c.cmps + 1 }
  | some (FInstr.jmp l) => { c with pc := l, iops := c.iops + 1 }
  | some (FInstr.fconst d k) => c.fwrite d (k : F) 1 0
  | some (FInstr.fcast d a) => c.fwrite d (c.mi a : F) 1 0
  | some (FInstr.fadd d a b) => c.fwrite d (c.mf a + c.mf b) 1 0
  | some (FInstr.fsub d a b) => c.fwrite d (c.mf a - c.mf b) 1 0
  | some (FInstr.fmul d a b) => c.fwrite d (c.mf a * c.mf b) 1 0
  | some (FInstr.fload d a) =>
      if c.mi a < 0 then c.fault else c.fwrite d (c.mf (c.mi a).toNat) 0 1
  | some (FInstr.fstore a s) =>
      if c.mi a < 0 then c.fault else c.fwrite (c.mi a).toNat (c.mf s) 0 1
  | some (FInstr.halt a) => { c with outcome := some (some (c.mf a)) }

/-- The configuration after `k` steps. -/
def frun {F : Type} [CommRing F] (P : List FInstr) (R : ℤ) (c : FConfig F) (k : ℕ) :
    FConfig F :=
  (fstep P R)^[k] c

/-- The input layout of Lemma 4.7: integer cells `0 ↦ n`, `1 ↦ Q₀`, `2 + u ↦ i_u`; field cells
`u ↦ λ_u`, `n + u ↦ α_u`, `2n + u ↦ β_u` (`u < n`); every other cell is `0`. Nothing has been
written yet and all counters are `0`. -/
def finit {F : Type} [CommRing F] (n : ℕ) (Q0 : ℤ) (i : Fin n → ℤ) (lam α β : Fin n → F) :
    FConfig F where
  pc := 0
  mi := fun a =>
    if a = 0 then (n : ℤ) else if a = 1 then Q0 else
      if h : 2 ≤ a ∧ a - 2 < n then i ⟨a - 2, h.2⟩ else 0
  mf := fun a =>
    if h : a < n then lam ⟨a, h⟩ else
      if h' : a < 2 * n then α ⟨a - n, by omega⟩ else
        if h'' : a < 3 * n then β ⟨a - 2 * n, by omega⟩ else 0
  cmps := 0
  fops := 0
  iops := 0
  written := ∅
  outcome := none

/-- The integer word bound `R = M^K` with `M = n + |Q₀| + max_u |i_u| + 2`: words of
`O(K log M)` bits, enough for every index, every difference of two indices and every address. -/
def wordBound {n : ℕ} (K : ℕ) (Q0 : ℤ) (i : Fin n → ℤ) : ℤ :=
  ((n + Q0.natAbs + Finset.univ.sup (fun u => (i u).natAbs) + 2 : ℕ) : ℤ) ^ K

/-- `clip(x, 0, Q₀)` on integers. -/
def clipQ (x Q0 : ℤ) : ℤ := min Q0 (max 0 x)

/-- `K⁺_j(ζ) = Σ_u λ_u clip(i_u − i_j, 0, Q₀)` (14), the clipping done on integers before the
cast into `F`. -/
def kernelPlus {F : Type} [CommRing F] {n : ℕ} (Q0 : ℤ) (i : Fin n → ℤ) (lam : Fin n → F)
    (j : Fin n) : F :=
  ∑ u, lam u * ((clipQ (i u - i j) Q0 : ℤ) : F)

/-- `K⁻_j(ζ) = Σ_u λ_u clip(i_j − i_u, 0, Q₀)` (14). -/
def kernelMinus {F : Type} [CommRing F] {n : ℕ} (Q0 : ℤ) (i : Fin n → ℤ) (lam : Fin n → F)
    (j : Fin n) : F :=
  ∑ u, lam u * ((clipQ (i j - i u) Q0 : ℤ) : F)

/-- The true value `E(ζ) = Σ_j (α_j K⁺_j(ζ) − β_j K⁻_j(ζ))` of (15) at the private point. -/
def evalE {F : Type} [CommRing F] {n : ℕ} (Q0 : ℤ) (i : Fin n → ℤ) (lam α β : Fin n → F) : F :=
  ∑ j, (α j * kernelPlus Q0 i lam j - β j * kernelMinus Q0 i lam j)

end RoundedPotentials.Main.Supplement


