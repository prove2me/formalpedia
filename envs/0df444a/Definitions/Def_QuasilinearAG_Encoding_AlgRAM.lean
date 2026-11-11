-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_AlgRAM
-- name    : QuasilinearAG_Encoding_AlgRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:40:56.487075+00:00
-- url     : https://prove2.me/theorems/895f2856-93ca-48a2-b6a8-2d36e0697d7a
-- title:
--   An algebraic RAM over a field $k$: field operations and live field slots
-- statement:
--   Statements in **field operations** and **live field slots** (Section 4) refer to an algebraic random-access machine over a field $k$. A program is a finite list of instructions over two memories: field cells $F[0],F[1],\dots$ holding elements of $k$, and index cells $I[0],I[1],\dots$ holding natural numbers.
--
--   - Field instructions: load a constant $c\in k$ of the program, add, subtract, multiply, invert (with $0^{-1}=0$), load and store indirectly through an index cell, and jump if a field cell is zero.
--   - Index instructions: constant, addition, truncated subtraction, indirect load and store, jump if $I[a]\le I[b]$; and halt.
--   - Every executed instruction counts as one **operation**.
--   - A state uses at most $B$ **slots** if every nonzero field cell and every nonzero index cell has address $<B$ and the index cells hold at most $B$ bits in total.
--
--   A program **computes** an output vector $\mathrm{out}\in k^n$ from index input $I_{\mathrm{in}}$ and field input $F_{\mathrm{in}}$ (placed from cell $0$ on) within $W$ operations and $S$ slots if it halts with $F[0],\dots,F[n-1]$ holding $\mathrm{out}$ after at most $W$ operations, and every state reached along the run uses at most $S$ slots.
--
--   **Formalization Note** Counting index instructions as operations, and charging index storage to the slot budget, makes these measures at least the paper's field-operation count and field-slot count; it also prevents field data from being stored for free in index cells.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), §4 pp. 11–16 (PDF 13–18)

import Mathlib

namespace QuasilinearAG.Encoding

/-!
# An algebraic RAM over a field `k`: field operations and live field slots

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), §4 pp. 11–16 (PDF 13–18): bounds in
"field operations" (field work) and "live field slots" (live field storage).

A program is a finite list of instructions over two memories: field cells `F[0], F[1], …` holding
elements of `k`, and index cells `I[0], I[1], …` holding natural numbers (counters, addresses).

* field instructions: `fconst d c` (`F[d] := c`, `c ∈ k` a constant of the program), `fadd`,
  `fsub`, `fmul` (`F[d] := F[a] ∘ F[b]`), `finv d a` (`F[d] := F[a]⁻¹`, with `0⁻¹ = 0`),
  `fload d a` (`F[d] := F[I[a]]`), `fstore a b` (`F[I[a]] := F[b]`), `fjz a target` (jump if
  `F[a] = 0`);
* index instructions: `iconst`, `iadd`, `imonus` (truncated subtraction), `iload`, `istore` (both
  indirect), `ijle a b target` (jump if `I[a] ≤ I[b]`);
* `halt`. An invalid program counter is stuck and never halts.

Every executed instruction costs one operation (`ops`): field operations and index bookkeeping
alike. `SlotsWithin st B`: every nonzero field cell and every nonzero index cell has address
`< B`, and the index cells hold at most `B` bits in total; so `B` bounds the live field slots and
also the control storage (index data cannot hold field data for free).

`AComputesVec p iIn fIn out W S`: started with `I` holding `iIn` and `F` holding `fIn` from cell
`0` on (zero elsewhere), `p` halts with `F[0], …, F[n-1]` holding the vector `out`, after at most
`W` operations, and every state reached along the run satisfies `SlotsWithin _ S`.
-/

/-- An instruction of the algebraic RAM over `k`. -/
inductive AInstr (k : Type*)
  | fconst (d : ℕ) (c : k)
  | fadd (d a b : ℕ)
  | fsub (d a b : ℕ)
  | fmul (d a b : ℕ)
  | finv (d a : ℕ)
  | fload (d a : ℕ)
  | fstore (a b : ℕ)
  | fjz (a target : ℕ)
  | iconst (d c : ℕ)
  | iadd (d a b : ℕ)
  | imonus (d a b : ℕ)
  | iload (d a : ℕ)
  | istore (a b : ℕ)
  | ijle (a b target : ℕ)
  | halt

/-- A program of the algebraic RAM over `k`. -/
abbrev AProgram (k : Type*) := List (AInstr k)

/-- Machine state: program counter, field memory, index memory, halted flag, operation count. -/
structure AState (k : Type*) where
  pc : ℕ
  fmem : ℕ → k
  imem : ℕ → ℕ
  halted : Bool
  ops : ℕ

variable {k : Type*} [Field k]

/-- The start state with index memory `iIn` and field memory `fIn` from cell `0` on. -/
def AState.init (iIn : List ℕ) (fIn : List k) : AState k :=
  ⟨0, fun i => fIn.getD i 0, fun i => iIn.getD i 0, false, 0⟩

open Classical in
/-- One step; a halted state stays, an invalid program counter is stuck. Each executed
instruction adds `1` to `ops`. -/
noncomputable def AProgram.step (p : AProgram k) (st : AState k) : AState k :=
  if st.halted then st
  else
    match p[st.pc]? with
    | none => st
    | some (.fconst d c) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d c, ops := st.ops + 1 }
    | some (.fadd d a b) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d (st.fmem a + st.fmem b),
                  ops := st.ops + 1 }
    | some (.fsub d a b) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d (st.fmem a - st.fmem b),
                  ops := st.ops + 1 }
    | some (.fmul d a b) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d (st.fmem a * st.fmem b),
                  ops := st.ops + 1 }
    | some (.finv d a) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d (st.fmem a)⁻¹,
                  ops := st.ops + 1 }
    | some (.fload d a) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem d (st.fmem (st.imem a)),
                  ops := st.ops + 1 }
    | some (.fstore a b) =>
        { st with pc := st.pc + 1, fmem := Function.update st.fmem (st.imem a) (st.fmem b),
                  ops := st.ops + 1 }
    | some (.fjz a target) =>
        { st with pc := if st.fmem a = 0 then target else st.pc + 1, ops := st.ops + 1 }
    | some (.iconst d c) =>
        { st with pc := st.pc + 1, imem := Function.update st.imem d c, ops := st.ops + 1 }
    | some (.iadd d a b) =>
        { st with pc := st.pc + 1, imem := Function.update st.imem d (st.imem a + st.imem b),
                  ops := st.ops + 1 }
    | some (.imonus d a b) =>
        { st with pc := st.pc + 1, imem := Function.update st.imem d (st.imem a - st.imem b),
                  ops := st.ops + 1 }
    | some (.iload d a) =>
        { st with pc := st.pc + 1, imem := Function.update st.imem d (st.imem (st.imem a)),
                  ops := st.ops + 1 }
    | some (.istore a b) =>
        { st with pc := st.pc + 1, imem := Function.update st.imem (st.imem a) (st.imem b),
                  ops := st.ops + 1 }
    | some (.ijle a b target) =>
        { st with pc := if st.imem a ≤ st.imem b then target else st.pc + 1, ops := st.ops + 1 }
    | some .halt => { st with halted := true, ops := st.ops + 1 }

/-- The state after `T` steps. -/
noncomputable def AProgram.run (p : AProgram k) (iIn : List ℕ) (fIn : List k) (T : ℕ) :
    AState k :=
  p.step^[T] (AState.init iIn fIn)

/-- Live storage of a state is at most `B`: nonzero field and index cells have addresses `< B`,
and the index cells hold at most `B` bits in total. -/
def SlotsWithin (st : AState k) (B : ℝ) : Prop :=
  (∀ i, st.fmem i ≠ 0 → (i : ℝ) < B) ∧ (∀ i, st.imem i ≠ 0 → (i : ℝ) < B) ∧
    ∀ S : Finset ℕ, ((∑ i ∈ S, (st.imem i).size : ℕ) : ℝ) ≤ B

/-- `p` halts from `(iIn, fIn)` with `F[0], …, F[n-1]` holding `out`, after at most `W`
operations, and every reached state has live storage at most `S`. -/
def AComputesVec {n : ℕ} (p : AProgram k) (iIn : List ℕ) (fIn : List k) (out : Fin n → k)
    (W S : ℝ) : Prop :=
  ∃ T : ℕ, (p.run iIn fIn T).halted = true ∧ (∀ i : Fin n, (p.run iIn fIn T).fmem i = out i) ∧
    ((p.run iIn fIn T).ops : ℝ) ≤ W ∧ ∀ T' : ℕ, SlotsWithin (p.run iIn fIn T') S

end QuasilinearAG.Encoding


