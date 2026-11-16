-- Prove2me | Definitions.Def_MatMulDS_Supplement_fexec
-- name    : MatMulDS_Supplement_fexec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:11:24.338183+00:00
-- url     : https://prove2.me/theorems/5dadb03e-943a-4f94-85d0-42f87c011bca
-- title:
--   Counting field operations on the algebraic RAM
-- statement:
--   On the algebraic RAM of the mission (two banks of cells: machine words and elements of a field $\mathbb F$), the **field-operation count** of a run is the number of executed instructions that touch a field cell: the constants $0,1$, the operations $+,-,\times,{}^{-1}$, the loads and stores of field cells, the zero test and the coin. Word instructions (indexing and control) are not charged.
--
--   A program $P$, started on given memories, **halts within $t$ field operations** with final memories $m'$ if some run of $P$ halts after finitely many steps, executing at most $t$ field instructions, with memories $m'$.
--
--   This is the cost measure of the phrase "with $O(\cdot)$ field operations" in Definition 8.1 and of the bounds of Theorem 8.8.
--
--   **Formalization Note** `fexec` mirrors the published `aexec` instruction by instruction, with a separate fuel for termination and a budget for field instructions.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Definition 8.1, pp.50–51 (PDF pp.52–53); Theorem 8.8, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS.Supplement

/-- The instruction touches a field cell: it is one of `fzero fone fadd fsub fmul finv fload fstore fbz fcoin`. -/
def IsFieldInstr : AInstr → Prop
  | .fzero _ | .fone _ | .fadd _ _ _ | .fsub _ _ _ | .fmul _ _ _ | .finv _ _ | .fload _ _ | .fstore _ _
  | .fbz _ _ | .fcoin _ => True
  | _ => False

/-- **Counting field operations on the published algebraic RAM.** The final memories, if `P`, run from position
`pc` with next coin index `c`, halts within `g` steps in all and executes at most `t` field instructions. Every
instruction has the semantics of `MatroidSensOracle.aexec`; a field instruction with no field budget left fails.

Source: Alman, Nogler, Vassilevska Williams, STOC 2027 submission (held file sha256 6c5a1c16…), Definition 8.1,
pp.50–51 (PDF pp.52–53): "preprocesses them with `O(N^{2−β})` field operations"; Theorem 8.8, p.55: "All operation
bounds are worst-case numbers of field operations".

**Formalization Note.**
* Only field instructions are charged: word instructions (indexing, control) are free, as in the algebraic cost
  model of "field operations". `g` is a fuel for termination only; a run halts within `t` field operations if
  some `g` works.
* Every instruction that touches a field cell is one field operation, including the moves `fload`, `fstore` and the
  zero test `fbz`. -/
noncomputable def fexec {F : Type} [Field F] [DecidableEq F] {w : ℕ} (P : List AInstr)
    (ω : ℕ → F) : (g t pc c : ℕ) → (wm : ℤ → BitVec w) → (fm : ℤ → F) →
    Option ((ℤ → BitVec w) × (ℤ → F))
  | 0, _, _, _, _, _ => none
  | g + 1, t, pc, c, wm, fm =>
    let wwrite (i : ℤ) (v : BitVec w) :=
      fexec P ω g t (pc + 1) c (fun x => if x = i then v else wm x) fm
    let fwrite (i : ℤ) (v : F) (c' : ℕ) :=
      if t = 0 then none else
        fexec P ω g (t - 1) (pc + 1) c' wm (fun x => if x = i then v else fm x)
    match P.getD pc .halt with
    | .one i => wwrite i 1
    | .add i j k => wwrite i (wm j + wm k)
    | .sub i j k => wwrite i (wm j - wm k)
    | .mul i j k => wwrite i (wm j * wm k)
    | .udiv i j k => wwrite i (wm j / wm k)
    | .umod i j k => wwrite i (wm j % wm k)
    | .load i j => wwrite i (wm (wm j).toInt)
    | .store i j => wwrite (wm i).toInt (wm j)
    | .bltz i l => fexec P ω g t (if (wm i).toInt < 0 then l else pc + 1) c wm fm
    | .fzero i => fwrite i 0 c
    | .fone i => fwrite i 1 c
    | .fadd i j k => fwrite i (fm j + fm k) c
    | .fsub i j k => fwrite i (fm j - fm k) c
    | .fmul i j k => fwrite i (fm j * fm k) c
    | .finv i j => fwrite i (fm j)⁻¹ c
    | .fload i j => fwrite i (fm (wm j).toInt) c
    | .fstore i j => fwrite (wm i).toInt (fm j) c
    | .fbz i l =>
      if t = 0 then none else
        fexec P ω g (t - 1) (if fm i = 0 then l else pc + 1) c wm fm
    | .fcoin i => fwrite i (ω c) (c + 1)
    | .halt => some (wm, fm)

/-- The coin-free program `P`, started at position `0` on the memories `mem`, halts with the memories `mem'` after
at most `t` field operations (and finitely many word operations). -/
def FHalts {F : Type} [Field F] [DecidableEq F] {w : ℕ} (P : List AInstr) (mem : (ℤ → BitVec w) × (ℤ → F))
    (t : ℕ) (mem' : (ℤ → BitVec w) × (ℤ → F)) : Prop :=
  ∃ g : ℕ, fexec P (fun _ => 0) g t 0 0 mem.1 mem.2 = some mem'

end MatMulDS.Supplement


