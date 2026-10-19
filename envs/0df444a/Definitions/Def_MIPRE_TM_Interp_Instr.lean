-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Instr
-- name    : MIPRE_TM_Interp_Instr
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:16.20465+00:00
-- url     : https://prove2.me/theorems/ce399929-12ce-4d92-a70d-d7a33ee16f24
-- title:
--   Definitions of Instr: The interpreter machine: alphabet, tapes, instructions and programs The interpreter `U`…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Instr` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The interpreter machine: alphabet, tapes, instructions and programs. The interpreter `U` (`planning/succinct-cook-levin.md`, S2) is a multi-input Turing machine that runs the evaluation machine of the ambient model (`MIPRE.Cost.Machine`) on a configuration held on its work tapes. Its control is a small language of *routine instructions* — copy a subtree, copy to a marker, push and pop, locate an environment entry, charge the budget — each executed over a few phases, organized in short straight-line programs, one per case of the evaluation step. This file has the alphabet, the tape names, the…
--
--   **Definitions** (48): `MIPRE.TM.Interp.A` (The answer `a'`.); `MIPRE.TM.Interp.B` (The answer `b'`.); `MIPRE.TM.Interp.BUD` (The budget.); `MIPRE.TM.Interp.C` (The control tape.); `MIPRE.TM.Interp.CNT` (The depth counter.); `MIPRE.TM.Interp.E` (The environment tape.); `MIPRE.TM.Interp.IT` (The input tapes.); `MIPRE.TM.Interp.Instr` (The routine instructions.); `MIPRE.TM.Interp.K` (The stack tape.); `MIPRE.TM.Interp.N` (`encode n`.); `MIPRE.TM.Interp.PROG` (The program `𝒟`.); `MIPRE.TM.Interp.Phase` (The phases of an instruction.); `MIPRE.TM.Interp.ProgId` (The programs: one per case of the evaluation step, the dispatcher, the initialization and the final check.); `MIPRE.TM.Interp.Sym` (The work alphabet: the two bits, the environment separator `#`, the frame end `$` and the environment mark `¶` of a closure frame.); `MIPRE.TM.Interp.T` (`T` in unary.); `MIPRE.TM.Interp.WT` (The work tapes.); `MIPRE.TM.Interp.X` (The scratch tape.); `MIPRE.TM.Interp.XS` (`encode x`.); `MIPRE.TM.Interp.YS` (`encode y`.); `MIPRE.TM.Interp.acceptProg`; `MIPRE.TM.Interp.dispatchProg` (The dispatcher of a step: on `ev`, read the tag; on `ret`, the top frame's tag, or finish when the stack is empty.); `MIPRE.TM.Interp.evConsProg` (`ev (cons h t)`: push the frame `cons1 t env`, evaluate `h`, at cost one.); `MIPRE.TM.Interp.evConstProg` (`ev (const d)`: return `d`, at cost its size.); `MIPRE.TM.Interp.evDispatchProg` (The tag of the program to evaluate: `(10)^k 0` for `k = 0 … 6`; and 5 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Instr` (`MIPRE/TM/Interp/Instr.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Instr.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Instr.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# The interpreter machine: alphabet, tapes, instructions and programs

The interpreter `U` (`planning/succinct-cook-levin.md`, S2) is a multi-input Turing machine
that runs the evaluation machine of the ambient model (`MIPRE.Cost.Machine`) on a
configuration held on its work tapes. Its control is a small language of *routine
instructions* — copy a subtree, copy to a marker, push and pop, locate an environment entry,
charge the budget — each executed over a few phases, organized in short straight-line
programs, one per case of the evaluation step. This file has the alphabet, the tape names,
the instructions and the programs; `Machine.lean` interprets them.

## Tapes

Seven input tapes: the program `𝒟` as the preorder bits of `𝒟.toData`; the bits of
`encode n`, `encode x`, `encode y`; the budget `T` in unary; the answers `a'`, `b'` as raw
bit strings. Six work tapes: `C` (the control), `E` (the environment), `K` (the stack), `X`
(scratch), `CNT` (a unary depth counter), `BUD` (the unary budget).

## Representation (`Repr.lean`)

Values `v : Data` as `v.toBits`, over the symbols `0`, `1`. The control on `C`: `0 · S(p.toData)`
for `ev p`, `1 · S(v)` for `ret v`, from cell `0`. The environment `[v₁, …, vₙ]` (`v₁` the
innermost) on `E` as `S(vₙ) # … # S(v₁) #`, head after the last `#`. The stack on `K`, frames
bottom to top, each `tag · payload · $`, closures carrying their environment in the same
form after a `¶`.
-/

namespace MIPRE.TM.Interp

/-- The work alphabet: the two bits, the environment separator `#`, the frame end `$` and
the environment mark `¶` of a closure frame. -/
inductive Sym
  | zero
  | one
  | sep
  | fr
  | en
  deriving DecidableEq, Repr

instance : Fintype Sym := derive_fintype% Sym

/-- The work tapes. -/
abbrev WT := Fin 6

/-- The input tapes. -/
abbrev IT := Fin 7

/-- The control tape. -/
abbrev C : WT := 0
/-- The environment tape. -/
abbrev E : WT := 1
/-- The stack tape. -/
abbrev K : WT := 2
/-- The scratch tape. -/
abbrev X : WT := 3
/-- The depth counter. -/
abbrev CNT : WT := 4
/-- The budget. -/
abbrev BUD : WT := 5

/-- The program `𝒟`. -/
abbrev PROG : IT := 0
/-- `encode n`. -/
abbrev N : IT := 1
/-- `T` in unary. -/
abbrev T : IT := 2
/-- `encode x`. -/
abbrev XS : IT := 3
/-- `encode y`. -/
abbrev YS : IT := 4
/-- The answer `a'`. -/
abbrev A : IT := 5
/-- The answer `b'`. -/
abbrev B : IT := 6

/-- The programs: one per case of the evaluation step, the dispatcher, the initialization
and the final check. -/
inductive ProgId
  | init
  | dispatch
  | ret0x
  | evDispatch
  | evVar
  | evNil
  | evConst
  | evCons
  | evElim
  | evElimNil
  | evElimCons
  | evLet
  | evLoop
  | retCons1
  | retCons2
  | retLet1
  | retLoop1
  | retLoopNil
  | retLoopStop
  | retLoopCont
  | final
  | finalA
  | finalB
  | accept
  deriving DecidableEq, Repr

instance : Fintype ProgId := derive_fintype% ProgId

/-- The routine instructions. Every instruction leaves the heads it does not name where
they are. -/
inductive Instr
  /-- Copy the subtree (a preorder-serialized `Data`) under the head of `src` to `dst`
  (skip it if `dst = none`), advancing both heads past it; with `charge`, pop one budget
  cell per bit (halting if the budget is exhausted). Uses `CNT`, which must be empty with
  its head at `0`, and leaves it so. -/
  | copyTree (src : WT) (dst : Option WT) (charge : Bool)
  /-- Copy from `src` to `dst` up to the symbol `m` (`none` the blank), which is not copied;
  the `src` head ends on it. -/
  | copyUntil (m : Option Sym) (src dst : WT)
  /-- Write `s` and move right. -/
  | write (t : WT) (s : Sym)
  /-- Move right (`dir = true`) or left. -/
  | move (t : WT) (dir : Bool)
  /-- One left, then left to the blank, then one right: to cell `0` when cells
  `0 … pos - 1` are not blank (the head may sit on the blank after the content). -/
  | rewind (t : WT)
  /-- Move right to the first blank. -/
  | toEnd (t : WT)
  /-- Erase rightwards to the first blank (the cells erased must not contain `$`, which
  marks the start meanwhile), ending where it started. -/
  | eraseRight (t : WT)
  /-- Move one left, then left to the marker `m` or a blank, then one right. -/
  | leftToMarker (m : Sym) (t : WT)
  /-- From the end: erase the last cell and everything before it back to the marker `m` or a
  blank (exclusive), ending right after the marker; nothing on an empty tape. -/
  | popBack (m : Sym) (t : WT)
  /-- With the head of `C` on the unary index `S(ofNat i)` and the head of `E` at the end of
  the environment: write `S(env.get i)` on `X` from its head, leave `C` past the index and `E`
  at its end. -/
  | getEnv
  /-- Pop one (or two) budget cells; halt if the budget is exhausted. -/
  | charge (two : Bool)
  /-- Jump to the start of `target` if the symbol under the head of `t` is `s`. -/
  | branch (t : WT) (s : Option Sym) (target : ProgId)
  /-- Jump to the start of `target`. -/
  | jump (target : ProgId)
  /-- Emit an output symbol. -/
  | emit (s : Sym)
  /-- Halt. -/
  | halt
  /-- Write one `1` on `dst` per symbol of input `j`, up to the blank. -/
  | copyUnary (j : IT) (dst : WT)
  /-- Copy the bits of input `j` to `dst`, up to the blank. -/
  | copyInputBits (j : IT) (dst : WT)
  /-- Write `S(encode l)` on `dst` for the bit string `l` on input `j`: `1 0` per `0`,
  `1 1 0 0` per `1`, then `0`. -/
  | buildAnswer (j : IT) (dst : WT)
  /-- Halt unless input `j` is at most as long as input `ref`; both heads advance. -/
  | checkLen (j ref : IT)
  /-- Move the head of input `j` to the blank before the input. -/
  | rewindInput (j : IT)
  /-- Move the head of input `j` right or left. -/
  | moveInput (j : IT) (dir : Bool)
  deriving DecidableEq, Repr

/-- The phases of an instruction. -/
inductive Phase
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9
  deriving DecidableEq, Repr

instance : Fintype Phase := derive_fintype% Phase

open Instr ProgId

/-- The initialization: the budget, the length checks of the answers, and the initial
configuration `⟨ev 𝒟, [encode (n, x, y, a', b')], []⟩`. -/
def initProg : List Instr :=
  [copyUnary T BUD, rewindInput T, moveInput T true,
   checkLen A T, rewindInput T, moveInput T true, rewindInput A, moveInput A true,
   checkLen B T, rewindInput B, moveInput B true,
   write C .zero, copyInputBits PROG C,
   write E .one, copyInputBits N E,
   write E .one, copyInputBits XS E,
   write E .one, copyInputBits YS E,
   write E .one, buildAnswer A E,
   buildAnswer B E,
   write E .sep,
   jump dispatch]

/-- The dispatcher of a step: on `ev`, read the tag; on `ret`, the top frame's tag, or
finish when the stack is empty. -/
def dispatchProg : List Instr :=
  [rewind C, branch C (some .zero) evDispatch,
   move C true, move K false, branch K none final, leftToMarker .fr K,
   branch K (some .zero) ret0x, move K true, branch K (some .zero) retLet1, jump retLoop1]

def ret0xProg : List Instr :=
  [move K true, branch K (some .zero) retCons1, jump retCons2]

/-- The tag of the program to evaluate: `(10)^k 0` for `k = 0 … 6`; every case starts with
the head of `C` on the final `0` of the tag. -/
def evDispatchProg : List Instr :=
  [move C true, move C true,
   branch C (some .zero) evVar, move C true, move C true,
   branch C (some .zero) evNil, move C true, move C true,
   branch C (some .zero) evCons, move C true, move C true,
   branch C (some .zero) evElim, move C true, move C true,
   branch C (some .zero) evLet, move C true, move C true,
   branch C (some .zero) evLoop, move C true, move C true,
   jump evConst]

/-- `ev (var i)`: return `env.get i`, at cost its size plus one. -/
def evVarProg : List Instr :=
  [move C true, rewind X, getEnv,
   rewind X, rewind C, write C .one, copyTree X (some C) true, charge false,
   jump dispatch]

/-- `ev nil`: return `nil`, at cost one. -/
def evNilProg : List Instr :=
  [rewind C, write C .one, write C .zero, charge false, jump dispatch]

/-- `ev (const d)`: return `d`, at cost its size. -/
def evConstProg : List Instr :=
  [move C true, rewind X, copyTree C (some X) true,
   rewind C, write C .one, rewind X, copyTree X (some C) false,
   jump dispatch]

/-- `ev (cons h t)`: push the frame `cons1 t env`, evaluate `h`, at cost one. -/
def evConsProg : List Instr :=
  [move C true, move C true, rewind X, copyTree C (some X) false,
   write K .zero, write K .zero, copyTree C (some K) false, write K .en,
   rewind E, copyUntil none E K, write K .fr,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   charge false, jump dispatch]

/-- `ev (elim i n c)`: fetch `env.get i` and dispatch on it. -/
def evElimProg : List Instr :=
  [move C true, move C true, rewind X, getEnv, move C true,
   rewind X, branch X (some .zero) evElimNil, jump evElimCons]

/-- `env.get i = nil`: evaluate `n`, at cost one. -/
def evElimNilProg : List Instr :=
  [rewind X, copyTree C (some X) false,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   charge false, jump dispatch]

/-- `env.get i = cons a b`: push `b` then `a`, evaluate `c`, at cost one. -/
def evElimConsProg : List Instr :=
  [move X true, copyTree X none false, copyTree X (some E) false, write E .sep,
   rewind X, move X true, copyTree X (some E) false, write E .sep,
   copyTree C none false, rewind X, copyTree C (some X) false,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   charge false, jump dispatch]

/-- `ev (let_ e b)`: push the frame `let1 b env`, evaluate `e`, at cost one. -/
def evLetProg : List Instr :=
  [move C true, move C true, rewind X, copyTree C (some X) false,
   write K .one, write K .zero, copyTree C (some K) false, write K .en,
   rewind E, copyUntil none E K, write K .fr,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   charge false, jump dispatch]

/-- `ev (loop b)`: push the frame `loop1 b env`, evaluate `b`, at no cost. -/
def evLoopProg : List Instr :=
  [move C true, rewind X, copyTree C (some X) false,
   write K .one, write K .one, rewind X, copyTree X (some K) false, write K .en,
   rewind E, copyUntil none E K, write K .fr,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   jump dispatch]

/-- `ret v` to `cons1 t env'`: environment `env'`, push `cons2 v`, evaluate `t`. -/
def retCons1Prog : List Instr :=
  [move K true, rewind X, copyTree K (some X) false, move K true,
   rewind E, copyUntil (some .fr) K E, eraseRight E,
   move K true, popBack .fr K,
   write K .zero, write K .one, copyTree C (some K) false, write K .fr,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   jump dispatch]

/-- `ret v` to `cons2 a`: return `cons a v`. -/
def retCons2Prog : List Instr :=
  [move K true, rewind X, write X .one,
   copyTree K (some X) false, copyTree C (some X) false,
   move K true, popBack .fr K,
   rewind C, write C .one, rewind X, copyTree X (some C) false,
   jump dispatch]

/-- `ret v` to `let1 b env'`: environment `v :: env'`, evaluate `b`. -/
def retLet1Prog : List Instr :=
  [move K true, rewind X, copyTree K (some X) false, move K true,
   rewind E, copyUntil (some .fr) K E, eraseRight E,
   copyTree C (some E) false, write E .sep,
   move K true, popBack .fr K,
   rewind C, write C .zero, rewind X, copyTree X (some C) false,
   jump dispatch]

/-- `ret v` to `loop1 b env'`: dispatch on the shape of `v`. -/
def retLoop1Prog : List Instr :=
  [branch C (some .zero) retLoopNil, move C true, branch C (some .zero) retLoopStop,
   jump retLoopCont]

/-- `v = nil`: return `nil` in `env'`, at cost one. -/
def retLoopNilProg : List Instr :=
  [move K true, copyTree K none false, move K true,
   rewind E, copyUntil (some .fr) K E, eraseRight E,
   move K true, popBack .fr K,
   rewind C, write C .one, write C .zero,
   charge false, jump dispatch]

/-- `v = cons nil r`: return `r` in `env'`, at cost one. -/
def retLoopStopProg : List Instr :=
  [move C true, rewind X, copyTree C (some X) false,
   move K true, copyTree K none false, move K true,
   rewind E, copyUntil (some .fr) K E, eraseRight E,
   move K true, popBack .fr K,
   rewind C, write C .one, rewind X, copyTree X (some C) false,
   charge false, jump dispatch]

/-- `v = cons (cons _ _) v'`: environment `v' :: env'.tail`, the frame updated, evaluate
`b`, at cost one. -/
def retLoopContProg : List Instr :=
  [copyTree C none false, rewind X, copyTree C (some X) false,
   move K true, copyTree K none false, move K true,
   rewind E, copyUntil (some .fr) K E, eraseRight E,
   popBack .sep E,
   rewind X, copyTree X (some E) false, write E .sep,
   move K true, popBack .en K, rewind E, copyUntil none E K, write K .fr,
   move K false, leftToMarker .fr K, move K true, move K true, rewind X,
   copyTree K (some X) false,
   rewind C, write C .zero, rewind X, copyTree X (some C) false, toEnd K,
   charge false, jump dispatch]

/-- The final check: the result must be `encode true = cons nil nil`, bits `1 0 0`. -/
def finalProg : List Instr := [branch C (some .one) finalA, halt]
def finalAProg : List Instr := [move C true, branch C (some .zero) finalB, halt]
def finalBProg : List Instr := [move C true, branch C (some .zero) accept, halt]
def acceptProg : List Instr := [emit .one, halt]

/-- The programs. -/
def prog : ProgId → List Instr
  | .init => initProg
  | .dispatch => dispatchProg
  | .ret0x => ret0xProg
  | .evDispatch => evDispatchProg
  | .evVar => evVarProg
  | .evNil => evNilProg
  | .evConst => evConstProg
  | .evCons => evConsProg
  | .evElim => evElimProg
  | .evElimNil => evElimNilProg
  | .evElimCons => evElimConsProg
  | .evLet => evLetProg
  | .evLoop => evLoopProg
  | .retCons1 => retCons1Prog
  | .retCons2 => retCons2Prog
  | .retLet1 => retLet1Prog
  | .retLoop1 => retLoop1Prog
  | .retLoopNil => retLoopNilProg
  | .retLoopStop => retLoopStopProg
  | .retLoopCont => retLoopContProg
  | .final => finalProg
  | .finalA => finalAProg
  | .finalB => finalBProg
  | .accept => acceptProg

/-- The length bound on the programs. -/
def maxPc : ℕ := 32

end MIPRE.TM.Interp


