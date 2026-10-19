-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Machine
-- name    : MIPRE_TM_Interp_Machine
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:17.477697+00:00
-- url     : https://prove2.me/theorems/da046e77-1175-47b8-a12a-230f36e10051
-- title:
--   Definitions of Machine: The interpreter machine `U` is the multi-input Turing machine interpreting the programs of `Instr.lean`: a state is a…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Machine` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The interpreter machine. `U` is the multi-input Turing machine interpreting the programs of `Instr.lean`: a state is a program, a position in it and the phase of the instruction there (`Ctl`), and one step executes one phase of the current instruction (`execInstr`), producing head moves, writes, an optional output symbol and the next control: the same instruction in another phase, the next instruction, a jump to the start of another program, or a halt. The instructions' semantics, phase by phase, is documented on `execInstr`; their specifications as reachability triples are in `Routines.lean`.
--
--   **Definitions** (12): `MIPRE.TM.Interp.Act` (The actions of one step: input head moves, work-tape writes and moves, the output, and the next control.); `MIPRE.TM.Interp.Act.base` (No moves, no writes, no output.); `MIPRE.TM.Interp.Act.emit` (Emit `s`.); `MIPRE.TM.Interp.Act.mi` (Move the head of input tape `j`.); `MIPRE.TM.Interp.Act.mw` (Move the head of work tape `t`.); `MIPRE.TM.Interp.Act.ww` (Write `s` (`none` the blank) on work tape `t`.); `MIPRE.TM.Interp.Ctl` (The control of the machine: a program, a position, a phase.); `MIPRE.TM.Interp.Next` (What an instruction phase does to the control.); `MIPRE.TM.Interp.U` (**The interpreter machine.**); `MIPRE.TM.Interp.execInstr` (The semantics of an instruction phase, given the symbols under the input heads `as` and the work heads `bs`.); `MIPRE.TM.Interp.instrAt` (The instruction at a position of a program (`halt` past the end).); `MIPRE.TM.Interp.resolve` (The control after a step.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Machine` (`MIPRE/TM/Interp/Machine.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Machine.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Machine.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr

/-!
# The interpreter machine

`U` is the multi-input Turing machine interpreting the programs of `Instr.lean`: a state is
a program, a position in it and the phase of the instruction there (`Ctl`), and one step
executes one phase of the current instruction (`execInstr`), producing head moves, writes,
an optional output symbol and the next control: the same instruction in another phase,
the next instruction, a jump to the start of another program, or a halt.

The instructions' semantics, phase by phase, is documented on `execInstr`; their
specifications as reachability triples are in `Routines.lean`.
-/

namespace MIPRE.TM.Interp

open Turing

/-- The control of the machine: a program, a position, a phase. -/
structure Ctl where
  k : ProgId
  pc : Fin maxPc
  ph : Phase
  deriving DecidableEq, Fintype

/-- What an instruction phase does to the control. -/
inductive Next
  | stay (ph : Phase)
  | adv
  | jmp (k : ProgId)
  | halt

/-- The actions of one step: input head moves, work-tape writes and moves, the output, and
the next control. -/
structure Act where
  inMoves : IT → SignType := fun _ => 0
  works : WT → Option (Option Sym) × SignType := fun _ => (none, 0)
  out : Option Sym := none
  next : Next

namespace Act

/-- No moves, no writes, no output. -/
def base (n : Next) : Act := { next := n }

/-- Move the head of work tape `t`. -/
def mw (a : Act) (t : WT) (m : SignType) : Act :=
  { a with works := Function.update a.works t ((a.works t).1, m) }

/-- Write `s` (`none` the blank) on work tape `t`. -/
def ww (a : Act) (t : WT) (s : Option Sym) : Act :=
  { a with works := Function.update a.works t (some s, (a.works t).2) }

/-- Move the head of input tape `j`. -/
def mi (a : Act) (j : IT) (m : SignType) : Act :=
  { a with inMoves := Function.update a.inMoves j m }

/-- Emit `s`. -/
def emit (a : Act) (s : Sym) : Act := { a with out := some s }

end Act

open Act Phase

/-- The semantics of an instruction phase, given the symbols under the input heads `as`
and the work heads `bs`. -/
def execInstr (ins : Instr) (ph : Phase) (as : IT → Option Sym) (bs : WT → Option Sym) : Act :=
  match ins with
  | .copyTree src dst ch =>
    match ph with
    -- `p0`: one pending subtree.
    | p0 => (base (.stay p1)).ww CNT (some .one) |>.mw CNT 1
    -- `p1`: scan a bit; a `1` adds a pending subtree, a `0` removes one.
    | p1 =>
      match bs src with
      | some .one =>
        let a := (base (.stay (if ch then p4 else p1))).mw src 1 |>.ww CNT (some .one) |>.mw CNT 1
        let a := if ch then a.mw BUD (-1) else a
        match dst with
        | some d => a.ww d (some .one) |>.mw d 1
        | none => a
      | some .zero =>
        let a := (base (.stay p2)).mw src 1 |>.mw CNT (-1)
        let a := if ch then a.mw BUD (-1) else a
        match dst with
        | some d => a.ww d (some .zero) |>.mw d 1
        | none => a
      | _ => base .halt
    -- `p2`: after a `0`: pop the counter (and charge).
    | p2 =>
      if ch then
        match bs BUD with
        | some .one => (base (.stay p3)).ww CNT none |>.mw CNT (-1) |>.ww BUD none
        | _ => base .halt
      else (base (.stay p3)).ww CNT none |>.mw CNT (-1)
    -- `p3`: no pending subtree left: done; else continue.
    | p3 =>
      match bs CNT with
      | none => (base .adv).mw CNT 1
      | some _ => (base (.stay p1)).mw CNT 1
    -- `p4`: after a `1`, with charging: check the budget.
    | p4 =>
      match bs BUD with
      | some .one => (base (.stay p1)).ww BUD none
      | _ => base .halt
    | _ => base .halt
  | .copyUntil m src dst =>
    if bs src = m then base .adv
    else
      match bs src with
      | some s => (base (.stay p0)).ww dst (some s) |>.mw dst 1 |>.mw src 1
      | none => base .halt
  | .write t s => (base .adv).ww t (some s) |>.mw t 1
  | .move t dir => (base .adv).mw t (if dir then 1 else -1)
  | .rewind t =>
    match ph with
    -- `p0`: one left, unconditionally (the head may sit on the blank after the content).
    | p0 => (base (.stay p1)).mw t (-1)
    | _ =>
      match bs t with
      | none => (base .adv).mw t 1
      | some _ => (base (.stay p1)).mw t (-1)
  | .toEnd t =>
    match bs t with
    | none => base .adv
    | some _ => (base (.stay p0)).mw t 1
  | .eraseRight t =>
    match ph with
    -- `p0`: nothing to erase, or mark the start with `$` and go right.
    | p0 =>
      match bs t with
      | none => base .adv
      | some _ => (base (.stay p1)).ww t (some .fr) |>.mw t 1
    -- `p1`: erase rightwards to the blank, then turn back.
    | p1 =>
      match bs t with
      | none => (base (.stay p2)).mw t (-1)
      | some _ => (base (.stay p1)).ww t none |>.mw t 1
    -- `p2`: back over the blanks to the mark, erase it, done.
    | _ =>
      match bs t with
      | none => (base (.stay p2)).mw t (-1)
      | some .fr => (base .adv).ww t none
      | some _ => base .halt
  | .leftToMarker m t =>
    match ph with
    | p0 => (base (.stay p1)).mw t (-1)
    | _ =>
      match bs t with
      | none => (base .adv).mw t 1
      | some s => if s = m then (base .adv).mw t 1 else (base (.stay p1)).mw t (-1)
  | .popBack m t =>
    match ph with
    | p0 => (base (.stay p1)).mw t (-1)
    | p1 =>
      match bs t with
      | none => (base .adv).mw t 1
      | some _ => (base (.stay p2)).ww t none |>.mw t (-1)
    | _ =>
      match bs t with
      | none => (base .adv).mw t 1
      | some s => if s = m then (base .adv).mw t 1 else (base (.stay p2)).ww t none |>.mw t (-1)
  | .getEnv =>
    match ph with
    -- `p0`: onto the last separator.
    | p0 => (base (.stay p1)).mw E (-1)
    -- `p1`: on a separator: read a unit of the index.
    | p1 =>
      match bs E with
      | none => base (.stay p6)
      | some _ =>
        match bs C with
        | some .one => (base (.stay p2)).mw C 1 |>.mw E (-1)
        | some .zero => (base (.stay p4)).mw C 1 |>.mw E (-1)
        | _ => base .halt
    -- `p2`: past the unit's `0`.
    | p2 => (base (.stay p3)).mw C 1
    -- `p3`: left over the bits of an element to its separator.
    | p3 =>
      match bs E with
      | some .zero => (base (.stay p3)).mw E (-1)
      | some .one => (base (.stay p3)).mw E (-1)
      | some .sep => base (.stay p1)
      | none => base (.stay p6)
      | _ => base .halt
    -- `p4`: index consumed: left over the bits of the element to its start.
    | p4 =>
      match bs E with
      | some .zero => (base (.stay p4)).mw E (-1)
      | some .one => (base (.stay p4)).mw E (-1)
      | _ => (base (.stay p5)).mw E 1
    -- `p5`: copy the element to `X`.
    | p5 =>
      match bs E with
      | some .sep => base (.stay p8)
      | some s => (base (.stay p5)).ww X (some s) |>.mw X 1 |>.mw E 1
      | none => base .halt
    -- `p6`, `p7`: out of range: consume the rest of the index, then `nil` on `X`.
    | p6 =>
      match bs C with
      | some .one => (base (.stay p7)).mw C 1
      | some .zero => (base (.stay p9)).mw C 1 |>.ww X (some .zero) |>.mw X 1 |>.mw E 1
      | _ => base .halt
    | p7 => (base (.stay p6)).mw C 1
    -- `p8`, `p9`: the head of `E` back to the end.
    | _ =>
      match bs E with
      | none => base .adv
      | some _ => (base (.stay ph)).mw E 1
  | .charge two =>
    match ph with
    | p0 => (base (.stay p1)).mw BUD (-1)
    | p1 =>
      match bs BUD with
      | some .one =>
        if two then (base (.stay p2)).ww BUD none |>.mw BUD (-1) else (base .adv).ww BUD none
      | _ => base .halt
    | _ =>
      match bs BUD with
      | some .one => (base .adv).ww BUD none
      | _ => base .halt
  | .branch t s target => if bs t = s then base (.jmp target) else base .adv
  | .jump target => base (.jmp target)
  | .emit s => (base .adv).emit s
  | .halt => base .halt
  | .copyUnary j dst =>
    match as j with
    | none => base .adv
    | some _ => (base (.stay p0)).ww dst (some .one) |>.mw dst 1 |>.mi j 1
  | .copyInputBits j dst =>
    match as j with
    | none => base .adv
    | some s => (base (.stay p0)).ww dst (some s) |>.mw dst 1 |>.mi j 1
  | .buildAnswer j dst =>
    match ph with
    | p0 =>
      match as j with
      | none => (base .adv).ww dst (some .zero) |>.mw dst 1
      | some .zero => (base (.stay p1)).ww dst (some .one) |>.mw dst 1
      | some .one => (base (.stay p2)).ww dst (some .one) |>.mw dst 1
      | _ => base .halt
    | p1 => (base (.stay p0)).ww dst (some .zero) |>.mw dst 1 |>.mi j 1
    | p2 => (base (.stay p3)).ww dst (some .one) |>.mw dst 1
    | p3 => (base (.stay p4)).ww dst (some .zero) |>.mw dst 1
    | _ => (base (.stay p0)).ww dst (some .zero) |>.mw dst 1 |>.mi j 1
  | .checkLen j ref =>
    match as j with
    | none => base .adv
    | some _ =>
      match as ref with
      | none => base .halt
      | some _ => (base (.stay p0)).mi j 1 |>.mi ref 1
  | .rewindInput j =>
    match ph with
    | p0 => (base (.stay p1)).mi j (-1)
    | _ =>
      match as j with
      | none => base .adv
      | some _ => (base (.stay p1)).mi j (-1)
  | .moveInput j dir => (base .adv).mi j (if dir then 1 else -1)

/-- The instruction at a position of a program (`halt` past the end). -/
def instrAt (k : ProgId) (pc : Fin maxPc) : Instr := (prog k).getD pc .halt

/-- The control after a step. -/
def resolve (k : ProgId) (pc : Fin maxPc) : Next → Option Ctl
  | .stay ph => some ⟨k, pc, ph⟩
  | .adv => if h : pc.val + 1 < maxPc then some ⟨k, ⟨pc.val + 1, h⟩, p0⟩ else none
  | .jmp k' => some ⟨k', ⟨0, by decide⟩, p0⟩
  | .halt => none

/-- **The interpreter machine.** -/
def U : MultiInputTM 7 6 Sym Ctl where
  q₀ := ⟨.init, ⟨0, by decide⟩, p0⟩
  tr q as bs :=
    let a := execInstr (instrAt q.k q.pc) q.ph as bs
    { inputMoves := a.inMoves, workActions := a.works, outS := a.out, q' := resolve q.k q.pc a.next }

end MIPRE.TM.Interp


