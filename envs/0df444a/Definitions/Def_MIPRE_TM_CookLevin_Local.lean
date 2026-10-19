-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Local
-- name    : MIPRE_TM_CookLevin_Local
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:10.773956+00:00
-- url     : https://prove2.me/theorems/ea265896-147b-4841-9888-b8cb7c891a74
-- title:
--   Definitions of Local: The local check of the Cook–Levin tableau The window of the tableau at a step `t` and a choice of a position on every…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Local` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The local check of the Cook–Levin tableau. The window of the tableau at a step `t` and a choice of a position on every tape (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `def:local-check-circuit`): for each tape the five cells and heads around the position at time `t`, the cell and head at the position at time `t + 1`, the states at `t` and `t + 1` and the emission flags of the step. Five cells rather than the paper's three, because the input heads of the repository's machine model clamp at both ends of the input (`Turing.moveInputPos`), and deciding whether a head one cell…
--
--   **Definitions** (16): `MIPRE.TM.CookLevin.CellVal` (The value of a tableau cell: a symbol, the blank, or the boundary marker.); `MIPRE.TM.CookLevin.CellVal.ofOpt` (The cell value of a tape symbol (`none` the blank).); `MIPRE.TM.CookLevin.CellVal.toOpt` (The tape symbol of a non-boundary cell value (the boundary reads as blank).); `MIPRE.TM.CookLevin.FullStep` (The full transition check, when every tape has its head at the offset `δ d` of the central three cells: the time-`t + 1` values are those…); `MIPRE.TM.CookLevin.LocalCfg` (A local configuration: the decoded content of a window.); `MIPRE.TM.CookLevin.LocalCfg.HeadAt` (The head of tape `d` is at offset `δ` and nowhere else in the window.); `MIPRE.TM.CookLevin.LocalCfg.HeadFar` (No head of tape `d` in the central three cells.); `MIPRE.TM.CookLevin.LocalCfg.TwoHeads` (Two heads of tape `d` in the window.); `MIPRE.TM.CookLevin.LocalCfg.encode` (The one-hot bits of a local configuration.); `MIPRE.TM.CookLevin.LocallyConsistent` (Local consistency of a decoded window.); `MIPRE.TM.CookLevin.Tape` (The tapes: `i` input tapes and `w` work tapes.); `MIPRE.TM.CookLevin.WinVar` (The variables of a window: for each tape, the five cells and heads at offsets `0..4` around the position at time `t`, the cell and head at…); `MIPRE.TM.CookLevin.checkPred` (The check predicate on window bits: the bits encode a locally consistent local configuration.); `MIPRE.TM.CookLevin.instFintypeCellValOfDecidableEq`; `MIPRE.TM.CookLevin.instFintypeWinVarOfDecidableEq`; and -10 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `toOpt_ofOpt`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Local` (`MIPRE/TM/CookLevin/Local.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Local.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Local.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
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

/-!
# The local check of the Cook–Levin tableau

The window of the tableau at a step `t` and a choice of a position on every tape
(`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `def:local-check-circuit`):
for each tape the five cells and heads around the position at time `t`, the cell and head
at the position at time `t + 1`, the states at `t` and `t + 1` and the emission flags of
the step. Five cells rather than the paper's three, because the input heads of the
repository's machine model clamp at both ends of the input (`Turing.moveInputPos`), and
deciding whether a head one cell off the center moves or stays needs the cell beyond it.

The window's bits are one-hot: one variable per cell and cell value, per state. A window
is *locally consistent* (`LocallyConsistent`) if it is the encoding of a local
configuration in which, wherever the local information suffices, the time-`t + 1` values are
the transition of the time-`t` ones: if every tape has its head in the central three cells
the whole transition is checked, including the state and the emission; a tape whose head is
not near the center keeps its cell and has no head at the center; a tape with two heads in
the window is accepted unconditionally, an invariant of the tableau excluding it. The
predicate `checkPred` on window bits is what the check circuit computes.
-/

namespace MIPRE.TM.CookLevin

open Turing

/-- The value of a tableau cell: a symbol, the blank, or the boundary marker. -/
inductive CellVal (Symbol : Type*) where
  | sym (s : Symbol)
  | blank
  | bdry
  deriving DecidableEq

instance {Symbol : Type*} [Fintype Symbol] [DecidableEq Symbol] : Fintype (CellVal Symbol) :=
  Fintype.ofEquiv (Option (Option Symbol))
    { toFun := fun o => match o with
        | some (some s) => .sym s
        | some none => .blank
        | none => .bdry
      invFun := fun v => match v with
        | .sym s => some (some s)
        | .blank => some none
        | .bdry => none
      left_inv := by rintro (_ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _) <;> rfl }

namespace CellVal

variable {Symbol : Type*}

/-- The cell value of a tape symbol (`none` the blank). -/
def ofOpt : Option Symbol → CellVal Symbol
  | some s => sym s
  | none => blank

/-- The tape symbol of a non-boundary cell value (the boundary reads as blank). -/
def toOpt : CellVal Symbol → Option Symbol
  | sym s => some s
  | blank => none
  | bdry => none

@[simp] theorem toOpt_ofOpt (o : Option Symbol) : (ofOpt o).toOpt = o := by cases o <;> rfl

end CellVal

/-- The tapes: `i` input tapes and `w` work tapes. -/
abbrev Tape (i w : ℕ) := Fin i ⊕ Fin w

/-- The variables of a window: for each tape, the five cells and heads at offsets `0..4`
around the position at time `t`, the cell and head at the position at time `t + 1`; the
states at `t` and `t + 1`; the emission flags of the step. -/
inductive WinVar (i w : ℕ) (Symbol State : Type*) where
  | cellPre (d : Tape i w) (δ : Fin 5) (v : CellVal Symbol)
  | headPre (d : Tape i w) (δ : Fin 5)
  | cellPost (d : Tape i w) (v : CellVal Symbol)
  | headPost (d : Tape i w)
  | statePre (q : Option State)
  | statePost (q : Option State)
  | emitOne
  | emitBad
  deriving DecidableEq

instance {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
    [DecidableEq State] : Fintype (WinVar i w Symbol State) :=
  derive_fintype% (WinVar i w Symbol State)

/-- A local configuration: the decoded content of a window. -/
structure LocalCfg (i w : ℕ) (Symbol State : Type*) where
  cellPre : Tape i w → Fin 5 → CellVal Symbol
  headPre : Tape i w → Fin 5 → Bool
  cellPost : Tape i w → CellVal Symbol
  headPost : Tape i w → Bool
  statePre : Option State
  statePost : Option State
  emitOne : Bool
  emitBad : Bool

namespace LocalCfg

variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]

/-- The one-hot bits of a local configuration. -/
def encode (L : LocalCfg i w Symbol State) : WinVar i w Symbol State → Bool
  | .cellPre d δ v => decide (L.cellPre d δ = v)
  | .headPre d δ => L.headPre d δ
  | .cellPost d v => decide (L.cellPost d = v)
  | .headPost d => L.headPost d
  | .statePre q => decide (L.statePre = q)
  | .statePost q => decide (L.statePost = q)
  | .emitOne => L.emitOne
  | .emitBad => L.emitBad

/-- The head of tape `d` is at offset `δ` and nowhere else in the window. -/
def HeadAt (L : LocalCfg i w Symbol State) (d : Tape i w) (δ : Fin 5) : Prop :=
  ∀ δ', L.headPre d δ' = decide (δ' = δ)

/-- Two heads of tape `d` in the window. -/
def TwoHeads (L : LocalCfg i w Symbol State) (d : Tape i w) : Prop :=
  ∃ δ δ', δ ≠ δ' ∧ L.headPre d δ = true ∧ L.headPre d δ' = true

/-- No head of tape `d` in the central three cells. -/
def HeadFar (L : LocalCfg i w Symbol State) (d : Tape i w) : Prop :=
  L.headPre d 1 = false ∧ L.headPre d 2 = false ∧ L.headPre d 3 = false

end LocalCfg

/-- The new offset of a head at offset `δ ∈ {1, 2, 3}` after a move `m`, on an input tape
(clamped: a move left from the first position, whose left neighbor is the boundary, and a
move right from the position after the input, a blank whose left neighbor is not the
boundary, stay) or a work tape (never clamped). -/
def newOffset {Symbol : Type*} [DecidableEq Symbol] (isInput : Bool)
    (cells : Fin 5 → CellVal Symbol) (δ : Fin 5) (m : SignType) : ℕ :=
  match m with
  | .zero => δ
  | .neg => if isInput ∧ cells ⟨(δ : ℕ) - 1, by omega⟩ = .bdry then δ else (δ : ℕ) - 1
  | .pos =>
    if isInput ∧ cells δ = .blank ∧ cells ⟨(δ : ℕ) - 1, by omega⟩ ≠ .bdry then δ else δ + 1

section Consistent

variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)

/-- The full transition check, when every tape has its head at the offset `δ d` of the
central three cells: the time-`t + 1` values are those of the machine's transition. -/
def FullStep (L : LocalCfg i w Symbol State) (δ : Tape i w → Fin 5) : Prop :=
  match L.statePre with
  | none =>
    (∀ d, L.cellPost d = L.cellPre d 2) ∧ (∀ d, L.headPost d = L.headPre d 2) ∧
      L.statePost = none ∧ L.emitOne = false ∧ L.emitBad = false
  | some q =>
    (∀ d, L.cellPre d (δ d) ≠ .bdry) ∧
    let out := M.tr q (fun j => (L.cellPre (.inl j) (δ (.inl j))).toOpt)
      (fun j => (L.cellPre (.inr j) (δ (.inr j))).toOpt)
    (∀ j, L.cellPost (.inl j) = L.cellPre (.inl j) 2) ∧
    (∀ j, L.cellPost (.inr j) =
      if δ (.inr j) = 2 then
        match (out.workActions j).1 with
        | none => L.cellPre (.inr j) 2
        | some s => CellVal.ofOpt s
      else L.cellPre (.inr j) 2) ∧
    (∀ j, L.headPost (.inl j) =
      decide (newOffset true (L.cellPre (.inl j)) (δ (.inl j)) (out.inputMoves j) = 2)) ∧
    (∀ j, L.headPost (.inr j) =
      decide (newOffset false (L.cellPre (.inr j)) (δ (.inr j)) (out.workActions j).2 = 2)) ∧
    L.statePost = out.q' ∧
    L.emitOne = decide (out.outS = some acc) ∧
    L.emitBad = decide (out.outS ≠ none ∧ out.outS ≠ some acc)

/-- Local consistency of a decoded window. -/
def LocallyConsistent (L : LocalCfg i w Symbol State) : Prop :=
  (∃ d, L.TwoHeads d) ∨
  ((∀ d, L.HeadFar d → L.cellPost d = L.cellPre d 2 ∧ L.headPost d = false) ∧
    ((∃ δ : Tape i w → Fin 5, (∀ d, 1 ≤ (δ d : ℕ) ∧ (δ d : ℕ) ≤ 3 ∧ L.HeadAt d (δ d)) ∧
        FullStep M acc L δ) ∨
      ¬ ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L.HeadAt d δ))

/-- The check predicate on window bits: the bits encode a locally consistent local
configuration. -/
def checkPred (win : WinVar i w Symbol State → Bool) : Prop :=
  ∃ L : LocalCfg i w Symbol State, L.encode = win ∧ LocallyConsistent M acc L

end Consistent

end MIPRE.TM.CookLevin


