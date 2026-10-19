-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Families
-- name    : MIPRE_TM_CookLevin_Families
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:08.521896+00:00
-- url     : https://prove2.me/theorems/175657cd-43de-4879-b8a6-e04038612531
-- title:
--   Definitions of Families: The clause families of the tableau, on decoded fields A *candidate* clause is three field records and three signs…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Families` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The clause families of the tableau, on decoded fields. A *candidate* clause is three field records and three signs (`Cand`): what the describer reads off its `3m + 3` input bits. `Cand.Dec c cl` says the candidate decodes to the tableau clause `cl` (each record to the variable of the corresponding literal, each sign to its polarity). For each sub-family of the tableau of the interpreter machine (`startClauses`, `freeClauses`, `bdryClauses`, `emitClauses`, `finalClauses` of `Tableau.lean`) this file gives a predicate on candidates, stated on the numeric fields alone, and proves it exact: it…
--
--   **Definitions** (46): `MIPRE.TM.CookLevin.Desc.Bdry` (`p` is a boundary cell.); `MIPRE.TM.CookLevin.Desc.BdryCell` (`unit (cell t d p v) (decide (v = bdry))` for `p` a boundary cell.); `MIPRE.TM.CookLevin.Desc.BdryHead` (`unit (head t d p) false` for `p` a boundary cell.); `MIPRE.TM.CookLevin.Desc.BdryPred` (The boundary family.); `MIPRE.TM.CookLevin.Desc.Cand` (A candidate clause: three field records and three signs.); `MIPRE.TM.CookLevin.Desc.Cand.Dec` (The candidate decodes to the clause `cl`.); `MIPRE.TM.CookLevin.Desc.EmitBad` (`unit (emitBad t) false`.); `MIPRE.TM.CookLevin.Desc.EmitMono` (`imp2 (emitted t) (emitted (t + 1))`.); `MIPRE.TM.CookLevin.Desc.EmitOnce` (`nand2 (emitOne t) (emitted t)`.); `MIPRE.TM.CookLevin.Desc.EmitOne` (`imp2 (emitOne t) (emitted (t + 1))`.); `MIPRE.TM.CookLevin.Desc.EmitPred` (The emission family.); `MIPRE.TM.CookLevin.Desc.EmitStep` (`¬ emitted (t + 1) ∨ emitted t ∨ emitOne t`.); `MIPRE.TM.CookLevin.Desc.EmitZero` (`unit (emitted 0) false`.); `MIPRE.TM.CookLevin.Desc.FinalEmitted` (`unit (emitted S) true`.); `MIPRE.TM.CookLevin.Desc.FinalPred` (The final family.); `MIPRE.TM.CookLevin.Desc.FinalState` (`unit (state S none) true`.); `MIPRE.TM.CookLevin.Desc.FreeBdry` (`unit (cell 0 (inl j) p v) (decide (v = bdry))` for `p` a boundary cell.); `MIPRE.TM.CookLevin.Desc.FreeBlank` (`imp2 (cell 0 (inl j) p blank) (cell 0 (inl j) p' blank)` for `2 < p < p'`, `p'` interior.); and 9 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Families` (`MIPRE/TM/CookLevin/Families.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Families.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Families.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds

/-!
# The clause families of the tableau, on decoded fields

A *candidate* clause is three field records and three signs (`Cand`): what the describer
reads off its `3m + 3` input bits. `Cand.Dec c cl` says the candidate decodes to the tableau
clause `cl` (each record to the variable of the corresponding literal, each sign to its
polarity). For each sub-family of the tableau of the interpreter machine
(`startClauses`, `freeClauses`, `bdryClauses`, `emitClauses`, `finalClauses` of
`Tableau.lean`) this file gives a predicate on candidates, stated on the numeric fields
alone, and proves it exact: it holds iff the candidate decodes to a clause of the
sub-family. The window family is `Window.lean`; the formulas computing these predicates are
`FamilyFml.lean` (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Candidates and decoding -/

/-- A candidate clause: three field records and three signs. -/
structure Cand where
  F₁ : Fields
  s₁ : Bool
  F₂ : Fields
  s₂ : Bool
  F₃ : Fields
  s₃ : Bool

variable (e G : ℕ)

/-- The record `F` with sign `s` decodes to the literal `l`. -/
def LitDec (F : Fields) (s : Bool) (l : Lit (TabVar 7 6 Sym Ctl (Sof e) G)) : Prop :=
  decodeVar e G F = some l.var ∧ s = l.pos

/-- The candidate decodes to the clause `cl`. -/
def Cand.Dec (c : Cand) (cl : Clause3 (TabVar 7 6 Sym Ctl (Sof e) G)) : Prop :=
  LitDec e G c.F₁ c.s₁ cl.l₁ ∧ LitDec e G c.F₂ c.s₂ cl.l₂ ∧ LitDec e G c.F₃ c.s₃ cl.l₃

/-! ## Codes of positions and values -/

/-- The code of the value of cell `p` of an input tape holding `x`. -/
def cellCode (x : List Sym) (S p : ℕ) : ℕ :=
  if p < 2 ∨ 2 * S + 5 ≤ p then 6
  else if h : 3 ≤ p ∧ p - 3 < x.length then symCode (.sym x[p - 3]) else 5

/-- The code of the value of cell `p` of a work tape at time `0`. -/
def workCode (S p : ℕ) : ℕ := if p < 2 ∨ 2 * S + 5 ≤ p then 6 else 5

/-! ## Decoding by kind: existence and same-variable lemmas -/

/-- Two records denote the same cell variable. -/
def cellEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p ∧ F.v = F'.v

/-- Two records denote the same head variable. -/
def headEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p

/-- Two records denote the same state variable. -/
def stateEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.q = F'.q

/-- Two records denote the same gate variable. -/
def auxEq (F F' : Fields) : Prop := F.t = F'.t ∧ (∀ k, F.js k = F'.js k) ∧ F.g = F'.g

/-! ## Unit clauses by kind -/

/-- The three records denote the same cell variable. -/
def UnitCell (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ cellEq c.F₁ c.F₂ ∧ cellEq c.F₁ c.F₃

/-- The three records denote the same head variable. -/
def UnitHead (c : Cand) : Prop :=
  IsHead e c.F₁ ∧ IsHead e c.F₂ ∧ IsHead e c.F₃ ∧ headEq c.F₁ c.F₂ ∧ headEq c.F₁ c.F₃

/-- The three records denote the same state variable. -/
def UnitState (c : Cand) : Prop :=
  IsState e c.F₁ ∧ IsState e c.F₂ ∧ IsState e c.F₃ ∧ stateEq c.F₁ c.F₂ ∧ stateEq c.F₁ c.F₃

/-- The three records denote the same `emitBad` variable. -/
def UnitEmitBad (c : Cand) : Prop :=
  IsEmitBad e c.F₁ ∧ IsEmitBad e c.F₂ ∧ IsEmitBad e c.F₃ ∧ c.F₁.t = c.F₂.t ∧ c.F₁.t = c.F₃.t

/-- The three records denote the same `emitted` variable. -/
def UnitEmitted (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₁.t = c.F₂.t ∧ c.F₁.t = c.F₃.t

/-- The three records denote the same gate variable. -/
def UnitAux (c : Cand) : Prop :=
  IsAux e G c.F₁ ∧ IsAux e G c.F₂ ∧ IsAux e G c.F₃ ∧ auxEq c.F₁ c.F₂ ∧ auxEq c.F₁ c.F₃

/-- The three signs agree. -/
def SameSigns (c : Cand) : Prop := c.s₂ = c.s₁ ∧ c.s₃ = c.s₁

/-! ## The start family -/

variable (fixed : Fin 7 → Option (List Sym))

/-- `unit (head 0 d p) (decide (p = startCell S d))`. -/
def StartHead (c : Cand) : Prop :=
  UnitHead e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧
    c.s₁ = decide (c.F₁.p = if c.F₁.d < 7 then 3 else Sof e + 3)

/-- `unit (state 0 q) (decide (q = some U.q₀))`. -/
def StartState (c : Cand) : Prop :=
  UnitState e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ c.s₁ = decide (c.F₁.q = qCode (some U.q₀))

/-- `unit (cell 0 (inl j) p v) (decide (v = inputCellVal x p))` for `fixed j = some x`. -/
def StartFixed (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧
    ∃ (j : Fin 7) (x : List Sym), fixed j = some x ∧ c.F₁.d = j ∧
      c.s₁ = decide (c.F₁.v = cellCode x (Sof e) c.F₁.p)

/-- `unit (cell 0 (inr j) p v) (decide (v = workCellVal₀ p))`. -/
def StartWork (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ 7 ≤ c.F₁.d ∧
    c.s₁ = decide (c.F₁.v = workCode (Sof e) c.F₁.p)

/-- The start family. -/
def StartPred (c : Cand) : Prop :=
  StartHead e c ∨ StartState e c ∨ StartFixed e fixed c ∨ StartWork e c

/-! ## The free family -/

/-- The tape `F.d` is free. -/
def FreeTape (F : Fields) : Prop := ∃ j : Fin 7, fixed j = none ∧ F.d = j

/-- `p` is a boundary cell. -/
def Bdry (S p : ℕ) : Prop := p < 2 ∨ 2 * S + 5 ≤ p

instance (S p : ℕ) : Decidable (Bdry S p) := by unfold Bdry; infer_instance

/-- `unit (cell 0 (inl j) p v) (decide (v = bdry))` for `p` a boundary cell. -/
def FreeBdry (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ Bdry (Sof e) c.F₁.p ∧
    c.s₁ = decide (c.F₁.v = 6)

/-- `unit (cell 0 (inl j) p v) false` for `p` interior and `v` none of `0`, `1`, blank. -/
def FreeOther (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧
    c.F₁.v ≠ 0 ∧ c.F₁.v ≠ 1 ∧ c.F₁.v ≠ 5 ∧ c.s₁ = false

/-- `unit (cell 0 (inl j) 2 v) (decide (v = blank))`. -/
def FreeTwo (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ c.F₁.p = 2 ∧
    c.s₁ = decide (c.F₁.v = 5)

/-- The records `F` and `F'` denote cells of the same tape and position. -/
def samePos (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p

/-- `cell 0 (inl j) p 0 ∨ cell 0 (inl j) p 1 ∨ cell 0 (inl j) p blank` for `p` interior. -/
def FreeOneOf (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ samePos c.F₁ c.F₂ ∧ samePos c.F₁ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧
    c.F₁.v = 0 ∧ c.F₂.v = 1 ∧ c.F₃.v = 5 ∧ c.s₁ = true ∧ c.s₂ = true ∧ c.s₃ = true

/-- `nand2 (cell 0 (inl j) p v) (cell 0 (inl j) p v')` for `p` interior and `v ≠ v'`. -/
def FreeNand (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ samePos c.F₁ c.F₂ ∧ cellEq c.F₂ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧ c.F₁.v ≠ c.F₂.v ∧
    c.s₁ = false ∧ c.s₂ = false ∧ c.s₃ = false

/-- `imp2 (cell 0 (inl j) p blank) (cell 0 (inl j) p' blank)` for `2 < p < p'`, `p'` interior. -/
def FreeBlank (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ cellEq c.F₂ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ c.F₂.t = c.F₁.t ∧ c.F₂.d = c.F₁.d ∧
    2 < c.F₁.p ∧ ¬ Bdry (Sof e) c.F₂.p ∧ c.F₁.p < c.F₂.p ∧ c.F₁.v = 5 ∧ c.F₂.v = 5 ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

/-- The free family. -/
def FreePred (c : Cand) : Prop :=
  FreeBdry e fixed c ∨ FreeOther e fixed c ∨ FreeTwo e fixed c ∨ FreeOneOf e fixed c ∨
    FreeNand e fixed c ∨ FreeBlank e fixed c

/-! ## The boundary family -/

/-- `unit (cell t d p v) (decide (v = bdry))` for `p` a boundary cell. -/
def BdryCell (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ Bdry (Sof e) c.F₁.p ∧ c.s₁ = decide (c.F₁.v = 6)

/-- `unit (head t d p) false` for `p` a boundary cell. -/
def BdryHead (c : Cand) : Prop :=
  UnitHead e c ∧ SameSigns c ∧ Bdry (Sof e) c.F₁.p ∧ c.s₁ = false

/-- The boundary family. -/
def BdryPred (c : Cand) : Prop := BdryCell e c ∨ BdryHead e c

/-! ## The emission family -/

/-- `unit (emitted 0) false`. -/
def EmitZero (c : Cand) : Prop := UnitEmitted e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ c.s₁ = false

/-- `¬ emitted (t + 1) ∨ emitted t ∨ emitOne t`. -/
def EmitStep (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitOne e c.F₃ ∧ c.F₁.t = c.F₃.t + 1 ∧ c.F₂.t = c.F₃.t ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

/-- `imp2 (emitted t) (emitted (t + 1))`. -/
def EmitMono (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₁.t < Sof e ∧ c.F₂.t = c.F₁.t + 1 ∧
    c.F₃.t = c.F₂.t ∧ c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

/-- `imp2 (emitOne t) (emitted (t + 1))`. -/
def EmitOne (c : Cand) : Prop :=
  IsEmitOne e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₂.t = c.F₁.t + 1 ∧ c.F₃.t = c.F₂.t ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

/-- `nand2 (emitOne t) (emitted t)`. -/
def EmitOnce (c : Cand) : Prop :=
  IsEmitOne e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₂.t = c.F₁.t ∧ c.F₃.t = c.F₂.t ∧
    c.s₁ = false ∧ c.s₂ = false ∧ c.s₃ = false

/-- `unit (emitBad t) false`. -/
def EmitBad (c : Cand) : Prop := UnitEmitBad e c ∧ SameSigns c ∧ c.s₁ = false

/-- The emission family. -/
def EmitPred (c : Cand) : Prop :=
  EmitZero e c ∨ EmitStep e c ∨ EmitMono e c ∨ EmitOne e c ∨ EmitOnce e c ∨ EmitBad e c

/-! ## The final family -/

/-- `unit (state S none) true`. -/
def FinalState (c : Cand) : Prop :=
  UnitState e c ∧ SameSigns c ∧ c.F₁.t = Sof e ∧ c.F₁.q = qCode none ∧ c.s₁ = true

/-- `unit (emitted S) true`. -/
def FinalEmitted (c : Cand) : Prop :=
  UnitEmitted e c ∧ SameSigns c ∧ c.F₁.t = Sof e ∧ c.s₁ = true

/-- The final family. -/
def FinalPred (c : Cand) : Prop := FinalState e c ∨ FinalEmitted e c

/-! ## The non-window families together -/

/-- The five explicit families. -/
def MainPred (c : Cand) : Prop :=
  StartPred e fixed c ∨ FreePred e fixed c ∨ BdryPred e c ∨ EmitPred e c ∨ FinalPred e c

end MIPRE.TM.CookLevin.Desc


