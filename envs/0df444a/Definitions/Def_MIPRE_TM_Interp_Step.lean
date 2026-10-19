-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Step
-- name    : MIPRE_TM_Interp_Step
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:05:40.235675+00:00
-- url     : https://prove2.me/theorems/1583dfef-8fc7-491f-9bbe-d422ff654559
-- title:
--   Definitions of Step: One step of the evaluation machine The representation of a configuration of the CEK machine on the tapes (`RepOf`), the…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   **Definitions** (13): `MIPRE.TM.Interp.AcceptsFrom` (`U` accepts from `c` within `n` silent steps followed by the output `1`.); `MIPRE.TM.Interp.CDesc` (The control and the tape `C` alone (the stack head may sit before the tape).); `MIPRE.TM.Interp.PreTo` (`c` reaches, within `B` silent steps, the control `q` with tapes representing `m'` (budget `r'`, heads of `C` and `K` at `pC`, `pK`), its…); `MIPRE.TM.Interp.PreTo1` (`PreTo` with at least one step.); `MIPRE.TM.Interp.RepOf` (The descriptions representing the machine configuration `m` with budget `r`: the control followed by garbage `g` (its head at `pC`), the…); `MIPRE.TM.Interp.RunTo` (`StepTo` with at least one step.); `MIPRE.TM.Interp.StepTo` (`c` reaches, within `B` silent steps, the dispatcher representing `m'` with budget `r'`, its scratch tape of length at most `xl`.); `MIPRE.TM.Interp.caseBound` (The bound on the steps of a case program.); `MIPRE.TM.Interp.evHead`; `MIPRE.TM.Interp.evTarget` (The case program of a control to evaluate, and the position of the final `0` of its tag.); `MIPRE.TM.Interp.retTarget` (The case program of a return to a frame.); `MIPRE.TM.Interp.stepBound` (The bound on the steps of `U` simulating one step of the machine from a representation with a scratch tape of length `xl`.); `MIPRE.TM.Interp.sz` (The size of the representation of `m`.).
--
--   **Embedded lemmas** (31): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `BUD_ne_C`, `BUD_ne_CNT`, `BUD_ne_E`, `BUD_ne_K`, `BUD_ne_X`, `CNT_ne_BUD`, `CNT_ne_C`, `CNT_ne_E`, `CNT_ne_K`, `CNT_ne_X`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Step` (`MIPRE/TM/Interp/Step.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc

/-!
# One step of the evaluation machine

The representation of a configuration of the CEK machine on the tapes (`RepOf`), the
dispatcher, and, for each case of `Machine.step`, the run of the case program from the
representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting
silently when the budget is short.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine

variable {input : Fin 7 → List Sym}

instance : NeZero maxPc := ⟨by decide⟩

/-! ## The tape names are distinct -/

@[simp] theorem C_ne_E : C ≠ E := by decide
@[simp] theorem C_ne_K : C ≠ K := by decide
@[simp] theorem C_ne_X : C ≠ X := by decide
@[simp] theorem C_ne_CNT : C ≠ CNT := by decide
@[simp] theorem C_ne_BUD : C ≠ BUD := by decide
@[simp] theorem E_ne_C : E ≠ C := by decide
@[simp] theorem E_ne_K : E ≠ K := by decide
@[simp] theorem E_ne_X : E ≠ X := by decide
@[simp] theorem E_ne_CNT : E ≠ CNT := by decide
@[simp] theorem E_ne_BUD : E ≠ BUD := by decide
@[simp] theorem K_ne_C : K ≠ C := by decide
@[simp] theorem K_ne_E : K ≠ E := by decide
@[simp] theorem K_ne_X : K ≠ X := by decide
@[simp] theorem K_ne_CNT : K ≠ CNT := by decide
@[simp] theorem K_ne_BUD : K ≠ BUD := by decide
@[simp] theorem X_ne_C : X ≠ C := by decide
@[simp] theorem X_ne_E : X ≠ E := by decide
@[simp] theorem X_ne_K : X ≠ K := by decide
@[simp] theorem X_ne_CNT : X ≠ CNT := by decide
@[simp] theorem X_ne_BUD : X ≠ BUD := by decide
@[simp] theorem CNT_ne_C : CNT ≠ C := by decide
@[simp] theorem CNT_ne_E : CNT ≠ E := by decide
@[simp] theorem CNT_ne_K : CNT ≠ K := by decide
@[simp] theorem CNT_ne_X : CNT ≠ X := by decide
@[simp] theorem CNT_ne_BUD : CNT ≠ BUD := by decide
@[simp] theorem BUD_ne_C : BUD ≠ C := by decide
@[simp] theorem BUD_ne_E : BUD ≠ E := by decide
@[simp] theorem BUD_ne_K : BUD ≠ K := by decide
@[simp] theorem BUD_ne_X : BUD ≠ X := by decide
@[simp] theorem BUD_ne_CNT : BUD ≠ CNT := by decide

/-! ## The representation -/

/-- The descriptions representing the machine configuration `m` with budget `r`: the
control followed by garbage `g` (its head at `pC`), the environment and the stack exactly
(the stack head at `pK`), a scratch tape with its head inside its content, an empty
counter, a unary budget. -/
structure RepOf (ds : WT → TapeSt) (m : Machine.Cfg) (r pC pK : ℕ) : Prop where
  ctrl : ∃ g, ds C = ⟨ctrlRepr m.ctrl ++ g, pC⟩
  env : ds E = ⟨envRepr m.env, (envRepr m.env).length⟩
  kont : ds K = ⟨kontRepr m.kont, pK⟩
  scratch : (ds X).p ≤ (ds X).l.length
  cnt : ds CNT = ⟨[], 0⟩
  bud : ds BUD = ⟨List.replicate r .one, r⟩

/-- The size of the representation of `m`. -/
def sz (m : Machine.Cfg) : ℕ :=
  (ctrlRepr m.ctrl).length + (envRepr m.env).length + (kontRepr m.kont).length + 1

/-- `c` reaches, within `B` silent steps, the control `q` with tapes representing `m'`
(budget `r'`, heads of `C` and `K` at `pC`, `pK`), its scratch tape of length at most `xl`. -/
abbrev PreTo (c : Cfg input) (B : ℕ) (q : Option Ctl) (m' : Machine.Cfg) (r' pC pK xl : ℕ) : Prop :=
  ∃ n ≤ B, ∃ c' ds', Reach c n c' [] ∧ Desc c' q ds' ∧ RepOf ds' m' r' pC pK ∧
    (ds' X).l.length ≤ xl

/-- `c` reaches, within `B` silent steps, the dispatcher representing `m'` with budget `r'`,
its scratch tape of length at most `xl`. -/
abbrev StepTo (c : Cfg input) (B : ℕ) (m' : Machine.Cfg) (r' xl : ℕ) : Prop :=
  PreTo c B (at_ .dispatch 0) m' r' (ctrlRepr m'.ctrl).length (kontRepr m'.kont).length xl

/-- `PreTo` with at least one step. -/
def PreTo1 (c : Cfg input) (B : ℕ) (q : Option Ctl) (m' : Machine.Cfg) (r' pC pK xl : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ B ∧ ∃ c' ds', Reach c n c' [] ∧ Desc c' q ds' ∧ RepOf ds' m' r' pC pK ∧
    (ds' X).l.length ≤ xl

/-- `StepTo` with at least one step. -/
abbrev RunTo (c : Cfg input) (B : ℕ) (m' : Machine.Cfg) (r' xl : ℕ) : Prop :=
  PreTo1 c B (at_ .dispatch 0) m' r' (ctrlRepr m'.ctrl).length (kontRepr m'.kont).length xl

/-! ## The control words -/

/-! ## List facts -/

/-! ## The dispatcher on `ev` -/

/-- The case program of a control to evaluate, and the position of the final `0` of its tag. -/
def evTarget : Prog → ProgId
  | .var _ => .evVar
  | .nil => .evNil
  | .cons _ _ => .evCons
  | .elim _ _ _ => .evElim
  | .let_ _ _ => .evLet
  | .loop _ => .evLoop
  | .const _ => .evConst

def evHead : Prog → ℕ
  | .var _ => 2
  | .nil => 4
  | .cons _ _ => 6
  | .elim _ _ _ => 8
  | .let_ _ _ => 10
  | .loop _ => 12
  | .const _ => 14

/-! ## The cases: `ev` -/

/-- The bound on the steps of a case program. -/
def caseBound (m : Machine.Cfg) (xl : ℕ) : ℕ := 100 * (sz m + xl + 1)

/-! ## Finishing a case: the charge and the jump -/

/-! ## `ev elim` -/

/-! ## `ev let` and `ev loop` -/

/-! ## The dispatcher on `ret` -/

/-- The case program of a return to a frame. -/
def retTarget : Frame → ProgId
  | .cons1 _ _ => .retCons1
  | .cons2 _ => .retCons2
  | .let1 _ _ => .retLet1
  | .loop1 _ _ => .retLoop1

/-! ## Popping the innermost environment entry -/

/-! ## The cases: `ret` -/

/-! ## `ret` to a `loop1` frame -/

/-! ## The final check -/

/-- The control and the tape `C` alone (the stack head may sit before the tape). -/
def CDesc (c : Cfg input) (q : Option Ctl) (s : TapeSt) : Prop :=
  c.state = q ∧ TapeIs (c.workTapes C) (c.workTapePos C) s

/-- `U` accepts from `c` within `n` silent steps followed by the output `1`. -/
def AcceptsFrom (c : Cfg input) (n : ℕ) : Prop := ∃ c', Reach c n c' [.one] ∧ c'.state = none

/-! ## The step -/

/-- The bound on the steps of `U` simulating one step of the machine from a representation with
a scratch tape of length `xl`. -/
def stepBound (m : Machine.Cfg) (xl : ℕ) : ℕ := caseBound m xl + sz m + 30

end MIPRE.TM.Interp


