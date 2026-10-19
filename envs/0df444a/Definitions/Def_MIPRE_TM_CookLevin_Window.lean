-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Window
-- name    : MIPRE_TM_CookLevin_Window
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:04:03.437552+00:00
-- url     : https://prove2.me/theorems/e7e71d16-1239-4684-9c24-845d8b6514af
-- title:
--   Definitions of Window: The window family, on decoded fields The window clauses of the tableau are the Tseitin clauses of the check circuit…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Window` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The window family, on decoded fields. The window clauses of the tableau are the Tseitin clauses of the check circuit `chk` at every step `t` and window `js` (`windowClauses`). Every such clause has a gate literal (`aux t js g`) in its third position: the *templates* of a gate (`gateTemplates`) list its clauses as triples of literal *specs* — a gate index (`.aux u`) or a window input (`.win n`) — with their signs, and the clause is recovered from the templates by instantiating the specs at `(t, js)` (`gateClauses_eq_templates`). A candidate matches a template when its third record is a gate…
--
--   **Definitions** (11): `MIPRE.TM.CookLevin.Desc.LitSpec` (A literal of a Tseitin clause, before instantiation: a gate variable or a window input.); `MIPRE.TM.CookLevin.Desc.SpecMatch` (The record `F` denotes the variable of the spec, relative to the gate record `Fa`.); `MIPRE.TM.CookLevin.Desc.Tpl` (A clause template: three specs with their signs.); `MIPRE.TM.CookLevin.Desc.Tpl.clause` (The clause of a template at step `t` and window `js`.); `MIPRE.TM.CookLevin.Desc.TplMatch` (The candidate matches the template, its third record being the gate literal.); `MIPRE.TM.CookLevin.Desc.WinMatch` (The record `F` denotes the window variable `wv` of the window of the record `Fa` (a gate variable: its time and centers are `Fa.t`,…); `MIPRE.TM.CookLevin.Desc.WindowGates` (The candidate matches a template of some gate of `chk`.); `MIPRE.TM.CookLevin.Desc.WindowOut` (The candidate is the output unit clause of a window.); `MIPRE.TM.CookLevin.Desc.WindowPred` (The window family.); `MIPRE.TM.CookLevin.Desc.gateTemplates` (The Tseitin clauses of gate `g`, as templates (`gateClauses`, `Tseitin.lean`).); `MIPRE.TM.CookLevin.Desc.specVar` (The tableau variable of a spec at step `t` and window `js`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Window` (`MIPRE/TM/CookLevin/Window.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Window.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Window.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_TM_CookLevin_Families

/-!
# The window family, on decoded fields

The window clauses of the tableau are the Tseitin clauses of the check circuit `chk` at
every step `t` and window `js` (`windowClauses`). Every such clause has a gate literal
(`aux t js g`) in its third position: the *templates* of a gate (`gateTemplates`) list its
clauses as triples of literal *specs* — a gate index (`.aux u`) or a window input (`.win n`)
— with their signs, and the clause is recovered from the templates by instantiating the
specs at `(t, js)` (`gateClauses_eq_templates`). A candidate matches a template when its
third record is a gate variable of the template's gate and the other two records denote the
spec's variable relative to it (`SpecMatch`: the time and centers are read off the third
record). `windowPred_iff`: the candidate decodes to a window clause iff it matches a
template of a gate, or is the output unit clause (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Templates -/

/-- A literal of a Tseitin clause, before instantiation: a gate variable or a window input. -/
inductive LitSpec where
  | aux (u : ℕ)
  | win (n : ℕ)
  deriving DecidableEq

/-- A clause template: three specs with their signs. -/
abbrev Tpl := (LitSpec × Bool) × (LitSpec × Bool) × (LitSpec × Bool)

/-- The Tseitin clauses of gate `g`, as templates (`gateClauses`, `Tseitin.lean`). -/
def gateTemplates (g : ℕ) : Gate → List Tpl
  | .input i => [((.win i, false), (.aux g, true), (.aux g, true)),
      ((.win i, true), (.aux g, false), (.aux g, false))]
  | .const b => [((.aux g, b), (.aux g, b), (.aux g, b))]
  | .and u v => [((.aux u, false), (.aux v, false), (.aux g, true)),
      ((.aux u, true), (.aux v, true), (.aux g, false)),
      ((.aux u, true), (.aux v, false), (.aux g, false)),
      ((.aux u, false), (.aux v, true), (.aux g, false))]
  | .or u v => [((.aux u, true), (.aux v, true), (.aux g, false)),
      ((.aux u, false), (.aux v, false), (.aux g, true)),
      ((.aux u, false), (.aux v, true), (.aux g, true)),
      ((.aux u, true), (.aux v, false), (.aux g, true))]
  | .not u => [((.aux u, true), (.aux g, true), (.aux g, true)),
      ((.aux u, false), (.aux g, false), (.aux g, false))]

section Instantiate

variable {S G : ℕ}

/-- The tableau variable of a spec at step `t` and window `js`. -/
noncomputable def specVar (t : Fin S) (js : Tape 7 6 → Center S) : LitSpec → TabVar 7 6 Sym Ctl S G
  | .aux u => auxOf t js u
  | .win n => inpOf t js n

/-- The clause of a template at step `t` and window `js`. -/
noncomputable def Tpl.clause (t : Fin S) (js : Tape 7 6 → Center S) (tp : Tpl) :
    Clause3 (TabVar 7 6 Sym Ctl S G) :=
  cl ⟨specVar t js tp.1.1, tp.1.2⟩ ⟨specVar t js tp.2.1.1, tp.2.1.2⟩ ⟨specVar t js tp.2.2.1, tp.2.2.2⟩

end Instantiate

/-! ## Matching a spec against the gate literal -/

variable (e G : ℕ)

/-- The record `F` denotes the window variable `wv` of the window of the record `Fa` (a gate
variable: its time and centers are `Fa.t`, `Fa.js`). -/
def WinMatch (Fa : Fields) : WinVar 7 6 Sym Ctl → Fields → Prop
  | .cellPre d δ v, F => IsCell e F ∧ F.t = Fa.t ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + δ ∧ F.v = symCode v
  | .headPre d δ, F => IsHead e F ∧ F.t = Fa.t ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + δ
  | .cellPost d v, F => IsCell e F ∧ F.t = Fa.t + 1 ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + 2 ∧ F.v = symCode v
  | .headPost d, F => IsHead e F ∧ F.t = Fa.t + 1 ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + 2
  | .statePre q, F => IsState e F ∧ F.t = Fa.t ∧ F.q = qCode q
  | .statePost q, F => IsState e F ∧ F.t = Fa.t + 1 ∧ F.q = qCode q
  | .emitOne, F => IsEmitOne e F ∧ F.t = Fa.t
  | .emitBad, F => IsEmitBad e F ∧ F.t = Fa.t

/-- The record `F` denotes the variable of the spec, relative to the gate record `Fa`. -/
def SpecMatch (Fa : Fields) : LitSpec → Fields → Prop
  | .aux u, F => IsAux e G F ∧ F.t = Fa.t ∧ (∀ k, F.js k = Fa.js k) ∧ F.g = u
  | .win n, F => ∃ h : n < winCard 7 6 Sym Ctl, WinMatch e Fa ((Fintype.equivFin _).symm ⟨n, h⟩) F

section Match

variable {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
  (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
include ht hjs

end Match

/-! ## The window predicate -/

/-- The candidate matches the template, its third record being the gate literal. -/
def TplMatch (tp : Tpl) (c : Cand) : Prop :=
  SpecMatch e G c.F₃ tp.1.1 c.F₁ ∧ c.s₁ = tp.1.2 ∧ SpecMatch e G c.F₃ tp.2.1.1 c.F₂ ∧ c.s₂ = tp.2.1.2 ∧
    SpecMatch e G c.F₃ tp.2.2.1 c.F₃ ∧ c.s₃ = tp.2.2.2

/-- The candidate matches a template of some gate of `chk`. -/
def WindowGates (chk : Circuit) (c : Cand) : Prop :=
  ∃ g : Fin chk.gates.length, ∃ tp ∈ gateTemplates g chk.gates[g], TplMatch e G tp c

/-- The candidate is the output unit clause of a window. -/
def WindowOut (c : Cand) : Prop := UnitAux e G c ∧ SameSigns c ∧ c.F₁.g = G - 1 ∧ c.s₁ = true

/-- The window family. -/
def WindowPred (chk : Circuit) (c : Cand) : Prop := WindowGates e G chk c ∨ WindowOut e G c

section Iff

variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])

end Iff

/-! ## The whole tableau -/

end MIPRE.TM.CookLevin.Desc


