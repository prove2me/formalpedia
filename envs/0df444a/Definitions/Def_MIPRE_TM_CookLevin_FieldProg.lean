-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_FieldProg
-- name    : MIPRE_TM_CookLevin_FieldProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:46.176975+00:00
-- url     : https://prove2.me/theorems/8e5baf20-3262-4b0d-87d4-98b2616afeb7
-- title:
--   Definitions of FieldProg: The fields of a literal, as programs `FieldsR ι` is a record of *readers*: one program per field of `FieldsF`, all of…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.FieldProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The fields of a literal, as programs. `FieldsR ι` is a record of *readers*: one program per field of `FieldsF`, all of them reading the same input `ι`. `FieldsR.ev A i` is the field record its programs produce on the input `i`, and it is a structure literal whose components are, definitionally, the values of those programs — so every formula built from a `FieldsR` matches the same formula built from `FieldsR.ev` by `rfl`, and the whole family of programs of `FamilyProg.lean` costs one `rfl` each. `litFieldsR` is the record of programs for `litFields`: the one place where the constants of the…
--
--   **Definitions** (23): `MIPRE.TM.CookLevin.Desc.CandR` (A candidate of programs.); `MIPRE.TM.CookLevin.Desc.CandR.ev` (The candidate the programs produce on an input.); `MIPRE.TM.CookLevin.Desc.FieldsR` (A field record of programs, all reading the same input.); `MIPRE.TM.CookLevin.Desc.FieldsR.ev` (The field record the programs produce on an input.); `MIPRE.TM.CookLevin.Desc.ansOkR` (The `ansOk` field.); `MIPRE.TM.CookLevin.Desc.dR` (The `d` field.); `MIPRE.TM.CookLevin.Desc.dblR` (Twice a number, as a bit string.); `MIPRE.TM.CookLevin.Desc.flagR` (`flagF`.); `MIPRE.TM.CookLevin.Desc.gR` (The `g` field.); `MIPRE.TM.CookLevin.Desc.jR` (`jF`.); `MIPRE.TM.CookLevin.Desc.jsR` (The `js` fields.); `MIPRE.TM.CookLevin.Desc.litFieldsR` (The field programs of the literal with base `b`.); `MIPRE.TM.CookLevin.Desc.lt2TR` (`lt2TF`.); `MIPRE.TM.CookLevin.Desc.offR` (An index into a field, from an offset in unary.); `MIPRE.TM.CookLevin.Desc.pAnsR` (`pAnsF`.); `MIPRE.TM.CookLevin.Desc.pR` (The `p` field.); `MIPRE.TM.CookLevin.Desc.qR` (The `q` field.); `MIPRE.TM.CookLevin.Desc.quadR` (Four times a number, as a bit string.); `MIPRE.TM.CookLevin.Desc.rR` (`rF`.); `MIPRE.TM.CookLevin.Desc.tR` (The `t` field.); `MIPRE.TM.CookLevin.Desc.tagR` (The `tag` field.); `MIPRE.TM.CookLevin.Desc.twoTbR` (`twoTb`.); `MIPRE.TM.CookLevin.Desc.vR` (The `v` field.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `offR_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.FieldProg` (`MIPRE/TM/CookLevin/FieldProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 58 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FieldProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FieldProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
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
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg

/-!
# The fields of a literal, as programs

`FieldsR ι` is a record of *readers*: one program per field of `FieldsF`, all of them reading
the same input `ι`. `FieldsR.ev A i` is the field record its programs produce on the input
`i`, and it is a structure literal whose components are, definitionally, the values of those
programs — so every formula built from a `FieldsR` matches the same formula built from
`FieldsR.ev` by `rfl`, and the whole family of programs of `FamilyProg.lean` costs one `rfl`
each.

`litFieldsR` is the record of programs for `litFields`: the one place where the constants of
the layout have to be produced, and the only proof in the program layer that is not
definitional (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Records of readers -/

variable {ι : Type*} [SizedEncoding ι]

/-- A field record of programs, all reading the same input. -/
structure FieldsR (ι : Type*) [SizedEncoding ι] where
  flag : PolyTimeFun ι Fml
  tag : PolyTimeFun ι (List Fml)
  t : PolyTimeFun ι (List Fml)
  d : PolyTimeFun ι (List Fml)
  p : PolyTimeFun ι (List Fml)
  v : PolyTimeFun ι (List Fml)
  q : PolyTimeFun ι (List Fml)
  js : Fin 13 → PolyTimeFun ι (List Fml)
  g : PolyTimeFun ι (List Fml)
  ansOk : PolyTimeFun ι Fml

/-- The field record the programs produce on an input. -/
def FieldsR.ev (A : FieldsR ι) (i : ι) : FieldsF :=
  ⟨A.flag i, A.tag i, A.t i, A.d i, A.p i, A.v i, A.q i, fun k => A.js k i, A.g i, A.ansOk i⟩

/-- A candidate of programs. -/
structure CandR (ι : Type*) [SizedEncoding ι] where
  A₁ : FieldsR ι
  σ₁ : PolyTimeFun ι Fml
  A₂ : FieldsR ι
  σ₂ : PolyTimeFun ι Fml
  A₃ : FieldsR ι
  σ₃ : PolyTimeFun ι Fml

/-- The candidate the programs produce on an input. -/
def CandR.ev (C : CandR ι) (i : ι) : CandF :=
  ⟨C.A₁.ev i, C.σ₁ i, C.A₂.ev i, C.σ₂ i, C.A₃.ev i, C.σ₃ i⟩

/-! ## The constants of the layout -/

/-- Twice a number, as a bit string. -/
noncomputable def dblR (T : PolyTimeFun ι ℕ) : PolyTimeFun ι BitStr :=
  ap₁ dblP (ap₁ natBits T)

/-- Four times a number, as a bit string. -/
noncomputable def quadR (T : PolyTimeFun ι ℕ) : PolyTimeFun ι BitStr := ap₁ dblP (dblR T)

/-! ## The fields of a literal -/

section Lit

variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)

/-- An index into a field, from an offset in unary. -/
noncomputable def offR (o : PolyTimeFun ι Unary) : PolyTimeFun ι ℕ :=
  ap₁ unaryToBin (ap₂ addU b o)

@[simp] theorem offR_apply (o : PolyTimeFun ι Unary) (i : ι) :
    offR b o i = (b i).length + (o i).length := by
  rw [offR, ap₁_apply, ap₂_apply, unaryToBin_apply, length_addU]

/-- `flagF`. -/
noncomputable def flagR : PolyTimeFun ι Fml := ap₁ Fml.inpF (offR b (flagOffU eu))

/-- `jF`. -/
noncomputable def jR : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin b) (flagOffU eu)

/-- `twoTb`. -/
noncomputable def twoTbR : PolyTimeFun ι BitStr := nbitsR (flagOffU eu) (dblR TR)

/-- `lt2TF`. -/
noncomputable def lt2TR : PolyTimeFun ι Fml := ap₂ ltConstP (jR eu b) (twoTbR eu TR)

/-- `rF`. -/
noncomputable def rR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (lt2TR eu TR b) (jR eu b) (ap₂ subConstBitsP (jR eu b) (twoTbR eu TR))

/-- `pAnsF`. -/
noncomputable def pAnsR : PolyTimeFun ι (List Fml) :=
  ap₂ addConstBitsP (ap₂ take (ap₁ tail (rR eu TR b)) (WU eu)) (nbitsR (WU eu) (bitsR 3))

/-! ### The ten fields -/

/-- The `tag` field. -/
noncomputable def tagR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (ap₁ unaryToBin b) threeU) (cstR threeU (bitsR 0))

/-- The `t` field. -/
noncomputable def tR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b threeU) (WU eu)) (cstR (WU eu) (bitsR 0))

/-- The `d` field. -/
noncomputable def dR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (dOffU eu)) fourU)
    (ap₃ muxListP (lt2TR eu TR b) (cstR fourU (bitsR 5)) (cstR fourU (bitsR 6)))

/-- The `p` field. -/
noncomputable def pR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (pOffU eu)) (WU eu)) (pAnsR eu TR b)

/-- The `v` field. -/
noncomputable def vR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (vOffU eu)) threeU)
    (ap₃ muxListP (ap₁ (headD (Fml.const false)) (rR eu TR b)) (cstR threeU (bitsR 1))
      (cstR threeU (bitsR 5)))

/-- The `q` field. -/
noncomputable def qR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (qOffU eu)) QbU) (cstR QbU (bitsR 0))

/-- The `js` fields. -/
noncomputable def jsR (k : ℕ) : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (jsOffU eu k)) (WU eu)) (cstR (WU eu) (bitsR 0))

/-- The `g` field. -/
noncomputable def gR : PolyTimeFun ι (List Fml) :=
  ap₃ muxListP (flagR eu b) (ap₂ fieldP (offR b (gOffU eu)) GbU) (cstR GbU (bitsR 0))

/-- The `ansOk` field. -/
noncomputable def ansOkR : PolyTimeFun ι Fml :=
  ap₂ Fml.andF (ap₁ Fml.notF (flagR eu b))
    (ap₂ ltConstP (jR eu b) (nbitsR (flagOffU eu) (quadR TR)))

/-- The field programs of the literal with base `b`. -/
noncomputable def litFieldsR : FieldsR ι where
  flag := flagR eu b
  tag := tagR eu b
  t := tR eu b
  d := dR eu TR b
  p := pR eu TR b
  v := vR eu TR b
  q := qR eu b
  js := fun k => jsR eu b k
  g := gR eu b
  ansOk := ansOkR eu TR b

end Lit

end MIPRE.TM.CookLevin.Desc


