-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_FieldFml
-- name    : MIPRE_TM_CookLevin_FieldFml
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:17.951525+00:00
-- url     : https://prove2.me/theorems/378ea011-a50d-4d93-bb24-47414c196fb8
-- title:
--   Definitions of FieldFml: The fields of a literal, as formulas For a literal whose `m` index bits are the input bits `b
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.FieldFml` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The fields of a literal, as formulas. For a literal whose `m` index bits are the input bits `b .. b + m`, the formulas computing its fields (`litFields`): the flag, the structured fields as slices of the input, and the answer decoding (`j < 2T`, `r = j` or `j - 2T`, `p = r / 2 + 3`, `v` from the parity of `r`), multiplexed by the flag. `evalFields_litFields` says that they compute exactly `fieldsOf` on the index (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (12): `MIPRE.TM.CookLevin.Desc.FieldsF` (The fields of a literal as formulas.); `MIPRE.TM.CookLevin.Desc.cst` (The constant `c` on `w` bits.); `MIPRE.TM.CookLevin.Desc.evalFields` (The values of the field formulas.); `MIPRE.TM.CookLevin.Desc.flagF` (The flag bit.); `MIPRE.TM.CookLevin.Desc.ibOf` (The input bits `b ..); `MIPRE.TM.CookLevin.Desc.jF` (The low `m - 1` bits, the value `j` of an answer index.); `MIPRE.TM.CookLevin.Desc.litFields` (The field formulas of the literal with base `b`.); `MIPRE.TM.CookLevin.Desc.lt2TF` (`j < 2T`.); `MIPRE.TM.CookLevin.Desc.muxList` (`if s then as else bs`, bitwise.); `MIPRE.TM.CookLevin.Desc.pAnsF` (`p = r / 2 + 3`, on `W` bits.); `MIPRE.TM.CookLevin.Desc.rF` (`r = j` or `j - 2T`.); `MIPRE.TM.CookLevin.Desc.twoTb` (`2T` on `m - 1` bits.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_cst`, `length_ibOf`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.FieldFml` (`MIPRE/TM/CookLevin/FieldFml.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FieldFml.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FieldFml.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The fields of a literal, as formulas

For a literal whose `m` index bits are the input bits `b .. b + m`, the formulas computing
its fields (`litFields`): the flag, the structured fields as slices of the input, and the
answer decoding (`j < 2T`, `r = j` or `j - 2T`, `p = r / 2 + 3`, `v` from the parity of
`r`), multiplexed by the flag. `evalFields_litFields` says that they compute exactly
`fieldsOf` on the index (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open SAT Cost Fml

/-! ## Input slices -/

/-- The input bits `b .. b + m` as a bit string. -/
def ibOf (b m : ℕ) (x : ℕ → Bool) : BitStr := (List.range' b m).map x

@[simp] theorem length_ibOf (b m : ℕ) (x : ℕ → Bool) : (ibOf b m x).length = m := by simp [ibOf]

/-! ## Multiplexed fields and constants -/

/-- `if s then as else bs`, bitwise. -/
def muxList (s : Fml) (as bs : List Fml) : List Fml := List.zipWith (mux s) as bs

/-- The constant `c` on `w` bits. -/
def cst (w c : ℕ) : List Fml := constBits (nbits w c)

@[simp] theorem length_cst (w c : ℕ) : (cst w c).length = w := by simp [cst]

/-! ## The fields of a literal -/

/-- The fields of a literal as formulas. -/
structure FieldsF where
  flag : Fml
  tag : List Fml
  t : List Fml
  d : List Fml
  p : List Fml
  v : List Fml
  q : List Fml
  js : Fin 13 → List Fml
  g : List Fml
  ansOk : Fml

/-- The values of the field formulas. -/
def evalFields (F : FieldsF) (x : ℕ → Bool) : Fields :=
  { flag := F.flag.eval x, tag := val F.tag x, t := val F.t x, d := val F.d x, p := val F.p x,
    v := val F.v x, q := val F.q x, js := fun k => val (F.js k) x, g := val F.g x,
    ansOk := F.ansOk.eval x }

section Lit

variable (e G T b : ℕ)

/-- The flag bit. -/
def flagF : Fml := inp (b + flagOff e G)

/-- The low `m - 1` bits, the value `j` of an answer index. -/
def jF : List Fml := field b (flagOff e G)

/-- `2T` on `m - 1` bits. -/
def twoTb : BitStr := nbits (flagOff e G) (2 * T)

/-- `j < 2T`. -/
def lt2TF : Fml := ltConst (jF e G b) (twoTb e G T)

/-- `r = j` or `j - 2T`. -/
def rF : List Fml := muxList (lt2TF e G T b) (jF e G b) (subConstBits (jF e G b) (twoTb e G T))

/-- `p = r / 2 + 3`, on `W` bits. -/
def pAnsF : List Fml := addConstBits ((rF e G T b).tail.take (W e)) (nbits (W e) 3)

/-- The field formulas of the literal with base `b`. -/
def litFields : FieldsF where
  flag := flagF e G b
  tag := muxList (flagF e G b) (field (b + tagOff) 3) (cst 3 0)
  t := muxList (flagF e G b) (field (b + tOff) (W e)) (cst (W e) 0)
  d := muxList (flagF e G b) (field (b + dOff e) 4) (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6))
  p := muxList (flagF e G b) (field (b + pOff e) (W e)) (pAnsF e G T b)
  v := muxList (flagF e G b) (field (b + vOff e) 3)
    (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5))
  q := muxList (flagF e G b) (field (b + qOff e) Qb) (cst Qb 0)
  js := fun k => muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)
  g := muxList (flagF e G b) (field (b + gOff e) (Gb G)) (cst (Gb G) 0)
  ansOk := and (not (flagF e G b)) (ltConst (jF e G b) (nbits (flagOff e G) (4 * T)))

/-! ### Lengths -/

/-! ### Values -/

variable (x : ℕ → Bool)

end Lit

end MIPRE.TM.CookLevin.Desc


