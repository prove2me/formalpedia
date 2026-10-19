-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
-- name    : MIPRE_TM_CookLevin_LayoutProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:35.426817+00:00
-- url     : https://prove2.me/theorems/57973a9f-b96a-4dbe-93fa-913d86af29a7
-- title:
--   Definitions of LayoutProg: The layout arithmetic as programs The widths and offsets of the index layout (`Layout.lean`) as programs
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.LayoutProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The layout arithmetic as programs. The widths and offsets of the index layout (`Layout.lean`) as programs. Two conventions make them cheap: * **widths and offsets are unary.** `W e`, `mOf e G`, the field offsets: all are affine in `e` with small coefficients, so in unary they are `append` and iterated `append`, and no arithmetic program is needed. `e` itself must be unary in any case — the formulas are of size polynomial in `e`, so a binary `e` would make the output exponential in the input. * **a constant of a field is a resize of a bit string.** `resize w bs` keeps the low `w` bits of `bs`,…
--
--   **Definitions** (24): `MIPRE.TM.CookLevin.Desc.GbU`; `MIPRE.TM.CookLevin.Desc.QbU`; `MIPRE.TM.CookLevin.Desc.WU` (`W e`, in unary.); `MIPRE.TM.CookLevin.Desc.addU` (Unary addition.); `MIPRE.TM.CookLevin.Desc.bitsR` (The bits of a numeral, as a reader.); `MIPRE.TM.CookLevin.Desc.cstR` (The formulas of the constant `k` on `w` bits.); `MIPRE.TM.CookLevin.Desc.dOffU` (`dOff e`, in unary.); `MIPRE.TM.CookLevin.Desc.dblP` (Doubling a bit string: a `false` in front.); `MIPRE.TM.CookLevin.Desc.flagOffU` (`flagOff e Gc`, in unary.); `MIPRE.TM.CookLevin.Desc.fourU`; `MIPRE.TM.CookLevin.Desc.gOffU` (`gOff e`, in unary.); `MIPRE.TM.CookLevin.Desc.incN` (Adding a constant to a number.); `MIPRE.TM.CookLevin.Desc.jsOffU` (`jsOff e d`, in unary.); `MIPRE.TM.CookLevin.Desc.mU` (`mOf e Gc`, in unary.); `MIPRE.TM.CookLevin.Desc.muxListP` (`muxList`.); `MIPRE.TM.CookLevin.Desc.nbitsR` (The constant `k` on `w` bits, read off a width in unary and the bits of `k`.); `MIPRE.TM.CookLevin.Desc.nsmulU` (Unary multiplication by a constant.); `MIPRE.TM.CookLevin.Desc.pOffU` (`pOff e`, in unary.); `MIPRE.TM.CookLevin.Desc.pow2P` (`2 ^ e`, from `e` in unary: its bit string is `e` zeros and a one.); `MIPRE.TM.CookLevin.Desc.qOffU` (`qOff e`, in unary.); `MIPRE.TM.CookLevin.Desc.resize` (The low `w` bits of a bit string, padded with `false` to the width `w`.); `MIPRE.TM.CookLevin.Desc.resizeP` (`resize`, the width in unary.); and -20 more.
--
--   **Embedded lemmas** (22): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `addU_apply`, `bits_two_pow`, `dblP_apply`, `incN_apply`, `length_GbU`, `length_QbU`, `length_WU`, `length_addU`, `length_dOffU`, `length_flagOffU`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.LayoutProg` (`MIPRE/TM/CookLevin/LayoutProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 57 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/LayoutProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/LayoutProg.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The layout arithmetic as programs

The widths and offsets of the index layout (`Layout.lean`) as programs. Two conventions make
them cheap:

* **widths and offsets are unary.** `W e`, `mOf e G`, the field offsets: all are affine in
  `e` with small coefficients, so in unary they are `append` and iterated `append`, and no
  arithmetic program is needed. `e` itself must be unary in any case — the formulas are of
  size polynomial in `e`, so a binary `e` would make the output exponential in the input.
* **a constant of a field is a resize of a bit string.** `resize w bs` keeps the low `w` bits
  of `bs`, padding with `false`, and `resize_eq_nbits` identifies it with `nbits w k` for any
  `bs` whose bits are those of `k`. So `nbits w (2 * T)` is a resize of `false :: T.bits` and
  `nbits w (T + 3)` one of `incBits (incBits (incBits T.bits))`, with no multiplication or
  addition on numbers (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Unary arithmetic -/

/-- Unary addition. -/
noncomputable def addU : PolyTimeFun (Unary × Unary) Unary := append

@[simp] theorem addU_apply (p : Unary × Unary) : addU p = p.1 ++ p.2 := rfl

@[simp] theorem length_addU (p : Unary × Unary) : (addU p).length = p.1.length + p.2.length := by
  rw [addU_apply, List.length_append]

/-- Unary multiplication by a constant. -/
noncomputable def nsmulU : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | k + 1 => ap₂ addU (nsmulU k) (PolyTimeFun.id _)

@[simp] theorem length_nsmulU : ∀ (k : ℕ) (u : Unary), (nsmulU k u).length = k * u.length
  | 0, u => by rw [nsmulU, const_apply, List.length_nil, Nat.zero_mul]
  | k + 1, u => by
    rw [nsmulU, ap₂_apply, length_addU, length_nsmulU k u, PolyTimeFun.id_apply]
    ring

/-! ## Resizing a bit string -/

/-- The low `w` bits of a bit string, padded with `false` to the width `w`. -/
def resize (w : ℕ) (bs : BitStr) : BitStr := (bs ++ List.replicate w false).take w

/-! ### The bit strings of the numbers the describer needs -/

/-! ### Powers of two -/

theorem bits_two_pow : ∀ e : ℕ, (2 ^ e).bits = List.replicate e false ++ [true]
  | 0 => by rw [pow_zero, Nat.one_bits, List.replicate_zero, List.nil_append]
  | e + 1 => by
    rw [pow_succ, mul_comm, Nat.bit0_bits _ (Nat.two_pow_pos e).ne', bits_two_pow e,
      List.replicate_succ, List.cons_append]

/-! ## Resizing, as a program -/

/-- `resize`, the width in unary. -/
noncomputable def resizeP : PolyTimeFun (Unary × BitStr) BitStr :=
  congr (ap₂ take (ap₂ append snd (ap₂ replicate fst (const false))) fst)
    (fun p => resize p.1.length p.2) fun _ => rfl

@[simp] theorem resizeP_apply (p : Unary × BitStr) : resizeP p = resize p.1.length p.2 := rfl

/-- Doubling a bit string: a `false` in front. -/
noncomputable def dblP : PolyTimeFun BitStr BitStr := cons (const false) (PolyTimeFun.id _)

@[simp] theorem dblP_apply (bs : BitStr) : dblP bs = false :: bs := rfl

/-- `2 ^ e`, from `e` in unary: its bit string is `e` zeros and a one. -/
noncomputable def pow2P : PolyTimeFun Unary ℕ :=
  PolyTimeFun.cast (ap₂ append (ap₂ replicate (PolyTimeFun.id _) (const false)) (const [true]))
    (fun u => 2 ^ u.length) (by
      intro u
      show (encode (2 ^ u.length) : Data) = encode (List.replicate u.length false ++ [true])
      rw [show (encode (2 ^ u.length) : Data) = encode ((2 ^ u.length).bits) from rfl,
        bits_two_pow])

@[simp] theorem pow2P_apply (u : Unary) : pow2P u = 2 ^ u.length := rfl

/-- Adding a constant to a number. -/
noncomputable def incN : ℕ → PolyTimeFun ℕ ℕ
  | 0 => PolyTimeFun.id _
  | k + 1 => PolyTimeFun.inc.comp (incN k)

@[simp] theorem incN_apply : ∀ (k n : ℕ), incN k n = n + k
  | 0, n => rfl
  | k + 1, n => by rw [incN, comp_apply, PolyTimeFun.inc_apply, incN_apply k n, Nat.add_assoc]

/-! ## Readers of the layout -/

section Reader

variable {ι : Type*} [SizedEncoding ι]

/-- The constant `k` on `w` bits, read off a width in unary and the bits of `k`. -/
noncomputable def nbitsR (w : PolyTimeFun ι Unary) (bs : PolyTimeFun ι BitStr) :
    PolyTimeFun ι BitStr := ap₂ resizeP w bs

/-- The formulas of the constant `k` on `w` bits. -/
noncomputable def cstR (w : PolyTimeFun ι Unary) (bs : PolyTimeFun ι BitStr) :
    PolyTimeFun ι (List Fml) := ap₁ constBitsP (nbitsR w bs)

/-- The bits of a numeral, as a reader. -/
noncomputable def bitsR (k : ℕ) : PolyTimeFun ι BitStr := const k.bits

/-! ### The widths and offsets -/

variable (eu : PolyTimeFun ι Unary)

/-- `W e`, in unary. -/
noncomputable def WU : PolyTimeFun ι Unary := ap₂ addU eu (const (unary 4))

@[simp] theorem length_WU (i : ι) : (WU eu i).length = W (eu i).length := by
  rw [WU, ap₂_apply, length_addU, const_apply, length_unary, W]

/-- `3`, `4` and `Qb` and `Gb Gc`, in unary: the widths that do not depend on `e`. -/
noncomputable def threeU : PolyTimeFun ι Unary := const (unary 3)
noncomputable def fourU : PolyTimeFun ι Unary := const (unary 4)
noncomputable def QbU : PolyTimeFun ι Unary := const (unary Qb)
noncomputable def GbU : PolyTimeFun ι Unary := const (unary (Gb Gc))

@[simp] theorem length_threeU (i : ι) : (threeU i : Unary).length = 3 := length_unary 3
@[simp] theorem length_fourU (i : ι) : (fourU i : Unary).length = 4 := length_unary 4
@[simp] theorem length_QbU (i : ι) : (QbU i : Unary).length = Qb := length_unary Qb
@[simp] theorem length_GbU (i : ι) : (GbU i : Unary).length = Gb Gc := length_unary (Gb Gc)

/-- `mOf e Gc`, in unary. -/
noncomputable def mU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (const (unary 11)) (ap₁ (nsmulU 15) (WU eu))) QbU) GbU

@[simp] theorem length_mU (i : ι) : (mU eu i).length = mOf (eu i).length Gc := by
  rw [mU, ap₂_apply, length_addU, ap₂_apply, length_addU, ap₂_apply, length_addU, const_apply,
    length_unary, ap₁_apply, length_nsmulU, length_WU, length_QbU, length_GbU, mOf]

/-- `flagOff e Gc`, in unary. -/
noncomputable def flagOffU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (const (unary 10)) (ap₁ (nsmulU 15) (WU eu))) QbU) GbU

@[simp] theorem length_flagOffU (i : ι) : (flagOffU eu i).length = flagOff (eu i).length Gc := by
  rw [flagOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, ap₂_apply, length_addU,
    const_apply, length_unary, ap₁_apply, length_nsmulU, length_WU, length_QbU, length_GbU,
    flagOff]

/-- `gOff e`, in unary. -/
noncomputable def gOffU : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (const (unary 10)) (ap₁ (nsmulU 15) (WU eu))) QbU

@[simp] theorem length_gOffU (i : ι) : (gOffU eu i).length = gOff (eu i).length := by
  rw [gOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, const_apply, length_unary,
    ap₁_apply, length_nsmulU, length_WU, length_QbU, gOff]

/-- `dOff e`, in unary. -/
noncomputable def dOffU : PolyTimeFun ι Unary := ap₂ addU (const (unary 3)) (WU eu)

@[simp] theorem length_dOffU (i : ι) : (dOffU eu i).length = dOff (eu i).length := by
  rw [dOffU, ap₂_apply, length_addU, const_apply, length_unary, length_WU, dOff]

/-- `pOff e`, in unary. -/
noncomputable def pOffU : PolyTimeFun ι Unary := ap₂ addU (const (unary 7)) (WU eu)

@[simp] theorem length_pOffU (i : ι) : (pOffU eu i).length = pOff (eu i).length := by
  rw [pOffU, ap₂_apply, length_addU, const_apply, length_unary, length_WU, pOff]

/-- `vOff e`, in unary. -/
noncomputable def vOffU : PolyTimeFun ι Unary :=
  ap₂ addU (const (unary 7)) (ap₁ (nsmulU 2) (WU eu))

@[simp] theorem length_vOffU (i : ι) : (vOffU eu i).length = vOff (eu i).length := by
  rw [vOffU, ap₂_apply, length_addU, const_apply, length_unary, ap₁_apply, length_nsmulU,
    length_WU, vOff]

/-- `qOff e`, in unary. -/
noncomputable def qOffU : PolyTimeFun ι Unary :=
  ap₂ addU (const (unary 10)) (ap₁ (nsmulU 2) (WU eu))

@[simp] theorem length_qOffU (i : ι) : (qOffU eu i).length = qOff (eu i).length := by
  rw [qOffU, ap₂_apply, length_addU, const_apply, length_unary, ap₁_apply, length_nsmulU,
    length_WU, qOff]

/-- `jsOff e d`, in unary. -/
noncomputable def jsOffU (d : ℕ) : PolyTimeFun ι Unary :=
  ap₂ addU (ap₂ addU (qOffU eu) QbU) (ap₁ (nsmulU d) (WU eu))

@[simp] theorem length_jsOffU (d : ℕ) (i : ι) :
    (jsOffU eu d i).length = jsOff (eu i).length d := by
  rw [jsOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, length_qOffU, length_QbU,
    ap₁_apply, length_nsmulU, length_WU, jsOff, qOff]

end Reader

/-! ## `muxList`, as a program -/

/-- `muxList`. -/
noncomputable def muxListP : PolyTimeFun (Fml × List Fml × List Fml) (List Fml) :=
  congr ((mapWith (ap₃ muxP snd (ap₁ fst fst) (ap₁ snd fst))).comp
      ((ap₂ zip (ap₁ fst snd) (ap₁ snd snd)).pair fst))
    (fun p => muxList p.1 p.2.1 p.2.2) (by
      intro p
      show (p.2.1.zip p.2.2).map (fun a => Fml.mux p.1 a.1 a.2) = muxList p.1 p.2.1 p.2.2
      exact List.map_zip_eq_zipWith)

@[simp] theorem muxListP_apply (p : Fml × List Fml × List Fml) :
    muxListP p = muxList p.1 p.2.1 p.2.2 := rfl

end MIPRE.TM.CookLevin.Desc


