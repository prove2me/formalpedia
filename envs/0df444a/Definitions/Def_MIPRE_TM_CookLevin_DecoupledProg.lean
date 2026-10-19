-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
-- name    : MIPRE_TM_CookLevin_DecoupledProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:00:20.026963+00:00
-- url     : https://prove2.me/theorems/237b8094-6261-4aef-9ddd-ff3cb4b291a0
-- title:
--   Definitions of DecoupledProg: The decoupled describer as a program, and `ℓ₀` `ℓ₀ = ⌈log 2T⌉` is pinned by its specification, `2T ≤ 2^{ℓ₀} < 4T` for…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.DecoupledProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The decoupled describer as a program, and `ℓ₀`. `ℓ₀ = ⌈log 2T⌉` is pinned by its specification, `2T ≤ 2^{ℓ₀} < 4T` for `T ≥ 1`, so it cannot be replaced by the cheaper `Nat.size T + 1`, which is right except at powers of two, where it gives `4T` and violates the strict bound. Written with `Nat.size` it is one more than `⌈log T⌉` unless `T` is a power of two, and *that* shows on the bits of `T` as every bit but the top one being zero — which is a fold, so `ℓ₀` is a program (`planning/decoupled-5sat.md`, A1e).
--
--   **Definitions** (32): `MIPRE.SAT.decoupledDescriber` (**Explicit succinct decoupled descriptions of deciders** (blueprint `lem:decoupled-5sat`; the paper's `prop:explicit-succinct-deciders`):…); `MIPRE.TM.CookLevin.Desc.anyTrueP` (Whether a bit string has a set bit.); `MIPRE.TM.CookLevin.Desc.candR5` (`candOf5`.); `MIPRE.TM.CookLevin.Desc.dDR`; `MIPRE.TM.CookLevin.Desc.dEu` (`e`, in unary.); `MIPRE.TM.CookLevin.Desc.dLu` (`ℓ₀`, in unary.); `MIPRE.TM.CookLevin.Desc.dTR`; `MIPRE.TM.CookLevin.Desc.descFml5R` (`descFml5`.); `MIPRE.TM.CookLevin.Desc.describe5P` (**The decoupled describer, as a program** (item 4 of `lem:decoupled-5sat`).); `MIPRE.TM.CookLevin.Desc.dnR`; `MIPRE.TM.CookLevin.Desc.dropLastP` (Dropping the last entry of a list.); `MIPRE.TM.CookLevin.Desc.dsR`; `MIPRE.TM.CookLevin.Desc.dxR`; `MIPRE.TM.CookLevin.Desc.dyR`; `MIPRE.TM.CookLevin.Desc.gatePoly5` (The time bound of the decoupled describer at a linear majorant of its input size.); `MIPRE.TM.CookLevin.Desc.jR₁` (The two answer indices, zero-padded, and the three auxiliary indices.); `MIPRE.TM.CookLevin.Desc.jR₂`; `MIPRE.TM.CookLevin.Desc.jR₃`; `MIPRE.TM.CookLevin.Desc.jR₄`; `MIPRE.TM.CookLevin.Desc.jR₅`; `MIPRE.TM.CookLevin.Desc.lOf` (`⌈log 2T⌉`, read off the bits of `T`.); `MIPRE.TM.CookLevin.Desc.lOfN` (`ℓ₀`.); `MIPRE.TM.CookLevin.Desc.lOfU` (`ℓ₀`, in unary.); `MIPRE.TM.CookLevin.Desc.linkFmlR` (`linkFml`.); `MIPRE.TM.CookLevin.Desc.orBoolP`; `MIPRE.TM.CookLevin.Desc.padToP`; `MIPRE.TM.CookLevin.Desc.params5`; and -7 more.
--
--   **Embedded lemmas** (37): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `anyTrueP_apply`, `bitsVal_append_singleton`, `candR5_ev`, `dDR_apply`, `dTR_apply`, `descFml5R_apply`, `describe5P_apply`, `describe5P_size_le`, `dnR_apply`, `dropLastP_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.DecoupledProg` (`MIPRE/TM/CookLevin/DecoupledProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 71 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/DecoupledProg.lean; blueprint lem:decoupled-5sat

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/DecoupledProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
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
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
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
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Theorems.Thm_MIPRE_SAT_bitsVal_lt
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_T_add_three_lt
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_T_le_Sof
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_dblR_spec
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_descCirc5_inputs
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_descCirc5_wellFormed
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_describes5
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_esize_nat_le
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_fixedLen_of_valid
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_four_T_le_m
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_le_roundUp
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_litFieldsR_ev
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_mParam_eq
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_mParam_le
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_roundUpProg_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_roundUp_le
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_runBound_le_two_pow
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_size_le_esize
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_size_le_self
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_tabsR_apply

/-!
# The decoupled describer as a program, and `ℓ₀`

`ℓ₀ = ⌈log 2T⌉` is pinned by its specification, `2T ≤ 2^{ℓ₀} < 4T` for `T ≥ 1`, so it cannot
be replaced by the cheaper `Nat.size T + 1`, which is right except at powers of two, where it
gives `4T` and violates the strict bound. Written with `Nat.size` it is one more than
`⌈log T⌉` unless `T` is a power of two, and *that* shows on the bits of `T` as every bit but
the top one being zero — which is a fold, so `ℓ₀` is a program
(`planning/decoupled-5sat.md`, A1e).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## `ℓ₀`, the index length of the answer blocks -/

theorem bitsVal_append_singleton : ∀ (l : BitStr) (b : Bool),
    bitsVal (l ++ [b]) = bitsVal l + (if b then 2 ^ l.length else 0)
  | [], b => by cases b <;> simp [Nat.bit_val]
  | a :: l, b => by
    rw [List.cons_append, bitsVal_cons, bitsVal_append_singleton l b, bitsVal_cons,
      List.length_cons, Nat.bit_val, Nat.bit_val, pow_succ]
    cases b <;> cases a <;> simp <;> ring

/-- `⌈log 2T⌉`, read off the bits of `T`. -/
def lOf (T : ℕ) : ℕ :=
  if T.bits.dropLast.any id = false then Nat.size T else Nat.size T + 1

/-- **`ℓ₀` is the ceiling of the logarithm of `2T`.** -/
theorem lOf_spec (T : ℕ) (hT : 1 ≤ T) : 2 * T ≤ 2 ^ lOf T ∧ 2 ^ lOf T < 4 * T := by
  have hsz : 0 < Nat.size T := Nat.size_pos.2 hT
  have hk1 : Nat.size T = (Nat.size T - 1) + 1 := by omega
  have hlow : 2 ^ (Nat.size T - 1) ≤ T := Nat.lt_size.1 (by omega)
  have hhigh : T < 2 ^ ((Nat.size T - 1) + 1) := by rw [← hk1]; exact Nat.lt_size_self T
  have hlen : T.bits.length = (Nat.size T - 1) + 1 := by
    rw [Nat.size_eq_bits_len]; omega
  have hne : T.bits ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen
    omega
  have hdl : T.bits.dropLast.length = Nat.size T - 1 := by
    rw [List.length_dropLast, hlen]; omega
  have hdlt : bitsVal T.bits.dropLast < 2 ^ (Nat.size T - 1) := by
    rw [← hdl]; exact bitsVal_lt _
  have hval : T = bitsVal T.bits.dropLast +
      (if T.bits.getLast hne then 2 ^ (Nat.size T - 1) else 0) :=
    calc T = bitsVal T.bits := (bitsVal_bits T).symm
      _ = bitsVal (T.bits.dropLast ++ [T.bits.getLast hne]) := by
          rw [List.dropLast_append_getLast hne]
      _ = bitsVal T.bits.dropLast +
            (if T.bits.getLast hne then 2 ^ (Nat.size T - 1) else 0) := by
          rw [bitsVal_append_singleton, hdl]
  have hlast : T.bits.getLast hne = true := by
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [hc, if_neg (by simp)] at hval
    omega
  rw [hlast, if_pos rfl] at hval
  rw [lOf]
  by_cases hany : T.bits.dropLast.any id = false
  · have hz : bitsVal T.bits.dropLast = 0 := (bitsVal_eq_zero_iff _).mpr hany
    rw [if_pos hany, hk1, pow_succ]
    omega
  · have hz : bitsVal T.bits.dropLast ≠ 0 := fun h =>
      hany ((bitsVal_eq_zero_iff _).mp h)
    rw [if_neg hany, hk1, pow_succ, pow_succ]
    omega

/-! ## `ℓ₀` as a program -/

noncomputable def orBoolP : PolyTimeFun (Bool × Bool) Bool :=
  PolyTimeFun.ite fst (const true) snd

@[simp] theorem orBoolP_apply (p : Bool × Bool) : orBoolP p = (p.1 || p.2) := by
  cases hp : p.1 <;> simp [orBoolP, hp]

theorem foldl_or_eq_any : ∀ (l : BitStr) (s : Bool),
    l.foldl (fun x a => x || a) s = (s || l.any id)
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, foldl_or_eq_any l, List.any_cons]
    cases s <;> cases a <;> simp

/-- Whether a bit string has a set bit. -/
noncomputable def anyTrueP : PolyTimeFun BitStr Bool :=
  PolyTimeFun.congr ((foldlAdd orBoolP (Polynomial.C 3) (by
      intro s a
      cases s <;> cases a <;> simp)).comp ((PolyTimeFun.id _).pair (const false)))
    (fun l => l.any id) (by
      intro l
      simp only [comp_apply, foldlAdd_apply, pair_apply, PolyTimeFun.id_apply, const_apply,
        orBoolP_apply]
      rw [foldl_or_eq_any l false]
      simp)

@[simp] theorem anyTrueP_apply (l : BitStr) : anyTrueP l = l.any id := rfl

theorem length_tail_unary (n : ℕ) : ((unary n).tail).length = n - 1 := by
  rw [List.length_tail, length_unary]

/-- Dropping the last entry of a list. -/
noncomputable def dropLastP {α : Type*} [SizedEncoding α] : PolyTimeFun (List α) (List α) :=
  PolyTimeFun.congr (ap₂ take (PolyTimeFun.id _) (ap₁ tail length)) List.dropLast (by
    intro l
    simp only [ap₂_apply, take_apply, PolyTimeFun.id_apply, ap₁_apply, tail_apply, length_apply,
      length_tail_unary]
    rw [List.dropLast_eq_take])

@[simp] theorem dropLastP_apply {α : Type*} [SizedEncoding α] (l : List α) :
    dropLastP l = l.dropLast := rfl

/-- `ℓ₀`, in unary. -/
noncomputable def lOfU : PolyTimeFun ℕ Unary :=
  PolyTimeFun.ite (anyTrueP.comp (dropLastP.comp PolyTimeFun.natBits))
    (ap₂ addU sizeU (const (unary 1))) sizeU

@[simp] theorem length_lOfU (T : ℕ) : (lOfU T).length = lOf T := by
  rw [lOfU, PolyTimeFun.ite_apply, lOf]
  have hc : (anyTrueP.comp (dropLastP.comp PolyTimeFun.natBits)) T = T.bits.dropLast.any id :=
    rfl
  rw [hc]
  cases h : T.bits.dropLast.any id
  · simp
  · simp

/-- `ℓ₀`. -/
noncomputable def lOfN : PolyTimeFun ℕ ℕ := ap₁ unaryToBin lOfU

@[simp] theorem lOfN_apply (T : ℕ) : lOfN T = lOf T := by
  rw [lOfN, ap₁_apply, unaryToBin_apply, length_lOfU]

/-! ## Padding a field, as a program -/

noncomputable def padToP : PolyTimeFun (Unary × List Fml) (List Fml) :=
  PolyTimeFun.congr (ap₂ append snd (ap₂ replicate (ap₂ drop fst (ap₁ length snd))
      (const (Fml.const false))))
    (fun p => Fml.padTo p.1.length p.2) (by
      rintro ⟨u, fs⟩
      simp only [ap₂_apply, ap₁_apply, append_apply, replicate_apply, drop_apply, snd_apply,
        fst_apply, length_apply, length_unary, List.length_drop, Fml.padTo, const_apply])

@[simp] theorem padToP_apply (p : Unary × List Fml) : padToP p = Fml.padTo p.1.length p.2 := rfl

/-! ## The link formula as a program -/

section Prog5

variable {ι : Type*} [SizedEncoding ι] (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
  (lu : PolyTimeFun ι Unary)

/-- `2 ℓ`, in unary. -/
noncomputable def twoLU : PolyTimeFun ι Unary := ap₁ (nsmulU 2) lu

@[simp] theorem length_twoLU (i : ι) : (twoLU lu i).length = 2 * (lu i).length := by
  rw [twoLU, ap₁_apply, length_nsmulU]

/-- The offset of the five signs, in unary. -/
noncomputable def sgOffU : PolyTimeFun ι Unary :=
  ap₂ addU (twoLU lu) (ap₁ (nsmulU 3) (mU eu))

@[simp] theorem length_sgOffU (i : ι) :
    (sgOffU eu lu i).length = sgOff (lu i).length (mOf (eu i).length Gc) := by
  rw [sgOffU, ap₂_apply, length_addU, length_twoLU, ap₁_apply, length_nsmulU, length_mU, sgOff]

/-- The `k`-th of the five signs. -/
noncomputable def sgR (k : ℕ) : PolyTimeFun ι Fml :=
  ap₁ Fml.inpF (ap₁ unaryToBin (ap₂ addU (sgOffU eu lu) (const (unary k))))

@[simp] theorem sgR_apply (k : ℕ) (i : ι) :
    sgR eu lu k i = Fml.inp (sgOff (lu i).length (mOf (eu i).length Gc) + k) := by
  rw [sgR, ap₁_apply, Fml.inpF_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_sgOffU, const_apply, length_unary]

/-- The two answer indices, zero-padded, and the three auxiliary indices. -/
noncomputable def jR₁ : PolyTimeFun ι (List Fml) :=
  ap₂ padToP (mU eu) (ap₂ fieldP (const 0) lu)
noncomputable def jR₂ : PolyTimeFun ι (List Fml) :=
  ap₂ padToP (mU eu) (ap₂ fieldP (ap₁ unaryToBin lu) lu)
noncomputable def jR₃ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (twoLU lu)) (mU eu)
noncomputable def jR₄ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (ap₂ addU (twoLU lu) (mU eu))) (mU eu)
noncomputable def jR₅ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (ap₂ addU (twoLU lu) (ap₁ (nsmulU 2) (mU eu)))) (mU eu)

@[simp] theorem jR₁_apply (i : ι) :
    jR₁ eu lu i = j₁F (lu i).length (mOf (eu i).length Gc) := by
  rw [jR₁, ap₂_apply, padToP_apply, ap₂_apply, fieldP_apply, length_mU, const_apply, j₁F]

@[simp] theorem jR₂_apply (i : ι) :
    jR₂ eu lu i = j₂F (lu i).length (mOf (eu i).length Gc) := by
  rw [jR₂, ap₂_apply, padToP_apply, ap₂_apply, fieldP_apply, length_mU, ap₁_apply,
    unaryToBin_apply, j₂F]

@[simp] theorem jR₃_apply (i : ι) :
    jR₃ eu lu i = j₃F (lu i).length (mOf (eu i).length Gc) := by
  rw [jR₃, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, length_twoLU, length_mU, j₃F]

@[simp] theorem jR₄_apply (i : ι) :
    jR₄ eu lu i = j₄F (lu i).length (mOf (eu i).length Gc) := by
  rw [jR₄, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_twoLU, length_mU, j₄F]

@[simp] theorem jR₅_apply (i : ι) :
    jR₅ eu lu i = j₅F (lu i).length (mOf (eu i).length Gc) := by
  rw [jR₅, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_twoLU, ap₁_apply, length_nsmulU, length_mU, j₅F]

/-- `2T` on `r` bits. -/
noncomputable def twoTR : PolyTimeFun ι BitStr := nbitsR (mU eu) (dblR TR)

@[simp] theorem twoTR_apply (i : ι) :
    twoTR eu TR i = nbits (mOf (eu i).length Gc) (2 * TR i) := by
  rw [twoTR, nbitsR_apply _ (dblR_spec TR i), length_mU]

/-- `xor` of two readers. -/
noncomputable def xorR (f g : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₂ xorP f g

@[simp] theorem xorR_apply (f g : PolyTimeFun ι Fml) (i : ι) :
    xorR f g i = Fml.xor (f i) (g i) := rfl

/-- `linkFml`. -/
noncomputable def linkFmlR : PolyTimeFun ι Fml :=
  orR [
    andR [ltC (jR₁ eu lu) (twoTR eu TR), eqF (jR₁ eu lu) (jR₃ eu lu),
      xorR (sgR eu lu 0) (sgR eu lu 2)],
    andR [ltC (jR₂ eu lu) (twoTR eu TR), addRelR (jR₂ eu lu) (jR₃ eu lu) (twoTR eu TR),
      xorR (sgR eu lu 1) (sgR eu lu 2)],
    andR [notR (ltC (jR₁ eu lu) (twoTR eu TR)),
      notR (ap₁ (headD (Fml.const false)) (jR₁ eu lu)), sgR eu lu 0],
    andR [notR (ltC (jR₁ eu lu) (twoTR eu TR)),
      ap₁ (headD (Fml.const false)) (jR₁ eu lu), notR (sgR eu lu 0)],
    andR [notR (ltC (jR₂ eu lu) (twoTR eu TR)),
      notR (ap₁ (headD (Fml.const false)) (jR₂ eu lu)), sgR eu lu 1],
    andR [notR (ltC (jR₂ eu lu) (twoTR eu TR)),
      ap₁ (headD (Fml.const false)) (jR₂ eu lu), notR (sgR eu lu 1)],
    andR [eqF (jR₃ eu lu) (jR₄ eu lu), xorR (sgR eu lu 2) (sgR eu lu 3)],
    andR [eqF (jR₄ eu lu) (jR₅ eu lu), xorR (sgR eu lu 3) (sgR eu lu 4)]]

theorem linkFmlR_apply (i : ι) :
    linkFmlR eu TR lu i = linkFml (lu i).length (mOf (eu i).length Gc) (TR i) := by
  simp only [linkFmlR, linkFml, orR_apply, andR_apply, List.map_cons, List.map_nil, ltC_apply,
    eqF_apply, xorR_apply, notR_apply, ap₁_apply, headD_apply, addRelR_apply, jR₁_apply,
    jR₂_apply, jR₃_apply, jR₄_apply, jR₅_apply, twoTR_apply, sgR_apply, s₁F, s₂F, s₃F, s₄F,
    s₅F, Nat.add_zero]

/-! ## The candidate and the whole formula -/

/-- `candOf5`. -/
noncomputable def candR5 : CandR ι where
  A₁ := litFieldsR eu TR (twoLU lu)
  σ₁ := sgR eu lu 2
  A₂ := litFieldsR eu TR (ap₂ addU (twoLU lu) (mU eu))
  σ₂ := sgR eu lu 3
  A₃ := litFieldsR eu TR (ap₂ addU (twoLU lu) (ap₁ (nsmulU 2) (mU eu)))
  σ₃ := sgR eu lu 4

theorem candR5_ev (i : ι) :
    (candR5 eu TR lu).ev i = candOf5 (lu i).length (eu i).length (TR i) := by
  have h2 : sgR eu lu 2 i =
      Fml.inp (2 * (lu i).length + 3 * mOf (eu i).length Gc + 2) := by
    rw [sgR_apply]; unfold sgOff; rfl
  have h3 : sgR eu lu 3 i =
      Fml.inp (2 * (lu i).length + 3 * mOf (eu i).length Gc + 3) := by
    rw [sgR_apply]; unfold sgOff; rfl
  have h4 : sgR eu lu 4 i =
      Fml.inp (2 * (lu i).length + 3 * mOf (eu i).length Gc + 4) := by
    rw [sgR_apply]; unfold sgOff; rfl
  simp only [CandR.ev, candR5, candOf5, CandF.mk.injEq]
  refine ⟨?_, h2, ?_, h3, ?_, h4⟩
  · rw [litFieldsR_ev, length_twoLU]
  · rw [litFieldsR_ev, ap₂_apply, length_addU, length_twoLU, length_mU]
  · rw [litFieldsR_ev, ap₂_apply, length_addU, length_twoLU, ap₁_apply, length_nsmulU,
      length_mU]

/-- `descFml5`. -/
noncomputable def descFml5R (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ)
    (xR yR : PolyTimeFun ι BitStr) : PolyTimeFun ι Fml :=
  orTwo (tableauPlusR eu TR (candR5 eu TR lu) (tabsR eu TR (twoLU lu) DR nR xR yR)
    (const [5, 6])) (linkFmlR eu TR lu)

theorem descFml5R_apply (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ)
    (xR yR : PolyTimeFun ι BitStr) (i : ι) :
    descFml5R eu TR lu DR nR xR yR i =
      descFml5 (lu i).length (TR i) (eu i).length (DR i) (nR i) (xR i) (yR i) := by
  rw [descFml5R, orTwo_apply, tableauPlusR_apply, candR5_ev, tabsR_apply, length_twoLU,
    linkFmlR_apply, descFml5, descBody5, const_apply]

end Prog5

/-! ## The describer in the structure's argument order -/

noncomputable def dDR : PolyTimeFun DescInput Prog := ap₁ fst fst
noncomputable def dnR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd fst)
noncomputable def dTR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd (ap₁ snd fst))
noncomputable def dsR : PolyTimeFun DescInput ℕ := ap₁ snd (ap₁ snd (ap₁ snd (ap₁ snd fst)))
noncomputable def dxR : PolyTimeFun DescInput BitStr := ap₁ fst snd
noncomputable def dyR : PolyTimeFun DescInput BitStr := ap₁ snd snd

@[simp] theorem dDR_apply (p : DescInput) : dDR p = p.1.1 := rfl
@[simp] theorem dnR_apply (p : DescInput) : dnR p = p.1.2.1 := rfl
@[simp] theorem dTR_apply (p : DescInput) : dTR p = p.1.2.2.1 := rfl
@[simp] theorem dsR_apply (p : DescInput) : dsR p = p.1.2.2.2.2 := rfl
@[simp] theorem dxR_apply (p : DescInput) : dxR p = p.2.1 := rfl
@[simp] theorem dyR_apply (p : DescInput) : dyR p = p.2.2 := rfl

/-- `e`, in unary. -/
noncomputable def dEu : PolyTimeFun DescInput Unary := ap₁ eP (dTR.pair dsR)

/-- `ℓ₀`, in unary. -/
noncomputable def dLu : PolyTimeFun DescInput Unary := ap₁ lOfU dTR

@[simp] theorem length_dEu (p : DescInput) : (dEu p).length = eOf p.1.2.2.1 p.1.2.2.2.2 := by
  rw [dEu, ap₁_apply, length_eP, pair_apply, dTR_apply, dsR_apply]

@[simp] theorem length_dLu (p : DescInput) : (dLu p).length = lOf p.1.2.2.1 := by
  rw [dLu, ap₁_apply, length_lOfU, dTR_apply]

/-- **The decoupled describer, as a program** (item 4 of `lem:decoupled-5sat`). -/
noncomputable def describe5P : PolyTimeFun DescInput Circuit :=
  ap₂ Fml.toCircuitF
    (ap₁ unaryToBin (ap₂ addU (ap₂ addU (twoLU dLu) (ap₁ (nsmulU 3) (mU dEu)))
      (const (unary 5))))
    (descFml5R dEu dTR dLu dDR dnR dxR dyR)

theorem describe5P_apply (p : DescInput) :
    describe5P p = descCirc5 (lOf p.1.2.2.1) p.1.2.2.1 (eOf p.1.2.2.1 p.1.2.2.2.2) p.1.1 p.1.2.1
      p.2.1 p.2.2 := by
  rw [describe5P, ap₂_apply, Fml.toCircuitF_apply, descFml5R_apply, ap₁_apply, unaryToBin_apply,
    ap₂_apply, length_addU, ap₂_apply, length_addU, length_twoLU, ap₁_apply, length_nsmulU,
    length_mU, const_apply, length_unary, length_dEu, length_dLu, dTR_apply, dDR_apply,
    dnR_apply, dxR_apply, dyR_apply, descCirc5]

/-! ## The gate bound -/

theorem lOf_le_mOf (T σ : ℕ) : lOf T ≤ mOf (eOf T σ) Gc := by
  have h1 : lOf T ≤ Nat.size T + 1 := by rw [lOf]; split <;> omega
  have h2 := mParam_eq T σ
  show lOf T ≤ mParam T σ
  omega

theorem one_le_mOf (T σ : ℕ) : 1 ≤ mOf (eOf T σ) Gc := by
  have h2 := mParam_eq T σ
  show 1 ≤ mParam T σ
  omega

theorem esize_descInput_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    esize (((D, n, T, Q, σ), x, y) : DescInput) ≤ 25 * LOf n T Q σ + 12 := by
  have h : esize (((D, n, T, Q, σ), x, y) : DescInput) =
      esize D + esize n + esize T + esize Q + esize σ + esize x + esize y + 6 := by
    simp only [esize_prod]
    omega
  have hn := esize_nat_le n
  have hT := esize_nat_le T
  have hQ := esize_nat_le Q
  have hσ := esize_nat_le σ
  have hQ' := size_le_self Q
  have hσ' := size_le_self σ
  have hx := esize_bitStr_le x
  have hy := esize_bitStr_le y
  have h1 := hV.size_le
  have h2 := hV.x_le
  have h3 := hV.y_le
  unfold LOf
  omega

/-- The time bound of the decoupled describer at a linear majorant of its input size. -/
noncomputable def gatePoly5 : Polynomial ℕ :=
  describe5P.timeBound.comp (Polynomial.C 25 * Polynomial.X + Polynomial.C 12)

/-- **The decoupled describer is small** (item 3 of `lem:decoupled-5sat`). -/
theorem describe5P_size_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    (describe5P ((D, n, T, Q, σ), x, y)).size ≤ roundUp gatePoly5 n T Q σ := by
  have h1 : (describe5P ((D, n, T, Q, σ), x, y)).size ≤
      describe5P.timeBound.eval (esize (((D, n, T, Q, σ), x, y) : DescInput)) :=
    (size_le_esize _).trans (describe5P.esize_apply_le _)
  have h2 := polynomial_eval_mono describe5P.timeBound (esize_descInput_le D n T Q σ x y hV)
  have h3 : describe5P.timeBound.eval (25 * LOf n T Q σ + 12) =
      gatePoly5.eval (LOf n T Q σ) := by
    rw [gatePoly5, Polynomial.eval_comp]
    simp
  exact ((h1.trans h2).trans (le_of_eq h3)).trans (le_roundUp gatePoly5 n T Q σ)

/-! ## The parameters as programs -/

noncomputable def params5 : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) (ℕ × ℕ × ℕ) :=
  (lOfN.comp (ap₁ fst snd)).pair
    ((describeM.comp ((ap₁ fst snd).pair (ap₁ snd (ap₁ snd snd)))).pair (roundUpProg gatePoly5))

theorem params5_apply (n T Q σ : ℕ) :
    params5 (n, T, Q, σ) = (lOf T, mParam T σ, roundUp gatePoly5 n T Q σ) := by
  rw [params5, pair_apply, pair_apply, comp_apply, comp_apply, lOfN_apply, describeM_apply,
    roundUpProg_apply]
  rfl

end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT

open Cost TM.CookLevin.Desc

/-- **Explicit succinct decoupled descriptions of deciders** (blueprint `lem:decoupled-5sat`;
the paper's `prop:explicit-succinct-deciders`): the structure is inhabited. -/
noncomputable def decoupledDescriber : DecoupledDescriber where
  ℓ₀ := lOf
  r₀ := mParam
  s₀ := roundUp gatePoly5
  describe := describe5P
  params := params5
  params_eq n T Q σ := params5_apply n T Q σ
  ℓ₀_spec := lOf_spec
  r₀_le := ⟨431 + Qb + Gb Gc + 75, mParam_le⟩
  s₀_le := ⟨roundPoly gatePoly5, fun n T Q σ => roundUp_le gatePoly5 n T Q σ⟩
  inputs_eq D n T Q σ x y := by
    rw [describe5P_apply]
    exact descCirc5_inputs _ _ _ _ _ _ _
  wellFormed inp := by
    obtain ⟨⟨D, n, T, Q, σ⟩, x, y⟩ := inp
    rw [describe5P_apply]
    exact descCirc5_wellFormed _ _ _ _ _ _ _ (lOf_le_mOf T σ)
  size_le D n T Q σ x y hV := describe5P_size_le D n T Q σ x y hV
  describes 𝒟 n T Q σ x y hV := by
    rw [describe5P_apply]
    exact describes5 𝒟 (lOf T) T (eOf T σ) n x y
      (by rcases Nat.eq_zero_or_pos T with rfl | hT
          · simp [lOf]
          · exact (lOf_spec T hT).1)
      (lOf_le_mOf T σ) (one_le_mOf T σ) (four_T_le_m T σ) (T_le_Sof T σ)
      (fixedLen_of_valid 𝒟.prog n T Q σ x y hV) (T_add_three_lt T σ)
      (fun ap bp hap hbp => runBound_le_two_pow 𝒟.prog n T Q σ x y ap bp hV hap hbp)

end MIPRE.SAT


