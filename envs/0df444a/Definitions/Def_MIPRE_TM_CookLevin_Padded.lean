-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Padded
-- name    : MIPRE_TM_CookLevin_Padded
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:02:18.447594+00:00
-- url     : https://prove2.me/theorems/16a32522-bb33-47f9-9ab3-2f7035b0ceab
-- title:
--   Definitions of Padded: The padded five-block clause describer The construction in `prop:exciting-padding-prop` of `answer_reduction.tex`,…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Padded` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The padded five-block clause describer. The construction in `prop:exciting-padding-prop` of `answer_reduction.tex`, applied to the formula used by the existing decoupled describer. Five index blocks acquire the common width `m`; the two answer tails are forced to be blank. Formula renaming preserves the original tree, so the construction remains polynomial in the old formula and the new width.
--
--   **Definitions** (15): `MIPRE.TM.CookLevin.Pad.blankSign` (The positive-at-even, negative-at-odd blank sign for one answer index.); `MIPRE.TM.CookLevin.Pad.circuit` (The padded circuit, before padding its number of gates to the exact PCP count.); `MIPRE.TM.CookLevin.Pad.circuitR` (The padded circuit itself, with the correct input count, as an ambient program.); `MIPRE.TM.CookLevin.Pad.describe` (The effective padded describer, before exact gate-count padding.); `MIPRE.TM.CookLevin.Pad.formula` (The padded formula: old clauses on old indices, or either answer-tail clause.); `MIPRE.TM.CookLevin.Pad.formulaR` (The padded clause formula, constructed uniformly in polynomial time.); `MIPRE.TM.CookLevin.Pad.gatePoly` (A polynomial bound for the padded circuit, derived from its verified program.); `MIPRE.TM.CookLevin.Pad.innerDim` (The common power-of-two index width.); `MIPRE.TM.CookLevin.Pad.innerDimU` (The common width in unary, computed directly from the succinct parameters.); `MIPRE.TM.CookLevin.Pad.layout` (Where the original five blocks and signs lie in the padded input.); `MIPRE.TM.CookLevin.Pad.layoutR` (The five-block offset table as an ambient program.); `MIPRE.TM.CookLevin.Pad.low` (Test that the `m`-bit index at `base` is below `2^old`.); `MIPRE.TM.CookLevin.Pad.lowR` (The original-width test, including the boundary case where both widths agree.); `_private.MIPRE.TM.CookLevin.Padded.0.MIPRE.TM.CookLevin.Pad.baseR`; `_private.MIPRE.TM.CookLevin.Padded.0.MIPRE.TM.CookLevin.Pad.blankSignR`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_layout`, `baseR_apply`, `blankSignR_apply`, `mem_layout_lt`, `slice_index`, `take_bitsOfNat`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Padded` (`MIPRE/TM/CookLevin/Padded.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 76 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Padded.lean; blueprint prop:pcp-padded-describer

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Padded.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
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
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD

/-!
# The padded five-block clause describer

The construction in `prop:exciting-padding-prop` of `answer_reduction.tex`,
applied to the formula used by the existing decoupled describer. Five index
blocks acquire the common width `m`; the two answer tails are forced to be blank.
Formula renaming preserves the original tree, so the construction remains
polynomial in the old formula and the new width.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Fml Desc

/-- Where the original five blocks and signs lie in the padded input. -/
def layout (ℓ r m : ℕ) : List ℕ :=
  List.range' 0 ℓ ++ List.range' m ℓ ++ List.range' (2 * m) r ++
    List.range' (3 * m) r ++ List.range' (4 * m) r ++ List.range' (5 * m) 5

@[simp] theorem length_layout (ℓ r m : ℕ) : (layout ℓ r m).length = 2 * ℓ + 3 * r + 5 := by
  simp [layout]
  omega

/-- Test that the `m`-bit index at `base` is below `2^old`. The comparison uses
one extra zero bit, so it also works at `old = m`. -/
def low (base old m : ℕ) : Fml :=
  ltConst (padTo (m + 1) (field base m)) (nbits (m + 1) (2 ^ old))

/-- The positive-at-even, negative-at-odd blank sign for one answer index. -/
def blankSign (base sign : ℕ) : Fml := xnor (inp sign) (not (inp base))

/-- The padded formula: old clauses on old indices, or either answer-tail clause. -/
def formula (ℓ r m : ℕ) (f : Fml) : Fml :=
  orList [and (andList [low 0 ℓ m, low m ℓ m, low (2 * m) r m,
      low (3 * m) r m, low (4 * m) r m])
      (Fml.rename (fun i => (layout ℓ r m).getD i 0) f),
    and (not (low 0 ℓ m)) (blankSign 0 (5 * m)),
    and (not (low m ℓ m)) (blankSign m (5 * m + 1))]

/-- The padded circuit, before padding its number of gates to the exact PCP count. -/
def circuit (ℓ r m : ℕ) (f : Fml) : Circuit := (formula ℓ r m f).toCircuit (5 * m + 5)

theorem take_bitsOfNat (n m j : ℕ) (h : n ≤ m) :
    (bitsOfNat m j).take n = bitsOfNat n j := by
  apply List.ext_getElem (by simp [h])
  intro k hk hk'
  simp only [bitsOfNat, List.getElem_take, List.getElem_ofFn]

theorem slice_index (pre post : BitStr) (m n j : ℕ) (hn : n ≤ m) :
    ibOf pre.length n (fun i => (pre ++ bitsOfNat m j ++ post).getD i false) = bitsOfNat n j := by
  rw [ibOf_getD _ _ _ (by simp; omega), List.append_assoc,
    List.drop_left' rfl, List.take_append]
  simp [length_bitsOfNat, Nat.sub_eq_zero_of_le hn, take_bitsOfNat _ _ _ hn]

theorem mem_layout_lt {ℓ r m j : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (hj : j ∈ layout ℓ r m) : j < 5 * m + 5 := by
  simp only [layout, List.mem_append, List.mem_range'_1] at hj
  omega

section Programs

variable {ι : Type*} [SizedEncoding ι]

noncomputable def baseR (mu : PolyTimeFun ι Unary) (k : ℕ) : PolyTimeFun ι ℕ :=
  ap₁ unaryToBin (ap₁ (nsmulU k) mu)

theorem baseR_apply (mu : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    baseR mu k i = k * (mu i).length := by simp [baseR]

/-- The five-block offset table as an ambient program. -/
noncomputable def layoutR (lu ru mu : PolyTimeFun ι Unary) : PolyTimeFun ι (List ℕ) :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append
    (ap₂ range'P (PolyTimeFun.const 0) lu) (ap₂ range'P (baseR mu 1) lu))
    (ap₂ range'P (baseR mu 2) ru)) (ap₂ range'P (baseR mu 3) ru))
    (ap₂ range'P (baseR mu 4) ru)) (ap₂ range'P (baseR mu 5) (PolyTimeFun.const (unary 5)))

/-- The original-width test, including the boundary case where both widths agree. -/
noncomputable def lowR (base : PolyTimeFun ι ℕ) (old mu : PolyTimeFun ι Unary) :
    PolyTimeFun ι Fml :=
  let wide := ap₂ addU mu (PolyTimeFun.const (unary 1))
  ap₂ ltConstP (ap₂ padToP wide (ap₂ fieldP base mu))
    (nbitsR wide (ap₁ natBits (ap₁ pow2P old)))

noncomputable def blankSignR (base sign : PolyTimeFun ι ℕ) : PolyTimeFun ι Fml :=
  xnorR (ap₁ Fml.inpF sign) (notR (ap₁ Fml.inpF base))

theorem blankSignR_apply (base sign : PolyTimeFun ι ℕ) (i : ι) :
    blankSignR base sign i = blankSign (base i) (sign i) := rfl

/-- The padded clause formula, constructed uniformly in polynomial time. -/
noncomputable def formulaR (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) :
    PolyTimeFun ι Fml :=
  orR [andTwo (andR [lowR (PolyTimeFun.const 0) lu mu, lowR (baseR mu 1) lu mu,
      lowR (baseR mu 2) ru mu, lowR (baseR mu 3) ru mu, lowR (baseR mu 4) ru mu])
      (ap₂ Fml.renameBy (layoutR lu ru mu) f),
    andTwo (notR (lowR (PolyTimeFun.const 0) lu mu))
      (blankSignR (PolyTimeFun.const 0) (baseR mu 5)),
    andTwo (notR (lowR (baseR mu 1) lu mu))
      (blankSignR (baseR mu 1) (ap₁ inc (baseR mu 5)))]

/-- The padded circuit itself, with the correct input count, as an ambient program. -/
noncomputable def circuitR (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) :
    PolyTimeFun ι Circuit :=
  ap₂ Fml.toCircuitF (ap₁ (incN 5) (baseR mu 5)) (formulaR lu ru mu f)

end Programs

/-! ## Applying the construction to the existing decoupled describer -/

/-- The common power-of-two index width. The old auxiliary width dominates the
old answer width, so this pads all five blocks. -/
noncomputable def innerDim (T σ : ℕ) : ℕ := ceilPower (mParam T σ)

/-- The common width in unary, computed directly from the succinct parameters. -/
noncomputable def innerDimU : PolyTimeFun DescInput Unary :=
  ceilPowerProg.comp (mU dEu)

/-- The effective padded describer, before exact gate-count padding. -/
noncomputable def describe : PolyTimeFun DescInput Circuit :=
  circuitR dLu (mU dEu) innerDimU (descFml5R dEu dTR dLu dDR dnR dxR dyR)

/-- A polynomial bound for the padded circuit, derived from its verified program. -/
noncomputable def gatePoly : Polynomial ℕ :=
  describe.timeBound.comp (Polynomial.C 25 * Polynomial.X + Polynomial.C 12)

end MIPRE.TM.CookLevin.Pad


