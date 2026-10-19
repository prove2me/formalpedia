-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
-- name    : MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:29:36.419224+00:00
-- url     : https://prove2.me/theorems/23153f49-0d49-48b7-aa70-af40b6552bd9
-- title:
--   Definitions of BinaryComponentsProg (addendum): Polynomial-time fixed-space component separation
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryComponentsProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial-time fixed-space component separation
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_LowDegree_BinaryComponentsProg` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (3): `MIPRE.LowDegree.BinaryLinear.componentStep`; `MIPRE.LowDegree.BinaryLinear.componentStepProg`; `MIPRE.LowDegree.BinaryLinear.groupComponentsProg` (Split by every computed fixed-space generator.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `componentStep_bounded`, `fold_componentStep_dimension`, `fold_componentStep_length`, `fold_componentStep_width`, `instFactPrimeOfNatNat_mIPRE_3`, `splitBitsCapped_width`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryComponentsProg` (`MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean; blueprint lem:effective-normal-element

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_esize_rows_of_width
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_split
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_splitBits_width

/-! # Polynomial-time fixed-space component separation -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

local instance instFactPrimeOfNatNat_mIPRE_3 : Fact (Nat.Prime 2) := ⟨by decide⟩

def componentStep (s : Unary × List BitStr) (b : BitStr) : Unary × List BitStr :=
  (s.1, splitBitsCapped s.1 s.2 b)

def componentStepProg : PolyTimeFun ((Unary × List BitStr) × BitStr) (Unary × List BitStr) :=
  congr ((fst.comp fst).pair (splitBitsCappedProg.comp
    ((fst.comp fst).pair ((snd.comp fst).pair snd))))
    (fun p => componentStep p.1 p.2) (by rintro ⟨⟨u, l⟩, b⟩; simp [componentStep])

theorem splitBitsCapped_width (u : Unary) (l : List BitStr) (b : BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) : ∀ e ∈ splitBitsCapped u l b, e.length ≤ N := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp (List.mem_of_mem_take he)
  rw [splitBits_width x b e he]
  exact hl x hx

theorem fold_componentStep_width (bs : List BitStr) (u : Unary) (l : List BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) :
    ∀ e ∈ (bs.foldl componentStep (u, l)).2, e.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ (splitBitsCapped_width u l b N hl)

theorem fold_componentStep_dimension (bs : List BitStr) (u : Unary) (l : List BitStr) :
    (bs.foldl componentStep (u, l)).1 = u := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem fold_componentStep_length (bs : List BitStr) (u : Unary) (l : List BitStr) (N : ℕ)
    (hu : u.length ≤ N) (hl : l.length ≤ N) :
    (bs.foldl componentStep (u, l)).2.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih =>
    apply ih
    exact (List.length_take_le _ _).trans hu

theorem componentStep_bounded : FoldBounded componentStepProg (5 * X ^ 2 + 5 * X + 5) := by
  intro bs s pre post hbs
  rcases s with ⟨u, l⟩
  let N := esize (bs, u, l)
  have hu : u.length ≤ N := by
    have h := length_le_esize_list u
    simp only [N, esize_prod]
    omega
  have hl : l.length ≤ N := by
    have h := length_le_esize_list l
    simp only [N, esize_prod]
    omega
  have hw : ∀ e ∈ l, e.length ≤ N := by
    intro e he
    have h₁ := esize_mem_le he
    have h₂ := length_le_esize_bitStr e
    simp only [N, esize_prod]
    omega
  have hh := esize_rows_of_width _ N (fold_componentStep_width pre u l N hw)
  have hn := fold_componentStep_length pre u l N hu hl
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl componentStep (u, l)) ≤ _
  rw [esize_prod, fold_componentStep_dimension]
  have he : esize u ≤ N := by simp only [N, esize_prod]; omega
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize u + esize (pre.foldl componentStep (u, l)).2 + 1 ≤ 5 * N ^ 2 + 5 * N + 5
  nlinarith

/-- Split by every computed fixed-space generator. Clipping controls malformed inputs too. -/
def groupComponentsProg : PolyTimeFun Unary (List BitStr) :=
  snd.comp ((foldl componentStepProg (5 * X ^ 2 + 5 * X + 5) componentStep_bounded).comp
    (groupFixedGeneratorsProg.pair ((PolyTimeFun.id _).pair
      (cons (unitBitsProg.comp ((const 0).pair (PolyTimeFun.id _))) (const [])))))

end MIPRE.LowDegree.BinaryLinear

end


