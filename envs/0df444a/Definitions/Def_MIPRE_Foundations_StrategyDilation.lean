-- Prove2me | Definitions.Def_MIPRE_Foundations_StrategyDilation
-- name    : MIPRE_Foundations_StrategyDilation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:53.201018+00:00
-- url     : https://prove2.me/theorems/bd3a5f9d-442e-4e40-80d9-9cee886a97b7
-- title:
--   Definitions of StrategyDilation: Dilating a POVM strategy to a projective one A strategy built by a rigidity argument arrives as a family of POVMs on…
-- statement:
--   The definitions of the module `MIPRE.Foundations.StrategyDilation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Dilating a POVM strategy to a projective one. A strategy built by a rigidity argument arrives as a family of POVMs on each party's register --- averages of sandwiches, coarse-grainings, mixtures --- while the soundness theorems take `TensorProductStrategy`, whose measurements are projective. Naimark's theorem closes the gap: each family of POVMs is the compression, by one question-independent isometry `ancillaEmbed d a₀`, of a projective family on `d × A` (`exists_projective_dilation`). This file packages that for a whole two-party strategy and records the two facts a consumer needs: *…
--
--   **Definitions** (2): `MIPRE.POVM.compress` (**The compression of a POVM is a POVM.**); `MIPRE.ancCompress` (The compression of an operator on `d × Anc` by the ancilla state `|a₀⟩`.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `compress_mats`, `ancCompress_conjTranspose`, `ancCompress_one`, `ancCompress_posSemidef`, `ancCompress_sum`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.StrategyDilation` (`MIPRE/Foundations/StrategyDilation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StrategyDilation.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StrategyDilation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_ancillaEmbed_isometry

/-!
# Dilating a POVM strategy to a projective one

A strategy built by a rigidity argument arrives as a family of POVMs on each party's register ---
averages of sandwiches, coarse-grainings, mixtures --- while the soundness theorems take
`TensorProductStrategy`, whose measurements are projective. Naimark's theorem closes the gap: each
family of POVMs is the compression, by one question-independent isometry `ancillaEmbed d a₀`, of a
projective family on `d × A` (`exists_projective_dilation`). This file packages that for a whole
two-party strategy and records the two facts a consumer needs:

* `povmValue_extVec2`: on the twice-extended state `extVec2 ψ a₀ b₀` a strategy has the value
  of its compression on `ψ`, so the dilated projective strategy has the value of the POVM strategy
  it came from;
* `inconsistency_extVec2`: likewise for the inconsistency of two measurement families, so a
  conclusion about the dilated strategy on the extended state reads back, through
  `POVM.compress`, as a conclusion about compressions on the original state.

`ancCompress a₀` is the compression of a single matrix and `POVM.compress a₀` of a POVM; the
latter is a POVM because the isometry preserves positivity and sends the identity to the identity.
`exists_projective_dilation_povm` is Naimark for a question-indexed family of bundled POVMs.
`MIPRE.Background.LIDT.Adapter.Registers` combines these with the reindexing of that file to state
the seeded low individual degree test's soundness for a POVM strategy.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Compression by an inert ancilla -/

section Compress

variable {d Anc : Type*} [Fintype d] [DecidableEq d] [Fintype Anc] [DecidableEq Anc]

/-- The compression of an operator on `d × Anc` by the ancilla state `|a₀⟩`. -/
def ancCompress (a₀ : Anc) (X : Matrix (d × Anc) (d × Anc) ℂ) : Matrix d d ℂ :=
  (ancillaEmbed d a₀)ᴴ * (X * ancillaEmbed d a₀)

theorem ancCompress_posSemidef (a₀ : Anc) {X : Matrix (d × Anc) (d × Anc) ℂ}
    (hX : X.PosSemidef) : (ancCompress a₀ X).PosSemidef := by
  rw [ancCompress, ← Matrix.mul_assoc]
  exact hX.conjTranspose_mul_mul_same _

theorem ancCompress_one (a₀ : Anc) :
    ancCompress a₀ (1 : Matrix (d × Anc) (d × Anc) ℂ) = 1 := by
  rw [ancCompress, Matrix.one_mul, ancillaEmbed_isometry]

theorem ancCompress_sum {ι : Type*} (a₀ : Anc) (s : Finset ι)
    (X : ι → Matrix (d × Anc) (d × Anc) ℂ) :
    ancCompress a₀ (∑ i ∈ s, X i) = ∑ i ∈ s, ancCompress a₀ (X i) := by
  simp only [ancCompress, Matrix.sum_mul, Matrix.mul_sum]

theorem ancCompress_conjTranspose (a₀ : Anc) (X : Matrix (d × Anc) (d × Anc) ℂ) :
    (ancCompress a₀ X)ᴴ = ancCompress a₀ Xᴴ := by
  rw [ancCompress, ancCompress, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

variable {A : Type*} [Fintype A]

/-- **The compression of a POVM is a POVM.** -/
def POVM.compress (a₀ : Anc) (M : POVM A (d × Anc)) : POVM A d where
  mats a := ⟨ancCompress a₀ (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, ancCompress_conjTranspose,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      (ancCompress_posSemidef a₀ (M.posSemidef a)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ancCompress a₀ (M.mats a).val = 1
    rw [← ancCompress_sum, POVM.sum_val, ancCompress_one]

@[simp] theorem POVM.compress_mats (a₀ : Anc) (M : POVM A (d × Anc)) (a : A) :
    ((M.compress a₀).mats a).val = ancCompress a₀ (M.mats a).val := rfl

end Compress

/-! ## The Born rule on the twice-extended state -/

section Ext

variable {dA dB Anc Bnc : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end Ext

/-! ## Naimark dilation of a POVM strategy -/

section Dilate

variable {X A d : Type*} [Fintype A] [DecidableEq A] [Fintype d] [DecidableEq d]

end Dilate

end MIPRE


