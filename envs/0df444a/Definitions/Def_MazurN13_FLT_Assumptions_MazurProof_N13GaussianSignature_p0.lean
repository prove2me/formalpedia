-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianSignature_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianSignature_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:16:48.279107+00:00
-- url     : https://prove2.me/theorems/23bc0dba-d9cc-46b1-8e9c-acdc7949a4b5
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianSignature source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianSignature

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianSignature
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Tactic

set_option autoImplicit false




/-!
# The signature of the N13 number field

The Gaussian unit embeds into the N13 cubic and still squares to `-1`.
Consequently there is no real embedding, so the sextic field is totally
complex.  The signature and Dirichlet unit rank then follow from the
structural degree computation.
-/

open Algebra Module

namespace MazurProof.N13GaussianSignature

noncomputable section

abbrev K := N13GaussianFractionField.K

abbrev L := N13GaussianNumberField.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

/-- The Gaussian square root of `-1`, embedded in the N13 field. -/
def iL : L :=
  algebraMap K L N13GaussianFractionField.iK

@[simp] theorem iL_mul_self :
    iL * iL = -1 := by
  rw [iL, ← map_mul,
    N13GaussianFractionField.iK_mul_self,
    map_neg, map_one]

/-- A real embedding would send `iL` to a real square root of `-1`. -/
theorem no_ringHom_to_real (φ : L →+* ℝ) : False := by
  have hsq : φ iL * φ iL = (-1 : ℝ) := by
    simpa only [map_mul, map_neg, map_one] using
      congrArg φ iL_mul_self
  nlinarith [sq_nonneg (φ iL)]

/-- Every infinite place of the N13 field is complex. -/
instance isTotallyComplexL :
    NumberField.IsTotallyComplex L where
  isComplex v := by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    exact no_ringHom_to_real
      (NumberField.InfinitePlace.embedding_of_isReal
        (K := L) hv)

@[simp] theorem nrRealPlaces_eq_zero :
    NumberField.InfinitePlace.nrRealPlaces L = 0 :=
  NumberField.IsTotallyComplex.nrRealPlaces_eq_zero L

@[simp] theorem nrComplexPlaces_eq_three :
    NumberField.InfinitePlace.nrComplexPlaces L = 3 := by
  have hsignature :
      Module.finrank ℚ L =
        2 * NumberField.InfinitePlace.nrComplexPlaces L :=
    NumberField.IsTotallyComplex.finrank L
  rw [N13GaussianNumberField.finrank_Q_L] at hsignature
  omega

@[simp] theorem infinitePlace_card_eq_three :
    Fintype.card (NumberField.InfinitePlace L) = 3 := by
  rw [
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L,
    nrRealPlaces_eq_zero,
    nrComplexPlaces_eq_three
  ]

@[simp] theorem units_rank_eq_two :
    NumberField.Units.rank L = 2 := by
  simp [NumberField.Units.rank]

end

end MazurProof.N13GaussianSignature


