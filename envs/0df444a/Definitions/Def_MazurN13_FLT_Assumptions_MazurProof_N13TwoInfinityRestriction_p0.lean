-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoInfinityRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoInfinityRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:34:19.837639+00:00
-- url     : https://prove2.me/theorems/ab0bd226-2ccc-4170-b401-a037a39914ed
-- title:
--   FLT.Assumptions.MazurProof.N13TwoInfinityRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoInfinityRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoInfinityRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinusAPI_p0
import Mathlib.RingTheory.FractionalIdeal.Operations

set_option autoImplicit false




/-!
# Restriction of N13 fractional ideals to the two infinity branches

The two Laurent expansions at infinity combine into a faithful map from the
N13 function field to the product of the two branch fields.  Consequently an
affine fractional ideal restricts canonically to a fractional submodule of
that product.  This construction uses the ideal itself, rather than a chosen
global generator.
-/

open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13TwoInfinityRestriction

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

abbrev CoordinateRing : Type u :=
  N13Mumford.CoordinateRing K

abbrev FunctionField : Type u :=
  N13Mumford.FunctionField K

abbrev BranchPair : Type u :=
  LaurentSeries K × LaurentSeries K

/-- Simultaneous restriction of affine functions to the two infinity
branches. -/
def coordinateToBranches :
    CoordinateRing K →+* BranchPair K :=
  (N13Infinity.coordinateToLaurent K).prod
    (N13InfinityMinus.coordinateToLaurentMinus K)

/-- Simultaneous restriction of rational functions to the two infinity
branches. -/
def functionFieldToBranches :
    FunctionField K →+* BranchPair K :=
  (N13Infinity.functionFieldToLaurent K).prod
    (N13InfinityMinus.functionFieldToLaurentMinus K)

theorem coordinateToBranches_injective :
    Function.Injective (coordinateToBranches K) := by
  intro f g h
  apply N13Infinity.coordinateToLaurent_injective K
  exact congrArg Prod.fst h

theorem functionFieldToBranches_injective :
    Function.Injective (functionFieldToBranches K) := by
  intro f g h
  apply N13Infinity.functionFieldToLaurent_injective K
  exact congrArg Prod.fst h

@[simp] theorem functionFieldToBranches_algebraMap
    (f : CoordinateRing K) :
    functionFieldToBranches K
        (algebraMap (CoordinateRing K) (FunctionField K) f) =
      coordinateToBranches K f := by
  apply Prod.ext
  · exact N13Infinity.functionFieldToLaurent_algebraMap K f
  · exact N13InfinityMinus.functionFieldToLaurentMinus_algebraMap K f

local instance branchPairAlgebra :
    Algebra (CoordinateRing K) (BranchPair K) :=
  (coordinateToBranches K).toAlgebra

/-- The rational restriction map as a morphism over the affine coordinate
ring. -/
def functionFieldToBranchesAlgHom :
    FunctionField K →ₐ[CoordinateRing K] BranchPair K where
  __ := functionFieldToBranches K
  commutes' f := functionFieldToBranches_algebraMap K f

abbrev AffineFractionalIdeal : Type u :=
  FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)

abbrev BranchFractionalIdeal : Type u :=
  FractionalIdeal (CoordinateRing K)⁰ (BranchPair K)

/-- Restrict an affine fractional ideal to the product of the two rational
Laurent branches. -/
def restrictFractionalIdeal
    (I : AffineFractionalIdeal K) :
    BranchFractionalIdeal K :=
  I.map (functionFieldToBranchesAlgHom K)

@[simp] theorem mem_restrictFractionalIdeal
    (I : AffineFractionalIdeal K) (z : BranchPair K) :
    z ∈ restrictFractionalIdeal K I ↔
      ∃ f, f ∈ I ∧ functionFieldToBranches K f = z := by
  exact FractionalIdeal.mem_map

theorem restrictFractionalIdeal_injective :
    Function.Injective (restrictFractionalIdeal K) :=
  FractionalIdeal.map_injective
    (functionFieldToBranchesAlgHom K)
    (functionFieldToBranches_injective K)

/-- Restriction respects the ring operations on fractional ideals. -/
def restrictFractionalIdealHom :
    AffineFractionalIdeal K →+* BranchFractionalIdeal K where
  toFun := restrictFractionalIdeal K
  map_one' := by simp [restrictFractionalIdeal]
  map_zero' := by simp [restrictFractionalIdeal]
  map_add' I J := by simp [restrictFractionalIdeal]
  map_mul' I J := by simp [restrictFractionalIdeal]

theorem restrictFractionalIdealHom_injective :
    Function.Injective (restrictFractionalIdealHom K) :=
  restrictFractionalIdeal_injective K

/-- Restriction of an invertible affine fractional ideal. -/
def restrictInvertibleFractionalIdeal :
    (AffineFractionalIdeal K)ˣ →*
      (BranchFractionalIdeal K)ˣ :=
  Units.map (restrictFractionalIdealHom K).toMonoidHom

@[simp] theorem coe_restrictInvertibleFractionalIdeal
    (I : (AffineFractionalIdeal K)ˣ) :
    (restrictInvertibleFractionalIdeal K I :
        BranchFractionalIdeal K) =
      restrictFractionalIdeal K
        (I : AffineFractionalIdeal K) :=
  rfl

end

end MazurProof.N13TwoInfinityRestriction


