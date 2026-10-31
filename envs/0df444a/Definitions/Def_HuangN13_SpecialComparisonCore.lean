-- Prove2me | Definitions.Def_HuangN13_SpecialComparisonCore
-- name    : HuangN13_SpecialComparisonCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:05:37.654259+00:00
-- url     : https://prove2.me/theorems/82e708d7-a778-47bc-8fb4-6692c2385884
-- title:
--   Special divisor chart tensors and coherent comparison data
-- statement:
--   The original coherent chart-pair type, the chart pair attached to each degree-two special divisor, tensor products of chart pairs, their coherent comparison witnesses, and the corresponding tensor polynomial.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof; exact source-owner ranges and hashes are recorded in metadata.json. This is only the exact SpecialComparison/ofDivisor/tensor/tensorPolynomial statement closure.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_affineCoeffMap_hPoly
import Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_map_infinityPointIdeal
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_overlap_unitPointIdeal

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
theorem affineCurve_relation :
    (N13GoodCoordinateRingTwo.curvePoly).eval₂
        affineCoeffMap affineYImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
      tOverlap xOverlap vOverlap
      tOverlap_mul_xOverlap infinityOverlap_coordinate_relation
  simp only [N13GoodCoordinateRingTwo.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, affineCoeffMap_hPoly,
    affineCoeffMap_rhsPoly]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
/-- Restriction of the affine coordinate ring to the special infinity
principal open. -/
def affineToInfinityOverlap :
    AffineCurve →+* InfinityOverlap :=
  AdjoinRoot.lift affineCoeffMap affineYImage affineCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_of (p : K[X]) :
    affineToInfinityOverlap
        (AdjoinRoot.of
          (N13GoodCoordinateRingTwo.curvePoly) p) =
      affineCoeffMap p := by
  exact AdjoinRoot.lift_of affineCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_yClass :
    affineToInfinityOverlap yClass = affineYImage := by
  exact AdjoinRoot.lift_root affineCurve_relation
end
end MazurProof.N13SpecialCurveOverlap
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Compatible ideals on the two affine charts of the completed special
curve. -/
structure ChartPair where
  affineIdeal : Ideal SpecialAffine
  infinityIdeal : Ideal SpecialInfinity
  overlap_eq :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        affineIdeal =
      Ideal.map
        (algebraMap SpecialInfinity
          N13SpecialCurveOverlap.InfinityOverlap)
        infinityIdeal
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
/-- Compatible ideals on the two special charts. -/
abbrev ChartPair : Type :=
  N13TwoChartSpecialRestriction.ChartPair
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- Extension of a finite point ideal to the common overlap has the expected
two explicit generators. -/
theorem map_affinePointIdeal (P : AffinePoint) :
    Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P) =
      Ideal.span
        {N13SpecialCurveOverlap.xOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13SpecialCurveOverlap.xOverlap ^ 3 *
              N13SpecialCurveOverlap.vOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2} := by
  simp [affinePointIdeal, N13GoodCoordinateRingTwo.mumfordIdeal,
    N13GoodCoordinateRingTwo.ySubClass, Ideal.map_span, Set.image_pair,
    N13GoodCoordinateRingTwo.xClass, N13GoodCoordinateRingTwo.mk,
    N13SpecialCurveOverlap.affineCoeffMap]
  change
    Ideal.span
        {N13SpecialCurveOverlap.xOverlap -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13SpecialCurveOverlap.affineToInfinityOverlap
              N13SpecialCurveOverlap.yClass -
            N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2} =
      _
  rw [N13SpecialCurveOverlap.affineToInfinityOverlap_yClass]
  rfl
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point with horizontal coordinate zero is absent from the
overlap, so its affine ideal extends to the unit ideal there. -/
def affineZeroPoint
    (P : AffinePoint)
    (hx : P.1.1 = 0) :
    ChartPair where
  affineIdeal := affinePointIdeal P
  infinityIdeal := ⊤
  overlap_eq := by
    rw [Ideal.map_top]
    apply
      (Ideal.map
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (affinePointIdeal P)).eq_top_of_isUnit_mem
    · apply Ideal.mem_map_of_mem
      exact
        N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
          (X - C P.1.1) (C P.1.2)
    · simpa [hx, N13GoodCoordinateRingTwo.xClass,
        N13GoodCoordinateRingTwo.mk,
        N13SpecialCurveOverlap.affineCoeffMap] using
        N13SpecialCurveOverlap.xOverlap_isUnit
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point with horizontal coordinate one is represented on both
charts by the same point after the change of coordinates. -/
def affineOnePoint
    (P : AffinePoint)
    (hx : P.1.1 = 1) :
    ChartPair where
  affineIdeal := affinePointIdeal P
  infinityIdeal := infinityPointIdeal 1 P.1.2
  overlap_eq := by
    rw [map_affinePointIdeal, map_infinityPointIdeal, hx]
    simpa using
      overlap_unitPointIdeal
        (N13SpecialCurveOverlap.coefficientToInfinityOverlap P.1.2)
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- An infinity point is absent from the ordinary affine chart.  Its
infinity ideal contains `t`, which becomes a unit on the overlap. -/
def infinityPoint (P : InfinityPoint) : ChartPair where
  affineIdeal := ⊤
  infinityIdeal := infinityPointIdeal 0 P.1
  overlap_eq := by
    rw [Ideal.map_top]
    symm
    apply
      (Ideal.map
        (algebraMap SpecialInfinity SpecialOverlap)
        (infinityPointIdeal 0 P.1)).eq_top_of_isUnit_mem
    · apply Ideal.mem_map_of_mem
      have ht :
          N13SpecialInfinityChart.tClass -
              algebraMap K[X] SpecialInfinity (C 0) ∈
            infinityPointIdeal 0 P.1 :=
        Ideal.subset_span (by simp)
      simpa using ht
    · simpa [N13SpecialCurveOverlap.tOverlap] using
        (IsLocalization.Away.algebraMap_isUnit
          N13SpecialInfinityChart.tClass :
          IsUnit N13SpecialCurveOverlap.tOverlap)
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- Canonical compatible chart ideals of one completed special point. -/
def point (P : CurvePoint) : ChartPair :=
  match P with
  | Sum.inl P =>
      if hx : P.1.1 = 0 then
        affineZeroPoint P hx
      else
        affineOnePoint P
          ((N13GoodModelTwo.fixedTwo_eq_zero_or_one
            P.1.1 (ZMod.pow_card P.1.1)).resolve_left hx)
  | Sum.inr P =>
      infinityPoint P
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
/-- Tensor product of two compatible chart pairs. -/
def tensor (L M : ChartPair) : ChartPair where
  affineIdeal := L.affineIdeal * M.affineIdeal
  infinityIdeal := L.infinityIdeal * M.infinityIdeal
  overlap_eq := by
    rw [Ideal.map_mul, Ideal.map_mul, L.overlap_eq, M.overlap_eq]
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
/-- Tensoring chart pairs is commutative. -/
theorem tensor_comm (L M : ChartPair) :
    tensor L M = tensor M L := by
  cases L
  cases M
  simp [tensor, mul_comm]
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
/-- Canonical chart ideals of an unordered effective divisor of degree two.
Commutativity of ideal multiplication is exactly the descent condition
through `Sym2`. -/
def ofDivisor : EffectiveDivisorTwo → ChartPair :=
  Sym2.lift
    ⟨fun P Q => tensor (point P) (point Q),
      fun P Q => tensor_comm (point P) (point Q)⟩
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13CoherentChartComparison
noncomputable section
/-- Nonzero numerator and denominator on both special charts, with their
fractions equal on the overlap. This encodes principal equivalence, not an
assertion about the finite Abel code. -/
structure SpecialComparison
    (L M : N13TwoChartSpecialRestriction.ChartPair) where
  aNum : As
  aDen : As
  iNum : Bs
  iDen : Bs
  aNum_ne : aNum ≠ 0
  aDen_ne : aDen ≠ 0
  iNum_ne : iNum ≠ 0
  iDen_ne : iDen ≠ 0
  affine_eq :
    Ideal.span ({aNum} : Set As) * L.affineIdeal =
      Ideal.span ({aDen} : Set As) * M.affineIdeal
  infinity_eq :
    Ideal.span ({iNum} : Set Bs) * L.infinityIdeal =
      Ideal.span ({iDen} : Set Bs) * M.infinityIdeal
  overlap_eq :
    N13SpecialCurveOverlap.affineToInfinityOverlap aNum * algebraMap Bs Os iDen =
      N13SpecialCurveOverlap.affineToInfinityOverlap aDen * algebraMap Bs Os iNum
end
end MazurProof.N13CoherentChartComparison
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
def pointPolynomial : CurvePoint → K[X]
  | Sum.inl P => X - C P.1.1
  | Sum.inr _ => 1
end
end MazurProof.N13SpecialComparisonFactorPair
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
def divisorPolynomial : EffectiveDivisorTwo → K[X] :=
  Sym2.lift ⟨fun P Q => pointPolynomial P * pointPolynomial Q, fun P Q => mul_comm _ _⟩
end
end MazurProof.N13SpecialComparisonFactorPair
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialComparisonFactorPair
noncomputable section
open Polynomial N13SpecialDivisorCharts
open scoped Sym2
def tensorPolynomial (D E : EffectiveDivisorTwo) : K[X] := divisorPolynomial D * divisorPolynomial E
end
end MazurProof.N13SpecialComparisonFactorPair
end
end
end
end
end
end
end
end


