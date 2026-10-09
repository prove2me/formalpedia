-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartLineTensor_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoChartLineTensor_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:43:08.580093+00:00
-- url     : https://prove2.me/theorems/b2464c10-44bb-4f63-b6d7-8e3a3552ccb3
-- title:
--   FLT.Assumptions.MazurProof.N13TwoChartLineTensor source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoChartLineTensor

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoChartLineTensor
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingDegreeOneSpread_p0

set_option autoImplicit false




/-!
# Tensor products of explicit N13 two-chart lines

The ordinary affine and infinity presentations of a line multiply
chartwise.  Ideal extension commutes with multiplication, so the overlap
compatibility is preserved.  This turns the explicit escaping point lines
into proper spreads of split effective divisors without constructing a
Picard functor.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13TwoChartLineTensor

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal

abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityPointSpread.InfinityFractionalIdeal

local instance integralRationalAlgebra :
    Algebra N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- The trivial line in the explicit two-chart presentation. -/
def one : TwoChartLine where
  affineIdeal := ⊤
  infinityIdeal := ⊤
  affine_isUnit := by
    rw [FractionalIdeal.coeIdeal_top]
    exact isUnit_one
  infinity_isUnit := by
    rw [FractionalIdeal.coeIdeal_top]
    exact isUnit_one
  overlap_eq := by
    rw [Ideal.map_top, Ideal.map_top]

/-- Tensor product in the explicit two-chart presentation. -/
def tensor (L M : TwoChartLine) : TwoChartLine where
  affineIdeal := L.affineIdeal * M.affineIdeal
  infinityIdeal := L.infinityIdeal * M.infinityIdeal
  affine_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.affine_isUnit.mul M.affine_isUnit
  infinity_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.infinity_isUnit.mul M.infinity_isUnit
  overlap_eq := by
    rw [Ideal.map_mul, Ideal.map_mul, L.overlap_eq, M.overlap_eq]

@[simp] theorem tensor_affineIdeal (L M : TwoChartLine) :
    (tensor L M).affineIdeal =
      L.affineIdeal * M.affineIdeal :=
  rfl

@[simp] theorem tensor_infinityIdeal (L M : TwoChartLine) :
    (tensor L M).infinityIdeal =
      L.infinityIdeal * M.infinityIdeal :=
  rfl

/-- Natural tensor powers of an explicit two-chart line.  Natural powers
are sufficient for balanced low-degree Mumford representatives because
their infinity multiplicity is nonnegative. -/
def tensorPow
    (L : TwoChartLine) :
    ℕ → TwoChartLine
  | 0 => one
  | n + 1 => tensor L (tensorPow L n)

@[simp] theorem tensorPow_zero
    (L : TwoChartLine) :
    tensorPow L 0 = one :=
  rfl

@[simp] theorem tensorPow_succ
    (L : TwoChartLine) (n : ℕ) :
    tensorPow L (n + 1) =
      tensor L (tensorPow L n) :=
  rfl

@[simp] theorem tensorPow_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensorPow L n).affineIdeal =
      L.affineIdeal ^ n := by
  induction n with
  | zero =>
      simp [tensorPow, one]
  | succ n ih =>
      simp [tensorPow, ih, pow_succ']

@[simp] theorem tensorPow_infinityIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensorPow L n).infinityIdeal =
      L.infinityIdeal ^ n := by
  induction n with
  | zero =>
      simp [tensorPow, one]
  | succ n ih =>
      simp [tensorPow, ih, pow_succ']

/-! ## The two rational points at infinity -/

abbrev IntegralInfinityPoint : Type :=
  N13IntegralInfinityPointSpread.IntegralInfinityPoint

/-- The positive point at infinity in the good chart, with coordinates
`t = 0` and `v = 0`. -/
def infinityPlusPoint : IntegralInfinityPoint :=
  ⟨(0, 0), by
    norm_num [N13GoodModelTwo.InfinityChartEquation]⟩

/-- The negative point at infinity in the good chart, with coordinates
`t = 0` and `v = -1`. -/
def infinityMinusPoint : IntegralInfinityPoint :=
  ⟨(0, -1), by
    norm_num [N13GoodModelTwo.InfinityChartEquation]⟩

/-- The proper two-chart point line supported at positive infinity. -/
def infinityPlusLine : TwoChartLine :=
  N13IntegralInfinityPointSpread.pointLine infinityPlusPoint

/-- The proper two-chart point line supported at negative infinity. -/
def infinityMinusLine : TwoChartLine :=
  N13IntegralInfinityPointSpread.pointLine infinityMinusPoint

/-- Both infinity point lines are trivial on the affine chart.  The branch
distinction is retained entirely by their infinity-chart point ideals. -/
@[simp] theorem infinityPlusLine_affineIdeal :
    infinityPlusLine.affineIdeal = ⊤ := by
  simp [infinityPlusLine,
    N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.affinePointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    N13IntegralInfinityPointSpread.affineU,
    infinityPlusPoint]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp)

/-- The negative infinity point line is likewise trivial on the affine
chart, although its infinity-chart ideal differs from the positive line. -/
@[simp] theorem infinityMinusLine_affineIdeal :
    infinityMinusLine.affineIdeal = ⊤ := by
  simp [infinityMinusLine,
    N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.affinePointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    N13IntegralInfinityPointSpread.affineU,
    infinityMinusPoint]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp)

/-- The natural tensor power of the positive-infinity point line.  Balanced
low-degree Mumford data use only nonnegative infinity multiplicities. -/
def positiveInfinityPowerLine
    (n : ℕ) :
    TwoChartLine :=
  tensorPow infinityPlusLine n

@[simp] theorem positiveInfinityPowerLine_affineIdeal
    (n : ℕ) :
    (positiveInfinityPowerLine n).affineIdeal = ⊤ := by
  simp [positiveInfinityPowerLine]

@[simp] theorem positiveInfinityPowerLine_infinityIdeal
    (n : ℕ) :
    (positiveInfinityPowerLine n).infinityIdeal =
      (N13IntegralInfinityPointSpread.pointIdeal
        infinityPlusPoint) ^ n := by
  simp [positiveInfinityPowerLine, infinityPlusLine,
    N13IntegralInfinityPointSpread.pointLine]

/-- Tensoring by a positive-infinity power changes only the infinity chart.
In particular it preserves the exact affine generic ideal of any previously
constructed proper spread. -/
@[simp] theorem tensor_positiveInfinityPowerLine_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (tensor L (positiveInfinityPowerLine n)).affineIdeal =
      L.affineIdeal := by
  simp

/-- Add a nonnegative positive-infinity multiplicity to a proper line.
This supplies the chart-level factor needed for the `nInf` field of a
balanced low-degree Mumford representative; identifying the resulting line
with the oriented Picard class is a separate semantic comparison. -/
def withPositiveInfinityMultiplicity
    (L : TwoChartLine) (n : ℕ) :
    TwoChartLine :=
  tensor L (positiveInfinityPowerLine n)

@[simp] theorem withPositiveInfinityMultiplicity_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    (withPositiveInfinityMultiplicity L n).affineIdeal =
      L.affineIdeal :=
  tensor_positiveInfinityPowerLine_affineIdeal L n

/-- Adding the positive-infinity correction preserves the exact Mumford
ideal seen on the generic affine chart. -/
theorem map_withPositiveInfinityMultiplicity_affineIdeal
    (L : TwoChartLine) (n : ℕ) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (withPositiveInfinityMultiplicity L n).affineIdeal =
      Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        L.affineIdeal := by
  rw [withPositiveInfinityMultiplicity_affineIdeal]

theorem map_tensor_affineIdeal
    (L M : TwoChartLine) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (tensor L M).affineIdeal =
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          M.affineIdeal := by
  rw [tensor_affineIdeal, Ideal.map_mul]

/-- The linear graph through two points with distinct horizontal
coordinates. -/
def secantV
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂[X] :=
  C z₁ +
    C ((z₂ - z₁) * (x₂ - x₁)⁻¹) * (X - C x₁)

@[simp] theorem secantV_eval_left
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₁ = z₁ := by
  simp [secantV]

@[simp] theorem secantV_eval_right
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₂ = z₂ := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  simp [secantV, hd]

private theorem linearFactors_coprime
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    ∃ a b : N13EscapingDegreeOneSpread.Q₂[X],
      a * (X - C x₁) + b * (X - C x₂) = 1 := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  refine
    ⟨C ((x₂ - x₁)⁻¹), -C ((x₂ - x₁)⁻¹), ?_⟩
  calc
    C ((x₂ - x₁)⁻¹) * (X - C x₁) +
          -C ((x₂ - x₁)⁻¹) * (X - C x₂) =
        C ((x₂ - x₁)⁻¹) * C (x₂ - x₁) := by
      rw [map_sub]
      ring
    _ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]

/-- The product of two distinct point graphs is the quadratic graph of
their secant interpolant. -/
theorem pointIdeal_mul_eq_secantGraph
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₁) (C z₁) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₂) (C z₂) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - C x₁) * (X - C x₂))
        (secantV x₁ z₁ x₂ z₂) := by
  have h₁ :
      X - C x₁ ∣ secantV x₁ z₁ x₂ z₂ - C z₁ := by
    simpa using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₁))
  have h₂ :
      X - C x₂ ∣ secantV x₁ z₁ x₂ z₂ - C z₂ := by
    simpa [secantV_eval_right x₁ z₁ x₂ z₂ hneq] using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₂))
  simpa [SexticMumford.mumfordIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    SexticMumford.ySubClass,
    GeneralizedGraphIdealCore.ySubClass,
    SexticMumford.xClassHom_apply] using
      (GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
        (SexticMumford.xClassHom
          N13EscapingDegreeOneSpread.Model)
        (SexticMumford.yClass
          N13EscapingDegreeOneSpread.Model)
        (X - C x₁) (X - C x₂) (C z₁) (C z₂)
        (secantV x₁ z₁ x₂ z₂)
        h₁ h₂ (linearFactors_coprime x₁ x₂ hneq))

/-- A reduced ordinate on a split monic quadratic is its secant
interpolant. -/
theorem mumford_v_eq_secant
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    D.v =
      secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂) := by
  have huDegree :
      D.u.degree = (2 : WithBot ℕ) := by
    rw [degree_eq_natDegree D.u_monic.ne_zero, hdeg]
    norm_num
  have hvDegree :
      D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvlt : D.v.natDegree < 2 := by
    by_cases hv0 : D.v = 0
    · simp [hv0]
    · rw [natDegree_lt_iff_degree_lt hv0]
      simpa [huDegree] using hvDegree
  have hsle :
      (secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂)).natDegree ≤ 1 := by
    unfold secantV
    compute_degree
  let f : Fin 2 → N13EscapingDegreeOneSpread.Q₂ :=
    fun i => if i = 0 then x₁ else x₂
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hneq, hneq.symm]
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    D.v
    (secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂))
    hf
  · intro i
    fin_cases i
    · simp [f]
    · simp [f, secantV_eval_right _ _ _ _ hneq]
  · simp only [Fintype.card_fin]
    omega

/-- The two factors of a split Mumford horizontal polynomial are actual
curve points. -/
theorem mumford_eval_onCurve_of_split
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂)) :
    (D.v.eval x₁) ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x₁ ∧
      (D.v.eval x₂) ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x₂ := by
  obtain ⟨w, hw⟩ := D.curve_dvd
  constructor
  · have hzero :=
      congrArg (Polynomial.eval x₁) hw
    simp [hfactor] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · have hzero :=
      congrArg (Polynomial.eval x₂) hw
    simp [hfactor] at hzero
    exact (sub_eq_zero.mp hzero).symm

/-- A split balanced quadratic Mumford graph is literally the product of
the two point ideals, not only equal to it in the Picard quotient. -/
theorem mumfordIdeal_eq_pointIdeal_mul_of_split
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₁) (C (D.v.eval x₁)) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₂) (C (D.v.eval x₂)) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model D.u D.v := by
  rw [pointIdeal_mul_eq_secantGraph _ _ _ _ hneq,
    ← hfactor, ← mumford_v_eq_secant
      D hdeg x₁ x₂ hneq]

/-- Tensor the proper lines of two escaping affine points. -/
def nonintegralPointPairLine
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    TwoChartLine :=
  tensor
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x₁ y₁ hx₁ hcurve₁)
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x₂ y₂ hx₂ hcurve₂)

/-- The generic affine ideal of the pair line is exactly the product of
the two standard sextic point ideals. -/
theorem map_nonintegralPointPairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (nonintegralPointPairLine
          x₁ y₁ x₂ y₂ hx₁ hcurve₁ hx₂ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - Polynomial.C x₁)
          (Polynomial.C
            (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - Polynomial.C x₂)
          (Polynomial.C
            (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [nonintegralPointPairLine, map_tensor_affineIdeal]
  change
    Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityPointSpread.affinePointIdeal
            (N13EscapingDegreeOneSpread.lift x₁ y₁ hx₁ hcurve₁)) *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityPointSpread.affinePointIdeal
            (N13EscapingDegreeOneSpread.lift x₂ y₂ hx₂ hcurve₂)) =
      _
  rw [
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint,
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint]

/-- With distinct horizontal coordinates, the generic fibre of the pair
line is one quadratic Mumford graph, not merely an ideal product. -/
theorem map_nonintegralPointPairLine_eq_secantGraph
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂)
    (hneq : x₁ ≠ x₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (nonintegralPointPairLine
          x₁ y₁ x₂ y₂ hx₁ hcurve₁ hx₂ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - C x₁) * (X - C x₂))
        (secantV
          x₁ (N13EscapingDegreeOneSpread.pointY x₁ y₁)
          x₂ (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [map_nonintegralPointPairLine_affineIdeal,
    pointIdeal_mul_eq_secantGraph _ _ _ _ hneq]

/-- Inverse completed-square ordinate over `ℚ₂`. -/
def goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂ :=
  (Y - N13GoodModelTwo.h x) / 2

@[simp] theorem pointY_goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.pointY x (goodY x Y) = Y := by
  simp only [N13EscapingDegreeOneSpread.pointY, goodY]
  ring

/-- Completing the square is an equivalence between the sextic and good
affine equations over `ℚ₂`. -/
theorem goodY_onCurve
    (x Y : N13EscapingDegreeOneSpread.Q₂)
    (hcurve :
      Y ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x) :
    N13GoodModelTwo.AffineEquation x (goodY x Y) := by
  have hf :
      N13GoodModelTwo.completedSextic x =
        N13EscapingDegreeOneSpread.Model.f.eval x := by
    simp [N13EscapingDegreeOneSpread.Model,
      N13Mumford.f, N13GoodModelTwo.completedSextic]
  have hs :=
    N13GoodModelTwo.completed_square_identity x (goodY x Y)
  have hround :
      2 * goodY x Y + N13GoodModelTwo.h x = Y := by
    exact pointY_goodY x Y
  rw [hround] at hs
  have hfour :
      (4 : N13EscapingDegreeOneSpread.Q₂) *
          ((goodY x Y) ^ 2 +
            N13GoodModelTwo.h x * goodY x Y -
            N13GoodModelTwo.rhs x) = 0 := by
    rw [hf, ← hcurve] at hs
    calc
      _ =
          (Y ^ 2 +
            4 * ((goodY x Y) ^ 2 +
              N13GoodModelTwo.h x * goodY x Y -
              N13GoodModelTwo.rhs x)) -
            Y ^ 2 := by ring
      _ = 0 := by rw [← hs, sub_self]
  have hres :
      (goodY x Y) ^ 2 +
          N13GoodModelTwo.h x * goodY x Y -
        N13GoodModelTwo.rhs x = 0 :=
    (mul_eq_zero.mp hfour).resolve_left (by norm_num)
  exact sub_eq_zero.mp hres

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- If the selected quadratic Padé graph splits over `ℚ` into two
distinct points and both points escape the affine integral chart, their
tensor point line is an explicit proper spread of the exact selected
two-adic graph. -/
theorem selectedGraph_has_pairLine_of_split_escape
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2)
    (x₁ x₂ : ℚ)
    (hfactor :
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u =
        (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂)
    (hx₁ :
      (N13ProperCurveReduction.ratToQ₂ x₁).valuation < 0)
    (hx₂ :
      (N13ProperCurveReduction.ratToQ₂ x₂).valuation < 0) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).u
          (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
            P).v := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  let x₁₂ : N13EscapingDegreeOneSpread.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x₁
  let x₂₂ : N13EscapingDegreeOneSpread.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x₂
  have hneq₂ : x₁₂ ≠ x₂₂ := by
    exact N13InfinityBaseChange.ratToQ₂_injective.ne hneq
  have hfactor₂ :
      D.u = (X - C x₁₂) * (X - C x₂₂) := by
    have hmap :=
      congrArg
        (Polynomial.map N13InfinityBaseChange.ratToQ₂)
        hfactor
    simpa [D, x₁₂, x₂₂,
      N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford]
      using hmap
  have hDdeg : D.u.natDegree = 2 := by
    change
      ((N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u.map N13InfinityBaseChange.ratToQ₂).natDegree = 2
    rw [
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u_monic.natDegree_map]
    exact
      (N13DegreeOneGraphPoint.normalizedGraphMumford_u_natDegree P).trans
        hdeg
  obtain ⟨hcurve₁, hcurve₂⟩ :=
    mumford_eval_onCurve_of_split D x₁₂ x₂₂ hfactor₂
  let y₁ := goodY x₁₂ (D.v.eval x₁₂)
  let y₂ := goodY x₂₂ (D.v.eval x₂₂)
  have hgood₁ :
      N13GoodModelTwo.AffineEquation x₁₂ y₁ :=
    goodY_onCurve x₁₂ (D.v.eval x₁₂) hcurve₁
  have hgood₂ :
      N13GoodModelTwo.AffineEquation x₂₂ y₂ :=
    goodY_onCurve x₂₂ (D.v.eval x₂₂) hcurve₂
  let L :=
    nonintegralPointPairLine
      x₁₂ y₁ x₂₂ y₂ hx₁ hgood₁ hx₂ hgood₂
  refine ⟨L, ?_⟩
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (nonintegralPointPairLine
          x₁₂ y₁ x₂₂ y₂ hx₁ hgood₁ hx₂ hgood₂).affineIdeal =
      _
  rw [map_nonintegralPointPairLine_eq_secantGraph
      x₁₂ y₁ x₂₂ y₂ hx₁ hgood₁ hx₂ hgood₂ hneq₂,
    pointY_goodY, pointY_goodY,
    ← mumford_v_eq_secant D hDdeg x₁₂ x₂₂ hneq₂,
    ← hfactor₂]

end

end MazurProof.N13TwoChartLineTensor


