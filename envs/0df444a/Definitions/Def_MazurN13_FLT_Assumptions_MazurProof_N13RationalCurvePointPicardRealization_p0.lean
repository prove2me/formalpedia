-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalCurvePointPicardRealization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RationalCurvePointPicardRealization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:29:41.543947+00:00
-- url     : https://prove2.me/theorems/a75fa8ec-c913-4af3-a7c9-ccdd6b924947
-- title:
--   FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityPointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralPointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EscapingPointPicardRealization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpreadRationalPointReduction_p0

set_option autoImplicit false




/-!
# Two-fibre Picard realization of every rational N13 curve point

The projective N13 curve has two infinity points and an affine chart.  The
two infinity points are realized by their integral chart lines.  An affine
rational point is first transported to the good two-adic model and then
realized by the integral or escaping point line according to the valuation
of its first coordinate.

The package below records both identifications needed for specialization:
its generic class is the rational Abel--Jacobi class after base change to
`ℚ₂`, and its special class is the anchored Abel class of the point's proper
reduction.  Thus this file proves pointwise existence of actual two-fibre
data; it does not postulate a specialization map on arbitrary Picard classes.
-/

namespace MazurProof.N13RationalCurvePointPicardRealization

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Rational points of the projective N13 sextic. -/
abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint

/-- Complete chartwise data realizing one rational point on both fibres. -/
structure Data (P : RationalCurvePoint) where
  realization : N13TwoChartPicardRealization.Data
  generic_eq :
    realization.toGenericPic =
      N13InfinityBaseChange.picMapRatToQ₂
        (N13RationalPointEndgame.rationalAbel P)
  special_eq :
    realization.toSpecialPic =
      N13RationalPointEndgame.specialPointClass
        (N13ProperCurveReduction.reduceCurve P)

/-!
## The two points at infinity

The chosen positive point at infinity is the Abel--Jacobi base point, whereas
the negative point contributes the distinguished infinity Mumford class.  The
existing integral chart lines realize these two classes and specialize to the
anchor and cusp, respectively.
-/

/-- Balanced Mumford representatives are equal when their three data fields
agree; all remaining structure fields are propositions. -/
private theorem mumford_eq_of_u_v_nInf
    {D E : SexticMumford.Mumford N13TwoChartPicardRealization.Model}
    (hu : D.u = E.u)
    (hv : D.v = E.v)
    (hn : D.nInf = E.nInf) :
    D = E := by
  cases D
  cases E
  simp_all

/-- Two-fibre realization of the positive infinity base point. -/
def infinityPlusData : Data .infinityPlus where
  realization :=
    N13InfinityPointPicardRealization.infinityPlusData
  generic_eq := by
    rw [N13InfinityPointPicardRealization.infinityPlusData_toGenericPic]
    simp [N13RationalPointEndgame.rationalAbel,
      N13MumfordAbelJacobi.abelJacobi, SexticMumford.pointMumford]
  special_eq := by
    rw [N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic]
    change
      N13RationalPointEndgame.specialPointClass
          N13InfinityLineSpecialRestriction.specialInfinityPlusPoint =
        N13RationalPointEndgame.specialPointClass
          N13RationalPointEndgame.specialAnchor
    exact congrArg N13RationalPointEndgame.specialPointClass
      N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor

/-- Two-fibre realization of the negative infinity point. -/
def infinityMinusData : Data .infinityMinus where
  realization :=
    N13InfinityPointPicardRealization.infinityMinusData
  generic_eq := by
    rw [N13InfinityPointPicardRealization.infinityMinusData_toGenericPic]
    rw [show N13RationalPointEndgame.rationalAbel
          (.infinityMinus : RationalCurvePoint) =
        SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.infinityMinusMumford
            (N13Mumford.model ℚ)) by rfl,
      N13InfinityBaseChange.picMapRatToQ₂_classOf]
    congr 1
    apply mumford_eq_of_u_v_nInf <;>
      simp [SexticMumford.infinityMinusMumford]
  special_eq := by
    rw [N13InfinityPointPicardRealization.infinityMinusData_toSpecialPic]
    change
      N13RationalPointEndgame.specialPointClass
          N13InfinityLineSpecialRestriction.specialInfinityMinusPoint =
        N13RationalPointEndgame.specialPointClass
          (N13SpecialCuspReduction.specialCuspEquiv
            N13Mumford.Cusp13.infinityMinus)
    exact congrArg N13RationalPointEndgame.specialPointClass
      N13InfinityLineSpecialRestriction.specialInfinityMinusPoint_eq_specialCusp

/-!
## Affine rational points

The sextic coordinates over `ℚ` are first sent to the good two-adic model by
the completion-of-the-square coordinate change.  The valuation of `x` then
selects one of the two proper integral chart constructions.  In either case we
compare the resulting degree-one Mumford representative componentwise with
the base change of the original rational point representative.
-/

/-- Two-fibre realization of an affine rational point whose two-adic first
coordinate is integral. -/
def integralAffineData
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1) :
    Data (.affine X Y hcurve) := by
  -- Rewrite the input equation in the sextic form expected by the good-model
  -- coordinate change; this changes presentation, not the rational point.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  -- The good model keeps `x` and replaces `Y` by the completed-square
  -- ordinate.  These are the coordinates whose integrality controls the
  -- proper reduction chart.
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  -- In the integral branch the two-adic point lifts to an integral point of
  -- the affine spread, whose anchored line supplies both chart ideals.
  let P₂ : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  let R : N13TwoChartPicardRealization.Data :=
    N13IntegralPointPicardRealization.data P₂
  let sourceD : N13Mumford.Mumford ℚ :=
    SexticMumford.pointMumford
      (N13Mumford.model ℚ) (.affine X Y hcurve)
  let targetD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    N13IntegralPointPicardRealization.degreeOneMumford P₂
  let mappedD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    sourceD.mapCoeffs
      N13InfinityBaseChange.ratToQ₂
      N13InfinityBaseChange.ratToQ₂_injective
      (N13InfinityBaseChange.map_n13_f
        N13InfinityBaseChange.ratToQ₂)
  -- Undoing the good-model ordinate change recovers the original sextic
  -- ordinate after base change.  This identity is the only non-definitional
  -- part of comparing the two point representatives.
  have hsexticY :
      N13IntegralAffinePointSpread.sexticY P₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [P₂, N13ProperCurveReduction.integralAffineLift,
      x₂, y₂, N13IntegralAffinePointSpread.sexticY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- Equality of the affine graph polynomial `u`, ordinate polynomial `v`,
  -- and infinity orientation identifies the entire balanced representative.
  have hu :
      targetD.u = mappedD.u := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      P₂, N13ProperCurveReduction.integralAffineLift, x₂]
  have hv :
      targetD.v = mappedD.v := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      hsexticY, N13ProperCurveReduction.ratToQ₂]
  have hn :
      targetD.nInf = mappedD.nInf := by
    simp [targetD, mappedD, sourceD,
      N13IntegralPointPicardRealization.degreeOneMumford,
      N13IntegralAffinePointSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
  have htarget :
      targetD = mappedD :=
    mumford_eq_of_u_v_nInf hu hv hn
  refine
    { realization := R
      generic_eq := ?_
      special_eq := ?_ }
  · rw [show R.toGenericPic =
        SexticMumford.classOf
          N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder
            N13ProperCurveReduction.Q₂)
          targetD by
        exact N13IntegralPointPicardRealization.data_toGenericPic_eq_classOf P₂]
    rw [htarget]
    exact
      (N13InfinityBaseChange.picMapRatToQ₂_classOf sourceD).symm
  · change
      N13RationalPointEndgame.specialPointClass
          (N13IntegralAffinePointSpecialClass.reducedPoint P₂) =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve (.affine X Y hcurve))
    -- The total reduction function branches on the same norm condition as
    -- this construction, so its special point is literally the integral
    -- affine reduction already carried by `R`.
    have hreduce :
        N13ProperCurveReduction.reduceCurve (.affine X Y hcurve) =
          N13ProperCurveReduction.reduceIntegralAffine
            x₂ y₂ hx hgood := by
      simp only [N13ProperCurveReduction.reduceCurve]
      unfold N13ProperCurveReduction.reduceAffine
      dsimp only
      split
      · rfl
      · rename_i hnot
        exact (hnot hx).elim
    rw [hreduce]
    congr 1

/-- Two-fibre realization of an affine rational point whose first coordinate
escapes the two-adic affine chart. -/
def escapingAffineData
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hxval :
      (N13ProperCurveReduction.ratToQ₂ X).valuation < 0) :
    Data (.affine X Y hcurve) := by
  -- As in the integral branch, first express the rational curve equation in
  -- the sextic presentation used by the good two-adic model.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  -- The completed-square coordinates lie on the good model even though `x₂`
  -- is outside its affine integral chart.
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  let R : N13TwoChartPicardRealization.Data :=
    N13EscapingPointPicardRealization.data x₂ y₂ hxval hgood
  let sourceD : N13Mumford.Mumford ℚ :=
    SexticMumford.pointMumford
      (N13Mumford.model ℚ) (.affine X Y hcurve)
  let targetD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    N13EscapingPointPicardRealization.degreeOneMumford
      x₂ y₂ hgood
  let mappedD : N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
    sourceD.mapCoeffs
      N13InfinityBaseChange.ratToQ₂
      N13InfinityBaseChange.ratToQ₂_injective
      (N13InfinityBaseChange.map_n13_f
        N13InfinityBaseChange.ratToQ₂)
  -- The escaping-chart ordinate is defined by reversing the same coordinate
  -- change, hence it agrees with the original rational `Y` over `ℚ₂`.
  have hpointY :
      N13EscapingDegreeOneSpread.pointY x₂ y₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [x₂, y₂, N13EscapingDegreeOneSpread.pointY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- The escaping line still represents the ordinary degree-one point ideal
  -- on the generic affine chart; only its integral extension uses infinity.
  have hu : targetD.u = mappedD.u := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford, x₂]
  have hv : targetD.v = mappedD.v := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford,
      hpointY, N13ProperCurveReduction.ratToQ₂]
  have hn : targetD.nInf = mappedD.nInf := by
    simp [targetD, mappedD, sourceD,
      N13EscapingPointPicardRealization.degreeOneMumford,
      N13EscapingDegreeOneSpread.curvePoint,
      SexticMumford.pointMumford,
      SexticMumford.affinePointMumford]
  have htarget : targetD = mappedD :=
    mumford_eq_of_u_v_nInf hu hv hn
  -- Negative valuation is exactly the negation of membership in the
  -- integral norm ball, so the global reduction function must take its
  -- nonintegral branch.
  have hnot : ¬ ‖x₂‖ ≤ 1 := by
    intro hnorm
    have hnonneg : 0 ≤ x₂.valuation :=
      (Padic.norm_le_one_iff_val_nonneg x₂).mp hnorm
    exact (not_lt_of_ge hnonneg) hxval
  refine
    { realization := R
      generic_eq := ?_
      special_eq := ?_ }
  · rw [show R.toGenericPic =
        SexticMumford.classOf
          N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder
            N13ProperCurveReduction.Q₂)
          targetD by
        exact
          N13EscapingPointPicardRealization.data_toGenericPic_eq_classOf
            x₂ y₂ hxval hgood]
    rw [htarget]
    exact
      (N13InfinityBaseChange.picMapRatToQ₂_classOf sourceD).symm
  · change
      N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceNonintegralAffine
            x₂ y₂ hxval hgood) =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve (.affine X Y hcurve))
    have hreduce :
        N13ProperCurveReduction.reduceCurve (.affine X Y hcurve) =
          N13ProperCurveReduction.reduceNonintegralAffine
            x₂ y₂ hxval hgood := by
      simp only [N13ProperCurveReduction.reduceCurve]
      unfold N13ProperCurveReduction.reduceAffine
      dsimp only
      split
      · rename_i hintegral
        exact (hnot hintegral).elim
      · rfl
    rw [hreduce]

/-- Every rational point on the projective N13 curve has a proper line whose
generic and special classes are exactly its Abel classes on the two fibres. -/
def data (P : RationalCurvePoint) : Data P := by
  cases P with
  | infinityPlus =>
      exact infinityPlusData
  | infinityMinus =>
      exact infinityMinusData
  | affine X Y hcurve =>
      -- The two-adic norm dichotomy is exhaustive and matches the two
      -- integral models proved above.
      by_cases hx :
          ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1
      · exact integralAffineData X Y hcurve hx
      · have hxval :
            (N13ProperCurveReduction.ratToQ₂ X).valuation < 0 :=
          lt_of_not_ge
            ((Padic.norm_le_one_iff_val_nonneg
              (N13ProperCurveReduction.ratToQ₂ X)).not.mp hx)
        exact escapingAffineData X Y hcurve hxval

/-!
## Literal generic ideals

The preceding constructions identify generic Picard classes.  Global spread
existence needs the stronger statement that the affine ideal itself is the
Mumford ideal obtained by coefficient extension.  The following two lemmas
expose that stronger invariant for the integral and escaping branches.
-/

/-- Coefficient extension of the balanced Mumford representative attached to
a rational curve point. -/
def mappedPointMumford (P : RationalCurvePoint) :
    N13Mumford.Mumford N13ProperCurveReduction.Q₂ :=
  (SexticMumford.pointMumford (N13Mumford.model ℚ) P).mapCoeffs
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- The integral affine-point realization retains the literal mapped Mumford
ideal, not only its class in the oriented Picard quotient. -/
theorem integralAffineData_map_affineIdeal
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (integralAffineData X Y hcurve hx).realization.charts.affineIdeal =
      SexticMumford.mumfordIdeal
        N13TwoChartPicardRealization.Model
        (mappedPointMumford (.affine X Y hcurve)).u
        (mappedPointMumford (.affine X Y hcurve)).v := by
  -- Reconstruct exactly the good-model point used inside
  -- `integralAffineData`; the theorem then reduces to the existing chart-line
  -- computation for this integral lift.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  let P₂ : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  -- The round-trip formula aligns the good-model ordinate with the original
  -- sextic ordinate, allowing a literal comparison of Mumford data.
  have hsexticY :
      N13IntegralAffinePointSpread.sexticY P₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [P₂, N13ProperCurveReduction.integralAffineLift,
      x₂, y₂, N13IntegralAffinePointSpread.sexticY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- Compare `u`, `v`, and `nInf` rather than quotient classes: this preserves
  -- the exact ideal needed when the line is later reoriented.
  have htarget :
      N13IntegralPointPicardRealization.degreeOneMumford P₂ =
        mappedPointMumford (.affine X Y hcurve) := by
    apply mumford_eq_of_u_v_nInf
    · simp [N13IntegralPointPicardRealization.degreeOneMumford,
        N13IntegralAffinePointSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford, P₂,
        N13ProperCurveReduction.integralAffineLift, x₂]
    · simp [N13IntegralPointPicardRealization.degreeOneMumford,
        N13IntegralAffinePointSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford, hsexticY,
        N13ProperCurveReduction.ratToQ₂]
    · simp [N13IntegralPointPicardRealization.degreeOneMumford,
        N13IntegralAffinePointSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford]
  change
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13FiniteAffinePointInfinityClosure.anchoredPointLine P₂).affineIdeal =
      _
  rw [N13IntegralPointPicardRealization.map_anchoredPointLine_affineIdeal]
  rw [htarget]

/-- The rational integral-point realization retains the vertical-saturation
certificate of its anchored integral affine line. -/
theorem integralAffineData_affineVerticallySaturated
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hx : ‖N13ProperCurveReduction.ratToQ₂ X‖ ≤ 1) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (integralAffineData X Y hcurve hx).realization.charts := by
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  let P₂ : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x₂ y₂ hx hgood
  change
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffinePointInfinityClosure.anchoredPointLine P₂)
  exact
    N13IntegralPointPicardRealization.anchoredPointLine_affineVerticallySaturated P₂

/-- The escaping affine-point realization retains the same literal mapped
Mumford ideal on the generic affine chart. -/
theorem escapingAffineData_map_affineIdeal
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hxval :
      (N13ProperCurveReduction.ratToQ₂ X).valuation < 0) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (escapingAffineData X Y hcurve hxval).realization.charts.affineIdeal =
      SexticMumford.mumfordIdeal
        N13TwoChartPicardRealization.Model
        (mappedPointMumford (.affine X Y hcurve)).u
        (mappedPointMumford (.affine X Y hcurve)).v := by
  -- Reconstruct the escaping good-model point appearing in
  -- `escapingAffineData`, keeping the negative-valuation hypothesis fixed.
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  -- Reversing the completed-square change again identifies the escaping
  -- point ordinate with the base-changed rational ordinate.
  have hpointY :
      N13EscapingDegreeOneSpread.pointY x₂ y₂ =
        N13ProperCurveReduction.ratToQ₂ Y := by
    have hround :=
      congrArg N13ProperCurveReduction.ratToQ₂
        (N13GoodModelTwo.sextic_good_y_roundtrip X Y)
    simpa [x₂, y₂, N13EscapingDegreeOneSpread.pointY,
      N13ProperCurveReduction.ratToQ₂,
      N13GoodModelTwo.h] using hround
  -- Componentwise equality shows that the generic affine ideal is unchanged
  -- by the alternative integral chart used to close the point at infinity.
  have htarget :
      N13EscapingPointPicardRealization.degreeOneMumford
          x₂ y₂ hgood =
        mappedPointMumford (.affine X Y hcurve) := by
    apply mumford_eq_of_u_v_nInf
    · simp [N13EscapingPointPicardRealization.degreeOneMumford,
        N13EscapingDegreeOneSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford, x₂]
    · simp [N13EscapingPointPicardRealization.degreeOneMumford,
        N13EscapingDegreeOneSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford, hpointY,
        N13ProperCurveReduction.ratToQ₂]
    · simp [N13EscapingPointPicardRealization.degreeOneMumford,
        N13EscapingDegreeOneSpread.curvePoint,
        SexticMumford.pointMumford,
        SexticMumford.affinePointMumford,
        mappedPointMumford]
  change
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (N13EscapingPointSpecialRestriction.anchoredPointLine
          x₂ y₂ hxval hgood).affineIdeal =
      _
  rw [N13EscapingPointPicardRealization.map_anchoredPointLine_affineIdeal]
  rw [htarget]

/-- The rational escaping-point realization retains the vertical-saturation
certificate transported from its infinity-chart point line. -/
theorem escapingAffineData_affineVerticallySaturated
    (X Y : ℚ)
    (hcurve : Y ^ 2 = (N13Mumford.model ℚ).f.eval X)
    (hxval :
      (N13ProperCurveReduction.ratToQ₂ X).valuation < 0) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (escapingAffineData X Y hcurve hxval).realization.charts := by
  have hC13 : N13CurveModel.C13SexticEq X Y := by
    rw [N13CurveModel.C13SexticEq,
      ← N13Mumford.f_eval_eq_sexticF13]
    exact hcurve
  let x₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂ X
  let y₂ : N13ProperCurveReduction.Q₂ :=
    N13ProperCurveReduction.ratToQ₂
      (N13GoodModelTwo.sexticToGoodY X Y)
  have hgood : N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13ProperCurveReduction.map_good_equation hC13
  change
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13EscapingPointSpecialRestriction.anchoredPointLine
        x₂ y₂ hxval hgood)
  exact
    N13EscapingPointPicardRealization.anchoredPointLine_affineVerticallySaturated
      x₂ y₂ hxval hgood

/-!
## Relation-first spread lines

A spread line remembers the rational Picard class it represents in addition
to its two-fibre geometric realization.  This makes the eventual reduction
classifier a statement about equality of concrete specializations, while the
pointwise constructions above supply Abel--Jacobi compatibility directly.
-/

/-- A relation-first spread line together with the rational generic class it
realizes after base change to `ℚ₂`. -/
structure SpreadLine where
  rationalClass : N13RationalPointEndgame.G
  realization : N13TwoChartPicardRealization.Data
  generic_eq :
    realization.toGenericPic =
      N13InfinityBaseChange.picMapRatToQ₂ rationalClass

/-- The spread line canonically attached to a rational curve point. -/
def pointSpreadLine (P : RationalCurvePoint) : SpreadLine where
  rationalClass := N13RationalPointEndgame.rationalAbel P
  realization := (data P).realization
  generic_eq := (data P).generic_eq

/-- The generic class of a rational spread line modulo a proposed reduction
kernel. -/
def genericClass
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (L : SpreadLine) :
    N13RationalPointEndgame.G ⧸ kernel :=
  QuotientAddGroup.mk' kernel L.rationalClass

/-- The literal special Abel class of a rational spread line. -/
def specialClass (L : SpreadLine) :
    N13RationalPointEndgame.SpecialSet :=
  L.realization.toSpecialPic

/-- Construct the relation-first classifier once existence for all rational
classes and equality reflection for the concrete spread lines are supplied.

The two hypotheses are the remaining global specialization statements; the
rational-point compatibility field is no longer among them. -/
def spreadData
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (exists_spread :
      ∀ P : N13RationalPointEndgame.G,
        ∃ L : SpreadLine,
          genericClass kernel L = QuotientAddGroup.mk' kernel P)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        specialClass L = specialClass M ↔
          genericClass kernel L = genericClass kernel M) :
    N13SpreadClassifier.SpreadData
      N13RationalPointEndgame.G
      N13RationalPointEndgame.SpecialSet
      SpreadLine where
  kernel := kernel
  genericClass := genericClass kernel
  specialClass := specialClass
  exists_spread := exists_spread
  class_eq_iff := class_eq_iff

/-- The pointwise realizations discharge `abel_reduces` automatically for
the concrete rational-line classifier.  Only its global existence and
class-equality reflection hypotheses remain. -/
def rationalPointReductionData
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (exists_spread :
      ∀ P : N13RationalPointEndgame.G,
        ∃ L : SpreadLine,
          genericClass kernel L = QuotientAddGroup.mk' kernel P)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        specialClass L = specialClass M ↔
          genericClass kernel L = genericClass kernel M) :
    N13SpreadRationalPointReduction.Data SpreadLine where
  spread := spreadData kernel exists_spread class_eq_iff
  abel_reduces := by
    intro P
    -- The canonical point line has the required generic quotient class by
    -- construction, and `Data.special_eq` identifies its literal special
    -- divisor with proper reduction of the same rational point.
    exact
      ⟨pointSpreadLine P, rfl, (data P).special_eq⟩

end

end MazurProof.N13RationalCurvePointPicardRealization


