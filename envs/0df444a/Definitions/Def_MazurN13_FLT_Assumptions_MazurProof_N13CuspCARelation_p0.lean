-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CuspCARelation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CuspCARelation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:39:20.062994+00:00
-- url     : https://prove2.me/theorems/8d679b92-fdd3-4890-bc36-c422a5a3b4ee
-- title:
--   FLT.Assumptions.MazurProof.N13CuspCARelation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CuspCARelation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CuspCARelation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Jacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordCantorReduction_p0

set_option autoImplicit false





set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section


open Polynomial
open scoped LaurentSeries nonZeroDivisors


namespace MazurProof.N13Arithmetic


private abbrev M13 : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ


private abbrev H13 :
    Subgroup (SexticMumford.OrientedFrac M13) :=
  (SexticMumford.principalOriented M13
    (N13Infinity.positiveInfinityOrder ℚ)).range


private abbrev Q13 : Type :=
  SexticMumford.OrientedFrac M13 ⧸ H13


/-- The cubic polynomial part of the positive infinity branch. -/
private def s13 : ℚ[X] :=
  N13MumfordInfinityBalance.sqrtInfinity


/-- The explicit rational function `Y + s(X) = Y - (-s(X))`. -/
def caFn13 : RatFun13ˣ :=
  SexticMumford.ySubFunctionUnit M13 (-s13)


private def cM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint C)


private def aM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint A)


private def tM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint T)


@[simp] private theorem cM13_u :
    cM13.u = (X : ℚ[X]) := by
  change X - Polynomial.C (0 : ℚ) = X
  simp


@[simp] private theorem cM13_v :
    cM13.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num


@[simp] private theorem cM13_nInf :
    cM13.nInf = 0 := by
  rfl


@[simp] private theorem aM13_u :
    aM13.u = (X + 1 : ℚ[X]) := by
  change X - Polynomial.C (-1 : ℚ) = X + 1
  simp


@[simp] private theorem aM13_v :
    aM13.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num


@[simp] private theorem aM13_nInf :
    aM13.nInf = 0 := by
  rfl


@[simp] private theorem tM13_nInf :
    tM13.nInf = 0 := by
  rfl


private def quarter13 : ℚ[X] :=
  Polynomial.C (1 / 4 : ℚ)


private theorem four_mul_quarter13 :
    (4 : ℚ[X]) * quarter13 = 1 := by
  change Polynomial.C (4 : ℚ) * Polynomial.C (1 / 4 : ℚ) = Polynomial.C (1 : ℚ)
  rw [← C_mul]
  norm_num


private theorem X_dvd_negs13_sub_one :
    (X : ℚ[X]) ∣ -s13 - (1 : ℚ[X]) := by
  refine ⟨-(X + 1) ^ 2, ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring


private theorem X_add_one_dvd_negs13_sub_one :
    (X + 1 : ℚ[X]) ∣ -s13 - (1 : ℚ[X]) := by
  refine ⟨-(X * (X + 1)), ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring


private theorem scaled_A_ideal :
    SexticMumford.mumfordIdeal M13
        (4 * (X + 1 : ℚ[X])) (-s13) =
      SexticMumford.mumfordIdeal M13
        (X + 1 : ℚ[X]) (-s13) := by
  apply SexticMumford.mumfordIdeal_eq_of_dvd_dvd
  · refine ⟨quarter13, ?_⟩
    calc
      (X + 1 : ℚ[X]) = 1 * (X + 1) := by ring
      _ = ((4 : ℚ[X]) * quarter13) * (X + 1) := by
        rw [four_mul_quarter13]
      _ = (4 * (X + 1)) * quarter13 := by ring
  · refine ⟨(4 : ℚ[X]), ?_⟩
    ring


private theorem ca_curve_factor :
    M13.f - (-s13) ^ 2 =
      (X : ℚ[X]) * (4 * (X + 1 : ℚ[X])) := by
  rw [neg_sq, N13Mumford.model_f]
  rw [show s13 =
      (N13MumfordInfinityBalance.sqrtInfinity : ℚ[X]) from rfl,
    N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq]
  ring


private theorem ca_bezout :
    ∃ a b c : ℚ[X],
      a * X + b * (2 * (-s13)) +
          c * (4 * (X + 1)) = 1 := by
  have hq :
      quarter13 * (4 : ℚ[X]) = 1 := by
    simpa [mul_comm] using four_mul_quarter13
  refine ⟨-1, 0, quarter13, ?_⟩
  calc
    (-1 : ℚ[X]) * X + 0 * (2 * (-s13)) +
          quarter13 * (4 * (X + 1)) =
        -X + (quarter13 * 4) * (X + 1) := by
          ring
    _ = -X + (X + 1) := by
      rw [hq, one_mul]
    _ = 1 := by ring


private theorem ca_point_ideal_mul :
    SexticMumford.mumfordIdeal M13
          cM13.toSemi.u cM13.toSemi.v *
        SexticMumford.mumfordIdeal M13
          aM13.toSemi.u aM13.toSemi.v =
      Ideal.span
        ({SexticMumford.ySubClass M13 (-s13)} :
          Set (N13Mumford.CoordinateRing ℚ)) := by
  simp only [SexticMumford.toSemi_u, SexticMumford.toSemi_v,
    cM13_u, cM13_v, aM13_u, aM13_v]
  calc
    SexticMumford.mumfordIdeal M13 X 1 *
          SexticMumford.mumfordIdeal M13 (X + 1) 1 =
        SexticMumford.mumfordIdeal M13 X (-s13) *
          SexticMumford.mumfordIdeal M13 (X + 1) (-s13) := by
            rw [← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 X 1 (-s13) X_dvd_negs13_sub_one,
              ← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 (X + 1) 1 (-s13)
                    X_add_one_dvd_negs13_sub_one]
    _ =
        SexticMumford.mumfordIdeal M13 X (-s13) *
          SexticMumford.mumfordIdeal M13
            (4 * (X + 1)) (-s13) := by
              rw [scaled_A_ideal]
    _ =
        Ideal.span
          ({SexticMumford.ySubClass M13 (-s13)} :
            Set (N13Mumford.CoordinateRing ℚ)) := by
              exact SexticMumford.mumfordIdeal_mul_cantor
                M13
                (X : ℚ[X])
                (4 * (X + 1 : ℚ[X]))
                (-s13)
                ca_curve_factor
                ca_bezout


private theorem caFn13_finite_principal :
    SexticMumford.mumfordIdealUnit M13 cM13.toSemi *
        SexticMumford.mumfordIdealUnit M13 aM13.toSemi =
      toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) caFn13 := by
  apply Units.ext
  simp only [Units.val_mul,
    SexticMumford.coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, caFn13,
    SexticMumford.coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    ca_point_ideal_mul,
    FractionalIdeal.coeIdeal_span_singleton]


/-! ## Exact order at the positive infinity branch -/


private def z13 : N13Mumford.SemiMumford ℚ :=
  (SexticMumford.zero M13).toSemi


private theorem z13_deg :
    z13.u.natDegree ≤ 2 := by
  simp [z13]


private theorem minusLift_z13 :
    N13MumfordInfinityBalance.minusLift z13 = -s13 := by
  simp [z13, s13,
    N13MumfordInfinityBalance.minusLift,
    N13MumfordInfinityBalance.minusRemainder]


private theorem ca_positive_order :
    (N13Infinity.coordinateToLaurent ℚ
      (SexticMumford.ySubClass M13 (-s13))).order = -3 := by
  have h :=
    N13MumfordInfinityBalance.minusYSub_plus_order
      z13 z13_deg
  rw [minusLift_z13] at h
  exact h


private theorem caFn13_ordPlus :
    Multiplicative.toAdd
        ((N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13) =
      -3 := by
  rw [caFn13,
    N13MumfordInfinityBalance.ordPlus_ySubFunctionUnit]
  exact ca_positive_order


/-! ## Pass the principal divisor to the oriented Picard quotient -/


private theorem tM13_idealUnit_one :
    SexticMumford.mumfordIdealUnit M13 tM13.toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal M13 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ)) = 1
  have hz := SexticMumford.zero_mumfordIdeal M13
  change SexticMumford.mumfordIdeal M13 1 0 = ⊤ at hz
  rw [hz]
  rfl


private theorem ca_mumfordRaw_relation :
    SexticMumford.mumfordRaw M13 cM13 *
        SexticMumford.mumfordRaw M13 aM13 *
          SexticMumford.mumfordRaw M13 tM13 =
      SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) caFn13 := by
  apply Prod.ext
  · change
      SexticMumford.mumfordIdealUnit M13 cM13.toSemi *
          SexticMumford.mumfordIdealUnit M13 aM13.toSemi *
            SexticMumford.mumfordIdealUnit M13 tM13.toSemi =
        toPrincipalIdeal
            (N13Mumford.CoordinateRing ℚ)
            (N13Mumford.FunctionField ℚ) caFn13
    rw [tM13_idealUnit_one, mul_one]
    exact caFn13_finite_principal
  · have hOrd :
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13 =
          Multiplicative.ofAdd (-3 : ℤ) := by
      simpa using
        congrArg Multiplicative.ofAdd caFn13_ordPlus
    change
      Multiplicative.ofAdd ((cM13.nInf : ℤ) - 1) *
          Multiplicative.ofAdd ((aM13.nInf : ℤ) - 1) *
            Multiplicative.ofAdd ((tM13.nInf : ℤ) - 1) =
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus caFn13
    rw [hOrd, cM13_nInf, aM13_nInf, tM13_nInf]
    change (-1 : ℤ) + (-1) + (-1) = -3
    norm_num


private def raw13 (P : Point13) :
    SexticMumford.OrientedFrac M13 :=
  SexticMumford.mumfordRaw M13
    (SexticMumford.pointMumford M13
      (point13EquivCurvePoint P))


private theorem ca_principal_mk_eq_one :
    QuotientGroup.mk' H13
        (SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) caFn13) =
      1 := by
  rw [QuotientGroup.mk'_apply]
  exact
    (QuotientGroup.eq_one_iff
      (SexticMumford.principalOriented M13
        (N13Infinity.positiveInfinityOrder ℚ) caFn13)).2
      (MonoidHom.mem_range.mpr ⟨caFn13, rfl⟩)


private theorem ca_quotient_relation :
    QuotientGroup.mk' H13 (raw13 C) *
        QuotientGroup.mk' H13 (raw13 A) *
          QuotientGroup.mk' H13 (raw13 T) = (1 : Q13) := by
  have h : raw13 C * raw13 A * raw13 T =
      SexticMumford.principalOriented M13
        (N13Infinity.positiveInfinityOrder ℚ) caFn13 :=
    ca_mumfordRaw_relation
  rw [← map_mul, ← map_mul, h]
  exact ca_principal_mk_eq_one


private theorem AJ13_eq_raw (P : Point13) :
    AJ13 P =
      Additive.ofMul (QuotientGroup.mk' H13 (raw13 P)) := by
  rfl


private theorem ofMul_add13 (a b : Q13) :
    (Additive.ofMul a : J13) + Additive.ofMul b =
      Additive.ofMul (a * b) := by
  rfl


/-- The cusp relation supplied by the principal divisor
    `div(Y+s) = C + A + T - 3O`, with `C = (0,1)`, `A = (-1,1)` the
    hyperelliptic conjugates of `D`, `B`. -/
theorem AJ13_C_add_A_add_T_eq_zero :
    AJ13 C + AJ13 A + AJ13 T = 0 := by
  rw [AJ13_eq_raw C, AJ13_eq_raw A, AJ13_eq_raw T,
    ofMul_add13, ofMul_add13, ca_quotient_relation]
  rfl


/-- Equivalently `AJ13 C + AJ13 A = -AJ13 T`: the class `O - T`
    (the degree-zero `nInf = 2` class relative to the anchor) is
    represented by `C + A - 2O`. -/
theorem AJ13_C_add_A_eq_neg_T :
    AJ13 C + AJ13 A = -AJ13 T :=
  eq_neg_of_add_eq_zero_left AJ13_C_add_A_add_T_eq_zero


end MazurProof.N13Arithmetic


