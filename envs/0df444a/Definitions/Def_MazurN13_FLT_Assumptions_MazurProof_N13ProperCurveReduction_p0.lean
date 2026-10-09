-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ProperCurveReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:29:02.115972+00:00
-- url     : https://prove2.me/theorems/1265c27d-0b3b-463a-a835-c4b961877102
-- title:
--   FLT.Assumptions.MazurProof.N13ProperCurveReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ProperCurveReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ProperCurveReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalPointEndgame_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogRegimes_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0

set_option autoImplicit false




/-!
# Proper two-chart reduction of N13 curve points at two

Rational points on the sextic are first transported to the generalized
hyperelliptic equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`.

If `x` is integral, its monic equation makes `y` integral and the point
reduces on the affine chart.  If `x` is nonintegral, put `t = x⁻¹` and
`v = t³y`; then the monic infinity-chart equation makes `v` integral,
while positive valuation of `t` forces its residue to be zero.  Thus the
construction is proper and genuinely uses both charts.

The final theorem identifies the reductions of the six rational cusps
with the previously constructed six-point special-fibre equivalence.
No point enumeration is used.
-/

namespace MazurProof.N13ProperCurveReduction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type := ℚ_[2]
abbrev Z₂ : Type := ℤ_[2]
abbrev F₂ : Type := ZMod 2

abbrev RationalCurvePoint : Type :=
  N13RationalPointEndgame.RationalCurvePoint

abbrev SpecialCurvePoint : Type :=
  N13RationalPointEndgame.SpecialCurvePoint

def ratToQ₂ : ℚ →+* Q₂ :=
  N13InfinityBaseChange.ratToQ₂

theorem norm_le_one_of_quadratic
    (a b y : Q₂)
    (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1)
    (h : y ^ 2 + a * y = b) :
    ‖y‖ ≤ 1 := by
  by_contra hy
  have hy1 : 1 < ‖y‖ := lt_of_not_ge hy
  have hay : ‖a * y‖ ≤ ‖y‖ := by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ha (norm_nonneg y)
  have hylt : ‖y‖ < ‖y ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hsmall : ‖a * y‖ < ‖y ^ 2‖ :=
    lt_of_le_of_lt hay hylt
  have hsum :
      ‖y ^ 2 + a * y‖ = ‖y ^ 2‖ := by
    rw [Padic.add_eq_max_of_ne (ne_of_gt hsmall),
      max_eq_left (le_of_lt hsmall)]
  have hbig : 1 < ‖b‖ := by
    rw [← h, hsum]
    exact hy1.trans hylt
  exact (not_lt_of_ge hb) hbig

theorem map_good_equation
    {X Y : ℚ} (hcurve : N13CurveModel.C13SexticEq X Y) :
    N13GoodModelTwo.AffineEquation
      (ratToQ₂ X)
      (ratToQ₂ (N13GoodModelTwo.sexticToGoodY X Y)) := by
  have hgood := N13GoodModelTwo.sextic_to_good hcurve
  simpa [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h,
    N13GoodModelTwo.rhs, ratToQ₂] using congrArg ratToQ₂ hgood

def integralAffineLift
    (x y : Q₂)
    (hx : ‖x‖ ≤ 1)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    {p : Z₂ × Z₂ //
      N13GoodModelTwo.AffineEquation p.1 p.2} := by
  let xi : Z₂ := ⟨x, hx⟩
  have ha :
      ‖(N13GoodModelTwo.h xi : Q₂)‖ ≤ 1 :=
    by
      change ‖((↑(N13GoodModelTwo.h xi)) : Q₂)‖ ≤ 1
      exact PadicInt.norm_le_one _
  have hb :
      ‖(N13GoodModelTwo.rhs xi : Q₂)‖ ≤ 1 :=
    by
      change ‖((↑(N13GoodModelTwo.rhs xi)) : Q₂)‖ ≤ 1
      exact PadicInt.norm_le_one _
  have hxy' :
      y ^ 2 + (N13GoodModelTwo.h xi : Q₂) * y =
        (N13GoodModelTwo.rhs xi : Q₂) := by
    simpa [xi, N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs] using hxy
  let yi : Z₂ :=
    ⟨y, norm_le_one_of_quadratic
      (N13GoodModelTwo.h xi : Q₂)
      (N13GoodModelTwo.rhs xi : Q₂) y ha hb hxy'⟩
  refine ⟨(xi, yi), ?_⟩
  exact Subtype.coe_injective (by
    push_cast
    simpa [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs, yi] using hxy')

def reduceIntegralAffine
    (x y : Q₂)
    (hx : ‖x‖ ≤ 1)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SpecialCurvePoint := by
  let P := integralAffineLift x y hx hxy
  exact Sum.inl ⟨
    (PadicInt.toZMod P.1.1, PadicInt.toZMod P.1.2),
    by
      simpa [N13GoodModelTwo.AffineEquation,
        N13GoodModelTwo.h, N13GoodModelTwo.rhs] using
        congrArg (PadicInt.toZMod (p := 2)) P.2⟩

def nonintegralInfinityLift
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    {p : Z₂ × Z₂ //
      N13GoodModelTwo.InfinityChartEquation p.1 p.2} := by
  let ti : Z₂ :=
    N13LocalDlogRegimes.inverseIntegralPart x hx
  let v : Q₂ := (ti : Q₂) ^ 3 * y
  have hx0 : x ≠ 0 :=
    N13LocalDlogRegimes.nonintegral_coordinate_ne_zero x hx
  have hxt : x * (ti : Q₂) = 1 := by
    simpa [ti, N13LocalDlogRegimes.inverseIntegralPart] using
      mul_inv_cancel₀ hx0
  have hyrel : x ^ 3 * v = y := by
    calc
      x ^ 3 * v = x ^ 3 * (x⁻¹ ^ 3 * y) := by
        simp [v, ti, N13LocalDlogRegimes.inverseIntegralPart]
      _ = (x * x⁻¹) ^ 3 * y := by rw [mul_pow, mul_assoc]
      _ = y := by rw [mul_inv_cancel₀ hx0, one_pow, one_mul]
  have hinf :
      N13GoodModelTwo.InfinityChartEquation (ti : Q₂) v := by
    apply (N13GoodModelTwo.affine_iff_infinity_on_overlap hxt).mp
    simpa only [hyrel] using hxy
  have ha :
      ‖((1 + ti ^ 2 + ti ^ 3 : Z₂) : Q₂)‖ ≤ 1 := by
    exact PadicInt.norm_le_one _
  have hb :
      ‖((ti + ti ^ 2 : Z₂) : Q₂)‖ ≤ 1 := by
    exact PadicInt.norm_le_one _
  have hv :
      ‖v‖ ≤ 1 := by
    apply norm_le_one_of_quadratic
      ((1 + ti ^ 2 + ti ^ 3 : Z₂) : Q₂)
      ((ti + ti ^ 2 : Z₂) : Q₂) v ha hb
    simpa [N13GoodModelTwo.InfinityChartEquation] using hinf
  let vi : Z₂ := ⟨v, hv⟩
  refine ⟨(ti, vi), ?_⟩
  exact Subtype.coe_injective (by
    push_cast
    simpa [N13GoodModelTwo.InfinityChartEquation, vi] using hinf)

def reduceNonintegralAffine
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SpecialCurvePoint := by
  let P := nonintegralInfinityLift x y hx hxy
  have htzero :
      PadicInt.toZMod P.1.1 = 0 := by
    change PadicInt.toZMod
      (N13LocalDlogRegimes.inverseIntegralPart x hx) = 0
    exact
      N13LocalDlogRegimes.inverseIntegralPart_residue_eq_zero x hx
  exact Sum.inr ⟨PadicInt.toZMod P.1.2, by
    have hred :=
      congrArg (PadicInt.toZMod (p := 2)) P.2
    simpa [N13GoodModelTwo.InfinityChartEquation, htzero] using hred⟩

def reduceAffine
    (X Y : ℚ) (hcurve : N13CurveModel.C13SexticEq X Y) :
    SpecialCurvePoint := by
  let x : Q₂ := ratToQ₂ X
  let y : Q₂ :=
    ratToQ₂ (N13GoodModelTwo.sexticToGoodY X Y)
  have hxy : N13GoodModelTwo.AffineEquation x y := by
    exact map_good_equation hcurve
  by_cases hx : ‖x‖ ≤ 1
  · exact reduceIntegralAffine x y hx hxy
  · have hxval : x.valuation < 0 := by
      exact lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg x).not.mp hx)
    exact reduceNonintegralAffine x y hxval hxy

def reduceCurve : RationalCurvePoint → SpecialCurvePoint
  | .infinityPlus =>
      N13SpecialCuspReduction.specialCuspEquiv .infinityPlus
  | .infinityMinus =>
      N13SpecialCuspReduction.specialCuspEquiv .infinityMinus
  | .affine X Y hcurve =>
      reduceAffine X Y (by
        rw [N13CurveModel.C13SexticEq,
          ← N13Mumford.f_eval_eq_sexticF13]
        exact hcurve)

@[simp] theorem toZMod_mk_one
    (h : ‖(1 : Q₂)‖ ≤ 1) :
    PadicInt.toZMod (⟨1, h⟩ : Z₂) = 1 := by
  have heq : (⟨1, h⟩ : Z₂) = (1 : ℤ_[2]) := by
    apply Subtype.ext
    simp
  rw [heq, map_one]

@[simp] theorem toZMod_mk_neg_one
    (h : ‖(-1 : Q₂)‖ ≤ 1) :
    PadicInt.toZMod (⟨-1, h⟩ : Z₂) = 1 := by
  have heq : (⟨-1, h⟩ : Z₂) = -(1 : ℤ_[2]) := by
    apply Subtype.ext
    simp
  rw [heq, map_neg, map_one]
  exact ZMod.neg_eq_self_mod_two 1

theorem reduceCurve_cusp
    (c : N13Mumford.Cusp13) :
    reduceCurve (N13Mumford.cuspPoint c) =
      N13SpecialCuspReduction.specialCuspEquiv c := by
  cases c <;>
    simp [reduceCurve, N13Mumford.cuspPoint, reduceAffine,
      reduceIntegralAffine, integralAffineLift,
      ratToQ₂, N13GoodModelTwo.sexticToGoodY,
      N13GoodModelTwo.h,
      N13SpecialCuspReduction.specialCuspEquiv,
      N13SpecialCuspReduction.cuspCoordinateEquiv,
      N13SpecialCuspReduction.cuspCoordinate,
      N13AbelFiberTwoModel.curvePointEquiv] <;>
    norm_num

end

end MazurProof.N13ProperCurveReduction


