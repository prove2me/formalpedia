-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:50:37.008778+00:00
-- url     : https://prove2.me/theorems/382cfd83-2a1c-41de-8925-7f9b5e1ae4b7
-- title:
--   FLT.Assumptions.MazurProof.N13GoodModelTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodModelTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodModelTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CurveModel_p0
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false




/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/

namespace MazurProof.N13GoodModelTwo

noncomputable section

open scoped CharTwo
open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient of `y` in the generalized equation. -/
def h (x : R) : R := x ^ 3 + x + 1

/-- The right-hand side of the generalized equation. -/
def rhs (x : R) : R := x ^ 5 + x ^ 4

/-- The affine equation with zero on the right. -/
def affineResidual (x y : R) : R :=
  y ^ 2 + h x * y - rhs x

/-- The affine generalized hyperelliptic equation. -/
def AffineEquation (x y : R) : Prop :=
  y ^ 2 + h x * y = rhs x

theorem affineEquation_iff_residual (x y : R) :
    AffineEquation x y ↔ affineResidual x y = 0 := by
  simp [AffineEquation, affineResidual, sub_eq_zero]

/-- Its completed-square polynomial. -/
def completedSextic (x : R) : R :=
  x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 + 2 * x ^ 3 + x ^ 2 + 2 * x + 1

theorem h_sq_add_four_rhs (x : R) :
    h x ^ 2 + 4 * rhs x = completedSextic x := by
  simp only [h, rhs, completedSextic]
  ring

/-- Completing the square before reduction. -/
theorem completed_square_identity (x y : R) :
    (2 * y + h x) ^ 2 =
      completedSextic x + 4 * (y ^ 2 + h x * y - rhs x) := by
  rw [← h_sq_add_four_rhs]
  ring

theorem completedSextic_rat (x : ℚ) :
    completedSextic x = N13CurveModel.sexticF13 x := by
  rfl

/-- The good generalized model maps to the standard sextic over `ℚ`. -/
theorem good_to_sextic
    {x y : ℚ} (hp : AffineEquation x y) :
    N13CurveModel.C13SexticEq x (2 * y + h x) := by
  rw [N13CurveModel.C13SexticEq, ← completedSextic_rat]
  rw [completed_square_identity]
  have hz : y ^ 2 + h x * y - rhs x = 0 :=
    sub_eq_zero.mpr hp
  rw [hz]
  ring

/-- The inverse completed-square coordinate over `ℚ`. -/
def sexticToGoodY (x Y : ℚ) : ℚ :=
  (Y - h x) / 2

theorem good_sextic_y_roundtrip (x y : ℚ) :
    sexticToGoodY x (2 * y + h x) = y := by
  simp only [sexticToGoodY]
  ring

theorem sextic_good_y_roundtrip (x Y : ℚ) :
    2 * sexticToGoodY x Y + h x = Y := by
  simp only [sexticToGoodY]
  ring

/-- The standard sextic maps back to the good generalized model over `ℚ`. -/
theorem sextic_to_good
    {x Y : ℚ} (hp : N13CurveModel.C13SexticEq x Y) :
    AffineEquation x (sexticToGoodY x Y) := by
  have hs := completed_square_identity x (sexticToGoodY x Y)
  rw [sextic_good_y_roundtrip] at hs
  rw [N13CurveModel.C13SexticEq, ← completedSextic_rat] at hp
  rw [hp] at hs
  have hz :
      sexticToGoodY x Y ^ 2 + h x * sexticToGoodY x Y - rhs x = 0 := by
    linarith
  exact sub_eq_zero.mp hz

/-! ## The two charts of the weighted projective completion -/

/-- Weighted-homogeneous equation in coordinates of weights `(1,3,1)`. -/
def WeightedEquation (X Y Z : R) : Prop :=
  Y ^ 2 + (X ^ 3 + X * Z ^ 2 + Z ^ 3) * Y =
    X ^ 5 * Z + X ^ 4 * Z ^ 2

/-- Residual form of the weighted-homogeneous equation. -/
def weightedResidual (X Y Z : R) : R :=
  Y ^ 2 + (X ^ 3 + X * Z ^ 2 + Z ^ 3) * Y -
    (X ^ 5 * Z + X ^ 4 * Z ^ 2)

theorem weightedEquation_iff (X Y Z : R) :
    WeightedEquation X Y Z ↔ weightedResidual X Y Z = 0 := by
  simp [WeightedEquation, weightedResidual, sub_eq_zero]

/-- Weighted homogeneity in weights `(1,3,1)` on `(X,Y,Z)`. -/
theorem weightedResidual_homogeneous (a X Y Z : R) :
    weightedResidual (a * X) (a ^ 3 * Y) (a * Z) =
      a ^ 6 * weightedResidual X Y Z := by
  simp only [weightedResidual]
  ring

/-- The `Z=1` chart is the affine generalized equation. -/
theorem weighted_affine_chart (x y : R) :
    WeightedEquation x y 1 ↔ AffineEquation x y := by
  simp [WeightedEquation, AffineEquation, h, rhs]

/-- Equation on the `X=1` chart, with `t=Z/X` and `v=Y/X³`. -/
def InfinityChartEquation (t v : R) : Prop :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2

/-- Residual form of the `X=1` chart. -/
def infinityChartResidual (t v : R) : R :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v - (t + t ^ 2)

theorem infinityChartEquation_iff (t v : R) :
    InfinityChartEquation t v ↔ infinityChartResidual t v = 0 := by
  simp [InfinityChartEquation, infinityChartResidual, sub_eq_zero]

theorem weighted_infinity_chart (t v : R) :
    WeightedEquation 1 v t ↔ InfinityChartEquation t v := by
  simp [WeightedEquation, InfinityChartEquation]

/-- Clearing the transition denominators identifies the two chart
residuals. -/
theorem overlap_residual
    {x t v : R} (hxt : x * t = 1) :
    affineResidual x (x ^ 3 * v) =
      x ^ 6 * infinityChartResidual t v := by
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt, mul_one]
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt, one_pow, mul_one]
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt, one_pow, mul_one]
  calc
    affineResidual x (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v -
          x ^ 5 - x ^ 4 := by
      simp only [affineResidual, h, rhs]
      ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v -
          x ^ 6 * t - x ^ 6 * t ^ 2 := by
      rw [hx6t, hx6t2, hx6t3]
    _ = x ^ 6 * infinityChartResidual t v := by
      simp only [infinityChartResidual]
      ring

/-- The two equations agree on the overlap `xt=1`. -/
theorem affine_iff_infinity_on_overlap
    {x t v : R} (hxt : x * t = 1) :
    AffineEquation x (x ^ 3 * v) ↔ InfinityChartEquation t v := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one t hxt
  have hx6 : IsUnit (x ^ 6) := hx.pow 6
  rw [affineEquation_iff_residual, infinityChartEquation_iff,
    overlap_residual hxt]
  constructor
  · intro hz
    exact hx6.mul_left_cancel (by simpa using hz)
  · intro hz
    rw [hz, mul_zero]

/-- Derivative of the affine equation with respect to `y`. -/
def affineDerivativeY (x y : R) : R :=
  2 * y + h x

/-- Derivative of the affine equation with respect to `x`, specialized to
characteristic two. -/
def affineDerivativeXCharTwo (x y : R) : R :=
  (x ^ 2 + 1) * y + x ^ 4

/-- Derivative of the infinity-chart equation with respect to `v`. -/
def infinityDerivativeV (t v : R) : R :=
  2 * v + (1 + t ^ 2 + t ^ 3)

/-- The affine equation as a polynomial in the second coordinate. -/
def affineFiber (x : R) : R[X] :=
  X ^ 2 + C (h x) * X - C (rhs x)

/-- The infinity-chart equation as a polynomial in the second coordinate. -/
def infinityFiber (t : R) : R[X] :=
  X ^ 2 + C (1 + t ^ 2 + t ^ 3) * X - C (t + t ^ 2)

@[simp] theorem affineFiber_eval (x y : R) :
    (affineFiber x).eval y = affineResidual x y := by
  simp [affineFiber, affineResidual]

@[simp] theorem infinityFiber_eval (t v : R) :
    (infinityFiber t).eval v = infinityChartResidual t v := by
  simp [infinityFiber, infinityChartResidual]

theorem affineFiber_derivative (x : R) :
    (affineFiber x).derivative = 2 * X + C (h x) := by
  simp only [affineFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]

theorem infinityFiber_derivative (t : R) :
    (infinityFiber t).derivative =
      2 * X + C (1 + t ^ 2 + t ^ 3) := by
  simp only [infinityFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]

theorem affineFiber_derivative_eval (x y : R) :
    (affineFiber x).derivative.eval y = affineDerivativeY x y := by
  rw [affineFiber_derivative]
  simp [affineDerivativeY]

theorem infinityFiber_derivative_eval (t v : R) :
    (infinityFiber t).derivative.eval v = infinityDerivativeV t v := by
  rw [infinityFiber_derivative]
  simp [infinityDerivativeV]

/-! ## Structural characteristic-two point classification -/

variable {K : Type u} [Field K] [CharP K 2]

/-- Elements fixed by the characteristic-two Frobenius. -/
abbrev FixedTwo (K : Type u) [Field K] :=
  {x : K // x ^ 2 = x}

omit [CharP K 2] in
theorem fixedTwo_eq_zero_or_one (x : K) (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have hfac : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hfac with hx0 | hx1
  · exact Or.inl hx0
  · exact Or.inr (sub_eq_zero.mp hx1)

/-- Frobenius-fixed elements are precisely the prime subfield. -/
def fixedTwoEquivPrimeSubfield :
    FixedTwo K ≃ (⊥ : Subfield K) where
  toFun x :=
    ⟨x.1, (Subfield.mem_bot_iff_pow_eq_self (F := K) 2).mpr x.2⟩
  invFun x :=
    ⟨x.1, (Subfield.mem_bot_iff_pow_eq_self (F := K) 2).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem fixedTwo_card [Finite K] :
    Nat.card (FixedTwo K) = 2 := by
  rw [Nat.card_congr (fixedTwoEquivPrimeSubfield (K := K)),
    Subfield.card_bot K 2]

/-- In a field with four-power Frobenius, an affine point has both
coordinates in the prime subfield.  The non-prime-field branch is excluded
by the Artin--Schreier identity, not by a finite table. -/
theorem affineEquation_iff_fixed
    (hfour : ∀ z : K, z ^ 4 = z) (x y : K) :
    AffineEquation x y ↔ x ^ 2 = x ∧ y ^ 2 = y := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro hp
    have hidem : (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
      linear_combination hfour x + x ^ 3 * htwo
    have hcases : x ^ 2 + x = 0 ∨ x ^ 2 + x = 1 := by
      have hfac : (x ^ 2 + x) * ((x ^ 2 + x) - 1) = 0 := by
        calc
          (x ^ 2 + x) * ((x ^ 2 + x) - 1) =
              (x ^ 2 + x) ^ 2 - (x ^ 2 + x) := by ring
          _ = 0 := sub_eq_zero.mpr hidem
      rcases mul_eq_zero.mp hfac with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (sub_eq_zero.mp hone)
    rcases hcases with hprime | hnonprime
    · have hx : x ^ 2 = x := by
        linear_combination hprime - x * htwo
      have hx3 : x ^ 3 = x := by
        calc
          x ^ 3 = x * x ^ 2 := by ring
          _ = x * x := by rw [hx]
          _ = x := by simpa [pow_two] using hx
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x := by simpa [pow_two] using hx
      have hh : h x = 1 := by
        simp only [h]
        linear_combination hx3 + x * htwo
      have hrhs : rhs x = 0 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + x * htwo
      have hy : y ^ 2 = y := by
        unfold AffineEquation at hp
        rw [hh, hrhs] at hp
        linear_combination hp - y * htwo
      exact ⟨hx, hy⟩
    · have hx3 : x ^ 3 = 1 := by
        linear_combination x * hnonprime - hnonprime + (x - 1) * htwo
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x ^ 2 := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x ^ 2 := by ring
      have hh : h x = x := by
        simp only [h]
        linear_combination hx3 + htwo
      have hrhs : rhs x = 1 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + hnonprime
      have hp' : y ^ 2 + x * y = 1 := by
        simpa [AffineEquation, hh, hrhs] using hp
      let t : K := y * x ^ 2
      have ht : t ^ 2 + t = x := by
        have hx4' : x ^ 4 = x := hfour x
        calc
          t ^ 2 + t = y ^ 2 * x ^ 4 + y * x ^ 2 := by
            simp only [t]
            ring
          _ = y ^ 2 * x + y * x ^ 2 := by rw [hx4']
          _ = x * (y ^ 2 + x * y) := by ring
          _ = x := by rw [hp']; ring
      have htFixed : (t ^ 2 + t) ^ 2 = t ^ 2 + t := by
        linear_combination hfour t + t ^ 3 * htwo
      rw [ht] at htFixed
      have hsumzero : x ^ 2 + x = 0 := by
        linear_combination htFixed + x * htwo
      have hzeroone : (0 : K) = 1 := hsumzero.symm.trans hnonprime
      exact (zero_ne_one hzeroone).elim
  · rintro ⟨hx, hy⟩
    have hx3 : x ^ 3 = x := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * x := by rw [hx]
        _ = x := by simpa [pow_two] using hx
    have hx4 : x ^ 4 = x := hfour x
    have hx5 : x ^ 5 = x := by
      calc
        x ^ 5 = x * x ^ 4 := by ring
        _ = x * x := by rw [hx4]
        _ = x := by simpa [pow_two] using hx
    have hh : h x = 1 := by
      simp only [h]
      linear_combination hx3 + x * htwo
    have hrhs : rhs x = 0 := by
      simp only [rhs]
      linear_combination hx5 + hx4 + x * htwo
    unfold AffineEquation
    rw [hh, hrhs, hy]
    linear_combination y * htwo

/-- Affine points as a finite type. -/
abbrev AffinePoint (K : Type u) [Field K] :=
  {p : K × K // AffineEquation p.1 p.2}

def affinePointEquivFixed
    (hfour : ∀ z : K, z ^ 4 = z) :
    AffinePoint K ≃ FixedTwo K × FixedTwo K where
  toFun P :=
    let hxy := (affineEquation_iff_fixed hfour P.1.1 P.1.2).mp P.2
    (⟨P.1.1, hxy.1⟩, ⟨P.1.2, hxy.2⟩)
  invFun P :=
    ⟨((P.1 : K), (P.2 : K)),
      (affineEquation_iff_fixed hfour (P.1 : K) (P.2 : K)).mpr
        ⟨P.1.property, P.2.property⟩⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv P := by
    ext <;> rfl

theorem affinePoint_card [Finite K]
    (hfour : ∀ z : K, z ^ 4 = z) :
    Nat.card (AffinePoint K) = 4 := by
  rw [Nat.card_congr (affinePointEquivFixed hfour), Nat.card_prod,
    fixedTwo_card]

/-- Points on the fibre `t=0` of the infinity chart. -/
abbrev InfinityPoint (K : Type u) [Field K] :=
  {v : K // InfinityChartEquation 0 v}

theorem infinityChartEquation_zero_iff_fixed (v : K) :
    InfinityChartEquation 0 v ↔ v ^ 2 = v := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  unfold InfinityChartEquation
  constructor <;> intro hv
  · linear_combination hv - v * htwo
  · linear_combination hv + v * htwo

def infinityPointEquivFixed :
    InfinityPoint K ≃ FixedTwo K where
  toFun P := ⟨P.1, (infinityChartEquation_zero_iff_fixed P.1).mp P.2⟩
  invFun P := ⟨P.1, (infinityChartEquation_zero_iff_fixed P.1).mpr P.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv P := by apply Subtype.ext; rfl

theorem infinityPoint_card [Finite K] :
    Nat.card (InfinityPoint K) = 2 := by
  rw [Nat.card_congr (infinityPointEquivFixed (K := K)), fixedTwo_card]

/-- The point type presented by the affine chart and its two infinity points. -/
abbrev CompletedPoint (K : Type u) [Field K] :=
  AffinePoint K ⊕ InfinityPoint K

theorem completedPoint_card [Finite K]
    (hfour : ∀ z : K, z ^ 4 = z) :
    Nat.card (CompletedPoint K) = 6 := by
  rw [Nat.card_sum, affinePoint_card hfour, infinityPoint_card]

/-- On every affine point, the second-coordinate derivative is one. -/
theorem affineDerivativeY_eq_one
    (hfour : ∀ z : K, z ^ 4 = z)
    {x y : K} (hp : AffineEquation x y) :
    affineDerivativeY x y = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hx := (affineEquation_iff_fixed hfour x y).mp hp |>.1
  have hx3 : x ^ 3 = x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * x := by rw [hx]
      _ = x := by simpa [pow_two] using hx
  simp only [affineDerivativeY, h]
  linear_combination y * htwo + hx3 + x * htwo

/-- The two points at infinity are smooth in the `X=1` chart. -/
theorem infinityDerivativeV_zero_eq_one (v : K) :
    infinityDerivativeV 0 v = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [infinityDerivativeV]
  linear_combination v * htwo

/-- The affine chart is geometrically smooth in characteristic two.  If the
`y`-derivative vanished, the curve equation would force `y=1`; the
`x`-derivative would then force `x=1`, contradicting `h(x)=0`. -/
theorem no_affine_singular_point (x y : K) :
    ¬(AffineEquation x y ∧
      affineDerivativeY x y = 0 ∧
      affineDerivativeXCharTwo x y = 0) := by
  rintro ⟨hp, hdy, hdx⟩
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hhzero : h x = 0 := by
    unfold affineDerivativeY at hdy
    linear_combination hdy - y * htwo
  have hx3 : x ^ 3 = x + 1 := by
    simp only [h] at hhzero
    linear_combination hhzero - (x + 1) * htwo
  have hx4 : x ^ 4 = x ^ 2 + x := by
    simp only [h] at hhzero
    linear_combination x * hhzero - (x ^ 2 + x) * htwo
  have hx5 : x ^ 5 = x ^ 2 + x + 1 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (x ^ 2 + x) := by rw [hx4]
      _ = x ^ 3 + x ^ 2 := by ring
      _ = x ^ 2 + x + 1 := by rw [hx3]; ring
  have hrhs : rhs x = 1 := by
    simp only [rhs]
    rw [hx5, hx4]
    linear_combination (x ^ 2 + x) * htwo
  have hy2 : y ^ 2 = 1 := by
    unfold AffineEquation at hp
    rw [hhzero, zero_mul, add_zero, hrhs] at hp
    exact hp
  have hyplus_sq : (y + 1) ^ 2 = 0 := by
    linear_combination hy2 + (y + 1) * htwo
  have hyplus : y + 1 = 0 := by
    exact (sq_eq_zero_iff).mp hyplus_sq
  have hy : y = 1 := by
    linear_combination hyplus - htwo
  have hxplus : x + 1 = 0 := by
    unfold affineDerivativeXCharTwo at hdx
    rw [hy, hx4] at hdx
    linear_combination hdx - x ^ 2 * htwo
  have hx : x = 1 := by
    linear_combination hxplus - htwo
  subst x
  simp only [h] at hhzero
  have hone : (1 : K) = 0 := by
    linear_combination hhzero - htwo
  exact one_ne_zero hone

/-- On the hyperplane at infinity, a nonzero weighted point has `X ≠ 0`;
therefore the `X=1` chart covers all points missing from the affine chart. -/
theorem infinity_has_nonzero_X
    {X Y Z : K}
    (hp : WeightedEquation X Y Z)
    (hnonzero : X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0)
    (hZ : Z = 0) :
    X ≠ 0 := by
  intro hX
  subst X
  subst Z
  have hy2 : Y ^ 2 = 0 := by
    simpa [WeightedEquation] using hp
  have hY : Y = 0 := (sq_eq_zero_iff).mp hy2
  exact hnonzero.elim (fun hx => hx rfl)
    (fun hrest => hrest.elim (fun hy => hy hY) (fun hz => hz rfl))

/-! ## The fields `F₂` and `F₄` -/

abbrev F2 := ZMod 2
abbrev F4 := GaloisField 2 2

theorem f2_fourth_eq (x : F2) : x ^ 4 = x := by
  have hx : x ^ 2 = x := ZMod.pow_card x
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := congrArg (fun z : F2 => z ^ 2) hx
    _ = x := hx

local instance instFintypeF4 : Fintype F4 := Fintype.ofFinite F4

theorem f4_card : Fintype.card F4 = 4 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem f4_fourth_eq (x : F4) : x ^ 4 = x := by
  have hx := FiniteField.pow_card x
  rwa [f4_card] at hx

theorem completed_points_f2_card :
    Nat.card (CompletedPoint F2) = 6 :=
  completedPoint_card f2_fourth_eq

theorem completed_points_f4_card :
    Nat.card (CompletedPoint F4) = 6 :=
  completedPoint_card f4_fourth_eq

end

end MazurProof.N13GoodModelTwo


