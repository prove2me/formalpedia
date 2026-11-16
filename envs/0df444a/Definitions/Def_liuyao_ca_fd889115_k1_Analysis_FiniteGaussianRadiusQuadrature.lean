-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianRadiusQuadrature
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteGaussianRadiusQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:28:47.355085+00:00
-- url     : https://prove2.me/theorems/5afc3c18-0b98-4529-808f-e9556193ac2d
-- title:
--   Computable analysis · FiniteGaussianRadiusQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteGaussianRadiusQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianApproximateIdentity
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianTail
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CauchyPi
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedPositiveSquareRoot

set_option autoImplicit true

/-!
# Arbitrary-radius finite Gaussian quadrature

This module gives the arbitrary-radius counterpart of the unit Gaussian
quadrature comparison.  At every stage it integrates a finite Gaussian Taylor
prefix by an explicit rational midpoint rule.  The number of cells is chosen
from the prefix's finite secant-error coefficient, so the construction does
not need a radius-independent analytic derivative bound.

The stabilized raw is proved equivalent to
`gaussianRadiusIntegratedSeriesRaw`.  Thus it is a bounded quadrature
presentation of the same computable value.  It still does not assert a
universal integral operator or an improper full-line integral.
-/

namespace ComputableAnalysis

/-- A symmetric secant box large enough to contain `[0,radius]`, including
the small-radius case where the polynomial certificate still requires a box
of radius at least one. -/
def gaussianRadiusSecantBox (radius : Rat) : Rat := radius + 1

/-- The exact finite Gaussian primitive carries a computable secant-error
certificate on every nonnegative rational radius. -/
def gaussianEvenPrimitiveSecantBoundAtRadius
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) :
    FinitePolynomial.SecantDerivativeBound (gaussianRadiusSecantBox radius)
      (gaussianEvenPrimitivePrefix terms)
      (gaussianEvenProfilePrefix terms) := by
  unfold gaussianRadiusSecantBox
  exact FinitePolynomial.integratedTaylorPrefixSecantBound
    (radius + 1) gaussianEvenTaylorCoeff (by grind) (2 * terms)

theorem gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_nonneg
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) :
    0 <= (gaussianEvenPrimitiveSecantBoundAtRadius
      radius hradius terms).errorCoefficient :=
  (gaussianEvenPrimitiveSecantBoundAtRadius
    radius hradius terms).errorCoefficient_nonneg

private theorem powerSecantErrorBound_odd_closed (C : Rat) (k : Nat) :
    FinitePolynomial.powerSecantErrorBound C (2 * k + 1) =
      (k : Rat) * ((2 * k + 1 : Nat) : Rat) * C ^ (2 * k) := by
  induction k with
  | zero => grind [FinitePolynomial.powerSecantErrorBound]
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        FinitePolynomial.powerSecantErrorBound,
        FinitePolynomial.powerSecantErrorBound, ih]
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega,
        show 2 * k + 1 = 2 * k + 1 by rfl,
        Rat.pow_succ, Rat.pow_succ]
      have hk1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
        exact_mod_cast (by omega : k + 1 = k + 1)
      have htwoKOne : (((2 * k + 1 : Nat) : Rat)) =
          2 * (k : Rat) + 1 := by
        exact_mod_cast (by omega : 2 * k + 1 = 2 * k + 1)
      have htwoKTwo : (((2 * k + 2 : Nat) : Rat)) =
          2 * (k : Rat) + 2 := by
        exact_mod_cast (by omega : 2 * k + 2 = 2 * k + 2)
      have htwoKThree : (((2 * (k + 1) + 1 : Nat) : Rat)) =
          2 * (k : Rat) + 3 := by
        exact_mod_cast (by omega : 2 * (k + 1) + 1 = 2 * k + 3)
      have htwoKThree' : (((2 * k + 1 + 1 + 1 : Nat) : Rat)) =
          2 * (k : Rat) + 3 := by
        exact_mod_cast (by omega : 2 * k + 1 + 1 + 1 = 2 * k + 3)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        show 2 * k + 2 = (2 * k + 1) + 1 by omega,
        Rat.pow_succ, show 2 * k + 1 = 2 * k + 1 by rfl,
        Rat.pow_succ]
      rw [hk1, htwoKOne, htwoKTwo, htwoKThree']
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_succ
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) :
    (gaussianEvenPrimitiveSecantBoundAtRadius
        radius hradius (terms + 1)).errorCoefficient =
      (gaussianEvenPrimitiveSecantBoundAtRadius
        radius hradius terms).errorCoefficient +
        qabs (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
          FinitePolynomial.powerSecantErrorBound
            (radius + 1) (2 * terms + 1) := by
  change
    (FinitePolynomial.integratedTaylorPrefixSecantBound
      (radius + 1) gaussianEvenTaylorCoeff (by grind)
      (2 * (terms + 1))).errorCoefficient =
    (FinitePolynomial.integratedTaylorPrefixSecantBound
      (radius + 1) gaussianEvenTaylorCoeff (by grind)
      (2 * terms)).errorCoefficient + _
  rw [FinitePolynomial.integratedTaylorPrefixSecantBound_errorCoefficient,
    FinitePolynomial.integratedTaylorPrefixSecantBound_errorCoefficient]
  rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega,
    FinitePolynomial.integratedTaylorPrefixSecantCoefficient,
    FinitePolynomial.integratedTaylorPrefixSecantCoefficient,
    gaussianEvenTaylorCoeff_odd, gaussianEvenTaylorCoeff_even]
  rw [qabs_eq_self_of_nonneg (show (0 : Rat) <= 0 by decide +kernel),
    Rat.zero_mul, Rat.add_zero]

private theorem qabs_expCoeff_mul_neg_one_pow_radius (k : Nat) :
    qabs (FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k) =
      FormalPowerSeries.expCoeff k := by
  rw [qabs_mul]
  have hsign : qabs ((-1 : Rat) ^ k) = 1 := by
    induction k with
    | zero => decide +kernel
    | succ k ih =>
        rw [Rat.pow_succ, qabs_mul, ih]
        decide +kernel
  rw [hsign, Rat.mul_one]
  apply qabs_eq_self_of_nonneg
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2
    (RationalMajorant.factorialRat_pos k))

private theorem gaussianRadiusSecantCoefficient_summand
    (C : Rat) (k : Nat) :
    qabs (FormalPowerSeries.expCoeff (k + 2) * (-1 : Rat) ^ (k + 2)) *
        FinitePolynomial.powerSecantErrorBound C (2 * (k + 2) + 1) =
      2 * (C * C) * (C * C) *
          RationalMajorant.factorialTailTerm (C * C) k +
        3 * (C * C) *
          RationalMajorant.factorialTailTerm (C * C) (k + 1) := by
  rw [qabs_expCoeff_mul_neg_one_pow_radius,
    powerSecantErrorBound_odd_closed]
  unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
  rw [FormalPowerSeries.factorialRat_succ,
    FormalPowerSeries.factorialRat_succ]
  have hk1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
    exact_mod_cast (by omega : k + 1 = k + 1)
  have hk2 : (((k + 2 : Nat) : Rat)) = (k : Rat) + 2 := by
    exact_mod_cast (by omega : k + 2 = k + 2)
  have hodd : (((2 * (k + 2) + 1 : Nat) : Rat)) =
      2 * (k : Rat) + 5 := by
    exact_mod_cast (by omega : 2 * (k + 2) + 1 = 2 * k + 5)
  rw [hk1, hk2, hodd, Rat.div_def, Rat.div_def, Rat.div_def,
    Rat.inv_mul_rev, Rat.inv_mul_rev]
  have hk1ne : (k : Rat) + 1 ≠ 0 := by
    exact Rat.ne_of_gt (by exact_mod_cast (Nat.succ_pos k))
  have hk2ne : (k : Rat) + 2 ≠ 0 := by
    exact Rat.ne_of_gt (by exact_mod_cast (show 0 < k + 2 by omega))
  have hcancel1 : ((k : Rat) + 1) * ((k : Rat) + 1)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hk1ne
  have hcancel2 : ((k : Rat) + 2) * ((k : Rat) + 2)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hk2ne
  have hcancel2' : ((k : Rat) + 2)⁻¹ * ((k : Rat) + 2) = 1 :=
    Rat.inv_mul_cancel _ hk2ne
  have hsquarePow : forall n : Nat, (C * C) ^ n = C ^ (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Rat.pow_succ, ih, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Rat.pow_succ, show 2 * n + 1 = 2 * n + 1 by rfl, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hsquarePow k, hsquarePow (k + 1)]
  rw [show 2 * (k + 2) = (((2 * k + 1) + 1) + 1) + 1 by omega,
    Rat.pow_succ, Rat.pow_succ, Rat.pow_succ,
    show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    Rat.pow_succ, show 2 * k + 1 = 2 * k + 1 by rfl, Rat.pow_succ]
  have hleft :
      1 * ((factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          ((k : Rat) + 2)⁻¹) *
            (((k : Rat) + 2) * (2 * (k : Rat) + 5) *
              (C ^ (2 * k) * C * C * C * C)) =
        ((factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          (2 * (k : Rat) + 5)) *
            (C ^ (2 * k) * C * C * C * C) := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hleft]
  rw [show 2 * k + 1 = 2 * k + 1 by rfl, Rat.pow_succ]
  have hsplit : 2 * (k : Rat) + 5 = 2 * ((k : Rat) + 1) + 3 := by
    grind [Rat.mul_add]
  rw [hsplit, Rat.mul_add]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_eq_factorialPartials
    (radius : Rat) (hradius : 0 <= radius) (n : Nat) :
    let C := radius + 1
    let A := C * C
    (gaussianEvenPrimitiveSecantBoundAtRadius
        radius hradius (n + 2)).errorCoefficient =
      3 * A +
        2 * A * A * RationalMajorant.factorialTailPartial A 0 n +
        3 * A * RationalMajorant.factorialTailPartial A 1 n := by
  let C : Rat := radius + 1
  let A : Rat := C * C
  induction n with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by omega,
        gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_succ,
        show 1 = 0 + 1 by omega,
        gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_succ,
        qabs_expCoeff_mul_neg_one_pow_radius,
        qabs_expCoeff_mul_neg_one_pow_radius,
        powerSecantErrorBound_odd_closed,
        powerSecantErrorBound_odd_closed]
      have hzero :
          (gaussianEvenPrimitiveSecantBoundAtRadius
            radius hradius 0).errorCoefficient = 0 := rfl
      have hcoeffZero : FormalPowerSeries.expCoeff 0 = 1 := by
        decide +kernel
      have hcoeffOne : FormalPowerSeries.expCoeff 1 = 1 := by
        decide +kernel
      rw [hzero]
      rw [hcoeffZero, hcoeffOne]
      simp [RationalMajorant.factorialTailPartial, A, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_succ, ih,
        gaussianRadiusSecantCoefficient_summand]
      change
        3 * A + 2 * A * A *
              RationalMajorant.factorialTailPartial A 0 n +
            3 * A * RationalMajorant.factorialTailPartial A 1 n +
          (2 * A * A * RationalMajorant.factorialTailTerm A n +
            3 * A * RationalMajorant.factorialTailTerm A (n + 1)) =
        3 * A +
          2 * A * A *
            (RationalMajorant.factorialTailPartial A 0 n +
              RationalMajorant.factorialTailTerm A (0 + n)) +
          3 * A *
            (RationalMajorant.factorialTailPartial A 1 n +
              RationalMajorant.factorialTailTerm A (1 + n))
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- A prefix-independent rational secant coefficient for every finite
Gaussian primitive on `[0,radius]`.  It uses only a finite factorial block
and the certified geometric remainder at `(radius+1)^2`. -/
def gaussianEvenPrimitiveSecantUniformBound (radius : Rat) : Rat :=
  let C := radius + 1
  let A := C * C
  3 * A + (2 * A * A + 3 * A) *
    RationalMajorant.factorialSeriesFiniteBound A

theorem gaussianEvenPrimitiveSecantUniformBound_nonneg
    (radius : Rat) (hradius : 0 <= radius) :
    0 <= gaussianEvenPrimitiveSecantUniformBound radius := by
  let C : Rat := radius + 1
  let A : Rat := C * C
  have hC : 0 <= C := by dsimp [C]; grind
  have hA : 0 <= A := by dsimp [A]; exact Rat.mul_nonneg hC hC
  unfold gaussianEvenPrimitiveSecantUniformBound
  exact Rat.add_nonneg
    (Rat.mul_nonneg (by decide +kernel) hA)
    (Rat.mul_nonneg
      (Rat.add_nonneg
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hA) hA)
        (Rat.mul_nonneg (by decide +kernel) hA))
      (RationalMajorant.factorialSeriesFiniteBound_nonneg hA))

theorem gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_le_uniform
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) :
    (gaussianEvenPrimitiveSecantBoundAtRadius
      radius hradius terms).errorCoefficient <=
        gaussianEvenPrimitiveSecantUniformBound radius := by
  let C : Rat := radius + 1
  let A : Rat := C * C
  have hC : 0 <= C := by dsimp [C]; grind
  have hA : 0 <= A := by dsimp [A]; exact Rat.mul_nonneg hC hC
  cases terms with
  | zero =>
      change 0 <= gaussianEvenPrimitiveSecantUniformBound radius
      exact gaussianEvenPrimitiveSecantUniformBound_nonneg radius hradius
  | succ terms =>
      cases terms with
      | zero =>
          have hone :
              (gaussianEvenPrimitiveSecantBoundAtRadius
                radius hradius 1).errorCoefficient = 0 := by
            rw [show 1 = 0 + 1 by omega,
              gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_succ,
              qabs_expCoeff_mul_neg_one_pow_radius,
              powerSecantErrorBound_odd_closed]
            change 0 + FormalPowerSeries.expCoeff 0 *
              (0 * 1 * (radius + 1) ^ 0) = 0
            grind
          rw [hone]
          exact gaussianEvenPrimitiveSecantUniformBound_nonneg radius hradius
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega,
            gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_eq_factorialPartials]
          have hzero := RationalMajorant.factorialTailPartial_le_finiteBound
            hA 0 n
          have hone := RationalMajorant.factorialTailPartial_le_finiteBound
            hA 1 n
          unfold gaussianEvenPrimitiveSecantUniformBound
          change
            3 * A + 2 * A * A *
                RationalMajorant.factorialTailPartial A 0 n +
              3 * A * RationalMajorant.factorialTailPartial A 1 n <=
            3 * A + (2 * A * A + 3 * A) *
              RationalMajorant.factorialSeriesFiniteBound A
          have htwo :
              2 * A * A * RationalMajorant.factorialTailPartial A 0 n <=
                2 * A * A * RationalMajorant.factorialSeriesFiniteBound A :=
            Rat.mul_le_mul_of_nonneg_left hzero
              (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hA) hA)
          have hthree :
              3 * A * RationalMajorant.factorialTailPartial A 1 n <=
                3 * A * RationalMajorant.factorialSeriesFiniteBound A :=
            Rat.mul_le_mul_of_nonneg_left hone
              (Rat.mul_nonneg (by decide +kernel) hA)
          calc
            3 * A + 2 * A * A *
                  RationalMajorant.factorialTailPartial A 0 n +
                3 * A * RationalMajorant.factorialTailPartial A 1 n <=
              3 * A + 2 * A * A *
                  RationalMajorant.factorialSeriesFiniteBound A +
                3 * A * RationalMajorant.factorialSeriesFiniteBound A :=
                rat_add_le_add (rat_add_le_add (Rat.le_refl) htwo) hthree
            _ = 3 * A + (2 * A * A + 3 * A) *
                RationalMajorant.factorialSeriesFiniteBound A := by
              grind [Rat.add_mul, Rat.mul_assoc]

/-- Exact termwise integration on `[0,radius]`, followed by reflection. -/
theorem two_mul_gaussianEvenPrimitivePrefix_endpointDifference_at_radius
    (terms : Nat) (radius : Rat) :
    2 * (gaussianEvenPrimitivePrefix terms radius -
      gaussianEvenPrimitivePrefix terms 0) =
        gaussianEvenIntegralPrefix terms radius := by
  induction terms with
  | zero =>
      simp [gaussianEvenPrimitivePrefix,
        FinitePolynomial.integratedTaylorPrefix,
        gaussianEvenIntegralPrefix]
      decide +kernel
  | succ terms ih =>
      unfold gaussianEvenPrimitivePrefix
      rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega]
      simp only [FinitePolynomial.integratedTaylorPrefix]
      simp only [gaussianEvenTaylorCoeff_odd, Rat.zero_mul, Rat.add_zero]
      rw [gaussianEvenTaylorCoeff_even, gaussianEvenIntegralPrefix_succ]
      have hzeroPow : (0 : Rat) ^ (2 * terms + 1) = 0 := by
        rw [Rat.pow_succ, Rat.mul_zero]
      have ih' :
          2 *
              (FinitePolynomial.integratedTaylorPrefix
                  gaussianEvenTaylorCoeff (2 * terms) radius -
                FinitePolynomial.integratedTaylorPrefix
                  gaussianEvenTaylorCoeff (2 * terms) 0) =
            gaussianEvenIntegralPrefix terms radius := by
        simpa [gaussianEvenPrimitivePrefix] using ih
      rw [hzeroPow]
      grind [Rat.div_def, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

/-- The difference of two symmetric finite Gaussian prefixes is twice the
matching primitive increment between their nonnegative radii. -/
theorem gaussianEvenIntegralPrefix_sub_eq_two_mul_primitiveDifference
    (terms : Nat) (inner outer : Rat) :
    gaussianEvenIntegralPrefix terms outer -
        gaussianEvenIntegralPrefix terms inner =
      2 * (gaussianEvenPrimitivePrefix terms outer -
        gaussianEvenPrimitivePrefix terms inner) := by
  have houter :=
    two_mul_gaussianEvenPrimitivePrefix_endpointDifference_at_radius
      terms outer
  have hinner :=
    two_mul_gaussianEvenPrimitivePrefix_endpointDifference_at_radius
      terms inner
  rw [← houter, ← hinner]
  grind [Rat.mul_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The finite midpoint error on `[0,radius]` with the literal radius-specific
secant coefficient. -/
theorem gaussianEvenPrimitive_uniformMidpoint_error_le_at_radius
    (radius : Rat) (hradius : 0 <= radius)
    (terms pieces : Nat) (hpieces : 0 < pieces) :
    let P := RationalPartition.uniform 0 radius pieces hpieces hradius
    qabs ((gaussianEvenPrimitivePrefix terms radius -
        gaussianEvenPrimitivePrefix terms 0) -
      P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <=
        (mesh 0 radius pieces * (radius - 0)) *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            radius hradius terms).errorCoefficient := by
  apply FinitePolynomial.SecantDerivativeBound.qabs_uniform_midpointRectangleAction_error_le
    (gaussianEvenPrimitiveSecantBoundAtRadius radius hradius terms)
    pieces hpieces hradius
  · unfold gaussianRadiusSecantBox qabs
    simp
    grind
  · rw [qabs_eq_self_of_nonneg hradius]
    unfold gaussianRadiusSecantBox
    grind

/-- After reflection, the symmetric integrated prefix differs from the
finite midpoint action by twice the half-interval secant budget. -/
theorem gaussianEvenIntegralPrefix_sub_midpointAction_le_at_radius
    (radius : Rat) (hradius : 0 <= radius)
    (terms pieces : Nat) (hpieces : 0 < pieces) :
    let P := RationalPartition.uniform 0 radius pieces hpieces hradius
    qabs (gaussianEvenIntegralPrefix terms radius -
        2 * P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <=
      2 * ((mesh 0 radius pieces * (radius - 0)) *
        (gaussianEvenPrimitiveSecantBoundAtRadius
          radius hradius terms).errorCoefficient) := by
  dsimp only
  let P := RationalPartition.uniform 0 radius pieces hpieces hradius
  have hfinite := gaussianEvenPrimitive_uniformMidpoint_error_le_at_radius
    radius hradius terms pieces hpieces
  change qabs ((gaussianEvenPrimitivePrefix terms radius -
      gaussianEvenPrimitivePrefix terms 0) -
        P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <= _
    at hfinite
  have hprefix :=
    two_mul_gaussianEvenPrimitivePrefix_endpointDifference_at_radius
      terms radius
  have hdecomp :
      gaussianEvenIntegralPrefix terms radius -
          2 * P.midpointRectangleAction (gaussianEvenProfilePrefix terms) =
        2 * ((gaussianEvenPrimitivePrefix terms radius -
            gaussianEvenPrimitivePrefix terms 0) -
          P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) := by
    rw [← hprefix]
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hdecomp, qabs_mul, show qabs (2 : Rat) = 2 by decide +kernel]
  exact Rat.mul_le_mul_of_nonneg_left hfinite (by decide +kernel)

/-! ## An executable radius-specific quadrature schedule -/

/-- The rational coefficient multiplying the reciprocal mesh budget after
reflection to `[-radius,radius]`. -/
def gaussianRadiusTaylorQuadratureBound
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) : Rat :=
  2 * (radius * radius) *
    (gaussianEvenPrimitiveSecantBoundAtRadius
      radius hradius terms).errorCoefficient

theorem gaussianRadiusTaylorQuadratureBound_nonneg
    (radius : Rat) (hradius : 0 <= radius) (terms : Nat) :
    0 <= gaussianRadiusTaylorQuadratureBound radius hradius terms := by
  unfold gaussianRadiusTaylorQuadratureBound
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg hradius hradius))
    (gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_nonneg
      radius hradius terms)

/-- The dyadic mesh shift computed from the finite prefix and requested raw
stage. -/
def gaussianRadiusTaylorQuadratureShift
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) : Nat :=
  RationalMajorant.halfDecayShift
    (gaussianRadiusTaylorQuadratureBound radius hradius terms)
    (precisionAtStage (stage + 1))

def gaussianRadiusTaylorQuadraturePieces
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) : Nat :=
  2 ^ gaussianRadiusTaylorQuadratureShift radius hradius terms stage

theorem gaussianRadiusTaylorQuadraturePieces_pos
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) :
    0 < gaussianRadiusTaylorQuadraturePieces radius hradius terms stage := by
  unfold gaussianRadiusTaylorQuadraturePieces
  exact Nat.pow_pos (by omega)

/-- The explicit enclosure radius paid for the finite midpoint quadrature. -/
def gaussianRadiusTaylorQuadratureErrorRadius
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) : Rat :=
  gaussianRadiusTaylorQuadratureBound radius hradius terms *
    ((1 : Rat) / 2) ^
      gaussianRadiusTaylorQuadratureShift radius hradius terms stage

theorem gaussianRadiusTaylorQuadratureErrorRadius_nonneg
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) :
    0 <= gaussianRadiusTaylorQuadratureErrorRadius
      radius hradius terms stage := by
  unfold gaussianRadiusTaylorQuadratureErrorRadius
  exact Rat.mul_nonneg
    (gaussianRadiusTaylorQuadratureBound_nonneg radius hradius terms)
    (Rat.pow_nonneg (by decide +kernel))

theorem gaussianRadiusTaylorQuadratureErrorRadius_le_precision
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) :
    gaussianRadiusTaylorQuadratureErrorRadius radius hradius terms stage <=
      (precisionAtStage (stage + 1)).val := by
  unfold gaussianRadiusTaylorQuadratureErrorRadius
    gaussianRadiusTaylorQuadratureShift
  exact RationalMajorant.halfDecayShift_spec
    (gaussianRadiusTaylorQuadratureBound_nonneg radius hradius terms)
    (precisionAtStage (stage + 1))

/-- The reflected midpoint action for the selected finite Gaussian prefix. -/
def gaussianRadiusTaylorQuadratureCenter
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) : Rat :=
  let pieces := gaussianRadiusTaylorQuadraturePieces
    radius hradius terms stage
  let P := RationalPartition.uniform 0 radius pieces
    (gaussianRadiusTaylorQuadraturePieces_pos radius hradius terms stage)
    hradius
  2 * P.midpointRectangleAction (gaussianEvenProfilePrefix terms)

theorem gaussianEvenIntegralPrefix_sub_gaussianRadiusTaylorQuadratureCenter_le
    (radius : Rat) (hradius : 0 <= radius) (terms stage : Nat) :
    qabs (gaussianEvenIntegralPrefix terms radius -
        gaussianRadiusTaylorQuadratureCenter
          radius hradius terms stage) <=
      gaussianRadiusTaylorQuadratureErrorRadius
        radius hradius terms stage := by
  let pieces := gaussianRadiusTaylorQuadraturePieces
    radius hradius terms stage
  have hpieces : 0 < pieces := by
    simpa [pieces] using
      gaussianRadiusTaylorQuadraturePieces_pos radius hradius terms stage
  let P := RationalPartition.uniform 0 radius pieces hpieces hradius
  have hbase := gaussianEvenIntegralPrefix_sub_midpointAction_le_at_radius
    radius hradius terms pieces hpieces
  change qabs (gaussianEvenIntegralPrefix terms radius -
      2 * P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <= _
    at hbase
  have hmesh : mesh 0 radius pieces =
      radius / ((pieces : Nat) : Rat) := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt hpieces)]
    grind
  have hbudget :
      2 * ((mesh 0 radius pieces * (radius - 0)) *
        (gaussianEvenPrimitiveSecantBoundAtRadius
          radius hradius terms).errorCoefficient) =
      gaussianRadiusTaylorQuadratureErrorRadius
        radius hradius terms stage := by
    rw [hmesh]
    dsimp [pieces, gaussianRadiusTaylorQuadraturePieces,
      gaussianRadiusTaylorQuadratureErrorRadius,
      gaussianRadiusTaylorQuadratureBound]
    rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  change qabs (gaussianEvenIntegralPrefix terms radius -
      2 * P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <= _
  rw [← hbudget]
  exact hbase

/-- Two independently scheduled midpoint rules approximate the exact finite
Gaussian annulus for one shared polynomial prefix. -/
theorem gaussianRadiusTaylorQuadratureCenter_annulus_sub_prefixAnnulus_le
    (inner outer : Rat) (hinner : 0 <= inner) (houter : 0 <= outer)
    (terms innerStage outerStage : Nat) :
    qabs ((gaussianRadiusTaylorQuadratureCenter
          outer houter terms outerStage -
        gaussianRadiusTaylorQuadratureCenter
          inner hinner terms innerStage) -
      (gaussianEvenIntegralPrefix terms outer -
        gaussianEvenIntegralPrefix terms inner)) <=
      gaussianRadiusTaylorQuadratureErrorRadius
          outer houter terms outerStage +
        gaussianRadiusTaylorQuadratureErrorRadius
          inner hinner terms innerStage := by
  let outerCenter := gaussianRadiusTaylorQuadratureCenter
    outer houter terms outerStage
  let innerCenter := gaussianRadiusTaylorQuadratureCenter
    inner hinner terms innerStage
  let outerPrefix := gaussianEvenIntegralPrefix terms outer
  let innerPrefix := gaussianEvenIntegralPrefix terms inner
  have houterError :=
    gaussianEvenIntegralPrefix_sub_gaussianRadiusTaylorQuadratureCenter_le
      outer houter terms outerStage
  have hinnerError :=
    gaussianEvenIntegralPrefix_sub_gaussianRadiusTaylorQuadratureCenter_le
      inner hinner terms innerStage
  have houterReverse :
      qabs (outerCenter - outerPrefix) <=
        gaussianRadiusTaylorQuadratureErrorRadius
          outer houter terms outerStage := by
    have hneg : outerCenter - outerPrefix = -(outerPrefix - outerCenter) := by
      grind [Rat.sub_eq_add_neg]
    rw [hneg, qabs_neg]
    simpa [outerCenter, outerPrefix] using houterError
  have hdecomp :
      (outerCenter - innerCenter) - (outerPrefix - innerPrefix) =
        (outerCenter - outerPrefix) + (innerPrefix - innerCenter) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs
      ((outerCenter - innerCenter) - (outerPrefix - innerPrefix)) <= _
  rw [hdecomp]
  exact Rat.le_trans (qabs_add_le _ _)
    (rat_add_le_add houterReverse
      (by simpa [innerPrefix, innerCenter] using hinnerError))

/-! ## Direct quadrature raw and comparison with the integrated series -/

def gaussianRadiusTaylorQuadratureTerms (radius : Rat) (stage : Nat) : Nat :=
  gaussianIntegralTailStart radius + 2 * stage

/-- A non-nested direct candidate computed from one finite midpoint rule and
its explicit secant-error radius. -/
def gaussianRadiusTaylorQuadratureCandidateRaw
    (radius : Rat) (hradius : 0 <= radius) : RealCompute where
  compute := fun stage =>
    let terms := gaussianRadiusTaylorQuadratureTerms radius stage
    QInterval.expand
      (QInterval.pointInterval
        (gaussianRadiusTaylorQuadratureCenter
          radius hradius terms stage))
      (gaussianRadiusTaylorQuadratureErrorRadius
        radius hradius terms stage)

theorem gaussianRadiusTaylorQuadratureCandidateRaw_contains_prefix
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute stage
      |>.ContainsInterval
        (QInterval.pointInterval
          (gaussianEvenIntegralPrefix
            (gaussianRadiusTaylorQuadratureTerms radius stage) radius)) := by
  have hclose :=
    gaussianEvenIntegralPrefix_sub_gaussianRadiusTaylorQuadratureCenter_le
      radius hradius (gaussianRadiusTaylorQuadratureTerms radius stage) stage
  unfold gaussianRadiusTaylorQuadratureCandidateRaw QInterval.expand
    QInterval.pointInterval QInterval.ContainsInterval
  constructor
  · have hneg := neg_qabs_le_self
      (gaussianEvenIntegralPrefix
          (gaussianRadiusTaylorQuadratureTerms radius stage) radius -
        gaussianRadiusTaylorQuadratureCenter radius hradius
          (gaussianRadiusTaylorQuadratureTerms radius stage) stage)
    grind
  · have hself := self_le_qabs
      (gaussianEvenIntegralPrefix
          (gaussianRadiusTaylorQuadratureTerms radius stage) radius -
        gaussianRadiusTaylorQuadratureCenter radius hradius
          (gaussianRadiusTaylorQuadratureTerms radius stage) stage)
    grind

theorem gaussianRadiusTaylorQuadratureCandidateRaw_width
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    ((gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute stage).width =
      2 * gaussianRadiusTaylorQuadratureErrorRadius radius hradius
        (gaussianRadiusTaylorQuadratureTerms radius stage) stage := by
  unfold gaussianRadiusTaylorQuadratureCandidateRaw
  rw [QInterval.expand_width, QInterval.pointInterval_width]
  grind

theorem precisionAtStage_succ_value (stage : Nat) :
    (precisionAtStage (stage + 1)).val =
      1 / (((stage + 1 : Nat) : Rat)) := by
  unfold precisionAtStage
  rw [dif_neg (Nat.succ_ne_zero stage)]

theorem gaussianRadiusTaylorQuadratureCandidateRaw_width_le_natRate
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    ((gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute stage).width <=
      2 / (((stage + 1 : Nat) : Rat)) := by
  rw [gaussianRadiusTaylorQuadratureCandidateRaw_width]
  have herror := gaussianRadiusTaylorQuadratureErrorRadius_le_precision
    radius hradius (gaussianRadiusTaylorQuadratureTerms radius stage) stage
  rw [precisionAtStage_succ_value] at herror
  have hscaled := Rat.mul_le_mul_of_nonneg_left herror
    (by decide +kernel : (0 : Rat) <= 2)
  simpa [Rat.div_def, Rat.mul_assoc] using hscaled

theorem gaussianRadiusTaylorQuadratureCandidateRaw_widths_shrink
    (radius : Rat) (hradius : 0 <= radius) :
    RealCompute.WidthsShrinkToZero
      (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute :=
  shrinksToZero_of_natOverSuccBound
    (gaussianRadiusTaylorQuadratureCandidateRaw_width_le_natRate
      radius hradius)

theorem gaussianRadiusIntegratedSeriesRaw_contains_quadraturePrefix
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    (gaussianRadiusIntegratedSeriesRaw radius hradius).compute stage
      |>.ContainsInterval
        (QInterval.pointInterval
          (gaussianEvenIntegralPrefix
            (gaussianRadiusTaylorQuadratureTerms radius stage) radius)) := by
  rw [gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval]
  unfold gaussianRadiusTaylorQuadratureTerms QInterval.ContainsInterval
    QInterval.pointInterval
  have hordered := RealCompute.interval_order_of_valid
    (gaussianRadiusIntegratedSeriesRaw radius hradius)
    (gaussianRadiusIntegratedSeriesRaw_valid radius hradius) stage
  rw [gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval] at hordered
  exact ⟨Rat.le_refl, hordered⟩

theorem gaussianRadiusTaylorQuadratureCandidateRaw_equiv_series
    (radius : Rat) (hradius : 0 <= radius) :
    (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).Equiv
      (gaussianRadiusIntegratedSeriesRaw radius hradius) := by
  intro stage
  apply (RealCompute.compareAt_overlap_iff
    (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius)
    (gaussianRadiusIntegratedSeriesRaw radius hradius) stage stage).2
  have hc := gaussianRadiusTaylorQuadratureCandidateRaw_contains_prefix
    radius hradius stage
  have ha := gaussianRadiusIntegratedSeriesRaw_contains_quadraturePrefix
    radius hradius stage
  unfold QInterval.ContainsInterval QInterval.pointInterval at hc ha
  exact ⟨Rat.le_trans hc.1 ha.2, Rat.le_trans ha.1 hc.2⟩

/-- The stabilization radius is the exact, computable width of the series
anchor at the same stage.  Only this rational width, not the anchor center,
is read by the stabilized quadrature evaluator. -/
def gaussianRadiusTaylorQuadratureStabilizationRadius
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) : Rat :=
  ((gaussianRadiusIntegratedSeriesRaw radius hradius).compute stage).width

theorem gaussianRadiusTaylorQuadratureStabilizationRadius_shrinks
    (radius : Rat) (hradius : 0 <= radius) :
    ShrinksToZero
      (gaussianRadiusTaylorQuadratureStabilizationRadius radius hradius) :=
  (gaussianRadiusIntegratedSeriesRaw_valid radius hradius).2.2

/-- A valid nested computation obtained solely by intersecting the finitely
many midpoint candidates seen so far, widened by the explicit series-width
schedule. -/
def gaussianRadiusTaylorQuadratureRaw
    (radius : Rat) (hradius : 0 <= radius) : RealCompute :=
  RealCompute.prefixStabilize
    (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius)
    (gaussianRadiusTaylorQuadratureStabilizationRadius radius hradius)

theorem gaussianRadiusTaylorQuadratureRaw_valid
    (radius : Rat) (hradius : 0 <= radius) :
    (gaussianRadiusTaylorQuadratureRaw radius hradius).Valid := by
  unfold gaussianRadiusTaylorQuadratureRaw
  exact RealCompute.prefixStabilize_valid
    (gaussianRadiusTaylorQuadratureCandidateRaw_widths_shrink radius hradius)
    (gaussianRadiusIntegratedSeriesRaw_valid radius hradius)
    (gaussianRadiusTaylorQuadratureCandidateRaw_equiv_series radius hradius)
    (fun _ => Rat.le_refl)
    (gaussianRadiusTaylorQuadratureStabilizationRadius_shrinks radius hradius)

theorem gaussianRadiusTaylorQuadratureRaw_equiv_series
    (radius : Rat) (hradius : 0 <= radius) :
    (gaussianRadiusTaylorQuadratureRaw radius hradius).Equiv
      (gaussianRadiusIntegratedSeriesRaw radius hradius) := by
  unfold gaussianRadiusTaylorQuadratureRaw
  exact RealCompute.prefixStabilize_equiv_anchor
    (gaussianRadiusIntegratedSeriesRaw_valid radius hradius)
    (gaussianRadiusTaylorQuadratureCandidateRaw_equiv_series radius hradius)
    (fun _ => Rat.le_refl)

/-! ## Growing-radius schedule for full-line gluing -/

/-- The leading coefficient in the geometric estimate for the shifted
alternating tail. -/
def gaussianIntegralShiftedGeometricBound
    (radius : Rat) : Rat :=
  2 * radius * RationalMajorant.factorialTailTerm (radius * radius)
    (gaussianIntegralTailStart radius)

theorem gaussianIntegralShiftedGeometricBound_nonneg
    (radius : Rat) (hradius : 0 <= radius) :
    0 <= gaussianIntegralShiftedGeometricBound radius := by
  unfold gaussianIntegralShiftedGeometricBound
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) hradius)
    (RationalMajorant.factorialTailTerm_nonneg
      (Rat.mul_nonneg hradius hradius) _)

theorem gaussianIntegralShiftedMagnitude_le_geometric
    (radius : Rat) (hradius : 0 <= radius) (j : Nat) :
    gaussianIntegralShiftedMagnitude radius j <=
      gaussianIntegralShiftedGeometricBound radius *
        ((1 : Rat) / 2) ^ j := by
  let C := radius * radius
  let start := gaussianIntegralTailStart radius
  have hC : 0 <= C := by
    dsimp [C]
    exact Rat.mul_nonneg hradius hradius
  have hstart : C <= (((start + 1 : Nat) : Rat) / 2) := by
    simpa [C, start] using gaussianIntegralTailStart_satisfies radius hradius
  have hgeom := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC hstart j
  have hleibniz : Series.leibnizTerm (start + j) <= 1 := by
    calc
      Series.leibnizTerm (start + j) <=
          1 / (((start + j + 1 : Nat) : Rat)) :=
        Series.leibnizTerm_le_one_div_succ _
      _ <= 1 / ((1 : Nat) : Rat) := by
        exact Series.one_div_nat_antitone_series (by omega) (by omega) (by omega)
      _ = 1 := by decide +kernel
  have hconst : 0 <= 2 * radius :=
    Rat.mul_nonneg (by decide +kernel) hradius
  have hfactor : 0 <= RationalMajorant.factorialTailTerm C (start + j) :=
    RationalMajorant.factorialTailTerm_nonneg hC _
  unfold gaussianIntegralShiftedMagnitude gaussianIntegralTermMagnitude
    gaussianIntegralShiftedGeometricBound
  change 2 * radius * RationalMajorant.factorialTailTerm C (start + j) *
      Series.leibnizTerm (start + j) <=
    2 * radius * RationalMajorant.factorialTailTerm C start *
      ((1 : Rat) / 2) ^ j
  calc
    2 * radius * RationalMajorant.factorialTailTerm C (start + j) *
        Series.leibnizTerm (start + j) <=
      2 * radius * RationalMajorant.factorialTailTerm C (start + j) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hleibniz
          (Rat.mul_nonneg hconst hfactor)
    _ = 2 * radius * RationalMajorant.factorialTailTerm C (start + j) := by
      simp
    _ <= 2 * radius *
        (RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ j) :=
      Rat.mul_le_mul_of_nonneg_left hgeom hconst
    _ = 2 * radius * RationalMajorant.factorialTailTerm C start *
        ((1 : Rat) / 2) ^ j := by
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianRadiusIntegratedSeriesRaw_width_eq_shiftedMagnitude
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    ((gaussianRadiusIntegratedSeriesRaw radius hradius).compute stage).width =
      gaussianIntegralShiftedMagnitude radius (2 * stage) := by
  let S := gaussianIntegralShiftedAlternatingRaw radius hradius
  let I := S.interval stage
  let p := gaussianEvenIntegralPrefix
    (gaussianIntegralTailStart radius) radius
  change p + I.hi - (p + I.lo) = _
  have hcancel : p + I.hi - (p + I.lo) = I.hi - I.lo := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  rw [hcancel]
  change I.width = _
  exact Series.AlternatingRaw.interval_width_eq S stage

def gaussianGrowingRadius (stage : Nat) : Rat := (stage + 1 : Nat)

theorem gaussianGrowingRadius_nonneg (stage : Nat) :
    0 <= gaussianGrowingRadius stage := by
  unfold gaussianGrowingRadius
  exact_mod_cast (Nat.zero_le (stage + 1))

theorem gaussianGrowingRadius_pos (stage : Nat) :
    0 < gaussianGrowingRadius stage := by
  unfold gaussianGrowingRadius
  exact_mod_cast (Nat.succ_pos stage)

/-- The reciprocal-chart lower endpoint mapping the inner growing radius
`k+1` to the outer growing radius `n+1`. -/
def gaussianGrowingAnnulusReciprocalLower (k n : Nat) : Rat :=
  gaussianGrowingRadius k / gaussianGrowingRadius n

theorem gaussianGrowingAnnulusReciprocalLower_pos (k n : Nat) :
    0 < gaussianGrowingAnnulusReciprocalLower k n := by
  unfold gaussianGrowingAnnulusReciprocalLower
  rw [Rat.div_def]
  exact Rat.mul_pos (gaussianGrowingRadius_pos k)
    ((Rat.inv_pos).2 (gaussianGrowingRadius_pos n))

theorem gaussianGrowingAnnulusReciprocalLower_le_one
    {k n : Nat} (hkn : k <= n) :
    gaussianGrowingAnnulusReciprocalLower k n <= 1 := by
  have hradii : gaussianGrowingRadius k <= gaussianGrowingRadius n := by
    unfold gaussianGrowingRadius
    exact_mod_cast (Nat.add_le_add_right hkn 1)
  have hnpos := gaussianGrowingRadius_pos n
  unfold gaussianGrowingAnnulusReciprocalLower
  rw [Rat.div_def]
  have hscaled := Rat.mul_le_mul_of_nonneg_right hradii
    (Rat.le_of_lt ((Rat.inv_pos).2 hnpos))
  simpa [Rat.mul_assoc,
    Rat.mul_inv_cancel (gaussianGrowingRadius n) (Rat.ne_of_gt hnpos)] using hscaled

theorem gaussianGrowingAnnulusReciprocalLower_lt_one
    {k n : Nat} (hkn : k < n) :
    gaussianGrowingAnnulusReciprocalLower k n < 1 := by
  have hradii : gaussianGrowingRadius k < gaussianGrowingRadius n := by
    unfold gaussianGrowingRadius
    exact_mod_cast (Nat.add_lt_add_right hkn 1)
  have hnpos := gaussianGrowingRadius_pos n
  unfold gaussianGrowingAnnulusReciprocalLower
  rw [Rat.div_def]
  have hscaled := Rat.mul_lt_mul_of_pos_right hradii
    ((Rat.inv_pos).2 hnpos)
  simpa [Rat.mul_assoc,
    Rat.mul_inv_cancel (gaussianGrowingRadius n) (Rat.ne_of_gt hnpos)] using hscaled

theorem gaussianGrowingRadius_div_reciprocalLower_eq
    (k n : Nat) :
    gaussianGrowingRadius k /
        gaussianGrowingAnnulusReciprocalLower k n =
      gaussianGrowingRadius n := by
  have hkNe : gaussianGrowingRadius k ≠ 0 :=
    Rat.ne_of_gt (gaussianGrowingRadius_pos k)
  have hnNe : gaussianGrowingRadius n ≠ 0 :=
    Rat.ne_of_gt (gaussianGrowingRadius_pos n)
  unfold gaussianGrowingAnnulusReciprocalLower
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel (gaussianGrowingRadius k) hkNe,
    Rat.mul_inv_cancel (gaussianGrowingRadius n) hnNe]

theorem gaussianGrowingRadius_div_one (k : Nat) :
    gaussianGrowingRadius k / 1 = gaussianGrowingRadius k := by
  have hinv : (1 : Rat)⁻¹ = 1 := by decide +kernel
  rw [Rat.div_def, hinv, Rat.mul_one]

/-- For fixed inner radius, the reciprocal-chart lower endpoint has the
explicit `(k+1)/(stage+1)` convergence modulus. -/
theorem gaussianGrowingAnnulusReciprocalLower_add_le_natRate
    (k stage : Nat) :
    gaussianGrowingAnnulusReciprocalLower k (k + stage) <=
      ((k + 1 : Nat) : Rat) / (((stage + 1 : Nat) : Rat)) := by
  have hinv := Series.one_div_nat_antitone_series
    (n := stage + 1) (m := k + stage + 1)
    (by omega) (by omega) (by omega)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hinv
    (Rat.le_of_lt (gaussianGrowingRadius_pos k))
  simpa [gaussianGrowingAnnulusReciprocalLower, gaussianGrowingRadius,
    Rat.div_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hscaled

theorem gaussianGrowingAnnulusReciprocalLower_add_shrinks (k : Nat) :
    ShrinksToZero
      (fun stage => gaussianGrowingAnnulusReciprocalLower k (k + stage)) :=
  shrinksToZero_of_natOverSuccBound
    (C := k + 1) (gaussianGrowingAnnulusReciprocalLower_add_le_natRate k)

/-! ## Reciprocal-chart Gaussian density for strict annuli -/

/-- The Jacobian-weighted reciprocal presentation of the Gaussian under
`x = cutoff / t`.  On a positive chart it represents
`(cutoff/t^2) * exp (-(cutoff/t)^2)`. -/
def reciprocalGaussianChartDensityRaw (cutoff t : Rat) : RealCompute :=
  RealCompute.scaleRat (cutoff / (t * t))
    (reciprocalGaussianRaw (cutoff / t))

theorem reciprocalGaussianChartDensityRaw_valid
    (cutoff t : Rat) :
    (reciprocalGaussianChartDensityRaw cutoff t).Valid := by
  unfold reciprocalGaussianChartDensityRaw
  exact RealCompute.scaleRat_valid
    (reciprocalGaussianRaw_valid (cutoff / t))

theorem reciprocalGaussianChartDensityRaw_compute_lo_nonneg
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t)
    (stage : Nat) :
    0 <= ((reciprocalGaussianChartDensityRaw cutoff t).compute stage).lo := by
  have htt : 0 < t * t := Rat.mul_pos ht ht
  have hcoeff : 0 <= cutoff / (t * t) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 htt))
  simp only [reciprocalGaussianChartDensityRaw, RealCompute.scaleRat,
    RealCompute.scaleRatCompute, if_pos hcoeff]
  exact Rat.mul_nonneg hcoeff
    (reciprocalNegativeExpRaw_compute_lo_nonneg
      ((cutoff / t) * (cutoff / t))
      (rat_square_nonneg_basic (cutoff / t)) stage)

theorem reciprocalGaussianChartDensityRaw_compute_hi_le
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t)
    (stage : Nat) :
    ((reciprocalGaussianChartDensityRaw cutoff t).compute stage).hi <=
      1 / cutoff := by
  have htt : 0 < t * t := Rat.mul_pos ht ht
  have hcoeff : 0 <= cutoff / (t * t) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 htt))
  have hx : 0 < cutoff / t := by
    rw [Rat.div_def]
    exact Rat.mul_pos hcutoff ((Rat.inv_pos).2 ht)
  have hpoint :=
    reciprocalGaussianRaw_compute_hi_le_reciprocalSquare
      (cutoff / t) hx stage
  simp only [reciprocalGaussianChartDensityRaw, RealCompute.scaleRat,
    RealCompute.scaleRatCompute, if_pos hcoeff]
  calc
    cutoff / (t * t) *
        ((reciprocalGaussianRaw (cutoff / t)).compute stage).hi <=
      cutoff / (t * t) * (1 / ((cutoff / t) * (cutoff / t))) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hcoeff
    _ = 1 / cutoff := by
      symm
      exact reciprocalSquareTail_fold_agrees cutoff t hcutoff ht

/-- Every positive reciprocal-chart Gaussian point has the constant rational
range `[0,1/cutoff]`, uniformly in evaluator precision. -/
theorem reciprocalGaussianChartDensityRaw_compute_mem_constantRange
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t)
    (stage : Nat) :
    (QInterval.mk 0 (1 / cutoff)).ContainsInterval
      ((reciprocalGaussianChartDensityRaw cutoff t).compute stage) :=
  ⟨reciprocalGaussianChartDensityRaw_compute_lo_nonneg
      cutoff t hcutoff ht stage,
    reciprocalGaussianChartDensityRaw_compute_hi_le
      cutoff t hcutoff ht stage⟩

theorem reciprocalGaussianChartDensityRaw_nonnegative
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t) :
    (RealCompute.ofRat 0).Le (reciprocalGaussianChartDensityRaw cutoff t) := by
  apply RealCompute.le_of_sameStage
    (x := RealCompute.ofRat 0)
    (y := reciprocalGaussianChartDensityRaw cutoff t)
    (RealCompute.ofRat_valid 0)
    (reciprocalGaussianChartDensityRaw_valid cutoff t)
  intro stage
  rw [RealCompute.ofRat_compute]
  have hlo := reciprocalGaussianChartDensityRaw_compute_lo_nonneg
    cutoff t hcutoff ht stage
  have hordered := RealCompute.interval_order_of_valid
    (reciprocalGaussianChartDensityRaw cutoff t)
    (reciprocalGaussianChartDensityRaw_valid cutoff t) stage
  exact Rat.le_trans hlo hordered

theorem reciprocalGaussianChartDensityRaw_le_constant
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t) :
    (reciprocalGaussianChartDensityRaw cutoff t).Le
      (RealCompute.ofRat (1 / cutoff)) := by
  apply RealCompute.le_of_sameStage
    (x := reciprocalGaussianChartDensityRaw cutoff t)
    (y := RealCompute.ofRat (1 / cutoff))
    (reciprocalGaussianChartDensityRaw_valid cutoff t)
    (RealCompute.ofRat_valid (1 / cutoff))
  intro stage
  rw [RealCompute.ofRat_compute]
  have hordered := RealCompute.interval_order_of_valid
    (reciprocalGaussianChartDensityRaw cutoff t)
    (reciprocalGaussianChartDensityRaw_valid cutoff t) stage
  exact Rat.le_trans hordered
    (reciprocalGaussianChartDensityRaw_compute_hi_le
      cutoff t hcutoff ht stage)

/-! ### Exact reciprocal Stieltjes cells

The midpoint chart rule above is convenient for Darboux enclosure.  For the
eventual comparison with an annulus in the original `x` coordinate we also
record the literal Stieltjes rectangle swept by `x = cutoff / t`.  Choosing
the left `t` endpoint means choosing the outer `x` endpoint; this is exactly
the orientation for which the reciprocal-square majorant pays no more than
the chart length divided by `cutoff`. -/

/-- A rational sample of the represented Gaussian at the outer endpoint
`x = cutoff / t` of a reciprocal-chart cell. -/
def reciprocalGaussianTailStieltjesSampleValue
    (cutoff t : Rat) (stage : Nat) : Rat :=
  ((reciprocalGaussianRaw (cutoff / t)).compute stage).midpoint

theorem reciprocalGaussianTailStieltjesSampleValue_pos
    (cutoff t : Rat) (stage : Nat) :
    0 < reciprocalGaussianTailStieltjesSampleValue cutoff t stage := by
  let I := (reciprocalGaussianRaw (cutoff / t)).compute stage
  have hlo : 0 < I.lo := by
    simpa [I] using
      reciprocalGaussianRaw_compute_lo_pos (cutoff / t) stage
  have hordered : I.lo <= I.hi :=
    RealCompute.interval_order_of_valid
      (reciprocalGaussianRaw (cutoff / t))
      (reciprocalGaussianRaw_valid (cutoff / t)) stage
  unfold reciprocalGaussianTailStieltjesSampleValue QInterval.midpoint
  have hsum : 0 < I.lo + I.hi := by grind
  rw [Rat.div_def]
  exact Rat.mul_pos hsum ((Rat.inv_pos).2 (by decide +kernel))

/-- Every reciprocal-Gaussian sample whose original-coordinate point lies
in `[0, radius]` inherits the same explicit positive rational lower bound,
uniformly in the evaluator stage. -/
theorem reciprocalGaussianUniformPositiveLowerBound_le_stieltjesSampleValue
    {cutoff t radius : Rat} (stage : Nat)
    (hpoint : 0 <= cutoff / t) (hpointRadius : cutoff / t <= radius) :
    reciprocalGaussianUniformPositiveLowerBound radius <=
      reciprocalGaussianTailStieltjesSampleValue cutoff t stage := by
  let I := (reciprocalGaussianRaw (cutoff / t)).compute stage
  have hlower : reciprocalGaussianUniformPositiveLowerBound radius <= I.lo := by
    simpa [I] using
      reciprocalGaussianUniformPositiveLowerBound_le_compute_lo
        hpoint hpointRadius stage
  have hordered : I.lo <= I.hi :=
    RealCompute.interval_order_of_valid
      (reciprocalGaussianRaw (cutoff / t))
      (reciprocalGaussianRaw_valid (cutoff / t)) stage
  have hmid := (QInterval.midpoint_mem hordered).1
  exact Rat.le_trans hlower (by
    simpa [I, reciprocalGaussianTailStieltjesSampleValue] using hmid)

/-- Changing from the reciprocal Gaussian representative to the matching
negative factorial-series representative costs at most the sum of the two
finite box widths. -/
theorem reciprocalGaussianTailStieltjesSampleValue_sub_profilePrefix_le_widths
    (cutoff t : Rat) (stage : Nat) :
    qabs (reciprocalGaussianTailStieltjesSampleValue cutoff t stage -
      gaussianEvenProfilePrefix
        (expPowerSeriesTerms (-(cutoff / t * (cutoff / t))) stage)
        (cutoff / t)) <=
      ((reciprocalGaussianRaw (cutoff / t)).compute stage).width +
        ((expPowerSeries
          (-(cutoff / t * (cutoff / t)))).compute stage).width := by
  let x : Rat := cutoff / t
  let I := (reciprocalGaussianRaw x).compute stage
  let J := (expPowerSeries (-(x * x))).compute stage
  have hI := RealCompute.interval_order_of_valid
    (reciprocalGaussianRaw x) (reciprocalGaussianRaw_valid x) stage
  have hJ := RealCompute.interval_order_of_valid
    (expPowerSeries (-(x * x)))
    (ExpProofs.expPowerSeries_valid (-(x * x))) stage
  have hcmp := reciprocalGaussianRaw_equiv_expPowerSeries_neg_square x stage
  have hover := (RealCompute.compareAt_overlap_iff
    (reciprocalGaussianRaw x) (expPowerSeries (-(x * x)))
      stage stage).1 hcmp
  have hmid :=
    QInterval.qabs_midpoint_sub_midpoint_le_width_add_of_overlaps
      hI hJ hover
  change qabs (I.midpoint -
      gaussianEvenProfilePrefix
        (expPowerSeriesTerms (-(x * x)) stage) x) <=
    I.width + J.width
  rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
  rw [← ExpProofs.expPowerSeries_compute_midpoint_eq_centerAtTerms]
  exact hmid

/-- Explicit geometric coefficient for changing Gaussian representatives at
one rational point. -/
def reciprocalGaussianRepresentationChangeBound (x : Rat) : Rat :=
  (4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
      (expPowerSeriesTerms (x * x) 0))) /
      ((1 + x * x) * (1 + x * x)) +
    4 * qabs (ExpProofs.powerSeriesTermAtTerms (-(x * x))
      (expPowerSeriesTerms (-(x * x)) 0))

theorem reciprocalGaussianRepresentationChangeBound_nonneg (x : Rat) :
    0 <= reciprocalGaussianRepresentationChangeBound x := by
  have hden : 0 < (1 + x * x) * (1 + x * x) := by
    have hsquare := rat_square_nonneg_basic x
    exact Rat.mul_pos (by grind) (by grind)
  unfold reciprocalGaussianRepresentationChangeBound
  rw [Rat.div_def]
  exact Rat.add_nonneg
    (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
      (Rat.le_of_lt ((Rat.inv_pos).2 hden)))
    (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))

theorem reciprocalGaussianTailStieltjesSampleValue_sub_profilePrefix_le_geometric
    (cutoff t : Rat) (stage : Nat) :
    qabs (reciprocalGaussianTailStieltjesSampleValue cutoff t stage -
      gaussianEvenProfilePrefix
        (expPowerSeriesTerms (-(cutoff / t * (cutoff / t))) stage)
        (cutoff / t)) <=
      reciprocalGaussianRepresentationChangeBound (cutoff / t) *
        ((1 : Rat) / 2) ^ stage := by
  let x : Rat := cutoff / t
  have hbase :=
    reciprocalGaussianTailStieltjesSampleValue_sub_profilePrefix_le_widths
      cutoff t stage
  have hrecip := reciprocalGaussianRaw_compute_width_le_geometric x stage
  have hexp := ExpProofs.expPowerSeries_compute_width_le_geometric
    (-(x * x)) stage
  have hadd := rat_add_le_add hrecip hexp
  exact Rat.le_trans hbase (by
    change
      ((reciprocalGaussianRaw x).compute stage).width +
          ((expPowerSeries (-(x * x))).compute stage).width <=
        reciprocalGaussianRepresentationChangeBound x *
          ((1 : Rat) / 2) ^ stage
    calc
      ((reciprocalGaussianRaw x).compute stage).width +
          ((expPowerSeries (-(x * x))).compute stage).width <=
        (((4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
              (expPowerSeriesTerms (x * x) 0))) /
            ((1 + x * x) * (1 + x * x))) *
              ((1 : Rat) / 2) ^ stage) +
          ((4 * qabs (ExpProofs.powerSeriesTermAtTerms (-(x * x))
              (expPowerSeriesTerms (-(x * x)) 0))) *
              ((1 : Rat) / 2) ^ stage) := hadd
      _ = reciprocalGaussianRepresentationChangeBound x *
          ((1 : Rat) / 2) ^ stage := by
        unfold reciprocalGaussianRepresentationChangeBound
        grind [Rat.add_mul])

/-- One computable factorial-prefix length dominating every Gaussian sample
used by a finite reciprocal-chart partition at the requested raw stage. -/
def reciprocalGaussianTailCommonProfileTerms
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) : Nat :=
  2 * (ExpProofs.finiteNatMax
      ((List.range P.pieces).map (fun k =>
        expPowerSeriesTerms
          (-(cutoff / P.point k * (cutoff / P.point k))) stage)) +
    gaussianIntegralTailStart (cutoff / lower) +
    gaussianIntegralTailStart (cutoff / upper) + stage + 1)

theorem reciprocalGaussianTailCommonProfileTerms_dominates
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat) (hk : k < P.pieces) :
    expPowerSeriesTerms
        (-(cutoff / P.point k * (cutoff / P.point k))) stage <=
      reciprocalGaussianTailCommonProfileTerms P cutoff stage := by
  have hbase :
      expPowerSeriesTerms
          (-(cutoff / P.point k * (cutoff / P.point k))) stage <=
        ExpProofs.finiteNatMax
          ((List.range P.pieces).map (fun i =>
            expPowerSeriesTerms
              (-(cutoff / P.point i * (cutoff / P.point i))) stage)) := by
    apply ExpProofs.finiteNatMax_mem
    apply List.mem_map.mpr
    exact ⟨k, List.mem_range.mpr hk, rfl⟩
  unfold reciprocalGaussianTailCommonProfileTerms
  omega

/-- The common Gaussian profile prefix is deliberately even, so it can be
read as an even shifted alternating endpoint at every radius. -/
theorem reciprocalGaussianTailCommonProfileTerms_even
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) :
    reciprocalGaussianTailCommonProfileTerms P cutoff stage % 2 = 0 := by
  unfold reciprocalGaussianTailCommonProfileTerms
  omega

/-- The common prefix lies at least `2*stage` terms beyond the outer endpoint's
alternating-tail start. -/
theorem gaussianIntegralTailStart_outer_add_two_stage_le_commonProfileTerms
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) :
    gaussianIntegralTailStart (cutoff / lower) + 2 * stage <=
      reciprocalGaussianTailCommonProfileTerms P cutoff stage := by
  unfold reciprocalGaussianTailCommonProfileTerms
  omega

/-- The same common prefix lies at least `2*stage` terms beyond the inner
endpoint's alternating-tail start. -/
theorem gaussianIntegralTailStart_inner_add_two_stage_le_commonProfileTerms
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) :
    gaussianIntegralTailStart (cutoff / upper) + 2 * stage <=
      reciprocalGaussianTailCommonProfileTerms P cutoff stage := by
  unfold reciprocalGaussianTailCommonProfileTerms
  omega

/-- A raw reciprocal-Gaussian sample differs from the single common finite
factorial prefix by the representation-change budget plus the literal finite
factorial block inserted when enlarging its adaptive prefix. -/
theorem reciprocalGaussianTailStieltjesSampleValue_sub_commonProfile_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat) (hk : k < P.pieces) :
    qabs (reciprocalGaussianTailStieltjesSampleValue
        cutoff (P.point k) stage -
      gaussianEvenProfilePrefix
        (reciprocalGaussianTailCommonProfileTerms P cutoff stage)
        (cutoff / P.point k)) <=
      reciprocalGaussianRepresentationChangeBound
          (cutoff / P.point k) * ((1 : Rat) / 2) ^ stage +
        RationalMajorant.factorialTailPartial
          ((cutoff / P.point k) * (cutoff / P.point k))
          (expPowerSeriesTerms
            (-(cutoff / P.point k * (cutoff / P.point k))) stage)
          (reciprocalGaussianTailCommonProfileTerms P cutoff stage -
            expPowerSeriesTerms
              (-(cutoff / P.point k * (cutoff / P.point k))) stage) := by
  let x : Rat := cutoff / P.point k
  let adaptive : Nat := expPowerSeriesTerms (-(x * x)) stage
  let common : Nat := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  have hdom : adaptive <= common := by
    simpa [x, adaptive, common] using
      reciprocalGaussianTailCommonProfileTerms_dominates
        P cutoff stage k hk
  have hsum : adaptive + (common - adaptive) = common :=
    Nat.add_sub_of_le hdom
  have hraw :=
    reciprocalGaussianTailStieltjesSampleValue_sub_profilePrefix_le_geometric
      cutoff (P.point k) stage
  have hx2 : 0 <= x * x := rat_square_nonneg_basic x
  have hinput : qabs (-(x * x)) <= x * x := by
    rw [qabs_neg, qabs_eq_self_of_nonneg hx2]
    exact Rat.le_refl
  have hcenters :=
    ExpProofs.qabs_powerSeriesCenterAtTerms_add_sub_le_factorialTailPartial
      (x * x) (-(x * x)) hx2 hinput adaptive (common - adaptive)
  have hprofiles :
      qabs (gaussianEvenProfilePrefix adaptive x -
        gaussianEvenProfilePrefix common x) <=
        RationalMajorant.factorialTailPartial
          (x * x) adaptive (common - adaptive) := by
    rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms,
      gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
    rw [hsum] at hcenters
    have hneg :
        ExpProofs.powerSeriesCenterAtTerms (-(x * x)) adaptive -
            ExpProofs.powerSeriesCenterAtTerms (-(x * x)) common =
          -(ExpProofs.powerSeriesCenterAtTerms (-(x * x)) common -
            ExpProofs.powerSeriesCenterAtTerms (-(x * x)) adaptive) := by
      grind [Rat.sub_eq_add_neg]
    rw [hneg, qabs_neg]
    exact hcenters
  have hdecomp :
      reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage -
          gaussianEvenProfilePrefix common x =
        (reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage -
            gaussianEvenProfilePrefix adaptive x) +
          (gaussianEvenProfilePrefix adaptive x -
            gaussianEvenProfilePrefix common x) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs
      (reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage -
        gaussianEvenProfilePrefix common x) <= _
  rw [hdecomp]
  calc
    qabs
        ((reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage -
            gaussianEvenProfilePrefix adaptive x) +
          (gaussianEvenProfilePrefix adaptive x -
            gaussianEvenProfilePrefix common x)) <=
      qabs (reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage -
          gaussianEvenProfilePrefix adaptive x) +
        qabs (gaussianEvenProfilePrefix adaptive x -
          gaussianEvenProfilePrefix common x) := qabs_add_le _ _
    _ <= reciprocalGaussianRepresentationChangeBound x *
          ((1 : Rat) / 2) ^ stage +
        RationalMajorant.factorialTailPartial
          (x * x) adaptive (common - adaptive) := by
      apply rat_add_le_add
      · simpa [x, adaptive] using hraw
      · exact hprofiles

/-- Enlarging an adaptive Gaussian prefix to the finite common prefix costs
at most a geometric tail whose coefficient is computed at stage zero. -/
theorem reciprocalGaussianCommonProfile_factorialBlock_le_geometric
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat) (hk : k < P.pieces) :
    RationalMajorant.factorialTailPartial
        ((cutoff / P.point k) * (cutoff / P.point k))
        (expPowerSeriesTerms
          (-(cutoff / P.point k * (cutoff / P.point k))) stage)
        (reciprocalGaussianTailCommonProfileTerms P cutoff stage -
          expPowerSeriesTerms
            (-(cutoff / P.point k * (cutoff / P.point k))) stage) <=
      2 * RationalMajorant.factorialTailTerm
          ((cutoff / P.point k) * (cutoff / P.point k))
          (expPowerSeriesTerms
            (-(cutoff / P.point k * (cutoff / P.point k))) 0) *
        ((1 : Rat) / 2) ^ stage := by
  let x : Rat := cutoff / P.point k
  let C : Rat := x * x
  let N : Nat := expPowerSeriesTerms (-C) 0
  let m : Nat := reciprocalGaussianTailCommonProfileTerms P cutoff stage -
    expPowerSeriesTerms (-C) stage
  have hC : 0 <= C := by
    dsimp [C]
    exact rat_square_nonneg_basic x
  have hstart : C <= (((N + 1 : Nat) : Rat) / 2) := by
    have h := ExpProofs.expPowerSeriesTerms_zero_factorialStart (-C)
    rw [qabs_neg, qabs_eq_self_of_nonneg hC] at h
    simpa [N] using h
  have hshift : expPowerSeriesTerms (-C) stage = N + stage := by
    dsimp [N]
    unfold expPowerSeriesTerms
    omega
  have hbound := RationalMajorant.factorialTailPartial_shifted_bound
    hC hstart stage m
  rw [← hshift] at hbound
  simpa [x, C, N, m] using hbound

/-- The exact rational cancellation behind a reciprocal substitution cell.
It is a finite identity, not a change-of-variables theorem. -/
theorem reciprocalPullback_reciprocalSquare_leftRectangle_eq
    (cutoff a b : Rat)
    (hcutoff : 0 < cutoff) (ha : 0 < a) (hb : 0 < b) :
    (1 / ((cutoff / a) * (cutoff / a))) *
        (cutoff / a - cutoff / b) =
      ((b - a) / cutoff) * (a / b) := by
  have hcutoffNe : cutoff ≠ 0 := Rat.ne_of_gt hcutoff
  have haNe : a ≠ 0 := Rat.ne_of_gt ha
  have hbNe : b ≠ 0 := Rat.ne_of_gt hb
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel cutoff hcutoffNe,
    Rat.mul_inv_cancel a haNe,
    Rat.mul_inv_cancel b hbNe]

/-- Exact width formula for a positive reciprocal-image cell. -/
theorem reciprocal_difference_eq_mul_div
    (cutoff a b : Rat) (ha : 0 < a) (hb : 0 < b) :
    cutoff / a - cutoff / b = cutoff * (b - a) / (a * b) := by
  have haNe : a ≠ 0 := Rat.ne_of_gt ha
  have hbNe : b ≠ 0 := Rat.ne_of_gt hb
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel a haNe, Rat.mul_inv_cancel b hbNe]

/-- One reciprocal Stieltjes cell sampled at its outer `x` endpoint is
nonnegative and is bounded by its exact chart-length budget. -/
theorem reciprocalGaussianTailStieltjesCell_nonneg_le
    (cutoff a b : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (ha : 0 < a) (hab : a <= b) :
    0 <= reciprocalGaussianTailStieltjesSampleValue cutoff a stage *
        (cutoff / a - cutoff / b) /\
      reciprocalGaussianTailStieltjesSampleValue cutoff a stage *
          (cutoff / a - cutoff / b) <= (b - a) / cutoff := by
  have hb : 0 < b := by grind
  have hx : 0 < cutoff / a := by
    rw [Rat.div_def]
    exact Rat.mul_pos hcutoff ((Rat.inv_pos).2 ha)
  have hsampleMem := QInterval.midpoint_mem
    (RealCompute.interval_order_of_valid
      (reciprocalGaussianRaw (cutoff / a))
      (reciprocalGaussianRaw_valid (cutoff / a)) stage)
  have hsampleNonneg :
      0 <= reciprocalGaussianTailStieltjesSampleValue cutoff a stage := by
    unfold reciprocalGaussianTailStieltjesSampleValue
    exact Rat.le_trans
      (reciprocalNegativeExpRaw_compute_lo_nonneg
        ((cutoff / a) * (cutoff / a))
        (rat_square_nonneg_basic (cutoff / a)) stage)
      hsampleMem.1
  have hsampleLe :
      reciprocalGaussianTailStieltjesSampleValue cutoff a stage <=
        1 / ((cutoff / a) * (cutoff / a)) := by
    exact Rat.le_trans hsampleMem.2
      (reciprocalGaussianRaw_compute_hi_le_reciprocalSquare
        (cutoff / a) hx stage)
  have hrecip : 1 / b <= 1 / a :=
    RealCompute.one_div_antitone_of_pos ha hab
  have hweight : 0 <= cutoff / a - cutoff / b := by
    rw [Rat.div_def, Rat.div_def]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
      (Rat.le_of_lt hcutoff)
    grind [Rat.sub_eq_add_neg]
  constructor
  · exact Rat.mul_nonneg hsampleNonneg hweight
  · have hmul := Rat.mul_le_mul_of_nonneg_right hsampleLe hweight
    have habdiv : a / b <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := b)
      · rw [Rat.div_def]
        have hbNe : b ≠ 0 := Rat.ne_of_gt hb
        grind [Rat.mul_assoc, Rat.mul_inv_cancel b hbNe]
      · exact hb
    have hbudget : 0 <= (b - a) / cutoff := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by grind [Rat.sub_eq_add_neg])
        (Rat.le_of_lt ((Rat.inv_pos).2 hcutoff))
    have hratio := Rat.mul_le_mul_of_nonneg_left habdiv hbudget
    calc
      reciprocalGaussianTailStieltjesSampleValue cutoff a stage *
          (cutoff / a - cutoff / b) <=
        (1 / ((cutoff / a) * (cutoff / a))) *
          (cutoff / a - cutoff / b) := hmul
      _ = ((b - a) / cutoff) * (a / b) :=
        reciprocalPullback_reciprocalSquare_leftRectangle_eq
          cutoff a b hcutoff ha hb
      _ <= (b - a) / cutoff := by
        simpa only [Rat.mul_one] using hratio

/-- A genuine positive reciprocal-chart cell contributes strictly positive
Gaussian mass at every finite evaluator stage. -/
theorem reciprocalGaussianTailStieltjesCell_pos
    (cutoff a b : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (ha : 0 < a) (hab : a < b) :
    0 < reciprocalGaussianTailStieltjesSampleValue cutoff a stage *
      (cutoff / a - cutoff / b) := by
  have hb : 0 < b := by grind
  have hsample :=
    reciprocalGaussianTailStieltjesSampleValue_pos cutoff a stage
  have hdiff : 0 < b - a := by grind [Rat.sub_eq_add_neg]
  have hden : 0 < a * b := Rat.mul_pos ha hb
  have hweight : 0 < cutoff / a - cutoff / b := by
    rw [reciprocal_difference_eq_mul_div cutoff a b ha hb, Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos hcutoff hdiff)
      ((Rat.inv_pos).2 hden)
  exact Rat.mul_pos hsample hweight

/-- The finite decreasing-coordinate Stieltjes action on an arbitrary
rational chart partition.  The second path is `-cutoff/t`, so its increments
are the positive original-coordinate widths
`cutoff/t_i - cutoff/t_(i+1)`. -/
def reciprocalGaussianTailStieltjesActionOnPartition
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) : Rat :=
  leftStieltjesSum
    (fun i => reciprocalGaussianTailStieltjesSampleValue
      cutoff (P.point i) stage)
    (fun i => -(cutoff / P.point i)) P.pieces

/-- Prefixes of the reciprocal Stieltjes action grow as cells are appended. -/
theorem reciprocalGaussianTailStieltjesAction_prefix_mono
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    forall {i j : Nat}, i <= j -> j <= P.pieces ->
      leftStieltjesSum
          (fun k => reciprocalGaussianTailStieltjesSampleValue
            cutoff (P.point k) stage)
          (fun k => -(cutoff / P.point k)) i <=
        leftStieltjesSum
          (fun k => reciprocalGaussianTailStieltjesSampleValue
            cutoff (P.point k) stage)
          (fun k => -(cutoff / P.point k)) j := by
  intro i j hij hj
  induction hij with
  | refl => exact Rat.le_refl
  | @step j hij ih =>
      have hjlt : j < P.pieces := by omega
      have hjle : j <= P.pieces := Nat.le_of_lt hjlt
      have hpointJ := P.point_in_bounds hjle
      have hpointJPos : 0 < P.point j := by grind
      have hmono : P.point j <= P.point (j + 1) :=
        P.monotone j (j + 1) (Nat.le_succ j) (by omega)
      have hcell := reciprocalGaussianTailStieltjesCell_nonneg_le
        cutoff (P.point j) (P.point (j + 1)) stage
        hcutoff hpointJPos hmono
      rw [leftStieltjesSum]
      have hweight :
          -(cutoff / P.point (j + 1)) - -(cutoff / P.point j) =
            cutoff / P.point j - cutoff / P.point (j + 1) := by
        grind [Rat.sub_eq_add_neg]
      rw [hweight]
      have ih' := ih hjle
      exact Rat.le_trans ih' (by
        have hadd := (Rat.add_le_add_left
          (a := (0 : Rat))
          (b := reciprocalGaussianTailStieltjesSampleValue
              cutoff (P.point j) stage *
            (cutoff / P.point j - cutoff / P.point (j + 1)))
          (c := leftStieltjesSum
            (fun k => reciprocalGaussianTailStieltjesSampleValue
              cutoff (P.point k) stage)
            (fun k => -(cutoff / P.point k)) j)).2 hcell.1
        simpa only [Rat.add_zero] using hadd)

namespace RationalPartition

/-- Reverse a positive rational chart partition through `x = cutoff / t`.
The output is an ordinary increasing rational partition of the corresponding
original-coordinate interval. -/
def reciprocalImage {lower upper : Rat}
    (P : RationalPartition lower upper) (cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    RationalPartition (cutoff / upper) (cutoff / lower) where
  pieces := P.pieces
  positive := P.positive
  point := fun i => cutoff / P.point (P.pieces - i)
  left_endpoint := by simp [P.right_endpoint]
  right_endpoint := by simp [P.left_endpoint]
  monotone := by
    intro i j hij hj
    have hsub : P.pieces - j <= P.pieces - i :=
      Nat.sub_le_sub_left hij P.pieces
    have hsubLe : P.pieces - i <= P.pieces := Nat.sub_le _ _
    have hden := P.monotone
      (P.pieces - j) (P.pieces - i) hsub hsubLe
    have hpointJ := P.point_in_bounds
      (i := P.pieces - j) (Nat.sub_le _ _)
    have hpointJPos : 0 < P.point (P.pieces - j) := by grind
    have hinv := RealCompute.one_div_antitone_of_pos hpointJPos hden
    have hscaled := Rat.mul_le_mul_of_nonneg_left hinv
      (Rat.le_of_lt hcutoff)
    simpa [Rat.div_def] using hscaled

/-- The reversed target-cell index corresponding to source chart cell `k`. -/
def reciprocalImageCellIndex {lower upper : Rat}
    (P : RationalPartition lower upper) (k : Nat) : Nat :=
  P.pieces - 1 - k

theorem reciprocalImageCellIndex_lt {lower upper : Rat}
    (P : RationalPartition lower upper) (k : Nat) (hk : k < P.pieces) :
    P.reciprocalImageCellIndex k < P.pieces := by
  unfold reciprocalImageCellIndex
  omega

/-- A reciprocal-image cell has exactly the reversed source endpoints and
the exact positive Stieltjes width. -/
theorem reciprocalImage_cell_endpoints_width {lower upper : Rat}
    (P : RationalPartition lower upper) (cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (k : Nat) (hk : k < P.pieces) :
    let i := P.reciprocalImageCellIndex k
    let C := (P.reciprocalImage cutoff hcutoff hlower).cell i
      (P.reciprocalImageCellIndex_lt k hk)
    C.lower = cutoff / P.point (k + 1) /\
      C.upper = cutoff / P.point k /\
      C.width = cutoff / P.point k - cutoff / P.point (k + 1) := by
  have hleft :
      P.pieces - (P.pieces - 1 - k) = k + 1 := by omega
  have hright :
      P.pieces - ((P.pieces - 1 - k) + 1) = k := by omega
  dsimp [reciprocalImageCellIndex, reciprocalImage,
    RationalPartition.cell, RationalSubinterval.width]
  rw [hleft, hright]
  exact ⟨rfl, rfl, rfl⟩

/-- A source step bound transports through the reciprocal map with the
explicit Lipschitz loss `cutoff/lower²`. -/
theorem reciprocalImage_maxStepAtMost {lower upper : Rat}
    (P : RationalPartition lower upper) (cutoff delta : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hstep : P.MaxStepAtMost delta) :
    (P.reciprocalImage cutoff hcutoff hlower).MaxStepAtMost
      (cutoff * delta / (lower * lower)) := by
  have hlower0 : 0 <= lower := Rat.le_of_lt hlower
  have hlowerSq : 0 < lower * lower := Rat.mul_pos hlower hlower
  constructor
  · rw [Rat.div_def]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.le_of_lt hcutoff) hstep.1)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlowerSq))
  · intro i hi
    change i < P.pieces at hi
    let k : Nat := P.pieces - 1 - i
    have hk : k < P.pieces := by
      dsimp [k]
      omega
    have hleft : P.pieces - (i + 1) = k := by
      dsimp [k]
      omega
    have hright : P.pieces - i = k + 1 := by
      dsimp [k]
      omega
    have hkle : k + 1 <= P.pieces := Nat.succ_le_of_lt hk
    have haBounds := P.point_in_bounds (Nat.le_of_lt hk)
    have hbBounds := P.point_in_bounds hkle
    have ha : 0 < P.point k := by grind
    have hb : 0 < P.point (k + 1) := by grind
    have hab : P.point k <= P.point (k + 1) :=
      P.monotone k (k + 1) (Nat.le_succ k) hkle
    have hcell := hstep.2 k hk
    have hdenLower : lower * lower <= P.point k * P.point (k + 1) := by
      calc
        lower * lower <= P.point k * lower :=
          Rat.mul_le_mul_of_nonneg_right haBounds.1 hlower0
        _ <= P.point k * P.point (k + 1) :=
          Rat.mul_le_mul_of_nonneg_left hbBounds.1 (Rat.le_of_lt ha)
    have hdenPos : 0 < P.point k * P.point (k + 1) := Rat.mul_pos ha hb
    have hinv := RealCompute.one_div_antitone_of_pos hlowerSq hdenLower
    have hinv' : (P.point k * P.point (k + 1))⁻¹ <=
        (lower * lower)⁻¹ := by
      simpa [Rat.div_def] using hinv
    have hnum0 : 0 <= cutoff * (P.point (k + 1) - P.point k) :=
      Rat.mul_nonneg (Rat.le_of_lt hcutoff) (by grind [Rat.sub_eq_add_neg])
    have hmax0 : 0 <= cutoff * delta :=
      Rat.mul_nonneg (Rat.le_of_lt hcutoff) hstep.1
    have hnum :
        cutoff * (P.point (k + 1) - P.point k) <= cutoff * delta :=
      Rat.mul_le_mul_of_nonneg_left hcell (Rat.le_of_lt hcutoff)
    change cutoff / P.point (P.pieces - (i + 1)) -
        cutoff / P.point (P.pieces - i) <= _
    rw [hleft, hright,
      reciprocal_difference_eq_mul_div cutoff (P.point k) (P.point (k + 1)) ha hb,
      Rat.div_def, Rat.div_def]
    calc
      cutoff * (P.point (k + 1) - P.point k) *
          (P.point k * P.point (k + 1))⁻¹ <=
        cutoff * delta * (P.point k * P.point (k + 1))⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hnum
            (Rat.le_of_lt ((Rat.inv_pos).2 hdenPos))
      _ <= cutoff * delta * (lower * lower)⁻¹ :=
          Rat.mul_le_mul_of_nonneg_left hinv' hmax0

/-- On a uniform source chart the reciprocal-image quadratic variation has
an explicit rational mesh bound. -/
theorem reciprocalImage_uniform_quadraticVariation_le
    (lower upper cutoff : Rat) (pieces : Nat)
    (hpieces : 0 < pieces) (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
    let Q := P.reciprocalImage cutoff hcutoff hlower
    quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces <=
      (cutoff * mesh lower upper pieces / (lower * lower)) *
        (cutoff / lower - cutoff / upper) := by
  let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
  let Q := P.reciprocalImage cutoff hcutoff hlower
  have hsource : P.MaxStepAtMost (mesh lower upper pieces) := by
    simpa [P] using
      (RationalPartition.uniform_maxStepAtMost_mesh
        lower upper pieces hpieces hlowerUpper)
  have himage : Q.MaxStepAtMost
      (cutoff * mesh lower upper pieces / (lower * lower)) := by
    simpa [Q] using
      (P.reciprocalImage_maxStepAtMost cutoff (mesh lower upper pieces)
        hcutoff hlower hsource)
  have hvariation :=
    RationalPartition.clampedPath_quadraticVariation_le_stepBound_mul_endpointDifference
      Q Q.clampedPath
      (cutoff * mesh lower upper pieces / (lower * lower))
      himage (RationalPartition.clampedPath_step_nonnegative Q)
  change quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces <=
    (cutoff * mesh lower upper pieces / (lower * lower)) *
      (Q.clampedPath Q.pieces - Q.clampedPath 0) at hvariation
  rw [Q.clampedPath_eq_point (Nat.le_refl Q.pieces),
    Q.clampedPath_eq_point (Nat.zero_le Q.pieces),
    Q.right_endpoint, Q.left_endpoint] at hvariation
  exact hvariation

end RationalPartition

/-- A total source-chart cell contribution; indices outside the finite
partition contribute zero. -/
def reciprocalGaussianTailStieltjesCellAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat) : Rat :=
  if _hk : k < P.pieces then
    reciprocalGaussianTailStieltjesSampleValue cutoff (P.point k) stage *
      (cutoff / P.point k - cutoff / P.point (k + 1))
  else 0

/-- The right-endpoint Gaussian rectangle on the reciprocal-image cell
corresponding to source chart cell `k`.  Cells are intentionally enumerated
in source order, hence in reverse target-partition order. -/
def reciprocalGaussianImageRightCellAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) : Rat :=
  if hk : k < P.pieces then
    let i := P.reciprocalImageCellIndex k
    let C := (P.reciprocalImage cutoff hcutoff hlower).cell i
      (P.reciprocalImageCellIndex_lt k hk)
    C.width * ((reciprocalGaussianRaw C.upper).compute stage).midpoint
  else 0

/-- One Stieltjes source cell is exactly the right-endpoint rectangle on its
reciprocal-image target cell. -/
theorem reciprocalGaussianImageRightCellAction_eq_stieltjesCellAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianImageRightCellAction
        P cutoff stage k hcutoff hlower =
      reciprocalGaussianTailStieltjesCellAction P cutoff stage k := by
  by_cases hk : k < P.pieces
  · rw [reciprocalGaussianImageRightCellAction, dif_pos hk,
      reciprocalGaussianTailStieltjesCellAction, dif_pos hk]
    have hleft : P.pieces - (P.pieces - 1 - k) = k + 1 := by omega
    have hright : P.pieces - ((P.pieces - 1 - k) + 1) = k := by omega
    dsimp [RationalPartition.reciprocalImageCellIndex,
      RationalPartition.reciprocalImage, RationalPartition.cell,
      RationalSubinterval.width]
    rw [hleft, hright]
    unfold reciprocalGaussianTailStieltjesSampleValue
    rw [Rat.mul_comm]
  · rw [reciprocalGaussianImageRightCellAction, dif_neg hk,
      reciprocalGaussianTailStieltjesCellAction, dif_neg hk]

/-- The complete right-endpoint rectangle action on every cell of the
reciprocal-image partition, enumerated by its source cell. -/
def reciprocalGaussianImageRightRectangleAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) : Rat :=
  (List.range P.pieces).foldl
    (fun acc k => acc + reciprocalGaussianImageRightCellAction
      P cutoff stage k hcutoff hlower) 0

/-- The matching source-enumerated right rectangle after replacing every raw
Gaussian sample by one common finite factorial prefix. -/
def reciprocalGaussianTailProfileRightCellAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (terms k : Nat) : Rat :=
  if hk : k < P.pieces then
    (cutoff / P.point k - cutoff / P.point (k + 1)) *
      gaussianEvenProfilePrefix terms (cutoff / P.point k)
  else 0

def reciprocalGaussianTailProfileRightRectangleAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (terms : Nat) : Rat :=
  (List.range P.pieces).foldl
    (fun acc k => acc + reciprocalGaussianTailProfileRightCellAction
      P cutoff terms k) 0

/-- Positivity of a reciprocal-image cell width, written in source-chart
coordinates. -/
theorem reciprocalGaussianTailWidth_nonneg
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (k : Nat) (hk : k < P.pieces)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 <= cutoff / P.point k - cutoff / P.point (k + 1) := by
  have hkLe : k + 1 <= P.pieces := Nat.succ_le_of_lt hk
  have hpointK := P.point_in_bounds (Nat.le_of_lt hk)
  have hpointKPos : 0 < P.point k := by grind
  have hmono : P.point k <= P.point (k + 1) :=
    P.monotone k (k + 1) (Nat.le_succ k) hkLe
  have hrecip := RealCompute.one_div_antitone_of_pos hpointKPos hmono
  rw [Rat.div_def, Rat.div_def]
  have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
    (Rat.le_of_lt hcutoff)
  grind [Rat.sub_eq_add_neg]

/-- The explicit error assigned to one source cell when all raw Gaussian
samples are replaced by the common finite factorial prefix. -/
def reciprocalGaussianTailCommonProfileCellErrorBound
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat) : Rat :=
  if _hk : k < P.pieces then
    (cutoff / P.point k - cutoff / P.point (k + 1)) *
      (reciprocalGaussianRepresentationChangeBound
          (cutoff / P.point k) * ((1 : Rat) / 2) ^ stage +
        RationalMajorant.factorialTailPartial
          ((cutoff / P.point k) * (cutoff / P.point k))
          (expPowerSeriesTerms
            (-(cutoff / P.point k * (cutoff / P.point k))) stage)
          (reciprocalGaussianTailCommonProfileTerms P cutoff stage -
            expPowerSeriesTerms
              (-(cutoff / P.point k * (cutoff / P.point k))) stage))
  else 0

/-- The total explicit representation-change budget on the finite source
partition. -/
def reciprocalGaussianTailCommonProfileErrorBound
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat) : Rat :=
  (List.range P.pieces).foldl
    (fun acc k => acc +
      reciprocalGaussianTailCommonProfileCellErrorBound P cutoff stage k) 0

/-- Stage-independent coefficient controlling the common-prefix error on one
reciprocal-chart cell.  Every quantity is a finite rational expression. -/
def reciprocalGaussianTailCommonProfileCellGeometricCoefficient
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (k : Nat) : Rat :=
  if _hk : k < P.pieces then
    (cutoff / P.point k - cutoff / P.point (k + 1)) *
      (reciprocalGaussianRepresentationChangeBound
          (cutoff / P.point k) +
        2 * RationalMajorant.factorialTailTerm
          ((cutoff / P.point k) * (cutoff / P.point k))
          (expPowerSeriesTerms
            (-(cutoff / P.point k * (cutoff / P.point k))) 0))
  else 0

/-- The finite rational sum of the stage-independent common-prefix
coefficients. -/
def reciprocalGaussianTailCommonProfileGeometricCoefficient
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) : Rat :=
  (List.range P.pieces).foldl
    (fun acc k => acc +
      reciprocalGaussianTailCommonProfileCellGeometricCoefficient
        P cutoff k) 0

/-- Each common-prefix cell error is bounded by its fixed coefficient times
the geometric stage factor. -/
theorem reciprocalGaussianTailCommonProfileCellErrorBound_le_geometric
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianTailCommonProfileCellErrorBound P cutoff stage k <=
      reciprocalGaussianTailCommonProfileCellGeometricCoefficient
        P cutoff k * ((1 : Rat) / 2) ^ stage := by
  by_cases hk : k < P.pieces
  · unfold reciprocalGaussianTailCommonProfileCellErrorBound
      reciprocalGaussianTailCommonProfileCellGeometricCoefficient
    rw [dif_pos hk, dif_pos hk]
    have hwidth := reciprocalGaussianTailWidth_nonneg
      P cutoff k hk hcutoff hlower
    have hblock := reciprocalGaussianCommonProfile_factorialBlock_le_geometric
      P cutoff stage k hk
    have hinside :
        reciprocalGaussianRepresentationChangeBound (cutoff / P.point k) *
            ((1 : Rat) / 2) ^ stage +
          RationalMajorant.factorialTailPartial
            ((cutoff / P.point k) * (cutoff / P.point k))
            (expPowerSeriesTerms
              (-(cutoff / P.point k * (cutoff / P.point k))) stage)
            (reciprocalGaussianTailCommonProfileTerms P cutoff stage -
              expPowerSeriesTerms
                (-(cutoff / P.point k * (cutoff / P.point k))) stage) <=
          (reciprocalGaussianRepresentationChangeBound
              (cutoff / P.point k) +
            2 * RationalMajorant.factorialTailTerm
            ((cutoff / P.point k) * (cutoff / P.point k))
            (expPowerSeriesTerms
              (-(cutoff / P.point k * (cutoff / P.point k))) 0)) *
            ((1 : Rat) / 2) ^ stage := by
      calc
        reciprocalGaussianRepresentationChangeBound (cutoff / P.point k) *
              ((1 : Rat) / 2) ^ stage +
            RationalMajorant.factorialTailPartial
              ((cutoff / P.point k) * (cutoff / P.point k))
              (expPowerSeriesTerms
                (-(cutoff / P.point k * (cutoff / P.point k))) stage)
              (reciprocalGaussianTailCommonProfileTerms P cutoff stage -
                expPowerSeriesTerms
                  (-(cutoff / P.point k * (cutoff / P.point k))) stage) <=
          reciprocalGaussianRepresentationChangeBound (cutoff / P.point k) *
              ((1 : Rat) / 2) ^ stage +
            (2 * RationalMajorant.factorialTailTerm
              ((cutoff / P.point k) * (cutoff / P.point k))
              (expPowerSeriesTerms
                (-(cutoff / P.point k * (cutoff / P.point k))) 0) *
              ((1 : Rat) / 2) ^ stage) :=
          rat_add_le_add (Rat.le_refl) hblock
        _ = (reciprocalGaussianRepresentationChangeBound
                (cutoff / P.point k) +
              2 * RationalMajorant.factorialTailTerm
                ((cutoff / P.point k) * (cutoff / P.point k))
                (expPowerSeriesTerms
                  (-(cutoff / P.point k * (cutoff / P.point k))) 0)) *
            ((1 : Rat) / 2) ^ stage := by
          grind [Rat.add_mul, Rat.mul_assoc]
    simpa [Rat.mul_assoc] using
      (Rat.mul_le_mul_of_nonneg_left hinside hwidth)
  · unfold reciprocalGaussianTailCommonProfileCellErrorBound
      reciprocalGaussianTailCommonProfileCellGeometricCoefficient
    rw [dif_neg hk, dif_neg hk]
    grind

/-- The total common-prefix representation error has a single explicit
geometric majorant. -/
theorem reciprocalGaussianTailCommonProfileErrorBound_le_geometric
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianTailCommonProfileErrorBound P cutoff stage <=
      reciprocalGaussianTailCommonProfileGeometricCoefficient P cutoff *
        ((1 : Rat) / 2) ^ stage := by
  unfold reciprocalGaussianTailCommonProfileErrorBound
    reciprocalGaussianTailCommonProfileGeometricCoefficient
  calc
    (List.range P.pieces).foldl
        (fun acc k => acc +
          reciprocalGaussianTailCommonProfileCellErrorBound
            P cutoff stage k) 0 <=
      (List.range P.pieces).foldl
        (fun acc k => acc +
          reciprocalGaussianTailCommonProfileCellGeometricCoefficient
            P cutoff k * ((1 : Rat) / 2) ^ stage) 0 := by
        apply RationalPartition.rat_add_fold_le_of_pointwise
        intro k _hkMem
        exact reciprocalGaussianTailCommonProfileCellErrorBound_le_geometric
          P cutoff stage k hcutoff hlower
    _ = (List.range P.pieces).foldl
          (fun acc k => acc +
            reciprocalGaussianTailCommonProfileCellGeometricCoefficient
              P cutoff k) 0 * ((1 : Rat) / 2) ^ stage :=
      RationalPartition.rat_add_fold_mul_right _ _ _

/-- The total geometric coefficient is nonnegative on a positive reciprocal
chart. -/
theorem reciprocalGaussianTailCommonProfileGeometricCoefficient_nonneg
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 <= reciprocalGaussianTailCommonProfileGeometricCoefficient P cutoff := by
  unfold reciprocalGaussianTailCommonProfileGeometricCoefficient
  have hzero :
      (List.range P.pieces).foldl (fun acc _k => acc + (0 : Rat)) 0 = 0 := by
    induction (List.range P.pieces) with
    | nil => rfl
    | cons k xs ih =>
        simp only [List.foldl, Rat.zero_add]
        simpa using ih
  calc
    0 = (List.range P.pieces).foldl
        (fun acc _k => acc + (0 : Rat)) 0 := hzero.symm
    _ <= (List.range P.pieces).foldl
        (fun acc k => acc +
          reciprocalGaussianTailCommonProfileCellGeometricCoefficient
            P cutoff k) 0 := by
      apply RationalPartition.rat_add_fold_le_of_pointwise
      intro k hkMem
      have hk : k < P.pieces := List.mem_range.mp hkMem
      unfold reciprocalGaussianTailCommonProfileCellGeometricCoefficient
      rw [dif_pos hk]
      apply Rat.mul_nonneg
      · exact reciprocalGaussianTailWidth_nonneg
          P cutoff k hk hcutoff hlower
      · apply Rat.add_nonneg
        · exact reciprocalGaussianRepresentationChangeBound_nonneg _
        · exact Rat.mul_nonneg (by decide +kernel)
            (RationalMajorant.factorialTailTerm_nonneg
              (rat_square_nonneg_basic (cutoff / P.point k)) _)

/-- A fully computable representation stage for a requested positive
rational tolerance. -/
def reciprocalGaussianTailCommonProfileStage
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
      (reciprocalGaussianTailCommonProfileGeometricCoefficient P cutoff) eps +
    RationalMajorant.halfDecayShift
      (gaussianIntegralShiftedGeometricBound (cutoff / lower)) eps +
    RationalMajorant.halfDecayShift
      (gaussianIntegralShiftedGeometricBound (cutoff / upper)) eps

/-- The scheduled common-prefix representation budget is below the requested
positive rational tolerance. -/
theorem reciprocalGaussianTailCommonProfileErrorBound_at_stage_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianTailCommonProfileErrorBound P cutoff
        (reciprocalGaussianTailCommonProfileStage P cutoff eps) <= eps.val := by
  let shift := RationalMajorant.halfDecayShift
    (reciprocalGaussianTailCommonProfileGeometricCoefficient P cutoff) eps
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff eps
  have hshift : shift <= stage := by
    unfold shift stage reciprocalGaussianTailCommonProfileStage
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hshift
  have hbase := reciprocalGaussianTailCommonProfileErrorBound_le_geometric
    P cutoff stage hcutoff hlower
  have hpow : ((1 : Rat) / 2) ^ stage <= ((1 : Rat) / 2) ^ shift := by
    rw [hd]
    exact Series.halfPow_add_le_left shift d
  have hcoeff :=
    reciprocalGaussianTailCommonProfileGeometricCoefficient_nonneg
      P cutoff hcutoff hlower
  exact Rat.le_trans hbase (Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_left hpow hcoeff)
    (by
      dsimp [shift]
      exact RationalMajorant.halfDecayShift_spec hcoeff eps))

private theorem halfDecayShift_bound_mul_halfPow_le_of_le
    {bound : Rat} (hbound : 0 <= bound) (eps : QPos) {stage : Nat}
    (hshift : RationalMajorant.halfDecayShift bound eps <= stage) :
    bound * ((1 : Rat) / 2) ^ stage <= eps.val := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hshift
  have hpow : ((1 : Rat) / 2) ^ stage <=
      ((1 : Rat) / 2) ^ RationalMajorant.halfDecayShift bound eps := by
    rw [hd]
    exact Series.halfPow_add_le_left
      (RationalMajorant.halfDecayShift bound eps) d
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hpow hbound)
    (RationalMajorant.halfDecayShift_spec hbound eps)

private theorem gaussianIntegralShiftedMagnitude_at_commonProfileTerms_le
    {lower upper radius : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos) (hradius : 0 <= radius)
    (hstart : gaussianIntegralTailStart radius +
        2 * reciprocalGaussianTailCommonProfileStage P cutoff eps <=
      reciprocalGaussianTailCommonProfileTerms P cutoff
        (reciprocalGaussianTailCommonProfileStage P cutoff eps))
    (hshift : RationalMajorant.halfDecayShift
        (gaussianIntegralShiftedGeometricBound radius) eps <=
      reciprocalGaussianTailCommonProfileStage P cutoff eps) :
    gaussianIntegralShiftedMagnitude radius
        (reciprocalGaussianTailCommonProfileTerms P cutoff
            (reciprocalGaussianTailCommonProfileStage P cutoff eps) -
          gaussianIntegralTailStart radius) <= eps.val := by
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff eps
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let start := gaussianIntegralTailStart radius
  have hoffset : RationalMajorant.halfDecayShift
      (gaussianIntegralShiftedGeometricBound radius) eps <= terms - start := by
    dsimp [stage, terms, start] at hstart ⊢
    omega
  have hgeom := gaussianIntegralShiftedMagnitude_le_geometric
    radius hradius (terms - start)
  have hbound := gaussianIntegralShiftedGeometricBound_nonneg radius hradius
  exact Rat.le_trans (by simpa [terms, start] using hgeom)
    (halfDecayShift_bound_mul_halfPow_le_of_le hbound eps hoffset)

/-- At the scheduled common-profile stage, the first omitted outer-radius
integrated Gaussian term is below the same requested tolerance. -/
theorem reciprocalGaussianTailCommonProfile_outerOmittedMagnitude_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) :
    gaussianIntegralShiftedMagnitude (cutoff / lower)
        (reciprocalGaussianTailCommonProfileTerms P cutoff
            (reciprocalGaussianTailCommonProfileStage P cutoff eps) -
          gaussianIntegralTailStart (cutoff / lower)) <= eps.val := by
  have hradius : 0 <= cutoff / lower := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  apply gaussianIntegralShiftedMagnitude_at_commonProfileTerms_le
    P cutoff eps hradius
  · exact gaussianIntegralTailStart_outer_add_two_stage_le_commonProfileTerms
      P cutoff (reciprocalGaussianTailCommonProfileStage P cutoff eps)
  · unfold reciprocalGaussianTailCommonProfileStage
    omega

/-- The corresponding first omitted inner-radius term is below the requested
tolerance at the same scheduled stage. -/
theorem reciprocalGaussianTailCommonProfile_innerOmittedMagnitude_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) :
    gaussianIntegralShiftedMagnitude (cutoff / upper)
        (reciprocalGaussianTailCommonProfileTerms P cutoff
            (reciprocalGaussianTailCommonProfileStage P cutoff eps) -
          gaussianIntegralTailStart (cutoff / upper)) <= eps.val := by
  have hlowerUpper : lower <= upper := by
    calc
      lower = P.point 0 := P.left_endpoint.symm
      _ <= P.point P.pieces := P.monotone 0 P.pieces
        (Nat.zero_le _) (Nat.le_refl _)
      _ = upper := P.right_endpoint
  have hupper : 0 < upper := by grind
  have hradius : 0 <= cutoff / upper := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hupper))
  apply gaussianIntegralShiftedMagnitude_at_commonProfileTerms_le
    P cutoff eps hradius
  · exact gaussianIntegralTailStart_inner_add_two_stage_le_commonProfileTerms
      P cutoff (reciprocalGaussianTailCommonProfileStage P cutoff eps)
  · unfold reciprocalGaussianTailCommonProfileStage
    omega

/-- One reciprocal-image raw rectangle differs from its common-prefix
counterpart by the cell width times the public representative-change bound. -/
theorem reciprocalGaussianImageRightCellAction_sub_profile_le_geometric
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage k : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    qabs (reciprocalGaussianImageRightCellAction
        P cutoff stage k hcutoff hlower -
      reciprocalGaussianTailProfileRightCellAction P cutoff
        (expPowerSeriesTerms
          (-(cutoff / P.point k * (cutoff / P.point k))) stage) k) <=
      (if hk : k < P.pieces then
        (cutoff / P.point k - cutoff / P.point (k + 1)) *
          reciprocalGaussianRepresentationChangeBound
            (cutoff / P.point k) * ((1 : Rat) / 2) ^ stage
      else 0) := by
  by_cases hk : k < P.pieces
  · rw [reciprocalGaussianImageRightCellAction, dif_pos hk,
      reciprocalGaussianTailProfileRightCellAction, dif_pos hk, dif_pos hk]
    have hleft : P.pieces - (P.pieces - 1 - k) = k + 1 := by omega
    have hright : P.pieces - ((P.pieces - 1 - k) + 1) = k := by omega
    dsimp [RationalPartition.reciprocalImageCellIndex,
      RationalPartition.reciprocalImage, RationalPartition.cell,
      RationalSubinterval.width]
    rw [hleft, hright]
    let width : Rat := cutoff / P.point k - cutoff / P.point (k + 1)
    let raw : Rat := reciprocalGaussianTailStieltjesSampleValue
      cutoff (P.point k) stage
    let profile : Rat := gaussianEvenProfilePrefix
      (expPowerSeriesTerms
        (-(cutoff / P.point k * (cutoff / P.point k))) stage)
      (cutoff / P.point k)
    have hkLe : k + 1 <= P.pieces := Nat.succ_le_of_lt hk
    have hpointK := P.point_in_bounds (Nat.le_of_lt hk)
    have hpointKPos : 0 < P.point k := by grind
    have hpointK1 := P.point_in_bounds hkLe
    have hpointK1Pos : 0 < P.point (k + 1) := by grind
    have hmono : P.point k <= P.point (k + 1) :=
      P.monotone k (k + 1) (Nat.le_succ k) hkLe
    have hrecip := RealCompute.one_div_antitone_of_pos hpointKPos hmono
    have hwidth0 : 0 <= width := by
      dsimp [width]
      rw [Rat.div_def, Rat.div_def]
      have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
        (Rat.le_of_lt hcutoff)
      grind [Rat.sub_eq_add_neg]
    have hsample :=
      reciprocalGaussianTailStieltjesSampleValue_sub_profilePrefix_le_geometric
        cutoff (P.point k) stage
    have hdecomp : width * raw - width * profile = width * (raw - profile) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
    change qabs (width * raw - width * profile) <=
      width * reciprocalGaussianRepresentationChangeBound
          (cutoff / P.point k) * ((1 : Rat) / 2) ^ stage
    rw [hdecomp, qabs_mul, qabs_eq_self_of_nonneg hwidth0]
    simpa [raw, profile, Rat.mul_assoc] using
      (Rat.mul_le_mul_of_nonneg_left hsample hwidth0)
  · rw [reciprocalGaussianImageRightCellAction, dif_neg hk,
      reciprocalGaussianTailProfileRightCellAction, dif_neg hk, dif_neg hk]
    rw [Rat.sub_self, qabs_eq_self_of_nonneg (by decide +kernel)]
    exact Rat.le_refl

/-- All raw reciprocal-image rectangles can be changed to one common finite
factorial prefix by adding the literal pointwise sample errors. -/
theorem reciprocalGaussianImageRightRectangleAction_sub_profile_le_sum
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (terms stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    qabs (reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower -
      reciprocalGaussianTailProfileRightRectangleAction P cutoff
        terms) <=
      (List.range P.pieces).foldl
        (fun acc k => acc +
          (if hk : k < P.pieces then
            (cutoff / P.point k - cutoff / P.point (k + 1)) *
              qabs (reciprocalGaussianTailStieltjesSampleValue
                  cutoff (P.point k) stage -
                gaussianEvenProfilePrefix
                  terms
                  (cutoff / P.point k))
          else 0)) 0 := by
  unfold reciprocalGaussianImageRightRectangleAction
    reciprocalGaussianTailProfileRightRectangleAction
  apply RationalPartition.qabs_rat_add_fold_sub_fold_le
  intro k hkMem
  have hk : k < P.pieces := List.mem_range.mp hkMem
  rw [reciprocalGaussianImageRightCellAction, dif_pos hk,
    reciprocalGaussianTailProfileRightCellAction, dif_pos hk, dif_pos hk]
  have hleft : P.pieces - (P.pieces - 1 - k) = k + 1 := by omega
  have hright : P.pieces - ((P.pieces - 1 - k) + 1) = k := by omega
  dsimp [RationalPartition.reciprocalImageCellIndex,
    RationalPartition.reciprocalImage, RationalPartition.cell,
    RationalSubinterval.width]
  rw [hleft, hright]
  have hkLe : k + 1 <= P.pieces := Nat.succ_le_of_lt hk
  have hpointK := P.point_in_bounds (Nat.le_of_lt hk)
  have hpointKPos : 0 < P.point k := by grind
  have hmono : P.point k <= P.point (k + 1) :=
    P.monotone k (k + 1) (Nat.le_succ k) hkLe
  have hrecip := RealCompute.one_div_antitone_of_pos hpointKPos hmono
  have hwidth0 : 0 <= cutoff / P.point k - cutoff / P.point (k + 1) := by
    rw [Rat.div_def, Rat.div_def]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
      (Rat.le_of_lt hcutoff)
    grind [Rat.sub_eq_add_neg]
  unfold reciprocalGaussianTailStieltjesSampleValue
  have hdecomp :
      (cutoff / P.point k - cutoff / P.point (k + 1)) *
            ((reciprocalGaussianRaw (cutoff / P.point k)).compute stage).midpoint -
          (cutoff / P.point k - cutoff / P.point (k + 1)) *
            gaussianEvenProfilePrefix
              terms
              (cutoff / P.point k) =
        (cutoff / P.point k - cutoff / P.point (k + 1)) *
          (((reciprocalGaussianRaw (cutoff / P.point k)).compute stage).midpoint -
            gaussianEvenProfilePrefix
              terms
              (cutoff / P.point k)) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add]
  rw [hdecomp, qabs_mul, qabs_eq_self_of_nonneg hwidth0]
  exact Rat.le_refl

/-- The whole raw reciprocal-image rectangle action is approximated by one
common finite Gaussian polynomial with a literal finite rational error sum. -/
theorem reciprocalGaussianImageRightRectangleAction_sub_commonProfile_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    qabs (reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower -
      reciprocalGaussianTailProfileRightRectangleAction P cutoff
        (reciprocalGaussianTailCommonProfileTerms P cutoff stage)) <=
      reciprocalGaussianTailCommonProfileErrorBound P cutoff stage := by
  have hbase :=
    reciprocalGaussianImageRightRectangleAction_sub_profile_le_sum
      P cutoff (reciprocalGaussianTailCommonProfileTerms P cutoff stage)
        stage hcutoff hlower
  exact Rat.le_trans hbase (by
    unfold reciprocalGaussianTailCommonProfileErrorBound
    apply RationalPartition.rat_add_fold_le_of_pointwise
    intro k hkMem
    have hk : k < P.pieces := List.mem_range.mp hkMem
    rw [dif_pos hk]
    unfold reciprocalGaussianTailCommonProfileCellErrorBound
    rw [dif_pos hk]
    exact Rat.mul_le_mul_of_nonneg_left
      (reciprocalGaussianTailStieltjesSampleValue_sub_commonProfile_le
        P cutoff stage k hk)
      (reciprocalGaussianTailWidth_nonneg
        P cutoff k hk hcutoff hlower))

/-- At the explicit scheduled stage, the complete raw reciprocal-image action
is within the requested rational tolerance of one common finite Gaussian
polynomial action. -/
theorem reciprocalGaussianImageRightRectangleAction_sub_commonProfile_at_stage_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (eps : QPos)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    qabs (reciprocalGaussianImageRightRectangleAction P cutoff
          (reciprocalGaussianTailCommonProfileStage P cutoff eps)
          hcutoff hlower -
        reciprocalGaussianTailProfileRightRectangleAction P cutoff
          (reciprocalGaussianTailCommonProfileTerms P cutoff
            (reciprocalGaussianTailCommonProfileStage P cutoff eps))) <=
      eps.val := by
  exact Rat.le_trans
    (reciprocalGaussianImageRightRectangleAction_sub_commonProfile_le
      P cutoff (reciprocalGaussianTailCommonProfileStage P cutoff eps)
        hcutoff hlower)
    (reciprocalGaussianTailCommonProfileErrorBound_at_stage_le
      P cutoff eps hcutoff hlower)

/-- Exact finite reciprocal substitution: the decreasing-coordinate
Stieltjes action is the right-endpoint Gaussian rectangle action on the
explicit reciprocal-image partition.  No limit or integral operator occurs
in this statement. -/
theorem reciprocalGaussianTailStieltjesAction_eq_imageRightRectangleAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianTailStieltjesActionOnPartition P cutoff stage =
      reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower := by
  unfold reciprocalGaussianTailStieltjesActionOnPartition
    reciprocalGaussianImageRightRectangleAction
  rw [leftStieltjesSum_eq_range_fold]
  calc
    (List.range P.pieces).foldl
        (fun acc k =>
          acc + reciprocalGaussianTailStieltjesSampleValue
              cutoff (P.point k) stage *
            (-(cutoff / P.point (k + 1)) -
              -(cutoff / P.point k))) 0 =
      (List.range P.pieces).foldl
        (fun acc k => acc + reciprocalGaussianTailStieltjesCellAction
          P cutoff stage k) 0 := by
          apply rat_add_fold_congr_on
          intro k hk
          have hklt : k < P.pieces := List.mem_range.mp hk
          rw [reciprocalGaussianTailStieltjesCellAction, dif_pos hklt]
          grind [Rat.sub_eq_add_neg]
    _ = (List.range P.pieces).foldl
        (fun acc k => acc + reciprocalGaussianImageRightCellAction
          P cutoff stage k hcutoff hlower) 0 := by
          apply rat_add_fold_congr_on
          intro k _hk
          exact
            (reciprocalGaussianImageRightCellAction_eq_stieltjesCellAction
              P cutoff stage k hcutoff hlower).symm

/-- Source-order common-prefix rectangles are exactly the ordinary
right-endpoint action on the reversed reciprocal-image partition. -/
theorem reciprocalGaussianTailProfileRightRectangleAction_eq_imageRightRectangleAction
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianTailProfileRightRectangleAction P cutoff terms =
      (P.reciprocalImage cutoff hcutoff hlower).rightRectangleAction
        (gaussianEvenProfilePrefix terms) := by
  unfold reciprocalGaussianTailProfileRightRectangleAction
    RationalPartition.rightRectangleAction
  change
    (List.range P.pieces).foldl
        (fun acc k => acc +
          reciprocalGaussianTailProfileRightCellAction P cutoff terms k) 0 =
      (List.range P.pieces).foldl
        (fun acc i => acc +
          (P.reciprocalImage cutoff hcutoff hlower).rightRectangleTerm
            (gaussianEvenProfilePrefix terms) i) 0
  calc
    _ = (List.range P.pieces).foldl
        (fun acc k => acc +
          (P.reciprocalImage cutoff hcutoff hlower).rightRectangleTerm
            (gaussianEvenProfilePrefix terms) (P.pieces - 1 - k)) 0 := by
      apply rat_add_fold_congr_on
      intro k hkMem
      have hk : k < P.pieces := List.mem_range.mp hkMem
      have hi : P.reciprocalImageCellIndex k < P.pieces :=
        P.reciprocalImageCellIndex_lt k hk
      have hiQ : P.reciprocalImageCellIndex k <
          (P.reciprocalImage cutoff hcutoff hlower).pieces := by
        change P.reciprocalImageCellIndex k < P.pieces
        exact hi
      have hcell :=
        P.reciprocalImage_cell_endpoints_width cutoff hcutoff hlower k hk
      rw [reciprocalGaussianTailProfileRightCellAction, dif_pos hk]
      change
        (cutoff / P.point k - cutoff / P.point (k + 1)) *
            gaussianEvenProfilePrefix terms (cutoff / P.point k) =
          (P.reciprocalImage cutoff hcutoff hlower).rightRectangleTerm
            (gaussianEvenProfilePrefix terms)
            (P.reciprocalImageCellIndex k)
      rw [RationalPartition.rightRectangleTerm, dif_pos hiQ]
      dsimp only at hcell
      rw [hcell.2.1, hcell.2.2]
    _ = _ :=
      (RationalPartition.rat_add_fold_range_reflect P.pieces
        (fun i =>
          (P.reciprocalImage cutoff hcutoff hlower).rightRectangleTerm
            (gaussianEvenProfilePrefix terms) i)).symm

/-- The polynomial right rectangles on the reciprocal-image mesh compare
with the exact finite Gaussian primitive by the mesh's explicit quadratic
variation.  This instantiates the generic right-endpoint secant theorem on
the nonuniform image partition. -/
theorem gaussianEvenProfilePrefix_reciprocalImage_rightRectangle_error_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <=
        quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) (by
              rw [Rat.div_def]
              exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient := by
  have hlowerUpper : lower <= upper := by
    have hmono := P.monotone 0 P.pieces (Nat.zero_le _) (Nat.le_refl _)
    simpa [P.left_endpoint, P.right_endpoint] using hmono
  have hupper : 0 < upper := by grind
  have hradius : 0 <= cutoff / lower := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  let Q := P.reciprocalImage cutoff hcutoff hlower
  let D := gaussianEvenPrimitiveSecantBoundAtRadius
    (cutoff / lower) hradius terms
  have hleftNonneg : 0 <= cutoff / upper := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hupper))
  have hrightNonneg : 0 <= cutoff / lower := hradius
  have hleftLe : cutoff / upper <= cutoff / lower := by
    have hinv := RealCompute.one_div_antitone_of_pos hlower hlowerUpper
    have hinv' : upper⁻¹ <= lower⁻¹ := by
      simpa [Rat.div_def] using hinv
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_left hinv' (Rat.le_of_lt hcutoff)
  have hleftAbs : qabs (cutoff / upper) <= gaussianRadiusSecantBox (cutoff / lower) := by
    rw [qabs_eq_self_of_nonneg hleftNonneg]
    unfold gaussianRadiusSecantBox
    exact Rat.le_trans hleftLe (by grind)
  have hrightAbs : qabs (cutoff / lower) <= gaussianRadiusSecantBox (cutoff / lower) := by
    rw [qabs_eq_self_of_nonneg hrightNonneg]
    unfold gaussianRadiusSecantBox
    grind
  have h := D.qabs_endpointDifference_sub_rightRectangleAction_le
    Q hleftAbs hrightAbs
  simpa [Q, D] using h

/-- A single finite certificate compares the raw reciprocal-Gaussian action
with the exact primitive increment of its common Gaussian polynomial.  Its
two summands are respectively the mesh error and the representation-change
error; every quantity is finite and rational. -/
theorem reciprocalGaussianImageRightRectangleAction_primitive_error_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower) <=
      quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) (by
              rw [Rat.div_def]
              exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient +
        reciprocalGaussianTailCommonProfileErrorBound P cutoff stage := by
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let Q := P.reciprocalImage cutoff hcutoff hlower
  let primitiveDifference : Rat :=
    gaussianEvenPrimitivePrefix terms (cutoff / lower) -
      gaussianEvenPrimitivePrefix terms (cutoff / upper)
  let profileAction : Rat :=
    Q.rightRectangleAction (gaussianEvenProfilePrefix terms)
  let rawAction : Rat :=
    reciprocalGaussianImageRightRectangleAction
      P cutoff stage hcutoff hlower
  have hpoly :=
    gaussianEvenProfilePrefix_reciprocalImage_rightRectangle_error_le
      P cutoff terms hcutoff hlower
  have hrepresentation :=
    reciprocalGaussianImageRightRectangleAction_sub_commonProfile_le
      P cutoff stage hcutoff hlower
  rw [reciprocalGaussianTailProfileRightRectangleAction_eq_imageRightRectangleAction
    P cutoff terms hcutoff hlower] at hrepresentation
  have hrepresentationReverse :
      qabs (profileAction - rawAction) <=
        reciprocalGaussianTailCommonProfileErrorBound P cutoff stage := by
    have hneg : profileAction - rawAction = -(rawAction - profileAction) := by
      grind [Rat.sub_eq_add_neg]
    rw [hneg, qabs_neg]
    simpa [profileAction, rawAction, Q, terms] using hrepresentation
  have hdecomp :
      primitiveDifference - rawAction =
        (primitiveDifference - profileAction) +
          (profileAction - rawAction) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs (primitiveDifference - rawAction) <= _
  rw [hdecomp]
  calc
    qabs ((primitiveDifference - profileAction) +
        (profileAction - rawAction)) <=
      qabs (primitiveDifference - profileAction) +
        qabs (profileAction - rawAction) := qabs_add_le _ _
    _ <= quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) (by
              rw [Rat.div_def]
              exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient +
        reciprocalGaussianTailCommonProfileErrorBound P cutoff stage :=
      rat_add_le_add
        (by simpa [primitiveDifference, profileAction, Q, terms] using hpoly)
        hrepresentationReverse

/-- After reflection, the raw reciprocal-image action approximates the exact
symmetric finite Gaussian annulus for the same common prefix. -/
theorem reciprocalGaussianImageRightRectangleAction_symmetricPrefixAnnulus_error_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenIntegralPrefix terms (cutoff / lower) -
        gaussianEvenIntegralPrefix terms (cutoff / upper)) -
      2 * reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower) <=
      2 *
        (quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces *
            (gaussianEvenPrimitiveSecantBoundAtRadius
              (cutoff / lower) (by
                rw [Rat.div_def]
                exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                  (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient +
          reciprocalGaussianTailCommonProfileErrorBound P cutoff stage) := by
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let rawAction := reciprocalGaussianImageRightRectangleAction
    P cutoff stage hcutoff hlower
  have hbase :=
    reciprocalGaussianImageRightRectangleAction_primitive_error_le
      P cutoff stage hcutoff hlower
  have hprefix :=
    gaussianEvenIntegralPrefix_sub_eq_two_mul_primitiveDifference
      terms (cutoff / upper) (cutoff / lower)
  have hdecomp :
      (gaussianEvenIntegralPrefix terms (cutoff / lower) -
          gaussianEvenIntegralPrefix terms (cutoff / upper)) -
        2 * rawAction =
      2 * ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
          gaussianEvenPrimitivePrefix terms (cutoff / upper)) - rawAction) := by
    rw [hprefix]
    grind [Rat.mul_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs
      ((gaussianEvenIntegralPrefix terms (cutoff / lower) -
          gaussianEvenIntegralPrefix terms (cutoff / upper)) -
        2 * rawAction) <= _
  rw [hdecomp, qabs_mul, show qabs (2 : Rat) = 2 by decide +kernel]
  exact Rat.mul_le_mul_of_nonneg_left
    (by simpa [terms, rawAction] using hbase)
    (by decide +kernel)

/-- The outer-minus-inner midpoint annulus and the symmetric reciprocal-tail
action are compared through their common exact polynomial annulus.  This is
the finite bridge needed before passing to the stabilized growing-radius raw
computations. -/
theorem gaussianMidpointAnnulus_sub_reciprocalImageAction_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (tailStage innerStage outerStage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff tailStage
    let innerRadius := cutoff / upper
    let outerRadius := cutoff / lower
    let hinnerRadius : 0 <= innerRadius := by
      have hmono := P.monotone 0 P.pieces (Nat.zero_le _) (Nat.le_refl _)
      have hlowerUpper : lower <= upper := by
        simpa [P.left_endpoint, P.right_endpoint] using hmono
      have hupper : 0 < upper := by
        grind
      dsimp [innerRadius]
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
        (Rat.le_of_lt ((Rat.inv_pos).2 hupper))
    let houterRadius : 0 <= outerRadius := by
      dsimp [outerRadius]
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
        (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianRadiusTaylorQuadratureCenter
          outerRadius houterRadius terms outerStage -
        gaussianRadiusTaylorQuadratureCenter
          innerRadius hinnerRadius terms innerStage) -
      2 * reciprocalGaussianImageRightRectangleAction
        P cutoff tailStage hcutoff hlower) <=
      (gaussianRadiusTaylorQuadratureErrorRadius
          outerRadius houterRadius terms outerStage +
        gaussianRadiusTaylorQuadratureErrorRadius
          innerRadius hinnerRadius terms innerStage) +
      2 *
        (quadraticVariationSum Q.clampedPath Q.clampedPath Q.pieces *
            (gaussianEvenPrimitiveSecantBoundAtRadius
              outerRadius houterRadius terms).errorCoefficient +
          reciprocalGaussianTailCommonProfileErrorBound
            P cutoff tailStage) := by
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff tailStage
  let innerRadius := cutoff / upper
  let outerRadius := cutoff / lower
  have hmono := P.monotone 0 P.pieces (Nat.zero_le _) (Nat.le_refl _)
  have hlowerUpper : lower <= upper := by
    simpa [P.left_endpoint, P.right_endpoint] using hmono
  have hupper : 0 < upper := by
    grind
  let hinnerRadius : 0 <= innerRadius := by
    dsimp [innerRadius]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hupper))
  let houterRadius : 0 <= outerRadius := by
    dsimp [outerRadius]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  let midpointAnnulus : Rat :=
    gaussianRadiusTaylorQuadratureCenter
        outerRadius houterRadius terms outerStage -
      gaussianRadiusTaylorQuadratureCenter
        innerRadius hinnerRadius terms innerStage
  let prefixAnnulus : Rat :=
    gaussianEvenIntegralPrefix terms outerRadius -
      gaussianEvenIntegralPrefix terms innerRadius
  let tailAction : Rat := reciprocalGaussianImageRightRectangleAction
    P cutoff tailStage hcutoff hlower
  have hmidpoint :=
    gaussianRadiusTaylorQuadratureCenter_annulus_sub_prefixAnnulus_le
      innerRadius outerRadius hinnerRadius houterRadius
      terms innerStage outerStage
  have htail :=
    reciprocalGaussianImageRightRectangleAction_symmetricPrefixAnnulus_error_le
      P cutoff tailStage hcutoff hlower
  have hdecomp :
      midpointAnnulus - 2 * tailAction =
        (midpointAnnulus - prefixAnnulus) +
          (prefixAnnulus - 2 * tailAction) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs (midpointAnnulus - 2 * tailAction) <= _
  rw [hdecomp]
  exact Rat.le_trans (qabs_add_le _ _)
    (rat_add_le_add
      (by simpa [midpointAnnulus, prefixAnnulus] using hmidpoint)
      (by simpa [prefixAnnulus, tailAction, innerRadius, outerRadius,
          terms, hinnerRadius, houterRadius] using htail))

/-- The canonical finite reciprocal partition for the growing annulus from
radius `k+1` to radius `n+1`. -/
def gaussianGrowingAnnulusReciprocalPartition
    (k n pieces : Nat) (hkn : k <= n) (hpieces : 0 < pieces) :
    RationalPartition (gaussianGrowingAnnulusReciprocalLower k n) 1 :=
  RationalPartition.uniform
    (gaussianGrowingAnnulusReciprocalLower k n) 1 pieces hpieces
    (gaussianGrowingAnnulusReciprocalLower_le_one hkn)

/-! ## An executable reciprocal-image mesh schedule -/

/-- Stage-independent rational coefficient for the reciprocal-image mesh
error of a fixed finite Gaussian prefix. -/
def reciprocalGaussianUniformMeshCoefficient
    (lower upper cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) : Rat :=
  ((cutoff * (upper - lower) / (lower * lower)) *
      (cutoff / lower - cutoff / upper)) *
    (gaussianEvenPrimitiveSecantBoundAtRadius
      (cutoff / lower) (by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
          (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient

theorem reciprocalGaussianUniformMeshCoefficient_nonneg
    (lower upper cutoff : Rat) (terms : Nat)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 <= reciprocalGaussianUniformMeshCoefficient
      lower upper cutoff terms hcutoff hlower := by
  have hupper : 0 < upper := by grind
  have hsource : 0 <= upper - lower := by grind [Rat.sub_eq_add_neg]
  have hlowerSq : 0 < lower * lower := Rat.mul_pos hlower hlower
  have hscaled : 0 <= cutoff * (upper - lower) :=
    Rat.mul_nonneg (Rat.le_of_lt hcutoff) hsource
  have hfirst : 0 <= cutoff * (upper - lower) / (lower * lower) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hscaled
      (Rat.le_of_lt ((Rat.inv_pos).2 hlowerSq))
  have hinv := RealCompute.one_div_antitone_of_pos hlower hlowerUpper
  have himage : 0 <= cutoff / lower - cutoff / upper := by
    rw [Rat.div_def, Rat.div_def]
    have hmul := Rat.mul_le_mul_of_nonneg_left hinv (Rat.le_of_lt hcutoff)
    grind [Rat.sub_eq_add_neg]
  unfold reciprocalGaussianUniformMeshCoefficient
  exact Rat.mul_nonneg
    (Rat.mul_nonneg hfirst himage)
    (gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_nonneg
      (cutoff / lower) (by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
          (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms)

def reciprocalGaussianUniformMeshShift
    (lower upper cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (reciprocalGaussianUniformMeshCoefficient
      lower upper cutoff terms hcutoff hlower) eps

def reciprocalGaussianUniformMeshPieces
    (lower upper cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) : Nat :=
  2 ^ reciprocalGaussianUniformMeshShift
    lower upper cutoff terms hcutoff hlower eps

theorem reciprocalGaussianUniformMeshPieces_pos
    (lower upper cutoff : Rat) (terms : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) :
    0 < reciprocalGaussianUniformMeshPieces
      lower upper cutoff terms hcutoff hlower eps := by
  unfold reciprocalGaussianUniformMeshPieces
  exact Nat.pow_pos (by omega)

/-- Fully explicit mesh form of the reciprocal-image polynomial rectangle
estimate for a uniform source chart. -/
theorem gaussianEvenProfilePrefix_uniformReciprocalImage_rightRectangle_error_le
    (lower upper cutoff : Rat) (pieces terms : Nat)
    (hpieces : 0 < pieces) (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <=
      ((cutoff * mesh lower upper pieces / (lower * lower)) *
        (cutoff / lower - cutoff / upper)) *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) (by
              rw [Rat.div_def]
              exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient := by
  let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
  let Q := P.reciprocalImage cutoff hcutoff hlower
  have hradius : 0 <= cutoff / lower := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  let D := gaussianEvenPrimitiveSecantBoundAtRadius
    (cutoff / lower) hradius terms
  have hbase :=
    gaussianEvenProfilePrefix_reciprocalImage_rightRectangle_error_le
      P cutoff terms hcutoff hlower
  have hvariation :=
    RationalPartition.reciprocalImage_uniform_quadraticVariation_le
      lower upper cutoff pieces hpieces hlowerUpper hcutoff hlower
  have hscaled := Rat.mul_le_mul_of_nonneg_right hvariation
    D.errorCoefficient_nonneg
  exact Rat.le_trans (by simpa [P, Q, D] using hbase)
    (by simpa [P, Q, D] using hscaled)

/-- The dyadically scheduled reciprocal-image mesh puts the polynomial
right-rectangle error below any requested positive rational tolerance. -/
theorem gaussianEvenProfilePrefix_uniformReciprocalImage_at_mesh_stage_le
    (lower upper cutoff : Rat) (terms : Nat) (eps : QPos)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let pieces := reciprocalGaussianUniformMeshPieces
      lower upper cutoff terms hcutoff hlower eps
    let P := RationalPartition.uniform lower upper pieces
      (reciprocalGaussianUniformMeshPieces_pos
        lower upper cutoff terms hcutoff hlower eps) hlowerUpper
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <= eps.val := by
  let shift := reciprocalGaussianUniformMeshShift
    lower upper cutoff terms hcutoff hlower eps
  let pieces := reciprocalGaussianUniformMeshPieces
    lower upper cutoff terms hcutoff hlower eps
  let P := RationalPartition.uniform lower upper pieces
    (reciprocalGaussianUniformMeshPieces_pos
      lower upper cutoff terms hcutoff hlower eps) hlowerUpper
  let Q := P.reciprocalImage cutoff hcutoff hlower
  have hbase :=
    gaussianEvenProfilePrefix_uniformReciprocalImage_rightRectangle_error_le
      lower upper cutoff pieces terms
      (reciprocalGaussianUniformMeshPieces_pos
        lower upper cutoff terms hcutoff hlower eps)
      hlowerUpper hcutoff hlower
  have hpieces : pieces = 2 ^ shift := by
    rfl
  have hmesh : mesh lower upper pieces =
      (upper - lower) * ((1 : Rat) / 2) ^ shift := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt
      (reciprocalGaussianUniformMeshPieces_pos
        lower upper cutoff terms hcutoff hlower eps))]
    rw [hpieces, RationalMajorant.half_pow_eq_one_div_nat_two_pow]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hbudget :
      ((cutoff * mesh lower upper pieces / (lower * lower)) *
          (cutoff / lower - cutoff / upper)) *
        (gaussianEvenPrimitiveSecantBoundAtRadius
          (cutoff / lower) (by
            rw [Rat.div_def]
            exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
              (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient =
      reciprocalGaussianUniformMeshCoefficient
          lower upper cutoff terms hcutoff hlower *
        ((1 : Rat) / 2) ^ shift := by
    rw [hmesh]
    unfold reciprocalGaussianUniformMeshCoefficient
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hschedule := RationalMajorant.halfDecayShift_spec
    (reciprocalGaussianUniformMeshCoefficient_nonneg
      lower upper cutoff terms hlowerUpper hcutoff hlower) eps
  change qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
      gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
    Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <= eps.val
  exact Rat.le_trans
    (by simpa [P, Q] using hbase)
    (by rw [hbudget]
        simpa [shift, reciprocalGaussianUniformMeshShift] using hschedule)

/-! ## A prefix-independent reciprocal-image mesh schedule -/

/-- A reciprocal-image mesh coefficient which is independent of the later
choice of Gaussian Taylor prefix.  This removes the apparent circularity
between selecting the partition and selecting a common representation
prefix on that partition. -/
def reciprocalGaussianUniformMeshUniversalCoefficient
    (lower upper cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) : Rat :=
  ((cutoff * (upper - lower) / (lower * lower)) *
      (cutoff / lower - cutoff / upper)) *
    gaussianEvenPrimitiveSecantUniformBound (cutoff / lower)

theorem reciprocalGaussianUniformMeshUniversalCoefficient_nonneg
    (lower upper cutoff : Rat)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 <= reciprocalGaussianUniformMeshUniversalCoefficient
      lower upper cutoff hcutoff hlower := by
  have hupper : 0 < upper := by grind
  have hsource : 0 <= upper - lower := by grind [Rat.sub_eq_add_neg]
  have hlowerSq : 0 < lower * lower := Rat.mul_pos hlower hlower
  have hscaled : 0 <= cutoff * (upper - lower) :=
    Rat.mul_nonneg (Rat.le_of_lt hcutoff) hsource
  have hfirst : 0 <= cutoff * (upper - lower) / (lower * lower) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hscaled
      (Rat.le_of_lt ((Rat.inv_pos).2 hlowerSq))
  have hinv := RealCompute.one_div_antitone_of_pos hlower hlowerUpper
  have himage : 0 <= cutoff / lower - cutoff / upper := by
    rw [Rat.div_def, Rat.div_def]
    have hmul := Rat.mul_le_mul_of_nonneg_left hinv (Rat.le_of_lt hcutoff)
    grind [Rat.sub_eq_add_neg]
  unfold reciprocalGaussianUniformMeshUniversalCoefficient
  exact Rat.mul_nonneg (Rat.mul_nonneg hfirst himage)
    (gaussianEvenPrimitiveSecantUniformBound_nonneg
      (cutoff / lower) (by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
          (Rat.le_of_lt ((Rat.inv_pos).2 hlower))))

/-- Dyadic shift selected before any Taylor-prefix length is known. -/
def reciprocalGaussianUniformMeshUniversalShift
    (lower upper cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (reciprocalGaussianUniformMeshUniversalCoefficient
      lower upper cutoff hcutoff hlower) eps

/-- Positive number of uniform source cells selected before any
Taylor-prefix length is known. -/
def reciprocalGaussianUniformMeshUniversalPieces
    (lower upper cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) : Nat :=
  2 ^ reciprocalGaussianUniformMeshUniversalShift
    lower upper cutoff hcutoff hlower eps

theorem reciprocalGaussianUniformMeshUniversalPieces_pos
    (lower upper cutoff : Rat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (eps : QPos) :
    0 < reciprocalGaussianUniformMeshUniversalPieces
      lower upper cutoff hcutoff hlower eps := by
  unfold reciprocalGaussianUniformMeshUniversalPieces
  exact Nat.pow_pos (by omega)

/-- The prefix-independent mesh controls the reciprocal-image rectangle
error for every subsequently chosen finite Gaussian prefix. -/
theorem gaussianEvenProfilePrefix_uniformReciprocalImage_at_universal_mesh_stage_le
    (lower upper cutoff : Rat) (terms : Nat) (eps : QPos)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let pieces := reciprocalGaussianUniformMeshUniversalPieces
      lower upper cutoff hcutoff hlower eps
    let P := RationalPartition.uniform lower upper pieces
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower upper cutoff hcutoff hlower eps) hlowerUpper
    let Q := P.reciprocalImage cutoff hcutoff hlower
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <= eps.val := by
  let shift := reciprocalGaussianUniformMeshUniversalShift
    lower upper cutoff hcutoff hlower eps
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower upper cutoff hcutoff hlower eps
  let P := RationalPartition.uniform lower upper pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower upper cutoff hcutoff hlower eps) hlowerUpper
  let Q := P.reciprocalImage cutoff hcutoff hlower
  have hradius : 0 <= cutoff / lower := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  have hbase :=
    gaussianEvenProfilePrefix_uniformReciprocalImage_rightRectangle_error_le
      lower upper cutoff pieces terms
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower upper cutoff hcutoff hlower eps)
      hlowerUpper hcutoff hlower
  have hpieces : pieces = 2 ^ shift := by rfl
  have hmesh : mesh lower upper pieces =
      (upper - lower) * ((1 : Rat) / 2) ^ shift := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower upper cutoff hcutoff hlower eps))]
    rw [hpieces, RationalMajorant.half_pow_eq_one_div_nat_two_pow]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hsource : 0 <= upper - lower := by grind [Rat.sub_eq_add_neg]
  have hlowerSq : 0 < lower * lower := Rat.mul_pos hlower hlower
  have hfirst : 0 <= cutoff * (upper - lower) / (lower * lower) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.le_of_lt hcutoff) hsource)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlowerSq))
  have hinv := RealCompute.one_div_antitone_of_pos hlower hlowerUpper
  have himage : 0 <= cutoff / lower - cutoff / upper := by
    rw [Rat.div_def, Rat.div_def]
    have hmul := Rat.mul_le_mul_of_nonneg_left hinv (Rat.le_of_lt hcutoff)
    grind [Rat.sub_eq_add_neg]
  have hcoefficient :=
    gaussianEvenPrimitiveSecantBoundAtRadius_errorCoefficient_le_uniform
      (cutoff / lower) hradius terms
  have hscaledCoefficient :
      (cutoff * (upper - lower) / (lower * lower) *
          (cutoff / lower - cutoff / upper)) *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) hradius terms).errorCoefficient <=
        reciprocalGaussianUniformMeshUniversalCoefficient
          lower upper cutoff hcutoff hlower := by
    unfold reciprocalGaussianUniformMeshUniversalCoefficient
    exact Rat.mul_le_mul_of_nonneg_left hcoefficient
      (Rat.mul_nonneg hfirst himage)
  have hdecay : 0 <= ((1 : Rat) / 2) ^ shift :=
    Rat.pow_nonneg (by decide +kernel)
  have hschedule := RationalMajorant.halfDecayShift_spec
    (reciprocalGaussianUniformMeshUniversalCoefficient_nonneg
      lower upper cutoff hlowerUpper hcutoff hlower) eps
  have hbudget :
      ((cutoff * mesh lower upper pieces / (lower * lower)) *
          (cutoff / lower - cutoff / upper)) *
        (gaussianEvenPrimitiveSecantBoundAtRadius
          (cutoff / lower) hradius terms).errorCoefficient <= eps.val := by
    rw [hmesh]
    have hfactor :
        ((cutoff * ((upper - lower) * ((1 : Rat) / 2) ^ shift) /
              (lower * lower)) *
            (cutoff / lower - cutoff / upper)) *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) hradius terms).errorCoefficient =
        ((cutoff * (upper - lower) / (lower * lower) *
              (cutoff / lower - cutoff / upper)) *
            (gaussianEvenPrimitiveSecantBoundAtRadius
              (cutoff / lower) hradius terms).errorCoefficient) *
          ((1 : Rat) / 2) ^ shift := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    rw [hfactor]
    have hscaled := Rat.mul_le_mul_of_nonneg_right hscaledCoefficient hdecay
    exact Rat.le_trans
      hscaled
      (by simpa [shift, reciprocalGaussianUniformMeshUniversalShift] using hschedule)
  change qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
      gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
    Q.rightRectangleAction (gaussianEvenProfilePrefix terms)) <= eps.val
  exact Rat.le_trans (by simpa [P, Q] using hbase) hbudget

/-- A synchronized finite certificate: first choose a prefix-independent
uniform partition, then choose the common representation stage on that
partition.  The resulting raw reciprocal-Gaussian rectangle action is within
`eps` of the exact primitive increment of its automatically selected common
finite Gaussian prefix. -/
theorem reciprocalGaussianUniformSynchronized_primitive_error_le
    (lower upper cutoff : Rat) (eps : QPos)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    let pieces := reciprocalGaussianUniformMeshUniversalPieces
      lower upper cutoff hcutoff hlower half
    let P := RationalPartition.uniform lower upper pieces
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower upper cutoff hcutoff hlower half) hlowerUpper
    let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower) <= eps.val := by
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower upper cutoff hcutoff hlower half
  let P := RationalPartition.uniform lower upper pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower upper cutoff hcutoff hlower half) hlowerUpper
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let Q := P.reciprocalImage cutoff hcutoff hlower
  let primitiveDifference : Rat :=
    gaussianEvenPrimitivePrefix terms (cutoff / lower) -
      gaussianEvenPrimitivePrefix terms (cutoff / upper)
  let profileAction : Rat :=
    Q.rightRectangleAction (gaussianEvenProfilePrefix terms)
  let rawAction : Rat := reciprocalGaussianImageRightRectangleAction
    P cutoff stage hcutoff hlower
  have hpoly :=
    gaussianEvenProfilePrefix_uniformReciprocalImage_at_universal_mesh_stage_le
      lower upper cutoff terms half hlowerUpper hcutoff hlower
  have hrepresentation :=
    reciprocalGaussianImageRightRectangleAction_sub_commonProfile_at_stage_le
      P cutoff half hcutoff hlower
  rw [reciprocalGaussianTailProfileRightRectangleAction_eq_imageRightRectangleAction
    P cutoff terms hcutoff hlower] at hrepresentation
  have hrepresentationReverse :
      qabs (profileAction - rawAction) <= half.val := by
    have hneg : profileAction - rawAction = -(rawAction - profileAction) := by
      grind [Rat.sub_eq_add_neg]
    rw [hneg, qabs_neg]
    simpa [profileAction, rawAction, Q, terms, stage] using hrepresentation
  have hdecomp :
      primitiveDifference - rawAction =
        (primitiveDifference - profileAction) +
          (profileAction - rawAction) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc]
  have hhalf : half.val + half.val = eps.val := by
    have htwoNe : (2 : Rat) ≠ 0 := by decide +kernel
    have hcancel : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel 2 htwoNe
    dsimp [half]
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  change qabs (primitiveDifference - rawAction) <= eps.val
  rw [hdecomp]
  exact Rat.le_trans (qabs_add_le _ _)
    (by
      rw [← hhalf]
      exact rat_add_le_add
        (by simpa [primitiveDifference, profileAction, P, Q, terms,
            pieces, half] using hpoly)
        hrepresentationReverse)

/-- Symmetric form of the synchronized certificate.  The exact finite
Gaussian annulus of the automatically selected common prefix is within
`2*eps` of the reflected raw reciprocal-image action. -/
theorem reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_error_le
    (lower upper cutoff : Rat) (eps : QPos)
    (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    let pieces := reciprocalGaussianUniformMeshUniversalPieces
      lower upper cutoff hcutoff hlower half
    let P := RationalPartition.uniform lower upper pieces
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower upper cutoff hcutoff hlower half) hlowerUpper
    let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    qabs ((gaussianEvenIntegralPrefix terms (cutoff / lower) -
        gaussianEvenIntegralPrefix terms (cutoff / upper)) -
      2 * reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower) <= 2 * eps.val := by
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower upper cutoff hcutoff hlower half
  let P := RationalPartition.uniform lower upper pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower upper cutoff hcutoff hlower half) hlowerUpper
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let rawAction := reciprocalGaussianImageRightRectangleAction
    P cutoff stage hcutoff hlower
  have hbase := reciprocalGaussianUniformSynchronized_primitive_error_le
    lower upper cutoff eps hlowerUpper hcutoff hlower
  have hprefix :=
    gaussianEvenIntegralPrefix_sub_eq_two_mul_primitiveDifference
      terms (cutoff / upper) (cutoff / lower)
  have hdecomp :
      (gaussianEvenIntegralPrefix terms (cutoff / lower) -
          gaussianEvenIntegralPrefix terms (cutoff / upper)) -
        2 * rawAction =
      2 * ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
          gaussianEvenPrimitivePrefix terms (cutoff / upper)) - rawAction) := by
    rw [hprefix]
    grind [Rat.mul_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  change qabs
      ((gaussianEvenIntegralPrefix terms (cutoff / lower) -
          gaussianEvenIntegralPrefix terms (cutoff / upper)) -
        2 * rawAction) <= 2 * eps.val
  rw [hdecomp, qabs_mul, show qabs (2 : Rat) = 2 by decide +kernel]
  exact Rat.mul_le_mul_of_nonneg_left
    (by simpa [half, pieces, P, stage, terms, rawAction] using hbase)
    (by decide +kernel)

/-- The synchronized symmetric certificate specialized to the canonical
reciprocal chart from growing radius `k+1` to growing radius `n+1`.  This is
the finite statement which the remaining integrated-series sign/tail proof
must pass to the limit. -/
theorem gaussianGrowingAnnulus_synchronized_symmetricPrefix_error_le
    (k n : Nat) (hkn : k <= n) (eps : QPos) :
    let lower := gaussianGrowingAnnulusReciprocalLower k n
    let cutoff := gaussianGrowingRadius k
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    let pieces := reciprocalGaussianUniformMeshUniversalPieces
      lower 1 cutoff (gaussianGrowingRadius_pos k)
        (gaussianGrowingAnnulusReciprocalLower_pos k n) half
    let P := RationalPartition.uniform lower 1 pieces
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower 1 cutoff (gaussianGrowingRadius_pos k)
          (gaussianGrowingAnnulusReciprocalLower_pos k n) half)
      (gaussianGrowingAnnulusReciprocalLower_le_one hkn)
    let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    qabs ((gaussianEvenIntegralPrefix terms (gaussianGrowingRadius n) -
        gaussianEvenIntegralPrefix terms (gaussianGrowingRadius k)) -
      2 * reciprocalGaussianImageRightRectangleAction P cutoff stage
        (gaussianGrowingRadius_pos k)
        (gaussianGrowingAnnulusReciprocalLower_pos k n)) <=
      2 * eps.val := by
  have hbase :=
    reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_error_le
      (gaussianGrowingAnnulusReciprocalLower k n) 1
      (gaussianGrowingRadius k) eps
      (gaussianGrowingAnnulusReciprocalLower_le_one hkn)
      (gaussianGrowingRadius_pos k)
      (gaussianGrowingAnnulusReciprocalLower_pos k n)
  simpa [gaussianGrowingRadius_div_reciprocalLower_eq,
    gaussianGrowingRadius_div_one] using hbase

/-- Fully explicit uniform-source form of the combined raw-evaluator and
mesh certificate. -/
theorem reciprocalGaussianUniformImageRightRectangleAction_primitive_error_le
    (lower upper cutoff : Rat) (pieces stage : Nat)
    (hpieces : 0 < pieces) (hlowerUpper : lower <= upper)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    qabs ((gaussianEvenPrimitivePrefix terms (cutoff / lower) -
        gaussianEvenPrimitivePrefix terms (cutoff / upper)) -
      reciprocalGaussianImageRightRectangleAction
        P cutoff stage hcutoff hlower) <=
      ((cutoff * mesh lower upper pieces / (lower * lower)) *
        (cutoff / lower - cutoff / upper)) *
          (gaussianEvenPrimitiveSecantBoundAtRadius
            (cutoff / lower) (by
              rw [Rat.div_def]
              exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
                (Rat.le_of_lt ((Rat.inv_pos).2 hlower))) terms).errorCoefficient +
        reciprocalGaussianTailCommonProfileErrorBound P cutoff stage := by
  let P := RationalPartition.uniform lower upper pieces hpieces hlowerUpper
  let Q := P.reciprocalImage cutoff hcutoff hlower
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  have hradius : 0 <= cutoff / lower := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
      (Rat.le_of_lt ((Rat.inv_pos).2 hlower))
  let D := gaussianEvenPrimitiveSecantBoundAtRadius
    (cutoff / lower) hradius terms
  have hbase :=
    reciprocalGaussianImageRightRectangleAction_primitive_error_le
      P cutoff stage hcutoff hlower
  have hvariation :=
    RationalPartition.reciprocalImage_uniform_quadraticVariation_le
      lower upper cutoff pieces hpieces hlowerUpper hcutoff hlower
  have hmesh := Rat.mul_le_mul_of_nonneg_right hvariation
    D.errorCoefficient_nonneg
  have htotal := rat_add_le_add hmesh
    (Rat.le_refl :
      reciprocalGaussianTailCommonProfileErrorBound P cutoff stage <=
        reciprocalGaussianTailCommonProfileErrorBound P cutoff stage)
  exact Rat.le_trans (by simpa [P, Q, terms, D] using hbase)
    (by simpa [P, Q, terms, D] using htotal)

/-- Every prefix of the reciprocal Stieltjes action is nonnegative and pays
at most its traversed chart length divided by the cutoff.  The proof is a
literal finite induction over cells. -/
theorem reciprocalGaussianTailStieltjesActionOnPartition_prefix_nonneg_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    forall n, n <= P.pieces ->
      0 <= leftStieltjesSum
          (fun i => reciprocalGaussianTailStieltjesSampleValue
            cutoff (P.point i) stage)
          (fun i => -(cutoff / P.point i)) n /\
        leftStieltjesSum
            (fun i => reciprocalGaussianTailStieltjesSampleValue
              cutoff (P.point i) stage)
            (fun i => -(cutoff / P.point i)) n <=
          (P.point n - lower) / cutoff := by
  intro n hn
  induction n with
  | zero =>
      rw [leftStieltjesSum, P.left_endpoint]
      simp [Rat.sub_self, Rat.div_def]
  | succ n ih =>
      have hnlt : n < P.pieces := Nat.lt_of_succ_le hn
      have hnle : n <= P.pieces := Nat.le_of_lt hnlt
      have hn1le : n + 1 <= P.pieces := hn
      have hpointN := P.point_in_bounds hnle
      have hposN : 0 < P.point n := by grind
      have hmono : P.point n <= P.point (n + 1) :=
        P.monotone n (n + 1) (Nat.le_succ n) hn1le
      have hcell := reciprocalGaussianTailStieltjesCell_nonneg_le
        cutoff (P.point n) (P.point (n + 1)) stage
        hcutoff hposN hmono
      have ih' := ih hnle
      have hweight :
          -(cutoff / P.point (n + 1)) - -(cutoff / P.point n) =
            cutoff / P.point n - cutoff / P.point (n + 1) := by
        grind [Rat.sub_eq_add_neg]
      rw [leftStieltjesSum, hweight]
      constructor
      · exact Rat.add_nonneg ih'.1 hcell.1
      · have hadd := rat_add_le_add ih'.2 hcell.2
        calc
          leftStieltjesSum
                (fun i => reciprocalGaussianTailStieltjesSampleValue
                  cutoff (P.point i) stage)
                (fun i => -(cutoff / P.point i)) n +
              reciprocalGaussianTailStieltjesSampleValue
                  cutoff (P.point n) stage *
                (cutoff / P.point n - cutoff / P.point (n + 1)) <=
            (P.point n - lower) / cutoff +
              (P.point (n + 1) - P.point n) / cutoff := hadd
          _ = (P.point (n + 1) - lower) / cutoff := by
            rw [Rat.div_def]
            grind [Rat.add_mul, Rat.sub_eq_add_neg,
              Rat.add_assoc, Rat.add_comm]

/-- Every prefix of a positive reciprocal-chart partition captures at least
the explicit uniform reciprocal-Gaussian lower bound times the traversed
original-coordinate length.  In particular, this estimate is independent
of both the number of cells and the evaluator stage. -/
theorem reciprocalGaussianTailStieltjesActionOnPartition_prefix_lower_bound
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    forall n, n <= P.pieces ->
      reciprocalGaussianUniformPositiveLowerBound (cutoff / lower) *
          (cutoff / lower - cutoff / P.point n) <=
        leftStieltjesSum
          (fun i => reciprocalGaussianTailStieltjesSampleValue
            cutoff (P.point i) stage)
          (fun i => -(cutoff / P.point i)) n := by
  intro n hn
  induction n with
  | zero =>
      rw [leftStieltjesSum, P.left_endpoint, Rat.sub_self, Rat.mul_zero]
      exact Rat.le_refl
  | succ n ih =>
      have hnlt : n < P.pieces := Nat.lt_of_succ_le hn
      have hnle : n <= P.pieces := Nat.le_of_lt hnlt
      have hn1le : n + 1 <= P.pieces := hn
      have hpointNBounds := P.point_in_bounds hnle
      have hpointNPos : 0 < P.point n := by grind
      have hpointNNonneg : 0 <= cutoff / P.point n := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.le_of_lt hcutoff)
          (Rat.le_of_lt ((Rat.inv_pos).2 hpointNPos))
      have hpointNRadius : cutoff / P.point n <= cutoff / lower := by
        have hinv := RealCompute.one_div_antitone_of_pos hlower hpointNBounds.1
        have hscaled := Rat.mul_le_mul_of_nonneg_left hinv
          (Rat.le_of_lt hcutoff)
        simpa [Rat.div_def, Rat.mul_assoc] using hscaled
      have hsample :=
        reciprocalGaussianUniformPositiveLowerBound_le_stieltjesSampleValue
          (cutoff := cutoff) (t := P.point n) (radius := cutoff / lower)
          stage hpointNNonneg hpointNRadius
      have hmono : P.point n <= P.point (n + 1) :=
        P.monotone n (n + 1) (Nat.le_succ n) hn1le
      have hpointN1Pos : 0 < P.point (n + 1) := by
        have hpointN1Bounds := P.point_in_bounds hn1le
        grind
      have hinvStep := RealCompute.one_div_antitone_of_pos hpointNPos hmono
      have hscaledStep := Rat.mul_le_mul_of_nonneg_left hinvStep
        (Rat.le_of_lt hcutoff)
      have hweight :
          0 <= cutoff / P.point n - cutoff / P.point (n + 1) := by
        have hdiv : cutoff / P.point (n + 1) <= cutoff / P.point n := by
          simpa [Rat.div_def, Rat.mul_assoc] using hscaledStep
        grind [Rat.sub_eq_add_neg]
      have hterm := Rat.mul_le_mul_of_nonneg_right hsample hweight
      have ih' := ih hnle
      have hadd := rat_add_le_add ih' hterm
      rw [leftStieltjesSum]
      have hweightEq :
          -(cutoff / P.point (n + 1)) - -(cutoff / P.point n) =
            cutoff / P.point n - cutoff / P.point (n + 1) := by
        grind [Rat.sub_eq_add_neg]
      rw [hweightEq]
      exact Rat.le_trans (by
          grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
            Rat.add_assoc, Rat.add_comm]) hadd

theorem reciprocalGaussianTailStieltjesActionOnPartition_nonneg_le
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 <= reciprocalGaussianTailStieltjesActionOnPartition P cutoff stage /\
      reciprocalGaussianTailStieltjesActionOnPartition P cutoff stage <=
        (upper - lower) / cutoff := by
  have h := reciprocalGaussianTailStieltjesActionOnPartition_prefix_nonneg_le
    P cutoff stage hcutoff hlower P.pieces (Nat.le_refl _)
  simpa only [reciprocalGaussianTailStieltjesActionOnPartition,
    P.right_endpoint] using h

/-- The full reciprocal Stieltjes action has a mesh- and stage-independent
positive-density lower estimate over its entire original-coordinate image. -/
theorem reciprocalGaussianTailStieltjesActionOnPartition_lower_bound
    {lower upper : Rat} (P : RationalPartition lower upper)
    (cutoff : Rat) (stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    reciprocalGaussianUniformPositiveLowerBound (cutoff / lower) *
        (cutoff / lower - cutoff / upper) <=
      reciprocalGaussianTailStieltjesActionOnPartition P cutoff stage := by
  have h :=
    reciprocalGaussianTailStieltjesActionOnPartition_prefix_lower_bound
      P cutoff stage hcutoff hlower P.pieces (Nat.le_refl _)
  simpa only [reciprocalGaussianTailStieltjesActionOnPartition,
    P.right_endpoint] using h

/-- The executable uniform reciprocal Stieltjes mesh on `[lower,1]`. -/
def reciprocalGaussianTailUniformStieltjesAction
    (cutoff lower : Rat) (pieces stage : Nat)
    (hpieces : 0 < pieces) (hlowerOne : lower <= 1) : Rat :=
  reciprocalGaussianTailStieltjesActionOnPartition
    (RationalPartition.uniform lower 1 pieces hpieces hlowerOne)
    cutoff stage

/-- An explicit lower certificate for the symmetric uniform Stieltjes
action.  It depends on the cutoff and omitted-chart endpoint but not on the
mesh size or evaluator stage. -/
def reciprocalGaussianTailUniformStieltjesLowerBound
    (cutoff lower : Rat) : Rat :=
  2 * reciprocalGaussianUniformPositiveLowerBound (cutoff / lower) *
    (cutoff / lower - cutoff)

theorem reciprocalGaussianTailUniformStieltjesLowerBound_pos
    (cutoff lower : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) (hlowerOne : lower < 1) :
    0 < reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower := by
  have hsample :=
    reciprocalGaussianUniformPositiveLowerBound_pos (cutoff / lower)
  have hdiff : 0 < cutoff / lower - cutoff / 1 := by
    rw [reciprocal_difference_eq_mul_div cutoff lower 1 hlower
      (by decide +kernel), Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos hcutoff
      (by grind [Rat.sub_eq_add_neg]))
      ((Rat.inv_pos).2 (by simpa only [Rat.mul_one] using hlower))
  have hcutoffOne : cutoff / 1 = cutoff := by
    rw [Rat.div_def]
    have hinvOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [hinvOne, Rat.mul_one]
  unfold reciprocalGaussianTailUniformStieltjesLowerBound
  have hdiff' : 0 < cutoff / lower - cutoff := by
    simpa only [hcutoffOne] using hdiff
  exact Rat.mul_pos (Rat.mul_pos (by decide +kernel) hsample) hdiff'

/-- The explicit symmetric lower certificate is below every nonempty
uniform reciprocal Stieltjes action, independently of mesh and stage. -/
theorem reciprocalGaussianTailUniformStieltjesLowerBound_le_action
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower <= 1) (hpieces : 0 < pieces) :
    reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower <=
      2 * reciprocalGaussianTailUniformStieltjesAction
        cutoff lower pieces stage hpieces hlowerOne := by
  let P := RationalPartition.uniform lower 1 pieces hpieces hlowerOne
  have hbase :=
    reciprocalGaussianTailStieltjesActionOnPartition_lower_bound
      P cutoff stage hcutoff hlower
  have hscaled := Rat.mul_le_mul_of_nonneg_left hbase
    (by decide +kernel : (0 : Rat) <= 2)
  have hcutoffOne : cutoff / 1 = cutoff := by
    rw [Rat.div_def]
    have hinvOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [hinvOne, Rat.mul_one]
  rw [hcutoffOne] at hscaled
  simpa [reciprocalGaussianTailUniformStieltjesLowerBound,
    reciprocalGaussianTailUniformStieltjesAction, P, Rat.mul_assoc] using hscaled

/-- A nonempty uniform reciprocal chart has strictly positive finite
Gaussian action.  The first cell is strictly positive and all later cells
are nonnegative. -/
theorem reciprocalGaussianTailUniformStieltjesAction_pos
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower < 1) (hpieces : 0 < pieces) :
    0 < reciprocalGaussianTailUniformStieltjesAction
      cutoff lower pieces stage hpieces (Rat.le_of_lt hlowerOne) := by
  let P := RationalPartition.uniform lower 1 pieces hpieces
    (Rat.le_of_lt hlowerOne)
  have hmesh : 0 < mesh lower 1 pieces := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt hpieces), Rat.div_def]
    exact Rat.mul_pos (by grind [Rat.sub_eq_add_neg])
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hpieces))
  have hpointStep : P.point 0 < P.point 1 := by
    change leftPoint lower 1 pieces 0 < leftPoint lower 1 pieces 1
    rw [leftPoint_zero]
    unfold leftPoint
    have hone : (((1 : Nat) : Rat)) = 1 := by decide +kernel
    rw [hone, Rat.one_mul]
    grind
  have hpointZero : P.point 0 = lower := P.left_endpoint
  have hpointZeroPos : 0 < P.point 0 := by simpa [hpointZero] using hlower
  have hfirstCell := reciprocalGaussianTailStieltjesCell_pos
    cutoff (P.point 0) (P.point 1) stage
    hcutoff hpointZeroPos hpointStep
  have hfirst : 0 < leftStieltjesSum
      (fun i => reciprocalGaussianTailStieltjesSampleValue
        cutoff (P.point i) stage)
      (fun i => -(cutoff / P.point i)) 1 := by
    rw [show 1 = 0 + 1 by omega, leftStieltjesSum, leftStieltjesSum]
    have hweight :
        -(cutoff / P.point 1) - -(cutoff / P.point 0) =
          cutoff / P.point 0 - cutoff / P.point 1 := by
      grind [Rat.sub_eq_add_neg]
    rw [hweight, Rat.zero_add]
    exact hfirstCell
  have hmono := reciprocalGaussianTailStieltjesAction_prefix_mono
    P cutoff stage hcutoff hlower
    (i := 1) (j := P.pieces) (by change 1 <= pieces; omega)
    (Nat.le_refl _)
  unfold reciprocalGaussianTailUniformStieltjesAction
  change 0 < leftStieltjesSum
      (fun i => reciprocalGaussianTailStieltjesSampleValue
        cutoff (P.point i) stage)
      (fun i => -(cutoff / P.point i)) P.pieces
  grind

/-- The exact positive budget left unused by restricting the reciprocal
chart to `[lower,1]` instead of `[0,1]`. -/
def reciprocalGaussianTailUniformStieltjesUpperMargin
    (cutoff lower : Rat) : Rat :=
  2 * lower / cutoff

theorem reciprocalGaussianTailUniformStieltjesUpperMargin_pos
    (cutoff lower : Rat) (hcutoff : 0 < cutoff) (hlower : 0 < lower) :
    0 < reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower := by
  unfold reciprocalGaussianTailUniformStieltjesUpperMargin
  rw [Rat.div_def]
  exact Rat.mul_pos (Rat.mul_pos (by decide +kernel) hlower)
    ((Rat.inv_pos).2 hcutoff)

/-- Half the smaller of the explicit lower and upper strict margins.  This
single rational budget is chosen before either the mesh or evaluator stage. -/
def reciprocalGaussianTailUniformStieltjesStrictErrorBudget
    (cutoff lower : Rat) : Rat :=
  minRat
      (reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower)
      (reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower) *
    ((1 : Rat) / 2)

theorem reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
    (cutoff lower : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) (hlowerOne : lower < 1) :
    0 < reciprocalGaussianTailUniformStieltjesStrictErrorBudget
      cutoff lower := by
  have hlowerMargin :=
    reciprocalGaussianTailUniformStieltjesLowerBound_pos
      cutoff lower hcutoff hlower hlowerOne
  have hupperMargin :=
    reciprocalGaussianTailUniformStieltjesUpperMargin_pos
      cutoff lower hcutoff hlower
  have hmin : 0 < minRat
      (reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower)
      (reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower) := by
    unfold minRat
    split <;> assumption
  unfold reciprocalGaussianTailUniformStieltjesStrictErrorBudget
  exact Rat.mul_pos hmin (by decide +kernel)

theorem reciprocalGaussianTailUniformStieltjesStrictErrorBudget_lt_lower
    (cutoff lower : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) (hlowerOne : lower < 1) :
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <
      reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower := by
  let L := reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower
  let U := reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower
  have hL : 0 < L := by
    simpa [L] using reciprocalGaussianTailUniformStieltjesLowerBound_pos
      cutoff lower hcutoff hlower hlowerOne
  have hmin : minRat L U <= L := by
    unfold minRat
    split <;> grind
  have hscaled := Rat.mul_le_mul_of_nonneg_right hmin
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
  have hhalf : L * ((1 : Rat) / 2) < L := by
    have hscale := Rat.mul_lt_mul_of_pos_left
      (by decide +kernel : (1 : Rat) / 2 < 1) hL
    simpa only [Rat.mul_one] using hscale
  have hbudgetLe :
      reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <=
        L * ((1 : Rat) / 2) := by
    simpa [reciprocalGaussianTailUniformStieltjesStrictErrorBudget,
      L, U] using hscaled
  grind

theorem reciprocalGaussianTailUniformStieltjesStrictErrorBudget_lt_upper
    (cutoff lower : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) :
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <
      reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower := by
  let L := reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower
  let U := reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower
  have hU : 0 < U := by
    simpa [U] using reciprocalGaussianTailUniformStieltjesUpperMargin_pos
      cutoff lower hcutoff hlower
  have hmin : minRat L U <= U := by
    unfold minRat
    split <;> grind
  have hscaled := Rat.mul_le_mul_of_nonneg_right hmin
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
  have hhalf : U * ((1 : Rat) / 2) < U := by
    have hscale := Rat.mul_lt_mul_of_pos_left
      (by decide +kernel : (1 : Rat) / 2 < 1) hU
    simpa only [Rat.mul_one] using hscale
  have hbudgetLe :
      reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <=
        U * ((1 : Rat) / 2) := by
    simpa [reciprocalGaussianTailUniformStieltjesStrictErrorBudget,
      L, U] using hscaled
  grind

theorem reciprocalGaussianTailUniformStieltjesStrictErrorBudget_twice_le_lower
    (cutoff lower : Rat) :
    2 * reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <=
      reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower := by
  unfold reciprocalGaussianTailUniformStieltjesStrictErrorBudget minRat
  split <;> grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem reciprocalGaussianTailUniformStieltjesStrictErrorBudget_twice_le_upper
    (cutoff lower : Rat) :
    2 * reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <=
      reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower := by
  unfold reciprocalGaussianTailUniformStieltjesStrictErrorBudget minRat
  split <;> grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- Before weakening to the full reciprocal-square tail budget, the
symmetric finite action pays only for the traversed chart length. -/
theorem reciprocalGaussianTailUniformStieltjesAction_symmetric_le_chartLength
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower <= 1) (hpieces : 0 < pieces) :
    2 * reciprocalGaussianTailUniformStieltjesAction
        cutoff lower pieces stage hpieces hlowerOne <=
      2 * ((1 - lower) / cutoff) := by
  let P := RationalPartition.uniform lower 1 pieces hpieces hlowerOne
  have haction :=
    reciprocalGaussianTailStieltjesActionOnPartition_nonneg_le
      P cutoff stage hcutoff hlower
  have hscaled := Rat.mul_le_mul_of_nonneg_left haction.2
    (by decide +kernel : (0 : Rat) <= 2)
  simpa [reciprocalGaussianTailUniformStieltjesAction, P] using hscaled

/-- The chart-length bound plus the explicit omitted-chart margin is at most
the full symmetric reciprocal-square tail allowance. -/
theorem reciprocalGaussianTailUniformStieltjesAction_add_upperMargin_le_tail
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower <= 1) (hpieces : 0 < pieces) :
    2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces hlowerOne +
        reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower <=
      2 / cutoff := by
  have haction :=
    reciprocalGaussianTailUniformStieltjesAction_symmetric_le_chartLength
      cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  unfold reciprocalGaussianTailUniformStieltjesUpperMargin
  calc
    2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces hlowerOne +
        2 * lower / cutoff <=
      2 * ((1 - lower) / cutoff) + 2 * lower / cutoff :=
        (Rat.add_le_add_right).2 haction
    _ = 2 / cutoff := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.sub_eq_add_neg]

/-- A candidate within the synchronized error budget retains the displayed
residual pieces of both strict action margins. -/
theorem reciprocalGaussianTailUniformStieltjes_candidate_margin_bounds
    (cutoff lower candidate : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower <= 1) (hpieces : 0 < pieces)
    (herror :
      qabs (candidate -
        2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces hlowerOne) <=
        reciprocalGaussianTailUniformStieltjesStrictErrorBudget
          cutoff lower) :
    reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower -
        reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower <=
      candidate /\
    candidate +
        (reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower -
          reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower) <=
      2 / cutoff := by
  let A := 2 * reciprocalGaussianTailUniformStieltjesAction
    cutoff lower pieces stage hpieces hlowerOne
  let L := reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower
  let U := reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower
  let E := reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
  have hactionLower : L <= A := by
    simpa [L, A] using
      reciprocalGaussianTailUniformStieltjesLowerBound_le_action
        cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  have hactionUpper : A + U <= 2 / cutoff := by
    simpa [A, U] using
      reciprocalGaussianTailUniformStieltjesAction_add_upperMargin_le_tail
        cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  have herror' : qabs (candidate - A) <= E := by
    simpa [A, E] using herror
  have hdeltaUpper : candidate - A <= E :=
    Rat.le_trans (self_le_qabs (candidate - A)) herror'
  have hdeltaLower : -E <= candidate - A := by
    have hneg := neg_qabs_le_self (candidate - A)
    grind
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Any rational candidate within the preselected strict error budget of the
symmetric finite action remains strictly between zero and the full
reciprocal-square tail allowance. -/
theorem reciprocalGaussianTailUniformStieltjes_candidate_strict_bounds
    (cutoff lower candidate : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower < 1) (hpieces : 0 < pieces)
    (herror :
      qabs (candidate -
        2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces (Rat.le_of_lt hlowerOne)) <=
        reciprocalGaussianTailUniformStieltjesStrictErrorBudget
          cutoff lower) :
    0 < candidate /\ candidate < 2 / cutoff := by
  let A := 2 * reciprocalGaussianTailUniformStieltjesAction
    cutoff lower pieces stage hpieces (Rat.le_of_lt hlowerOne)
  let L := reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower
  let U := reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower
  let E := reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
  have hactionLower : L <= A := by
    simpa [L, A] using
      reciprocalGaussianTailUniformStieltjesLowerBound_le_action
        cutoff lower pieces stage hcutoff hlower
        (Rat.le_of_lt hlowerOne) hpieces
  have hactionUpper : A + U <= 2 / cutoff := by
    simpa [A, U] using
      reciprocalGaussianTailUniformStieltjesAction_add_upperMargin_le_tail
        cutoff lower pieces stage hcutoff hlower
        (Rat.le_of_lt hlowerOne) hpieces
  have hbudgetLower : E < L := by
    simpa [E, L] using
      reciprocalGaussianTailUniformStieltjesStrictErrorBudget_lt_lower
        cutoff lower hcutoff hlower hlowerOne
  have hbudgetUpper : E < U := by
    simpa [E, U] using
      reciprocalGaussianTailUniformStieltjesStrictErrorBudget_lt_upper
        cutoff lower hcutoff hlower
  have herror' : qabs (candidate - A) <= E := by
    simpa [A, E] using herror
  have hdeltaUpper : candidate - A <= E :=
    Rat.le_trans (self_le_qabs (candidate - A)) herror'
  have hdeltaLower : -E <= candidate - A := by
    have hneg := neg_qabs_le_self (candidate - A)
    grind
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Choosing the synchronized quadrature tolerance from the precomputed
two-margin budget produces a literal finite Gaussian-prefix annulus which is
strictly positive and strictly below the reciprocal-square tail bound. -/
theorem reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_strict_bounds
    (lower cutoff : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) (hlowerOne : lower < 1) :
    let budget :=
      reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
    let eps : QPos := ⟨budget / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
          cutoff lower hcutoff hlower hlowerOne)
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    let pieces := reciprocalGaussianUniformMeshUniversalPieces
      lower 1 cutoff hcutoff hlower half
    let P := RationalPartition.uniform lower 1 pieces
      (reciprocalGaussianUniformMeshUniversalPieces_pos
        lower 1 cutoff hcutoff hlower half)
      (Rat.le_of_lt hlowerOne)
    let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
    let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
    let candidate := gaussianEvenIntegralPrefix terms (cutoff / lower) -
      gaussianEvenIntegralPrefix terms cutoff
    0 < candidate /\ candidate < 2 / cutoff := by
  let budget :=
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
  let eps : QPos := ⟨budget / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos
      (reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
        cutoff lower hcutoff hlower hlowerOne)
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower 1 cutoff hcutoff hlower half
  have hpieces : 0 < pieces := by
    simpa [pieces] using
      reciprocalGaussianUniformMeshUniversalPieces_pos
        lower 1 cutoff hcutoff hlower half
  let P := RationalPartition.uniform lower 1 pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower 1 cutoff hcutoff hlower half)
    (Rat.le_of_lt hlowerOne)
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let candidate := gaussianEvenIntegralPrefix terms (cutoff / lower) -
    gaussianEvenIntegralPrefix terms cutoff
  have hsync :=
    reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_error_le
      lower 1 cutoff eps (Rat.le_of_lt hlowerOne) hcutoff hlower
  have hcutoffOne : cutoff / 1 = cutoff := by
    rw [Rat.div_def]
    have hinvOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [hinvOne, Rat.mul_one]
  rw [hcutoffOne] at hsync
  have hactionEq :=
    reciprocalGaussianTailStieltjesAction_eq_imageRightRectangleAction
      P cutoff stage hcutoff hlower
  have hbudgetEq : 2 * eps.val = budget := by
    have htwoNe : (2 : Rat) ≠ 0 := by decide +kernel
    have hcancel : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel 2 htwoNe
    dsimp [eps]
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have herror :
      qabs (candidate -
        2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces (Rat.le_of_lt hlowerOne)) <=
        budget := by
    rw [hbudgetEq.symm]
    simpa [candidate, reciprocalGaussianTailUniformStieltjesAction,
      P, stage, terms, pieces, half, hactionEq] using hsync
  simpa [candidate, budget] using
    reciprocalGaussianTailUniformStieltjes_candidate_strict_bounds
      cutoff lower candidate pieces stage hcutoff hlower hlowerOne hpieces
      (by simpa [budget] using herror)

/-- The synchronized construction can be read directly as four alternating
endpoint prefixes: an outer even/odd pair and an inner even/odd pair already
satisfy the nonnegative annulus and reciprocal-square tail inequalities. -/
theorem reciprocalGaussianUniformSynchronized_exists_fourPrefix_bounds
    (lower cutoff : Rat) (hcutoff : 0 < cutoff)
    (hlower : 0 < lower) (hlowerOne : lower < 1) :
    Exists fun outerStage : Nat => Exists fun innerStage : Nat =>
      0 <= gaussianEvenIntegralPrefix
              (gaussianIntegralTailStart (cutoff / lower) + 2 * outerStage)
              (cutoff / lower) -
            gaussianEvenIntegralPrefix
              (gaussianIntegralTailStart cutoff + (2 * innerStage + 1))
              cutoff /\
        gaussianEvenIntegralPrefix
              (gaussianIntegralTailStart (cutoff / lower) +
                (2 * outerStage + 1))
              (cutoff / lower) -
            gaussianEvenIntegralPrefix
              (gaussianIntegralTailStart cutoff + 2 * innerStage) cutoff <=
          2 / cutoff := by
  let budget :=
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
  let eps : QPos := ⟨budget / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos
      (reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
        cutoff lower hcutoff hlower hlowerOne)
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower 1 cutoff hcutoff hlower half
  have hpieces : 0 < pieces := by
    simpa [pieces] using
      reciprocalGaussianUniformMeshUniversalPieces_pos
        lower 1 cutoff hcutoff hlower half
  let P := RationalPartition.uniform lower 1 pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower 1 cutoff hcutoff hlower half)
    (Rat.le_of_lt hlowerOne)
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  let candidate := gaussianEvenIntegralPrefix terms (cutoff / lower) -
    gaussianEvenIntegralPrefix terms cutoff
  have hsync :=
    reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_error_le
      lower 1 cutoff eps (Rat.le_of_lt hlowerOne) hcutoff hlower
  have hcutoffOne : cutoff / 1 = cutoff := by
    rw [Rat.div_def]
    have hinvOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [hinvOne, Rat.mul_one]
  rw [hcutoffOne] at hsync
  have hactionEq :=
    reciprocalGaussianTailStieltjesAction_eq_imageRightRectangleAction
      P cutoff stage hcutoff hlower
  have hbudgetEq : 2 * eps.val = budget := by
    have htwoNe : (2 : Rat) ≠ 0 := by decide +kernel
    have hcancel : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel 2 htwoNe
    dsimp [eps]
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have herror :
      qabs (candidate -
        2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces (Rat.le_of_lt hlowerOne)) <=
        budget := by
    rw [hbudgetEq.symm]
    simpa [candidate, reciprocalGaussianTailUniformStieltjesAction,
      P, stage, terms, pieces, half, hactionEq] using hsync
  have hmargins :=
    reciprocalGaussianTailUniformStieltjes_candidate_margin_bounds
      cutoff lower candidate pieces stage hcutoff hlower
      (Rat.le_of_lt hlowerOne) hpieces
      (by simpa [budget] using herror)
  have htwiceLower :=
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget_twice_le_lower
      cutoff lower
  have htwiceUpper :=
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget_twice_le_upper
      cutoff lower
  have hhalfBudget : half.val <= budget := by
    have hbudgetPos : 0 < budget := by
      simpa [budget] using
        (reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
          cutoff lower hcutoff hlower hlowerOne)
    have hbudgetNonneg : 0 <= budget := Rat.le_of_lt hbudgetPos
    dsimp [half, eps]
    rw [Rat.div_def, Rat.div_def]
    have hquarter : (2 : Rat)⁻¹ * (2 : Rat)⁻¹ <= 1 := by decide +kernel
    have hscaled := Rat.mul_le_mul_of_nonneg_left hquarter hbudgetNonneg
    simpa [Rat.mul_assoc] using hscaled
  have houterOmitted :=
    reciprocalGaussianTailCommonProfile_outerOmittedMagnitude_le
      P cutoff half hcutoff hlower
  have hinnerOmitted :=
    reciprocalGaussianTailCommonProfile_innerOmittedMagnitude_le
      P cutoff half hcutoff hlower
  rw [hcutoffOne] at hinnerOmitted
  have htermsEven : terms % 2 = 0 := by
    simpa [terms, stage] using
      reciprocalGaussianTailCommonProfileTerms_even P cutoff stage
  have houterStartEven :
      gaussianIntegralTailStart (cutoff / lower) % 2 = 0 :=
    gaussianIntegralTailStart_even _
  have hinnerStartEven : gaussianIntegralTailStart cutoff % 2 = 0 :=
    gaussianIntegralTailStart_even _
  have houterStartLe : gaussianIntegralTailStart (cutoff / lower) <= terms := by
    have h :=
      gaussianIntegralTailStart_outer_add_two_stage_le_commonProfileTerms
        P cutoff stage
    simpa [terms] using (Nat.le_trans (by omega :
      gaussianIntegralTailStart (cutoff / lower) <=
        gaussianIntegralTailStart (cutoff / lower) + 2 * stage) h)
  have hinnerStartLe : gaussianIntegralTailStart cutoff <= terms := by
    have h :=
      gaussianIntegralTailStart_inner_add_two_stage_le_commonProfileTerms
        P cutoff stage
    rw [hcutoffOne] at h
    simpa [terms] using (Nat.le_trans (by omega :
      gaussianIntegralTailStart cutoff <=
        gaussianIntegralTailStart cutoff + 2 * stage) h)
  let outerStage :=
    (terms - gaussianIntegralTailStart (cutoff / lower)) / 2
  let innerStage := (terms - gaussianIntegralTailStart cutoff) / 2
  have houterTerms :
      gaussianIntegralTailStart (cutoff / lower) + 2 * outerStage = terms := by
    dsimp [outerStage]
    omega
  have hinnerTerms :
      gaussianIntegralTailStart cutoff + 2 * innerStage = terms := by
    dsimp [innerStage]
    omega
  have houterOffset :
      2 * outerStage = terms - gaussianIntegralTailStart (cutoff / lower) := by
    dsimp [outerStage]
    omega
  have hinnerOffset :
      2 * innerStage = terms - gaussianIntegralTailStart cutoff := by
    dsimp [innerStage]
    omega
  have houterNext :=
    gaussianEvenIntegralPrefix_tailStart_even_succ
      (cutoff / lower) outerStage
  have hinnerNext :=
    gaussianEvenIntegralPrefix_tailStart_even_succ cutoff innerStage
  have houterNext' :
      gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart (cutoff / lower) +
            (2 * outerStage + 1)) (cutoff / lower) =
        gaussianEvenIntegralPrefix
            (gaussianIntegralTailStart (cutoff / lower) + 2 * outerStage)
            (cutoff / lower) +
          gaussianIntegralShiftedMagnitude (cutoff / lower) (2 * outerStage) := by
    simpa only [Nat.add_assoc] using houterNext
  have hinnerNext' :
      gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart cutoff + (2 * innerStage + 1)) cutoff =
        gaussianEvenIntegralPrefix
            (gaussianIntegralTailStart cutoff + 2 * innerStage) cutoff +
          gaussianIntegralShiftedMagnitude cutoff (2 * innerStage) := by
    simpa only [Nat.add_assoc] using hinnerNext
  have houterMagnitude :
      gaussianIntegralShiftedMagnitude (cutoff / lower) (2 * outerStage) <=
        budget := by
    exact Rat.le_trans (by simpa [terms, stage, houterOffset] using houterOmitted)
      hhalfBudget
  have hinnerMagnitude :
      gaussianIntegralShiftedMagnitude cutoff (2 * innerStage) <= budget := by
    exact Rat.le_trans (by simpa [terms, stage, hinnerOffset] using hinnerOmitted)
      hhalfBudget
  refine ⟨outerStage, innerStage, ?_⟩
  constructor
  · rw [houterTerms, hinnerNext', hinnerTerms]
    have hlowerResidual : budget <=
        reciprocalGaussianTailUniformStieltjesLowerBound cutoff lower -
          budget := by
      dsimp [budget] at htwiceLower ⊢
      grind [Rat.sub_eq_add_neg]
    have hcandidate : budget <= candidate :=
      Rat.le_trans hlowerResidual (by simpa [candidate, budget] using hmargins.1)
    grind [Rat.sub_eq_add_neg]
  · rw [houterNext', houterTerms, hinnerTerms]
    have hupperResidual : budget <=
        reciprocalGaussianTailUniformStieltjesUpperMargin cutoff lower -
          budget := by
      dsimp [budget] at htwiceUpper ⊢
      grind [Rat.sub_eq_add_neg]
    have hcandidateUpper : candidate + budget <= 2 / cutoff := by
      have hmain := hmargins.2
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]

/-- Every strict pair of growing radii admits a completely explicit finite
Gaussian Taylor-prefix annulus already lying strictly between zero and the
desired symmetric reciprocal-square tail budget.  The witness is computed
by the synchronized mesh/stage scheduler. -/
theorem gaussianGrowingAnnulus_exists_strict_finitePrefix
    (k n : Nat) (hkn : k < n) :
    Exists fun terms : Nat =>
      0 < gaussianEvenIntegralPrefix terms (gaussianGrowingRadius n) -
          gaussianEvenIntegralPrefix terms (gaussianGrowingRadius k) /\
        gaussianEvenIntegralPrefix terms (gaussianGrowingRadius n) -
            gaussianEvenIntegralPrefix terms (gaussianGrowingRadius k) <
          symmetricReciprocalSquareTailRadius k := by
  let lower := gaussianGrowingAnnulusReciprocalLower k n
  let cutoff := gaussianGrowingRadius k
  have hlower : 0 < lower := by
    simpa [lower] using gaussianGrowingAnnulusReciprocalLower_pos k n
  have hlowerOne : lower < 1 := by
    simpa [lower] using gaussianGrowingAnnulusReciprocalLower_lt_one hkn
  have hstrict :=
    reciprocalGaussianUniformSynchronized_symmetricPrefixAnnulus_strict_bounds
      lower cutoff (gaussianGrowingRadius_pos k) hlower hlowerOne
  let budget :=
    reciprocalGaussianTailUniformStieltjesStrictErrorBudget cutoff lower
  let eps : QPos := ⟨budget / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos
      (reciprocalGaussianTailUniformStieltjesStrictErrorBudget_pos
        cutoff lower (gaussianGrowingRadius_pos k) hlower hlowerOne)
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
  let pieces := reciprocalGaussianUniformMeshUniversalPieces
    lower 1 cutoff (gaussianGrowingRadius_pos k) hlower half
  let P := RationalPartition.uniform lower 1 pieces
    (reciprocalGaussianUniformMeshUniversalPieces_pos
      lower 1 cutoff (gaussianGrowingRadius_pos k) hlower half)
    (Rat.le_of_lt hlowerOne)
  let stage := reciprocalGaussianTailCommonProfileStage P cutoff half
  let terms := reciprocalGaussianTailCommonProfileTerms P cutoff stage
  refine ⟨terms, ?_⟩
  have hradiusEq : cutoff / lower = gaussianGrowingRadius n := by
    simpa [cutoff, lower] using
      gaussianGrowingRadius_div_reciprocalLower_eq k n
  rw [hradiusEq] at hstrict
  simpa [lower, cutoff, budget, eps, half, pieces, P, stage, terms,
    symmetricReciprocalSquareTailRadius, gaussianGrowingRadius] using hstrict

/-- The symmetric finite reciprocal Stieltjes action already satisfies the
full represented tail budget `2/cutoff`, independently of mesh and evaluator
stage. -/
theorem reciprocalGaussianTailUniformStieltjesAction_symmetric_bounds
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower)
    (hlowerOne : lower <= 1) (hpieces : 0 < pieces) :
    0 <= 2 * reciprocalGaussianTailUniformStieltjesAction
        cutoff lower pieces stage hpieces hlowerOne /\
      2 * reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces hlowerOne <= 2 / cutoff := by
  let P := RationalPartition.uniform lower 1 pieces hpieces hlowerOne
  have haction :=
    reciprocalGaussianTailStieltjesActionOnPartition_nonneg_le
      P cutoff stage hcutoff hlower
  have hlength : 1 - lower <= 1 := by
    grind [Rat.sub_eq_add_neg]
  have hinv : 0 <= 1 / cutoff := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 hcutoff))
  have hbudget : (1 - lower) / cutoff <= 1 / cutoff := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hlength
      (Rat.le_of_lt ((Rat.inv_pos).2 hcutoff))
  have hactionLe :
      reciprocalGaussianTailUniformStieltjesAction
          cutoff lower pieces stage hpieces hlowerOne <= 1 / cutoff := by
    exact Rat.le_trans haction.2 hbudget
  constructor
  · exact Rat.mul_nonneg (by decide +kernel) haction.1
  · have hscaled := Rat.mul_le_mul_of_nonneg_left hactionLe
      (by decide +kernel : (0 : Rat) <= 2)
    simpa [Rat.div_def, Rat.mul_assoc] using hscaled

/-- A literal finite midpoint/Darboux rule for the reciprocal-chart Gaussian
on a positive compact subinterval `[lower,1]`.  Every cell uses the single
constant range `[0,1/cutoff]`; sample values are rational midpoints of the
chosen raw-evaluator boxes. -/
def reciprocalGaussianChartCellSample {a b : Rat}
    (C : RationalSubinterval a b) : Rat :=
  (SampledDarbouxCell.cellInterval C).midpoint

theorem reciprocalGaussianChartCellSample_mem {a b : Rat}
    (C : RationalSubinterval a b) :
    C.contains (reciprocalGaussianChartCellSample C) := by
  exact QInterval.midpoint_mem
    (I := SampledDarbouxCell.cellInterval C) C.ordered

def reciprocalGaussianChartCellSampleValue {a b : Rat}
    (cutoff : Rat) (stage : Nat) (C : RationalSubinterval a b) : Rat :=
  ((reciprocalGaussianChartDensityRaw cutoff
    (reciprocalGaussianChartCellSample C)).compute stage).midpoint

theorem reciprocalGaussianChartCellSampleValue_mem {a b : Rat}
    (cutoff : Rat) (stage : Nat) (C : RationalSubinterval a b) :
    ((reciprocalGaussianChartDensityRaw cutoff
      (reciprocalGaussianChartCellSample C)).compute stage).ContainsInterval
        (QInterval.pointInterval
          (reciprocalGaussianChartCellSampleValue cutoff stage C)) := by
  exact QInterval.midpoint_mem
    (RealCompute.interval_order_of_valid
      (reciprocalGaussianChartDensityRaw cutoff
        (reciprocalGaussianChartCellSample C))
      (reciprocalGaussianChartDensityRaw_valid cutoff
        (reciprocalGaussianChartCellSample C)) stage)

def reciprocalGaussianChartUniformRule
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    SampledRawDarbouxPartition
      (reciprocalGaussianChartDensityRaw cutoff)
      (RationalPartition.uniform lower 1 pieces hpieces hlowerOne) where
  evalStage := stage
  sample := fun k hk => reciprocalGaussianChartCellSample
    ((RationalPartition.uniform lower 1 pieces hpieces hlowerOne).cell k hk)
  sample_mem := by
    intro k hk
    exact reciprocalGaussianChartCellSample_mem _
  sampleValue := fun k hk => reciprocalGaussianChartCellSampleValue cutoff stage
    ((RationalPartition.uniform lower 1 pieces hpieces hlowerOne).cell k hk)
  sampleValue_mem := by
    intro k hk
    exact reciprocalGaussianChartCellSampleValue_mem cutoff stage _
  range := fun _k _hk => { lo := 0, hi := 1 / cutoff }
  range_contains := by
    intro k hk t ht
    let C := (RationalPartition.uniform lower 1 pieces hpieces hlowerOne).cell k hk
    have hcellLower : lower <= C.lower := C.lower_mem
    have htpos : 0 < t := by
      change C.contains t at ht
      change C.lower <= t /\ t <= C.upper at ht
      grind
    exact reciprocalGaussianChartDensityRaw_compute_mem_constantRange
      cutoff t hcutoff htpos stage

theorem reciprocalGaussianChartUniformRule_darbouxSum_width_le
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    ((reciprocalGaussianChartUniformRule cutoff lower pieces stage
      hcutoff hlower hlowerOne hpieces).darbouxSum).width <=
        (1 - lower) * (1 / cutoff) := by
  change
    ((RationalPartition.uniform lower 1 pieces hpieces hlowerOne).boundIntegralSum
      (fun _k _hk => ({ lo := 0, hi := 1 / cutoff } : QInterval))).width <= _
  apply RationalPartition.uniform_boundIntegralSum_width_le
  intro k hk
  unfold QInterval.width
  grind

theorem reciprocalGaussianChartUniformRule_darbouxSum_lo_eq_zero
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    ((reciprocalGaussianChartUniformRule cutoff lower pieces stage
      hcutoff hlower hlowerOne hpieces).darbouxSum).lo = 0 := by
  change
    ((RationalPartition.uniform lower 1 pieces hpieces hlowerOne).boundIntegralSum
      (fun _k _hk => ({ lo := 0, hi := 1 / cutoff } : QInterval))).lo = 0
  apply RationalPartition.boundIntegralSum_lo_eq_zero_of_bound_lo_zero
  intro _k _hk
  rfl

theorem reciprocalGaussianChartUniformRule_darbouxSum_hi_le_one_div
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    ((reciprocalGaussianChartUniformRule cutoff lower pieces stage
      hcutoff hlower hlowerOne hpieces).darbouxSum).hi <= 1 / cutoff := by
  have hwidth := reciprocalGaussianChartUniformRule_darbouxSum_width_le
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  have hlo := reciprocalGaussianChartUniformRule_darbouxSum_lo_eq_zero
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  have hinv : 0 <= 1 / cutoff := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 hcutoff))
  have hlength : 1 - lower <= 1 := by grind [Rat.sub_eq_add_neg]
  have hscaled := Rat.mul_le_mul_of_nonneg_right hlength hinv
  unfold QInterval.width at hwidth
  rw [hlo] at hwidth
  have hhiWidth :
      ((reciprocalGaussianChartUniformRule cutoff lower pieces stage
        hcutoff hlower hlowerOne hpieces).darbouxSum).hi <=
        (1 - lower) * (1 / cutoff) := by
    simpa only [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero] using hwidth
  have hscaled' : (1 - lower) * (1 / cutoff) <= 1 / cutoff := by
    simpa only [Rat.one_mul] using hscaled
  exact Rat.le_trans hhiWidth hscaled'

theorem reciprocalGaussianChartUniformRule_sampledAction_nonneg
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    0 <= (reciprocalGaussianChartUniformRule cutoff lower pieces stage
      hcutoff hlower hlowerOne hpieces).sampledAction := by
  let R := reciprocalGaussianChartUniformRule cutoff lower pieces stage
    hcutoff hlower hlowerOne hpieces
  have hcontains := R.darbouxSum_contains_sampledAction
  have hlo := reciprocalGaussianChartUniformRule_darbouxSum_lo_eq_zero
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  change R.darbouxSum.ContainsInterval
    (QInterval.pointInterval R.sampledAction) at hcontains
  unfold QInterval.ContainsInterval QInterval.pointInterval at hcontains
  change R.darbouxSum.lo = 0 at hlo
  grind

theorem reciprocalGaussianChartUniformRule_sampledAction_le_one_div
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    (reciprocalGaussianChartUniformRule cutoff lower pieces stage
      hcutoff hlower hlowerOne hpieces).sampledAction <= 1 / cutoff := by
  let R := reciprocalGaussianChartUniformRule cutoff lower pieces stage
    hcutoff hlower hlowerOne hpieces
  have hcontains := R.darbouxSum_contains_sampledAction
  have hhi := reciprocalGaussianChartUniformRule_darbouxSum_hi_le_one_div
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  change R.darbouxSum.ContainsInterval
    (QInterval.pointInterval R.sampledAction) at hcontains
  unfold QInterval.ContainsInterval QInterval.pointInterval at hcontains
  change R.darbouxSum.hi <= 1 / cutoff at hhi
  exact Rat.le_trans hcontains.2 hhi

theorem reciprocalGaussianChartUniformRule_symmetricSampledAction_bounds
    (cutoff lower : Rat) (pieces stage : Nat)
    (hcutoff : 0 < cutoff) (hlower : 0 < lower) (hlowerOne : lower <= 1)
    (hpieces : 0 < pieces) :
    0 <= 2 * (reciprocalGaussianChartUniformRule cutoff lower pieces stage
        hcutoff hlower hlowerOne hpieces).sampledAction /\
      2 * (reciprocalGaussianChartUniformRule cutoff lower pieces stage
        hcutoff hlower hlowerOne hpieces).sampledAction <= 2 / cutoff := by
  have hlo := reciprocalGaussianChartUniformRule_sampledAction_nonneg
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  have hhi := reciprocalGaussianChartUniformRule_sampledAction_le_one_div
    cutoff lower pieces stage hcutoff hlower hlowerOne hpieces
  constructor
  · exact Rat.mul_nonneg (by decide +kernel) hlo
  · have hscaled := Rat.mul_le_mul_of_nonneg_left hhi
      (by decide +kernel : (0 : Rat) <= 2)
    simpa [Rat.div_def, Rat.mul_assoc] using hscaled

/-- The inner precision needed at outer stage `n`.  The first summand keeps
the quadrature mesh at least as fine as outer stage `n`; the second makes the
alternating tail no wider than that stage's rational precision. -/
def gaussianGrowingRadiusInternalStage (stage : Nat) : Nat :=
  stage + RationalMajorant.halfDecayShift
    (gaussianIntegralShiftedGeometricBound (gaussianGrowingRadius stage))
    (precisionAtStage (stage + 1))

theorem gaussianGrowingRadiusSeries_width_le_precision (stage : Nat) :
    ((gaussianRadiusIntegratedSeriesRaw
        (gaussianGrowingRadius stage) (gaussianGrowingRadius_nonneg stage)).compute
      (gaussianGrowingRadiusInternalStage stage)).width <=
        (precisionAtStage (stage + 1)).val := by
  let radius := gaussianGrowingRadius stage
  let shift := RationalMajorant.halfDecayShift
    (gaussianIntegralShiftedGeometricBound radius)
    (precisionAtStage (stage + 1))
  let internal := gaussianGrowingRadiusInternalStage stage
  have hradius : 0 <= radius := by
    simpa [radius] using gaussianGrowingRadius_nonneg stage
  have hshift : shift <= 2 * internal := by
    change RationalMajorant.halfDecayShift
        (gaussianIntegralShiftedGeometricBound (gaussianGrowingRadius stage))
        (precisionAtStage (stage + 1)) <=
      2 * (stage + RationalMajorant.halfDecayShift
        (gaussianIntegralShiftedGeometricBound (gaussianGrowingRadius stage))
        (precisionAtStage (stage + 1)))
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hshift
  rw [gaussianRadiusIntegratedSeriesRaw_width_eq_shiftedMagnitude]
  have hgeom := gaussianIntegralShiftedMagnitude_le_geometric
    radius hradius (2 * internal)
  have hpow : ((1 : Rat) / 2) ^ (2 * internal) <=
      ((1 : Rat) / 2) ^ shift := by
    rw [hd]
    exact Series.halfPow_add_le_left shift d
  have hbound := gaussianIntegralShiftedGeometricBound_nonneg radius hradius
  calc
    gaussianIntegralShiftedMagnitude radius (2 * internal) <=
        gaussianIntegralShiftedGeometricBound radius *
          ((1 : Rat) / 2) ^ (2 * internal) := hgeom
    _ <= gaussianIntegralShiftedGeometricBound radius *
          ((1 : Rat) / 2) ^ shift :=
      Rat.mul_le_mul_of_nonneg_left hpow hbound
    _ <= (precisionAtStage (stage + 1)).val := by
      dsimp [shift]
      exact RationalMajorant.halfDecayShift_spec hbound
        (precisionAtStage (stage + 1))

/-- The executable growing bounded-quadrature candidate.  Outer stage `n`
uses radius `n+1` and the explicit inner precision above. -/
def gaussianGrowingRadiusBoundedQuadratureRaw (stage : Nat) : RealCompute :=
  gaussianRadiusTaylorQuadratureRaw
    (gaussianGrowingRadius stage) (gaussianGrowingRadius_nonneg stage)

def gaussianGrowingRadiusQuadratureCandidate : RealCompute where
  compute := fun stage =>
    (gaussianGrowingRadiusBoundedQuadratureRaw stage).compute
        (gaussianGrowingRadiusInternalStage stage)

theorem gaussianGrowingRadiusQuadratureCandidate_ordered (stage : Nat) :
    0 <= (gaussianGrowingRadiusQuadratureCandidate.compute stage).width := by
  exact (gaussianRadiusTaylorQuadratureRaw_valid
    (gaussianGrowingRadius stage) (gaussianGrowingRadius_nonneg stage)).1
      (gaussianGrowingRadiusInternalStage stage)

theorem gaussianGrowingRadiusQuadratureCandidate_width_le_natRate
    (stage : Nat) :
    (gaussianGrowingRadiusQuadratureCandidate.compute stage).width <=
      4 / (((stage + 1 : Nat) : Rat)) := by
  let radius := gaussianGrowingRadius stage
  let hradius : 0 <= radius := by
    simpa [radius] using gaussianGrowingRadius_nonneg stage
  let internal := gaussianGrowingRadiusInternalStage stage
  have hcontain := RealCompute.prefixStabilize_contained_in_current_expand
    (gaussianRadiusTaylorQuadratureCandidateRaw radius hradius)
    (gaussianRadiusTaylorQuadratureStabilizationRadius radius hradius)
    internal
  have hwidth := QInterval.width_le_of_contains hcontain
  rw [QInterval.expand_width] at hwidth
  have hinternal : stage <= internal := by
    dsimp [internal, gaussianGrowingRadiusInternalStage]
    omega
  have hcandidateBase :=
    gaussianRadiusTaylorQuadratureCandidateRaw_width_le_natRate
      radius hradius internal
  have hrecip := Series.one_div_nat_antitone_series
    (n := stage + 1) (m := internal + 1)
    (by omega) (by omega) (by omega)
  have hcandidate :
      ((gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute
        internal).width <= 2 / (((stage + 1 : Nat) : Rat)) :=
    Rat.le_trans hcandidateBase (by
      have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
        (by decide +kernel : (0 : Rat) <= 2)
      simpa [Rat.div_def, Rat.mul_assoc] using hscaled)
  have hanchor := gaussianGrowingRadiusSeries_width_le_precision stage
  rw [precisionAtStage_succ_value] at hanchor
  change ((gaussianRadiusTaylorQuadratureRaw radius hradius).compute
    internal).width <= _
  calc
    ((gaussianRadiusTaylorQuadratureRaw radius hradius).compute internal).width <=
        ((gaussianRadiusTaylorQuadratureCandidateRaw radius hradius).compute
          internal).width +
          2 * gaussianRadiusTaylorQuadratureStabilizationRadius
            radius hradius internal := by
      simpa [gaussianRadiusTaylorQuadratureRaw] using hwidth
    _ <= 2 / (((stage + 1 : Nat) : Rat)) +
          2 * (1 / (((stage + 1 : Nat) : Rat))) := by
      exact rat_add_le_add hcandidate
        (Rat.mul_le_mul_of_nonneg_left hanchor (by decide +kernel))
    _ = 4 / (((stage + 1 : Nat) : Rat)) := by
      grind [Rat.div_def, Rat.mul_assoc]

theorem gaussianGrowingRadiusQuadratureCandidate_widths_shrink :
    RealCompute.WidthsShrinkToZero gaussianGrowingRadiusQuadratureCandidate.compute :=
  shrinksToZero_of_natOverSuccBound
    gaussianGrowingRadiusQuadratureCandidate_width_le_natRate

theorem gaussianGrowingRadiusQuadratureCandidate_endpoints_ordered
    (stage : Nat) :
    (gaussianGrowingRadiusQuadratureCandidate.compute stage).lo <=
      (gaussianGrowingRadiusQuadratureCandidate.compute stage).hi := by
  have hwidth := gaussianGrowingRadiusQuadratureCandidate_ordered stage
  unfold QInterval.width at hwidth
  grind

/-! ## From represented annular order to literal interval containment -/

/-- Raw-real order in both directions, with an exact rational upper budget,
contains a selected target box after paying that target box's numerical
width.  This is the finite bookkeeping needed when a semantic tail inequality
is converted into literal stagewise containment. -/
theorem expand_contains_of_raw_le_add_target_width
    (x y : RealCompute) (nx ny : Nat) (delta : Rat)
    (hdelta : 0 <= delta)
    (hxy : x.Le y)
    (hyx : y.Le (RealCompute.add x (RealCompute.ofRat delta))) :
    (QInterval.expand (x.compute nx)
      (delta + (y.compute ny).width)).ContainsInterval (y.compute ny) := by
  have hlower := hxy nx ny
  have hupper := hyx ny nx
  change (y.compute ny).lo <=
      (x.compute nx).hi + delta at hupper
  unfold QInterval.ContainsInterval QInterval.expand QInterval.width
  constructor <;>
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
      Rat.add_left_comm]

/-- The semantic annular theorem still required from the Gaussian integrand.
It states monotonicity of the bounded values and bounds the added annulus by
the represented reciprocal-square tail.  Unlike literal box containment,
this formulation is invariant under replacement by equivalent raw
algorithms. -/
def GaussianGrowingQuadratureAnnularOrder : Prop :=
  forall k n, k <= n ->
    (gaussianGrowingRadiusBoundedQuadratureRaw k).Le
        (gaussianGrowingRadiusBoundedQuadratureRaw n) /\
      (gaussianGrowingRadiusBoundedQuadratureRaw n).Le
        (RealCompute.add (gaussianGrowingRadiusBoundedQuadratureRaw k)
          (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k)))

/-- The literal represented difference between the outer and inner bounded
Gaussian computations.  It is executable before its sign and tail bounds are
known. -/
def gaussianGrowingRadiusAnnulusRaw (k n : Nat) : RealCompute :=
  RealCompute.sub (gaussianGrowingRadiusBoundedQuadratureRaw n)
    (gaussianGrowingRadiusBoundedQuadratureRaw k)

theorem gaussianGrowingRadiusAnnulusRaw_valid (k n : Nat) :
    (gaussianGrowingRadiusAnnulusRaw k n).Valid := by
  unfold gaussianGrowingRadiusAnnulusRaw
  exact RealCompute.sub_valid
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)

/-- The representation-invariant anchor for a growing Gaussian annulus: the
difference of the two stabilized integrated-series values. -/
def gaussianGrowingRadiusIntegratedSeriesAnnulusRaw (k n : Nat) : RealCompute :=
  RealCompute.sub
    (gaussianRadiusIntegratedSeriesRaw
      (gaussianGrowingRadius n) (gaussianGrowingRadius_nonneg n))
    (gaussianRadiusIntegratedSeriesRaw
      (gaussianGrowingRadius k) (gaussianGrowingRadius_nonneg k))

theorem gaussianGrowingRadiusIntegratedSeriesAnnulusRaw_valid (k n : Nat) :
    (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n).Valid := by
  unfold gaussianGrowingRadiusIntegratedSeriesAnnulusRaw
  exact RealCompute.sub_valid
    (gaussianRadiusIntegratedSeriesRaw_valid _ _)
    (gaussianRadiusIntegratedSeriesRaw_valid _ _)

/-- Four explicit finite Gaussian prefixes bracket the represented annulus.
The outer even prefix and inner odd prefix give the lower bound; the outer
odd prefix and inner even prefix give the upper bound.  The two prefix stages
may be selected independently. -/
theorem gaussianGrowingRadiusIntegratedSeriesAnnulusRaw_between_shifted_prefixes
    (k n outerStage innerStage : Nat) :
    let outerRadius := gaussianGrowingRadius n
    let innerRadius := gaussianGrowingRadius k
    let outerEven := gaussianEvenIntegralPrefix
      (gaussianIntegralTailStart outerRadius + 2 * outerStage) outerRadius
    let outerOdd := gaussianEvenIntegralPrefix
      (gaussianIntegralTailStart outerRadius + (2 * outerStage + 1)) outerRadius
    let innerEven := gaussianEvenIntegralPrefix
      (gaussianIntegralTailStart innerRadius + 2 * innerStage) innerRadius
    let innerOdd := gaussianEvenIntegralPrefix
      (gaussianIntegralTailStart innerRadius + (2 * innerStage + 1)) innerRadius
    (RealCompute.sub (RealCompute.ofRat outerEven) (RealCompute.ofRat innerOdd)).Le
        (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n) /\
      (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n).Le
        (RealCompute.sub (RealCompute.ofRat outerOdd) (RealCompute.ofRat innerEven)) := by
  let outerRadius := gaussianGrowingRadius n
  let innerRadius := gaussianGrowingRadius k
  have houter :=
    gaussianRadiusIntegratedSeriesRaw_between_shifted_even_odd_prefixes
      outerRadius (gaussianGrowingRadius_nonneg n) outerStage
  have hinner :=
    gaussianRadiusIntegratedSeriesRaw_between_shifted_even_odd_prefixes
      innerRadius (gaussianGrowingRadius_nonneg k) innerStage
  constructor
  · exact RealCompute.le_sub_le_sub houter.1 hinner.2
  · exact RealCompute.le_sub_le_sub houter.2 hinner.1

/-- Even and odd endpoint prefixes of the alternating integrated Gaussian
series at a growing rational radius. -/
def gaussianGrowingIntegralEvenPrefix
    (radiusStage prefixStage : Nat) : Rat :=
  gaussianEvenIntegralPrefix
    (gaussianIntegralTailStart (gaussianGrowingRadius radiusStage) +
      2 * prefixStage)
    (gaussianGrowingRadius radiusStage)

def gaussianGrowingIntegralOddPrefix
    (radiusStage prefixStage : Nat) : Rat :=
  gaussianEvenIntegralPrefix
    (gaussianIntegralTailStart (gaussianGrowingRadius radiusStage) +
      (2 * prefixStage + 1))
    (gaussianGrowingRadius radiusStage)

/-- The strict annulus obligation stated directly on the integrated-series
anchors, with no prefix-stabilization implementation detail. -/
def GaussianGrowingIntegratedSeriesStrictAnnulusBounds : Prop :=
  forall k n, k < n ->
    (RealCompute.ofRat 0).Le
        (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n) /\
      (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n).Le
        (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k))

/-- A purely finite rational certificate family for strict growing Gaussian
annuli.  For each strict pair it supplies two alternating-series stages whose
four prefix endpoints already lie inside the desired sign and tail bounds. -/
def GaussianGrowingIntegratedSeriesFinitePrefixBounds : Prop :=
  forall k n, k < n ->
    Exists fun outerStage : Nat => Exists fun innerStage : Nat =>
      0 <= gaussianGrowingIntegralEvenPrefix n outerStage -
          gaussianGrowingIntegralOddPrefix k innerStage /\
        gaussianGrowingIntegralOddPrefix n outerStage -
            gaussianGrowingIntegralEvenPrefix k innerStage <=
          symmetricReciprocalSquareTailRadius k

/-- The finite four-prefix obligation is discharged by the synchronized
reciprocal-chart construction. -/
theorem gaussianGrowingIntegratedSeriesFinitePrefixBounds_checked :
    GaussianGrowingIntegratedSeriesFinitePrefixBounds := by
  intro k n hkn
  let lower := gaussianGrowingAnnulusReciprocalLower k n
  let cutoff := gaussianGrowingRadius k
  have hlower : 0 < lower := by
    simpa [lower] using gaussianGrowingAnnulusReciprocalLower_pos k n
  have hlowerOne : lower < 1 := by
    simpa [lower] using gaussianGrowingAnnulusReciprocalLower_lt_one hkn
  have hfour :=
    reciprocalGaussianUniformSynchronized_exists_fourPrefix_bounds
      lower cutoff (gaussianGrowingRadius_pos k) hlower hlowerOne
  have hradiusEq : cutoff / lower = gaussianGrowingRadius n := by
    simpa [cutoff, lower] using
      gaussianGrowingRadius_div_reciprocalLower_eq k n
  rw [hradiusEq] at hfour
  simpa [cutoff, gaussianGrowingIntegralEvenPrefix,
    gaussianGrowingIntegralOddPrefix, symmetricReciprocalSquareTailRadius,
    gaussianGrowingRadius] using hfour

/-- Finite prefix certificates imply the representation-invariant strict
annulus theorem.  This turns the remaining analytic target into literal
rational inequalities between four explicitly computed Taylor prefixes. -/
theorem gaussianGrowingIntegratedSeriesStrictAnnulusBounds_of_finitePrefixBounds
    (hfinite : GaussianGrowingIntegratedSeriesFinitePrefixBounds) :
    GaussianGrowingIntegratedSeriesStrictAnnulusBounds := by
  intro k n hkn
  obtain ⟨outerStage, innerStage, hlower, hupper⟩ := hfinite k n hkn
  have hbracket :=
    gaussianGrowingRadiusIntegratedSeriesAnnulusRaw_between_shifted_prefixes
      k n outerStage innerStage
  let outerEven := gaussianGrowingIntegralEvenPrefix n outerStage
  let outerOdd := gaussianGrowingIntegralOddPrefix n outerStage
  let innerEven := gaussianGrowingIntegralEvenPrefix k innerStage
  let innerOdd := gaussianGrowingIntegralOddPrefix k innerStage
  let lowerRaw := RealCompute.sub (RealCompute.ofRat outerEven)
    (RealCompute.ofRat innerOdd)
  let upperRaw := RealCompute.sub (RealCompute.ofRat outerOdd)
    (RealCompute.ofRat innerEven)
  have hzeroLower : (RealCompute.ofRat 0).Le lowerRaw := by
    intro a b
    change (0 : Rat) <= outerEven - innerOdd
    simpa [outerEven, innerOdd] using hlower
  have hupperTail : upperRaw.Le
      (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k)) := by
    intro a b
    change outerOdd - innerEven <= symmetricReciprocalSquareTailRadius k
    simpa [outerOdd, innerEven] using hupper
  have hlowerAnnulus : lowerRaw.Le
      (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n) := by
    simpa [lowerRaw, outerEven, innerOdd,
      gaussianGrowingIntegralEvenPrefix,
      gaussianGrowingIntegralOddPrefix] using hbracket.1
  have hannulusUpper :
      (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n).Le upperRaw := by
    simpa [upperRaw, outerOdd, innerEven,
      gaussianGrowingIntegralEvenPrefix,
      gaussianGrowingIntegralOddPrefix] using hbracket.2
  have hlowerValid : lowerRaw.Valid := by
    dsimp [lowerRaw]
    exact RealCompute.sub_valid (RealCompute.ofRat_valid _) (RealCompute.ofRat_valid _)
  have hupperValid : upperRaw.Valid := by
    dsimp [upperRaw]
    exact RealCompute.sub_valid (RealCompute.ofRat_valid _) (RealCompute.ofRat_valid _)
  exact
    ⟨RealCompute.le_trans hlowerValid hzeroLower hlowerAnnulus,
      RealCompute.le_trans hupperValid hannulusUpper hupperTail⟩

theorem gaussianGrowingIntegratedSeriesStrictAnnulusBounds_checked :
    GaussianGrowingIntegratedSeriesStrictAnnulusBounds :=
  gaussianGrowingIntegratedSeriesStrictAnnulusBounds_of_finitePrefixBounds
    gaussianGrowingIntegratedSeriesFinitePrefixBounds_checked

/-- Prefix stabilization does not change the represented Gaussian annulus.
This is the exact transport from the executable bounded quadratures to their
integrated-series anchors. -/
theorem gaussianGrowingRadiusAnnulusRaw_equiv_integratedSeriesAnnulus
    (k n : Nat) :
    (gaussianGrowingRadiusAnnulusRaw k n).Equiv
      (gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n) := by
  unfold gaussianGrowingRadiusAnnulusRaw
    gaussianGrowingRadiusIntegratedSeriesAnnulusRaw
    gaussianGrowingRadiusBoundedQuadratureRaw
  exact RealCompute.sub_equiv
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)
    (gaussianRadiusIntegratedSeriesRaw_valid _ _)
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)
    (gaussianRadiusIntegratedSeriesRaw_valid _ _)
    (gaussianRadiusTaylorQuadratureRaw_equiv_series _ _)
    (gaussianRadiusTaylorQuadratureRaw_equiv_series _ _)

theorem gaussianGrowingRadius_outer_equiv_inner_add_annulus
    (k n : Nat) :
    (gaussianGrowingRadiusBoundedQuadratureRaw n).Equiv
      (RealCompute.add (gaussianGrowingRadiusBoundedQuadratureRaw k)
        (gaussianGrowingRadiusAnnulusRaw k n)) := by
  let inner := gaussianGrowingRadiusBoundedQuadratureRaw k
  let outer := gaussianGrowingRadiusBoundedQuadratureRaw n
  let annulus := gaussianGrowingRadiusAnnulusRaw k n
  have hinner : inner.Valid := by
    dsimp [inner, gaussianGrowingRadiusBoundedQuadratureRaw]
    exact gaussianRadiusTaylorQuadratureRaw_valid _ _
  have houter : outer.Valid := by
    dsimp [outer, gaussianGrowingRadiusBoundedQuadratureRaw]
    exact gaussianRadiusTaylorQuadratureRaw_valid _ _
  have hannulus : annulus.Valid := by
    simpa [annulus] using gaussianGrowingRadiusAnnulusRaw_valid k n
  have hcomm : (RealCompute.add inner annulus).Equiv
      (RealCompute.add annulus inner) :=
    RealCompute.add_comm_equiv inner annulus hinner hannulus
  have hcancel : (RealCompute.add annulus inner).Equiv outer := by
    dsimp [annulus, gaussianGrowingRadiusAnnulusRaw]
    exact RealCompute.sub_add_cancel_equiv houter hinner
  have hsumLeft : (RealCompute.add inner annulus).Valid :=
    RealCompute.add_valid hinner hannulus
  have hsumRight : (RealCompute.add annulus inner).Valid :=
    RealCompute.add_valid hannulus hinner
  exact RealCompute.equiv_symm
    (RealCompute.equiv_trans hsumLeft hsumRight houter hcomm hcancel)

/-- The irreducible analytic obligation after the additive algebra has been
discharged: the explicit annulus difference is nonnegative and no larger than
the reciprocal-square tail at the inner radius. -/
def GaussianGrowingQuadratureAnnulusBounds : Prop :=
  forall k n, k <= n ->
    (RealCompute.ofRat 0).Le (gaussianGrowingRadiusAnnulusRaw k n) /\
      (gaussianGrowingRadiusAnnulusRaw k n).Le
        (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k))

/-- The genuinely analytic part of the annulus bound excludes the already
solved zero-width diagonal case. -/
def GaussianGrowingQuadratureStrictAnnulusBounds : Prop :=
  forall k n, k < n ->
    (RealCompute.ofRat 0).Le (gaussianGrowingRadiusAnnulusRaw k n) /\
      (gaussianGrowingRadiusAnnulusRaw k n).Le
        (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k))

/-- The strict Gaussian annulus theorem is unchanged by replacing the
stabilized midpoint quadratures with their equivalent integrated-series
anchors.  This discharges the stabilization-transport part of the roadmap;
only the finite analytic sign and tail comparison remains. -/
theorem gaussianGrowingQuadratureStrictAnnulusBounds_iff_integratedSeries :
    GaussianGrowingQuadratureStrictAnnulusBounds ↔
      GaussianGrowingIntegratedSeriesStrictAnnulusBounds := by
  constructor
  · intro hquadrature k n hkn
    let quadrature := gaussianGrowingRadiusAnnulusRaw k n
    let series := gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n
    have hquadratureValid : quadrature.Valid := by
      simpa [quadrature] using gaussianGrowingRadiusAnnulusRaw_valid k n
    have hseriesValid : series.Valid := by
      simpa [series] using
        gaussianGrowingRadiusIntegratedSeriesAnnulusRaw_valid k n
    have hequiv : quadrature.Equiv series := by
      simpa [quadrature, series] using
        gaussianGrowingRadiusAnnulusRaw_equiv_integratedSeriesAnnulus k n
    have hbounds := hquadrature k n hkn
    have hquadratureLeSeries : quadrature.Le series :=
      RealCompute.le_of_equiv hquadratureValid hseriesValid hequiv
    have hseriesLeQuadrature : series.Le quadrature :=
      RealCompute.le_of_equiv hseriesValid hquadratureValid
        (RealCompute.equiv_symm hequiv)
    constructor
    · exact RealCompute.le_trans hquadratureValid hbounds.1 hquadratureLeSeries
    · exact RealCompute.le_trans hquadratureValid hseriesLeQuadrature hbounds.2
  · intro hseries k n hkn
    let quadrature := gaussianGrowingRadiusAnnulusRaw k n
    let series := gaussianGrowingRadiusIntegratedSeriesAnnulusRaw k n
    have hquadratureValid : quadrature.Valid := by
      simpa [quadrature] using gaussianGrowingRadiusAnnulusRaw_valid k n
    have hseriesValid : series.Valid := by
      simpa [series] using
        gaussianGrowingRadiusIntegratedSeriesAnnulusRaw_valid k n
    have hequiv : quadrature.Equiv series := by
      simpa [quadrature, series] using
        gaussianGrowingRadiusAnnulusRaw_equiv_integratedSeriesAnnulus k n
    have hbounds := hseries k n hkn
    have hquadratureLeSeries : quadrature.Le series :=
      RealCompute.le_of_equiv hquadratureValid hseriesValid hequiv
    have hseriesLeQuadrature : series.Le quadrature :=
      RealCompute.le_of_equiv hseriesValid hquadratureValid
        (RealCompute.equiv_symm hequiv)
    constructor
    · exact RealCompute.le_trans hseriesValid hbounds.1 hseriesLeQuadrature
    · exact RealCompute.le_trans hseriesValid hquadratureLeSeries hbounds.2

theorem gaussianGrowingQuadratureStrictAnnulusBounds_checked :
    GaussianGrowingQuadratureStrictAnnulusBounds :=
  gaussianGrowingQuadratureStrictAnnulusBounds_iff_integratedSeries.mpr
    gaussianGrowingIntegratedSeriesStrictAnnulusBounds_checked

/-- Concrete finite data for one annulus between two growing rational
radii.  The annulus has its own valid executable raw, is nonnegative, is at
most the reciprocal-square tail budget at the inner radius, and adds back to
the outer bounded Gaussian value. -/
structure GaussianGrowingQuadratureAnnularCertificate (k n : Nat) where
  annulus : RealCompute
  annulus_valid : annulus.Valid
  annulus_nonnegative : (RealCompute.ofRat 0).Le annulus
  annulus_upper : annulus.Le
    (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k))
  outer_equiv_inner_add_annulus :
    (gaussianGrowingRadiusBoundedQuadratureRaw n).Equiv
      (RealCompute.add (gaussianGrowingRadiusBoundedQuadratureRaw k) annulus)

namespace GaussianGrowingQuadratureAnnularCertificate

theorem annulusRaw_self_equiv_zero (k : Nat) :
    (gaussianGrowingRadiusAnnulusRaw k k).Equiv (RealCompute.ofRat 0) := by
  unfold gaussianGrowingRadiusAnnulusRaw
  exact RealCompute.sub_self_equiv_zero
    (gaussianRadiusTaylorQuadratureRaw_valid _ _)

/-- The zero-width annulus is a complete regression instance of the
certificate interface. -/
def self (k : Nat) :
    GaussianGrowingQuadratureAnnularCertificate k k := by
  let annulus := gaussianGrowingRadiusAnnulusRaw k k
  have hannulus : annulus.Valid := by
    simpa [annulus] using gaussianGrowingRadiusAnnulusRaw_valid k k
  have hzero : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0
  have hequiv : annulus.Equiv (RealCompute.ofRat 0) := by
    simpa [annulus] using annulusRaw_self_equiv_zero k
  have hzeroTail : (RealCompute.ofRat 0).Le
      (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k)) := by
    intro n m
    rw [RealCompute.ofRat_compute, RealCompute.ofRat_compute]
    exact symmetricReciprocalSquareTailRadius_nonneg k
  exact {
    annulus := annulus
    annulus_valid := hannulus
    annulus_nonnegative :=
      RealCompute.le_of_equiv hzero hannulus (RealCompute.equiv_symm hequiv)
    annulus_upper :=
      RealCompute.le_trans hzero
        (RealCompute.le_of_equiv hannulus hzero hequiv) hzeroTail
    outer_equiv_inner_add_annulus :=
      gaussianGrowingRadius_outer_equiv_inner_add_annulus k k
  }

theorem annulusBounds_of_strict
    (hstrict : GaussianGrowingQuadratureStrictAnnulusBounds) :
    GaussianGrowingQuadratureAnnulusBounds := by
  intro k n hkn
  rcases Nat.eq_or_lt_of_le hkn with hEq | hlt
  · subst n
    exact ⟨(self k).annulus_nonnegative, (self k).annulus_upper⟩
  · exact hstrict k n hlt

/-- A positive, tail-bounded annulus implies the representation-invariant
two-sided order needed by full-line gluing. -/
theorem toAnnularOrder {k n : Nat}
    (C : GaussianGrowingQuadratureAnnularCertificate k n) :
    (gaussianGrowingRadiusBoundedQuadratureRaw k).Le
        (gaussianGrowingRadiusBoundedQuadratureRaw n) /\
      (gaussianGrowingRadiusBoundedQuadratureRaw n).Le
        (RealCompute.add (gaussianGrowingRadiusBoundedQuadratureRaw k)
          (RealCompute.ofRat (symmetricReciprocalSquareTailRadius k))) := by
  let inner := gaussianGrowingRadiusBoundedQuadratureRaw k
  let outer := gaussianGrowingRadiusBoundedQuadratureRaw n
  let tail := RealCompute.ofRat (symmetricReciprocalSquareTailRadius k)
  have hinner : inner.Valid := by
    dsimp [inner, gaussianGrowingRadiusBoundedQuadratureRaw]
    exact gaussianRadiusTaylorQuadratureRaw_valid _ _
  have houter : outer.Valid := by
    dsimp [outer, gaussianGrowingRadiusBoundedQuadratureRaw]
    exact gaussianRadiusTaylorQuadratureRaw_valid _ _
  have hzero : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0
  have htail : tail.Valid := RealCompute.ofRat_valid _
  have hinnerAnnulus : (RealCompute.add inner C.annulus).Valid :=
    RealCompute.add_valid hinner C.annulus_valid
  have hinnerZero : (RealCompute.add inner (RealCompute.ofRat 0)).Valid :=
    RealCompute.add_valid hinner hzero
  have hinnerTail : (RealCompute.add inner tail).Valid :=
    RealCompute.add_valid hinner htail
  have hinner_le_innerZero : inner.Le
      (RealCompute.add inner (RealCompute.ofRat 0)) :=
    RealCompute.le_of_equiv hinner hinnerZero
      (RealCompute.equiv_symm (RealCompute.add_zero_equiv hinner))
  have hinnerZero_le_innerAnnulus :
      (RealCompute.add inner (RealCompute.ofRat 0)).Le
        (RealCompute.add inner C.annulus) :=
    RealCompute.le_add_le_add (RealCompute.le_refl inner hinner)
      C.annulus_nonnegative
  have hinner_le_innerAnnulus : inner.Le
      (RealCompute.add inner C.annulus) :=
    RealCompute.le_trans hinnerZero
      hinner_le_innerZero hinnerZero_le_innerAnnulus
  have hinnerAnnulus_le_outer :
      (RealCompute.add inner C.annulus).Le outer :=
    RealCompute.le_of_equiv hinnerAnnulus houter
      (RealCompute.equiv_symm C.outer_equiv_inner_add_annulus)
  have houter_le_innerAnnulus :
      outer.Le (RealCompute.add inner C.annulus) :=
    RealCompute.le_of_equiv houter hinnerAnnulus
      C.outer_equiv_inner_add_annulus
  have hinnerAnnulus_le_innerTail :
      (RealCompute.add inner C.annulus).Le (RealCompute.add inner tail) :=
    RealCompute.le_add_le_add (RealCompute.le_refl inner hinner) C.annulus_upper
  exact
    ⟨RealCompute.le_trans hinnerAnnulus
        hinner_le_innerAnnulus hinnerAnnulus_le_outer,
      RealCompute.le_trans hinnerAnnulus
        houter_le_innerAnnulus hinnerAnnulus_le_innerTail⟩

end GaussianGrowingQuadratureAnnularCertificate

theorem gaussianGrowingQuadratureAnnulusBounds_checked :
    GaussianGrowingQuadratureAnnulusBounds :=
  GaussianGrowingQuadratureAnnularCertificate.annulusBounds_of_strict
    gaussianGrowingQuadratureStrictAnnulusBounds_checked

/-- A certificate for every ordered pair of growing rational radii. -/
def GaussianGrowingQuadratureAnnularCertificateFamily : Prop :=
  forall k n, k <= n ->
    Nonempty (GaussianGrowingQuadratureAnnularCertificate k n)

theorem gaussianGrowingQuadratureAnnularOrder_of_certificateFamily
    (hfamily : GaussianGrowingQuadratureAnnularCertificateFamily) :
    GaussianGrowingQuadratureAnnularOrder := by
  intro k n hkn
  obtain ⟨C⟩ := hfamily k n hkn
  exact C.toAnnularOrder

theorem gaussianGrowingQuadratureAnnularCertificateFamily_of_bounds
    (hbounds : GaussianGrowingQuadratureAnnulusBounds) :
    GaussianGrowingQuadratureAnnularCertificateFamily := by
  intro k n hkn
  refine ⟨{
    annulus := gaussianGrowingRadiusAnnulusRaw k n
    annulus_valid := gaussianGrowingRadiusAnnulusRaw_valid k n
    annulus_nonnegative := (hbounds k n hkn).1
    annulus_upper := (hbounds k n hkn).2
    outer_equiv_inner_add_annulus :=
      gaussianGrowingRadius_outer_equiv_inner_add_annulus k n
  }⟩

theorem gaussianGrowingQuadratureAnnularCertificateFamily_checked :
    GaussianGrowingQuadratureAnnularCertificateFamily :=
  gaussianGrowingQuadratureAnnularCertificateFamily_of_bounds
    gaussianGrowingQuadratureAnnulusBounds_checked

theorem gaussianGrowingQuadratureAnnularOrder_of_bounds
    (hbounds : GaussianGrowingQuadratureAnnulusBounds) :
    GaussianGrowingQuadratureAnnularOrder :=
  gaussianGrowingQuadratureAnnularOrder_of_certificateFamily
    (gaussianGrowingQuadratureAnnularCertificateFamily_of_bounds hbounds)

theorem gaussianGrowingQuadratureAnnularOrder_checked :
    GaussianGrowingQuadratureAnnularOrder :=
  gaussianGrowingQuadratureAnnularOrder_of_bounds
    gaussianGrowingQuadratureAnnulusBounds_checked

/-- Numerical width must be added to the analytic tail budget when whole
rational boxes, rather than represented values, are glued. -/
def gaussianGrowingRadiusQuadratureGluingRadius (stage : Nat) : Rat :=
  6 / (((stage + 1 : Nat) : Rat))

theorem gaussianGrowingRadiusQuadratureGluingRadius_nonneg (stage : Nat) :
    0 <= gaussianGrowingRadiusQuadratureGluingRadius stage := by
  unfold gaussianGrowingRadiusQuadratureGluingRadius
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (Nat.succ_pos stage))))

theorem gaussianGrowingRadiusQuadratureGluingRadius_shrinks :
    ShrinksToZero gaussianGrowingRadiusQuadratureGluingRadius :=
  shrinksToZero_of_natOverSuccBound (C := 6) (by
    intro stage
    exact Rat.le_refl)

theorem gaussianGrowingRadiusQuadratureCandidate_width_le_earlier
    (k n : Nat) (hkn : k <= n) :
    (gaussianGrowingRadiusQuadratureCandidate.compute n).width <=
      4 / (((k + 1 : Nat) : Rat)) := by
  have hwidth := gaussianGrowingRadiusQuadratureCandidate_width_le_natRate n
  have hrecip := Series.one_div_nat_antitone_series
    (n := k + 1) (m := n + 1) (by omega) (by omega) (by omega)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
    (by decide +kernel : (0 : Rat) <= 4)
  exact Rat.le_trans hwidth (by
    simpa [Rat.div_def, Rat.mul_assoc] using hscaled)

/-- The represented annular inequality supplies the old literal
`future_contained` field once the later candidate's certified width is paid.
The resulting radius is `2/(k+1) + 4/(k+1) = 6/(k+1)`. -/
theorem gaussianGrowingRadiusQuadrature_future_contained_of_annularOrder
    (hannular : GaussianGrowingQuadratureAnnularOrder) :
    forall k n, k <= n ->
      (QInterval.expand (gaussianGrowingRadiusQuadratureCandidate.compute k)
        (gaussianGrowingRadiusQuadratureGluingRadius k)).ContainsInterval
          (gaussianGrowingRadiusQuadratureCandidate.compute n) := by
  intro k n hkn
  have horder := hannular k n hkn
  have hsmall := expand_contains_of_raw_le_add_target_width
    (gaussianGrowingRadiusBoundedQuadratureRaw k)
    (gaussianGrowingRadiusBoundedQuadratureRaw n)
    (gaussianGrowingRadiusInternalStage k)
    (gaussianGrowingRadiusInternalStage n)
    (symmetricReciprocalSquareTailRadius k)
    (symmetricReciprocalSquareTailRadius_nonneg k) horder.1 horder.2
  have hwidth :=
    gaussianGrowingRadiusQuadratureCandidate_width_le_earlier k n hkn
  have hradius :
      symmetricReciprocalSquareTailRadius k +
          (gaussianGrowingRadiusQuadratureCandidate.compute n).width <=
        gaussianGrowingRadiusQuadratureGluingRadius k := by
    unfold symmetricReciprocalSquareTailRadius
      gaussianGrowingRadiusQuadratureGluingRadius
    grind [Rat.div_def, Rat.mul_assoc, Rat.add_mul]
  change
    (QInterval.expand (gaussianGrowingRadiusQuadratureCandidate.compute k)
      (symmetricReciprocalSquareTailRadius k +
        (gaussianGrowingRadiusQuadratureCandidate.compute n).width))
      |>.ContainsInterval
        (gaussianGrowingRadiusQuadratureCandidate.compute n) at hsmall
  unfold QInterval.ContainsInterval QInterval.expand at hsmall ⊢
  constructor <;> grind

/-- Direct growing-radius full-line candidate using the corrected sum of the
analytic tail and numerical enclosure budgets. -/
def gaussianGrowingRadiusQuadratureFullLineRaw : RealCompute :=
  RealCompute.prefixStabilize gaussianGrowingRadiusQuadratureCandidate
    gaussianGrowingRadiusQuadratureGluingRadius

theorem gaussianGrowingRadiusQuadratureFullLineRaw_valid
    (hannular : GaussianGrowingQuadratureAnnularOrder) :
    gaussianGrowingRadiusQuadratureFullLineRaw.Valid := by
  unfold gaussianGrowingRadiusQuadratureFullLineRaw
  exact RealCompute.prefixStabilize_valid_of_future_containment
    gaussianGrowingRadiusQuadratureCandidate_endpoints_ordered
    gaussianGrowingRadiusQuadratureCandidate_widths_shrink
    (gaussianGrowingRadiusQuadrature_future_contained_of_annularOrder hannular)
    gaussianGrowingRadiusQuadratureGluingRadius_shrinks

theorem gaussianGrowingRadiusQuadratureFullLineRaw_valid_of_annularCertificateFamily
    (hfamily : GaussianGrowingQuadratureAnnularCertificateFamily) :
    gaussianGrowingRadiusQuadratureFullLineRaw.Valid :=
  gaussianGrowingRadiusQuadratureFullLineRaw_valid
    (gaussianGrowingQuadratureAnnularOrder_of_certificateFamily hfamily)

theorem gaussianGrowingRadiusQuadratureFullLineRaw_valid_of_annulusBounds
    (hbounds : GaussianGrowingQuadratureAnnulusBounds) :
    gaussianGrowingRadiusQuadratureFullLineRaw.Valid :=
  gaussianGrowingRadiusQuadratureFullLineRaw_valid
    (gaussianGrowingQuadratureAnnularOrder_of_bounds hbounds)

/-- End-to-end stabilization transport: it is enough to prove the strict
sign and reciprocal-tail bounds for the integrated-series annuli.  The
equivalence theorem above transfers them to the executable quadrature raws,
the diagonal case is filled explicitly, and the existing gluing theorem then
validates the growing full-line evaluator. -/
theorem gaussianGrowingRadiusQuadratureFullLineRaw_valid_of_integratedSeriesStrictAnnulusBounds
    (hbounds : GaussianGrowingIntegratedSeriesStrictAnnulusBounds) :
    gaussianGrowingRadiusQuadratureFullLineRaw.Valid := by
  apply gaussianGrowingRadiusQuadratureFullLineRaw_valid_of_annulusBounds
  apply GaussianGrowingQuadratureAnnularCertificate.annulusBounds_of_strict
  exact
    gaussianGrowingQuadratureStrictAnnulusBounds_iff_integratedSeries.mpr
      hbounds

/-- The growing-radius full-line Gaussian quadrature is now unconditionally
valid: all annular sign, tail, representation, diagonal, and stabilization
obligations have explicit finite rational certificates. -/
theorem gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked :
    gaussianGrowingRadiusQuadratureFullLineRaw.Valid :=
  gaussianGrowingRadiusQuadratureFullLineRaw_valid_of_integratedSeriesStrictAnnulusBounds
    gaussianGrowingIntegratedSeriesStrictAnnulusBounds_checked

/-! ## Constructive full-line Gaussian normalization

The radius-one alternating enclosure already gives the exact positive lower
prefix `31049 / 20790`.  Annular monotonicity carries this lower certificate
through all growing radii, and finite-prefix stabilization keeps every
current candidate inside the full-line box.  This supplies the uniform
positive rational bound needed by `RealCompute.positiveReciprocal`, without
identifying the full-line mass with `sqrt pi` or invoking an improper
integral. -/

/-- The explicit rational lower certificate used to normalize the full-line
Gaussian raw. -/
def gaussianFullLineMassLower : Rat := 31049 / 20790

theorem gaussianFullLineMassLower_pos : 0 < gaussianFullLineMassLower := by
  unfold gaussianFullLineMassLower
  decide +kernel

theorem gaussianIntegralTailStart_one : gaussianIntegralTailStart 1 = 6 := by
  decide +kernel

/-- The radius-one bounded Gaussian mass lies above the first certified even
alternating prefix. -/
theorem gaussianFullLineMassLower_le_radiusOne :
    (RealCompute.ofRat gaussianFullLineMassLower).Le
      (gaussianGrowingRadiusBoundedQuadratureRaw 0) := by
  have hlower :=
    (gaussianRadiusIntegratedSeriesRaw_between_shifted_even_odd_prefixes
      1 (by decide +kernel) 0).1
  have hseriesValid :=
    gaussianRadiusIntegratedSeriesRaw_valid 1 (by decide +kernel)
  have hquadratureValid :=
    gaussianRadiusTaylorQuadratureRaw_valid 1 (by decide +kernel)
  have hseriesLeQuadrature :
      (gaussianRadiusIntegratedSeriesRaw 1 (by decide +kernel)).Le
        (gaussianRadiusTaylorQuadratureRaw 1 (by decide +kernel)) :=
    RealCompute.le_of_equiv hseriesValid hquadratureValid
      (RealCompute.equiv_symm
        (gaussianRadiusTaylorQuadratureRaw_equiv_series 1
          (by decide +kernel)))
  have h := RealCompute.le_trans hseriesValid hlower hseriesLeQuadrature
  simpa [gaussianFullLineMassLower, gaussianGrowingRadiusBoundedQuadratureRaw,
    gaussianGrowingRadius, gaussianIntegralTailStart_one,
    gaussianEvenIntegralPrefix_stage_six] using h

/-- Every stabilized full-line stage contains its direct growing-radius
quadrature candidate. -/
theorem gaussianGrowingRadiusQuadratureFullLineRaw_contains_current
    (stage : Nat) :
    (gaussianGrowingRadiusQuadratureFullLineRaw.compute stage).ContainsInterval
      (gaussianGrowingRadiusQuadratureCandidate.compute stage) := by
  unfold gaussianGrowingRadiusQuadratureFullLineRaw
  exact RealCompute.prefixStabilize_contains_current_of_future
    (gaussianGrowingRadiusQuadrature_future_contained_of_annularOrder
      gaussianGrowingQuadratureAnnularOrder_checked) stage

/-- The full-line Gaussian computation has the same explicit positive lower
bound at the upper endpoint of every rational enclosure. -/
theorem gaussianFullLineMassLower_le_fullLine_hi (stage : Nat) :
    gaussianFullLineMassLower <=
      (gaussianGrowingRadiusQuadratureFullLineRaw.compute stage).hi := by
  have hmonotone :=
    (gaussianGrowingQuadratureAnnularOrder_checked 0 stage
      (Nat.zero_le stage)).1
  have hradiusOneValid :=
    gaussianRadiusTaylorQuadratureRaw_valid
      (gaussianGrowingRadius 0) (gaussianGrowingRadius_nonneg 0)
  have hlowerGrowing :
      (RealCompute.ofRat gaussianFullLineMassLower).Le
        (gaussianGrowingRadiusBoundedQuadratureRaw stage) :=
    RealCompute.le_trans hradiusOneValid
      gaussianFullLineMassLower_le_radiusOne hmonotone
  have hlowerCandidate := hlowerGrowing 0
    (gaussianGrowingRadiusInternalStage stage)
  have hcontains :=
    gaussianGrowingRadiusQuadratureFullLineRaw_contains_current stage
  change gaussianFullLineMassLower <=
    (gaussianGrowingRadiusQuadratureCandidate.compute stage).hi at hlowerCandidate
  exact Rat.le_trans hlowerCandidate hcontains.2

/-- The computable reciprocal of the full-line Gaussian mass.  This is the
normalization factor needed for Gaussian kernels; its construction depends
only on rational interval arithmetic and the explicit lower certificate. -/
def gaussianFullLineMassReciprocalRaw : RealCompute :=
  RealCompute.positiveReciprocal gaussianGrowingRadiusQuadratureFullLineRaw
    gaussianFullLineMassLower

theorem gaussianFullLineMassReciprocalRaw_valid :
    gaussianFullLineMassReciprocalRaw.Valid := by
  unfold gaussianFullLineMassReciprocalRaw
  exact RealCompute.positiveReciprocal_valid
    gaussianGrowingRadiusQuadratureFullLineRaw gaussianFullLineMassLower
    gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked
    gaussianFullLineMassLower_pos
    gaussianFullLineMassLower_le_fullLine_hi

theorem gaussianFullLineMassReciprocalRaw_nonneg_bounded (stage : Nat) :
    0 <= (gaussianFullLineMassReciprocalRaw.compute stage).lo /\
      (gaussianFullLineMassReciprocalRaw.compute stage).hi <=
        1 / gaussianFullLineMassLower := by
  have hmassHi :
      0 < (gaussianGrowingRadiusQuadratureFullLineRaw.compute stage).hi := by
    have hlower := gaussianFullLineMassLower_le_fullLine_hi stage
    have hlowerPos := gaussianFullLineMassLower_pos
    grind
  constructor
  · unfold gaussianFullLineMassReciprocalRaw
    rw [RealCompute.positiveReciprocal_compute
      gaussianGrowingRadiusQuadratureFullLineRaw gaussianFullLineMassLower
      gaussianFullLineMassLower_pos stage]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 hmassHi))
  · unfold gaussianFullLineMassReciprocalRaw
    exact RealCompute.positiveReciprocal_compute_hi_le
      gaussianGrowingRadiusQuadratureFullLineRaw gaussianFullLineMassLower
      gaussianFullLineMassLower_pos stage

theorem reciprocalGaussianRaw_nonneg_bounded_by_one
    (x : Rat) (stage : Nat) :
    0 <= ((reciprocalGaussianRaw x).compute stage).lo /\
      ((reciprocalGaussianRaw x).compute stage).hi <= 1 := by
  have hsquare : 0 <= x * x := rat_square_nonneg_basic x
  constructor
  · exact reciprocalNegativeExpRaw_compute_lo_nonneg (x * x) hsquare stage
  · have hmain :=
      reciprocalNegativeExpRaw_compute_hi_le_one_div_one_add
        (x * x) hsquare stage
    have hrecip : 1 / (1 + x * x) <= (1 : Rat) := by
      have hone : (0 : Rat) < 1 := by decide +kernel
      have hdenom : 1 <= 1 + x * x := by grind
      have h := RealCompute.one_div_antitone_of_pos hone hdenom
      calc
        1 / (1 + x * x) <= 1 / (1 : Rat) := h
        _ = 1 := by decide +kernel
    exact Rat.le_trans hmain hrecip

/-- The normalized full-line Gaussian profile at a rational spatial point.
Its normalization is the reciprocal of the computed full-line mass, rather
than a prior identification of that mass with `sqrt pi`. -/
def gaussianNormalizedProfileRaw (x : Rat) : RealCompute :=
  RealCompute.mul gaussianFullLineMassReciprocalRaw (reciprocalGaussianRaw x)

theorem gaussianNormalizedProfileRaw_valid (x : Rat) :
    (gaussianNormalizedProfileRaw x).Valid := by
  unfold gaussianNormalizedProfileRaw
  apply RealCompute.mul_valid_of_nonneg_bounded
    gaussianFullLineMassReciprocalRaw_valid
    (reciprocalGaussianRaw_valid x)
    (show 0 < 1 / gaussianFullLineMassLower by
      rw [Rat.div_def]
      exact Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 gaussianFullLineMassLower_pos))
    (by decide +kernel : (0 : Rat) < 1)
    gaussianFullLineMassReciprocalRaw_nonneg_bounded
    (reciprocalGaussianRaw_nonneg_bounded_by_one x)

/-- The normalized Gaussian profile is even, directly at the executable raw
level. -/
theorem gaussianNormalizedProfileRaw_neg (x : Rat) :
    gaussianNormalizedProfileRaw (-x) = gaussianNormalizedProfileRaw x := by
  unfold gaussianNormalizedProfileRaw reciprocalGaussianRaw
  congr 1
  grind

/-- The direct full-line runtime has an explicit rational rate.  This theorem
records the finite width arithmetic independently of the semantic validity
proof above. -/
theorem gaussianGrowingRadiusQuadratureFullLineRaw_width_le_natRate
    (stage : Nat) :
    (gaussianGrowingRadiusQuadratureFullLineRaw.compute stage).width <=
      16 / (((stage + 1 : Nat) : Rat)) := by
  have hcontain := RealCompute.prefixStabilize_contained_in_current_expand
    gaussianGrowingRadiusQuadratureCandidate
    gaussianGrowingRadiusQuadratureGluingRadius stage
  have hwidth := QInterval.width_le_of_contains hcontain
  rw [QInterval.expand_width] at hwidth
  have hcandidate :=
    gaussianGrowingRadiusQuadratureCandidate_width_le_natRate stage
  have hsum := rat_add_le_add hcandidate
    (Rat.mul_le_mul_of_nonneg_left
      (Rat.le_refl : gaussianGrowingRadiusQuadratureGluingRadius stage <=
        gaussianGrowingRadiusQuadratureGluingRadius stage)
      (by decide +kernel : (0 : Rat) <= 2))
  exact Rat.le_trans hwidth (by
    unfold gaussianGrowingRadiusQuadratureGluingRadius at hsum ⊢
    grind [Rat.div_def, Rat.mul_assoc, Rat.add_mul])

/-- Explicit rational width rate for the Gaussian normalization factor. -/
theorem gaussianFullLineMassReciprocalRaw_width_le_natRate (stage : Nat) :
    (gaussianFullLineMassReciprocalRaw.compute stage).width <=
      (16 / (gaussianFullLineMassLower * gaussianFullLineMassLower)) /
        (((stage + 1 : Nat) : Rat)) := by
  have hrecip := RealCompute.positiveReciprocal_compute_width_le
    gaussianGrowingRadiusQuadratureFullLineRaw gaussianFullLineMassLower
    gaussianGrowingRadiusQuadratureFullLineRaw_valid_checked
    gaussianFullLineMassLower_pos
    gaussianFullLineMassLower_le_fullLine_hi stage
  have hinput :=
    gaussianGrowingRadiusQuadratureFullLineRaw_width_le_natRate stage
  have hdenInv0 : 0 <=
      (gaussianFullLineMassLower * gaussianFullLineMassLower)⁻¹ := by
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (Rat.mul_pos gaussianFullLineMassLower_pos
        gaussianFullLineMassLower_pos))
  calc
    (gaussianFullLineMassReciprocalRaw.compute stage).width <=
        (gaussianGrowingRadiusQuadratureFullLineRaw.compute stage).width /
          (gaussianFullLineMassLower * gaussianFullLineMassLower) := hrecip
    _ <= (16 / (((stage + 1 : Nat) : Rat))) /
          (gaussianFullLineMassLower * gaussianFullLineMassLower) := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right hinput hdenInv0
    _ = (16 / (gaussianFullLineMassLower * gaussianFullLineMassLower)) /
          (((stage + 1 : Nat) : Rat)) := by
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

end ComputableAnalysis

namespace ComputableAnalysis

def gaussianPiSquareRootInput :
    RepresentedPositiveSquareRoot.PositiveInput 4 1 where
  raw := piCircleArea
  valid := CauchyPi.piCircleArea_valid
  margin_pos := by decide +kernel
  center_le_bound := by
    intro n
    have hvalid := CauchyPi.piCircleArea_valid
    have hnest := hvalid.2.1 0 n (Nat.zero_le n)
    have horder := RealCompute.interval_order_of_valid piCircleArea hvalid n
    have hmid := QInterval.midpoint_mem horder
    rw [piCircleArea_compute_zero] at hnest
    exact Rat.le_trans hmid.2 hnest.2.2
  margin_sq_le_center := by
    intro n
    have hvalid := CauchyPi.piCircleArea_valid
    have hnest := hvalid.2.1 0 n (Nat.zero_le n)
    have horder := RealCompute.interval_order_of_valid piCircleArea hvalid n
    have hmid := QInterval.midpoint_mem horder
    rw [piCircleArea_compute_zero] at hnest
    have htwo : (2 : Rat) <= (piCircleArea.compute n).lo := by
      simpa using hnest.1
    have hone : (1 : Rat) <= 2 := by decide +kernel
    have hmidLower := Rat.le_trans htwo hmid.1
    have hsq : sq (1 : Rat) = 1 := by decide +kernel
    rw [hsq]
    exact Rat.le_trans hone hmidLower

def gaussianPiSquareRootRaw : RealCompute :=
  RepresentedPositiveSquareRoot.PositiveInput.sqrt gaussianPiSquareRootInput

theorem gaussianPiSquareRootRaw_valid :
    gaussianPiSquareRootRaw.Valid :=
  RepresentedPositiveSquareRoot.PositiveInput.sqrt_valid
    gaussianPiSquareRootInput

end ComputableAnalysis


