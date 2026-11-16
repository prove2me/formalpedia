-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianApproximateIdentity
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteGaussianApproximateIdentity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:24:39.768202+00:00
-- url     : https://prove2.me/theorems/28e91af3-edc5-46d9-bf26-c11caa526bb1
-- title:
--   Computable analysis · FiniteGaussianApproximateIdentity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteGaussianApproximateIdentity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteApproximateIdentity
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianIntegral
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteQuadratureComparison
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteFTCIntervalRegular

set_option autoImplicit true

/-!
# A finite Gaussian-shaped approximate identity

This module exercises exact finite-kernel normalization on a concrete
three-node stencil.  The two outer weights are the certified rational upper
box for `exp(-1)` and the central weight is the corresponding upper box for
`exp(0)`.  The nodes shrink as `-1/(n+1), 0, 1/(n+1)`.

This is a genuine executable Gaussian-shaped finite family, but not yet a
quadrature theorem for the continuous Gaussian heat kernel.  That later
comparison still needs shrinking exponential-kernel cell enclosures and an
omitted-tail certificate.
-/

namespace ComputableAnalysis

/-! ## A bounded-cell comparison checkpoint -/

/-- The first nonconstant even Taylor prefix of `exp (-x^2)`. -/
def gaussianQuadraticProfile (x : Rat) : Rat := 1 - x * x

theorem gaussianQuadraticProfile_lipschitzOnIntervalNat :
    Integral.LipschitzOnIntervalNat gaussianQuadraticProfile (-1) 1 2 := by
  refine ⟨by decide +kernel, ?_⟩
  intro s t hsLower hsUpper htLower htUpper
  have hsAbs : qabs s <= 1 :=
    qabs_le_of_neg_le_le hsLower hsUpper
  have htAbs : qabs t <= 1 :=
    qabs_le_of_neg_le_le htLower htUpper
  have hsum : qabs (s + t) <= 2 := by
    exact Rat.le_trans (qabs_add_le s t) (by grind)
  have hfactor : gaussianQuadraticProfile s - gaussianQuadraticProfile t =
      (t - s) * (s + t) := by
    unfold gaussianQuadraticProfile
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hfactor, qabs_mul]
  have hscaled := Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg (t - s))
  calc
    qabs (t - s) * qabs (s + t) <= qabs (t - s) * 2 := hscaled
    _ = (2 : Rat) * qabs (t - s) := by rw [Rat.mul_comm]

/-- The scalable bounded-cell rule for the first Gaussian Taylor profile.
Stage `n` uses `n+1` genuine uniform midpoint cells on `[-1,1]`. -/
def gaussianQuadraticUniformMidpointRule (stage : Nat) :=
  SampledDarbouxPartition.uniformMidpoint gaussianQuadraticProfile (-1) 1 2
    (stage + 1) (Nat.succ_pos stage)
    gaussianQuadraticProfile_lipschitzOnIntervalNat

theorem gaussianQuadraticUniformMidpointRule_range_width
    (stage k : Nat) (hk : k < stage + 1) :
    ((gaussianQuadraticUniformMidpointRule stage).range k hk).width =
      4 * mesh (-1) 1 (stage + 1) := by
  rw [gaussianQuadraticUniformMidpointRule,
    SampledDarbouxPartition.uniformMidpoint_range_width]
  grind

/-- Explicit first-order shrinking of the assembled finite Darboux box. -/
theorem gaussianQuadraticUniformMidpointRule_darbouxSum_width_le
    (stage : Nat) :
    (gaussianQuadraticUniformMidpointRule stage).darbouxSum.width <=
      16 / ((stage + 1 : Nat) : Rat) := by
  have h := SampledDarbouxPartition.uniformMidpoint_darbouxSum_width_le
    gaussianQuadraticProfile (-1) 1 2 (stage + 1)
    (Nat.succ_pos stage) gaussianQuadraticProfile_lipschitzOnIntervalNat
  rw [gaussianQuadraticUniformMidpointRule]
  exact Rat.le_trans h (by
    unfold mesh
    rw [if_neg (Nat.succ_ne_zero stage)]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm])

/-! ## A nested bounded integral candidate on the unit chart -/

/-- The affine pullback of `1-x^2` from `[-1,1]` to `[0,1]`, including the
Jacobian factor `2`. -/
def gaussianQuadraticUnitProfile (t : Rat) : Rat :=
  8 * t - 8 * t ^ 2

theorem gaussianQuadraticUnitProfile_eq_pullback (t : Rat) :
    gaussianQuadraticUnitProfile t =
      2 * gaussianQuadraticProfile (2 * t - 1) := by
  unfold gaussianQuadraticUnitProfile gaussianQuadraticProfile
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem gaussianQuadraticUnitProfile_lipschitzOnUnit :
    Integral.LipschitzOnUnit gaussianQuadraticUnitProfile 8 := by
  constructor
  · decide +kernel
  · intro s t hsLower hsUpper htLower htUpper
    have hsMappedLower : (-1 : Rat) <= 2 * s - 1 := by grind
    have hsMappedUpper : 2 * s - 1 <= (1 : Rat) := by
      have hscaled : (2 : Rat) * s <= 2 * 1 :=
        Rat.mul_le_mul_of_nonneg_left hsUpper (by decide +kernel)
      grind
    have htMappedLower : (-1 : Rat) <= 2 * t - 1 := by grind
    have htMappedUpper : 2 * t - 1 <= (1 : Rat) := by
      have hscaled : (2 : Rat) * t <= 2 * 1 :=
        Rat.mul_le_mul_of_nonneg_left htUpper (by decide +kernel)
      grind
    have hbase := gaussianQuadraticProfile_lipschitzOnIntervalNat.2
      (2 * s - 1) (2 * t - 1)
      hsMappedLower hsMappedUpper htMappedLower htMappedUpper
    rw [gaussianQuadraticUnitProfile_eq_pullback,
      gaussianQuadraticUnitProfile_eq_pullback]
    rw [show 2 * gaussianQuadraticProfile (2 * s - 1) -
        2 * gaussianQuadraticProfile (2 * t - 1) =
      2 * (gaussianQuadraticProfile (2 * s - 1) -
        gaussianQuadraticProfile (2 * t - 1)) by
          grind [Rat.mul_add, Rat.sub_eq_add_neg],
      qabs_mul, qabs_eq_self_of_nonneg (by decide +kernel : (0 : Rat) <= 2)]
    have hargument :
        qabs ((2 * t - 1) - (2 * s - 1)) = 2 * qabs (t - s) := by
      rw [show (2 * t - 1) - (2 * s - 1) = 2 * (t - s) by
        grind [Rat.mul_add, Rat.sub_eq_add_neg], qabs_mul,
        qabs_eq_self_of_nonneg (by decide +kernel : (0 : Rat) <= 2)]
    rw [hargument] at hbase
    have hscaled := Rat.mul_le_mul_of_nonneg_left hbase (by decide +kernel : (0 : Rat) <= 2)
    grind [Rat.mul_assoc, Rat.mul_comm]

/-- The existing nested Lipschitz--Darboux implementation applied to the
bounded Gaussian quadratic pullback. -/
def gaussianQuadraticUnitIntegralRaw : RealCompute :=
  IntegralIdentities.LipschitzDyadic.raw gaussianQuadraticUnitProfile 8

theorem gaussianQuadraticUnitIntegralRaw_valid :
    gaussianQuadraticUnitIntegralRaw.Valid :=
  IntegralIdentities.LipschitzDyadic.raw_valid
    gaussianQuadraticUnitProfile_lipschitzOnUnit

theorem gaussianQuadraticUnitIntegralRaw_width
    (stage : Nat) :
    (gaussianQuadraticUnitIntegralRaw.compute stage).width =
      16 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  change (IntegralIdentities.LipschitzDyadic.compute
    gaussianQuadraticUnitProfile 8 stage).width = _
  rw [IntegralIdentities.LipschitzDyadic.compute_width]
  grind

/-! ## Common-stage exponential Gaussian cells -/

/-- The actual bounded Gaussian evaluator, retaining the certified
common-prefix exponential boxes at the rational input `-x^2`. -/
def gaussianExponentialRaw (x : Rat) : RealCompute :=
  ExpProofs.uniformExpRaw (-(x * x))

theorem gaussianExponentialRaw_valid {x : Rat}
    (hx : (-1 : Rat) <= x /\ x <= 1) :
    (gaussianExponentialRaw x).Valid := by
  apply ExpProofs.uniformExpRaw_valid
  rw [qabs_neg, qabs_mul]
  have hxabs : qabs x <= 1 := qabs_le_of_neg_le_le hx.1 hx.2
  have hsquare := rat_mul_le_mul_of_nonneg
    (qabs_nonneg x) hxabs (qabs_nonneg x) hxabs
  exact Rat.le_trans hsquare (by decide +kernel)

/-- The exact image endpoints of `x |-> -x^2` on a nonnegative rational
cell, passed to the symmetric exponential range evaluator. -/
def gaussianExponentialCellRange {a b : Rat}
    (C : RationalSubinterval a b) (stage : Nat) : QInterval :=
  ExpProofs.uniformExpSymmetricCellRange
    (-(C.upper * C.upper)) (-(C.lower * C.lower)) stage

def gaussianCellMidpoint {a b : Rat} (C : RationalSubinterval a b) : Rat :=
  (SampledDarbouxCell.cellInterval C).midpoint

def gaussianExponentialSampleValue {a b : Rat}
    (C : RationalSubinterval a b) (stage : Nat) : Rat :=
  ExpProofs.uniformExpCenter
    (-(gaussianCellMidpoint C * gaussianCellMidpoint C)) stage

/-! ## Exact finite primitives for the Gaussian factorial center

The coefficient stream below inserts the factorial coefficients, with
alternating sign, in the even degrees and zeroes in the odd degrees.  Its
finite rational primitive is therefore a literal antiderivative of the
finite evaluator center for `exp (-x^2)`. -/

def gaussianEvenTaylorCoeff (n : Nat) : Rat :=
  if n % 2 = 0 then
    FormalPowerSeries.expCoeff (n / 2) * (-1 : Rat) ^ (n / 2)
  else 0

theorem gaussianEvenTaylorCoeff_even (k : Nat) :
    gaussianEvenTaylorCoeff (2 * k) =
      FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k := by
  simp [gaussianEvenTaylorCoeff]

theorem gaussianEvenTaylorCoeff_odd (k : Nat) :
    gaussianEvenTaylorCoeff (2 * k + 1) = 0 := by
  simp [gaussianEvenTaylorCoeff]

def gaussianEvenPrimitivePrefix (terms : Nat) (x : Rat) : Rat :=
  FinitePolynomial.integratedTaylorPrefix gaussianEvenTaylorCoeff
    (2 * terms) x

def gaussianEvenProfilePrefix (terms : Nat) (x : Rat) : Rat :=
  FinitePolynomial.taylorDerivativePrefix gaussianEvenTaylorCoeff
    (2 * terms) x

/-- The literal formal derivative of the finite even Gaussian profile.
Writing it recursively keeps the zero-term case total: the factor `2*k`
kills the harmless truncated exponent when `k = 0`. -/
def gaussianEvenProfileFormalDerivativePrefix : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 => fun x =>
      gaussianEvenProfileFormalDerivativePrefix terms x +
        ((2 * terms : Nat) : Rat) *
          (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
            x ^ (2 * terms - 1)

theorem gaussianEvenProfilePrefix_succ (terms : Nat) (x : Rat) :
    gaussianEvenProfilePrefix (terms + 1) x =
      gaussianEvenProfilePrefix terms x +
        (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
          x ^ (2 * terms) := by
  unfold gaussianEvenProfilePrefix
  rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega]
  simp only [FinitePolynomial.taylorDerivativePrefix]
  rw [gaussianEvenTaylorCoeff_odd, Rat.zero_mul, Rat.add_zero,
    gaussianEvenTaylorCoeff_even]

theorem gaussianEvenProfileFormalDerivativePrefix_succ
    (terms : Nat) (x : Rat) :
    gaussianEvenProfileFormalDerivativePrefix (terms + 1) x =
      gaussianEvenProfileFormalDerivativePrefix terms x +
        ((2 * terms : Nat) : Rat) *
          (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
            x ^ (2 * terms - 1) := by
  rfl

theorem gaussianEvenProfilePrefix_eq_taylorPrefix
    (terms : Nat) (x : Rat) :
    gaussianEvenProfilePrefix terms x =
      FinitePolynomial.taylorPrefix gaussianEvenTaylorCoeff (2 * terms) x := by
  unfold gaussianEvenProfilePrefix
  exact (FinitePolynomial.taylorPrefix_eq_taylorDerivativePrefix
    gaussianEvenTaylorCoeff (2 * terms) x).symm

/-- The recursive Gaussian derivative prefix is exactly the generic finite
Taylor coefficient-shift polynomial. -/
theorem gaussianEvenProfileFormalDerivativePrefix_eq_taylorPrefixShift :
    forall terms x,
      gaussianEvenProfileFormalDerivativePrefix terms x =
        FinitePolynomial.taylorPrefixShift gaussianEvenTaylorCoeff
          (2 * terms) x
  | 0, _x => rfl
  | terms + 1, x => by
      rw [gaussianEvenProfileFormalDerivativePrefix_succ,
        gaussianEvenProfileFormalDerivativePrefix_eq_taylorPrefixShift terms x]
      cases terms with
      | zero =>
          simp [FinitePolynomial.taylorPrefixShift,
            FinitePolynomial.taylorDerivativePrefix,
            FormalPowerSeries.coefficientShift,
            gaussianEvenTaylorCoeff]
      | succ terms =>
          unfold FinitePolynomial.taylorPrefixShift
          rw [show 2 * (terms + 1 + 1) =
              ((2 * (terms + 1) + 1) + 1) by omega]
          simp only [FinitePolynomial.taylorDerivativePrefix]
          rw [show 2 * (terms + 1) =
              ((2 * terms + 1) + 1) by omega]
          simp only [FinitePolynomial.taylorDerivativePrefix]
          unfold FormalPowerSeries.coefficientShift
          rw [gaussianEvenTaylorCoeff_odd]
          rw [show 2 * terms + 1 + 1 = 2 * (terms + 1) by omega,
            gaussianEvenTaylorCoeff_even]
          rw [gaussianEvenTaylorCoeff_odd]
          push_cast
          grind [Rat.mul_assoc, Rat.mul_comm]

/-- Every finite Gaussian profile carries the repository's quantitative
two-sided interval derivative certificate, with the explicit recursive
Gaussian derivative prefix as derivative. -/
def gaussianEvenProfilePrefix_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (gaussianEvenProfilePrefix terms) a b)
      (FunctionOnInterval.exactRat
        (gaussianEvenProfileFormalDerivativePrefix terms) a b) := by
  have hgeneric := FinitePolynomial.taylorPrefix_hasDerivativeOnInterval
    gaussianEvenTaylorCoeff (2 * terms) a b C hleft hright hC1
  rw [show gaussianEvenProfilePrefix terms =
      FinitePolynomial.taylorPrefix gaussianEvenTaylorCoeff (2 * terms) by
    funext x
    exact gaussianEvenProfilePrefix_eq_taylorPrefix terms x]
  rw [show gaussianEvenProfileFormalDerivativePrefix terms =
      FinitePolynomial.taylorPrefixShift gaussianEvenTaylorCoeff
        (2 * terms) by
    funext x
    exact gaussianEvenProfileFormalDerivativePrefix_eq_taylorPrefixShift
      terms x]
  exact hgeneric

/-- Exact finite Gaussian ODE residual.  Every internal Taylor coefficient
cancels; the sole defect is the next odd boundary monomial.  This is the
finite algebraic precursor of `g' + 2*x*g = 0` for `g(x) = exp(-x^2)`. -/
theorem gaussianEvenProfilePrefix_ode_residual
    (terms : Nat) (x : Rat) :
    gaussianEvenProfileFormalDerivativePrefix (terms + 1) x +
        2 * x * gaussianEvenProfilePrefix (terms + 1) x =
      2 * (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
        x ^ (2 * terms + 1) := by
  induction terms with
  | zero =>
      have hinvOne : ((1 : Rat)⁻¹) = 1 := by decide +kernel
      simp [gaussianEvenProfileFormalDerivativePrefix,
        gaussianEvenProfilePrefix, FinitePolynomial.taylorDerivativePrefix,
        gaussianEvenTaylorCoeff, FormalPowerSeries.expCoeff,
        factorialRat, factorial, Rat.div_def, hinvOne]
      grind [Rat.mul_assoc, Rat.mul_comm]
  | succ terms ih =>
      rw [gaussianEvenProfileFormalDerivativePrefix_succ,
        gaussianEvenProfilePrefix_succ]
      have hcoeff := congrFun FormalPowerSeries.expCoeff_derivative terms
      change (((terms + 1 : Nat) : Rat)) *
          FormalPowerSeries.expCoeff (terms + 1) =
        FormalPowerSeries.expCoeff terms at hcoeff
      have hsign : (-1 : Rat) ^ (terms + 1) = -((-1 : Rat) ^ terms) := by
        rw [Rat.pow_succ]
        grind [Rat.mul_comm]
      rw [hsign]
      have hpow : x ^ (2 * (terms + 1) - 1) =
          x ^ (2 * terms + 1) := by
        congr 1 <;> omega
      have hlastPow : x * x ^ (2 * (terms + 1)) =
          x ^ (2 * (terms + 1) + 1) := by
        rw [Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
      rw [Rat.mul_add, hpow]
      calc
        gaussianEvenProfileFormalDerivativePrefix (terms + 1) x +
              (((2 * (terms + 1) : Nat) : Rat)) *
                  (FormalPowerSeries.expCoeff (terms + 1) *
                    -((-1 : Rat) ^ terms)) * x ^ (2 * terms + 1) +
            (2 * x * gaussianEvenProfilePrefix (terms + 1) x +
              2 * x *
                (FormalPowerSeries.expCoeff (terms + 1) *
                  -((-1 : Rat) ^ terms) * x ^ (2 * (terms + 1)))) =
            (gaussianEvenProfileFormalDerivativePrefix (terms + 1) x +
              2 * x * gaussianEvenProfilePrefix (terms + 1) x) +
              (((2 * (terms + 1) : Nat) : Rat)) *
                (FormalPowerSeries.expCoeff (terms + 1) *
                  -((-1 : Rat) ^ terms)) * x ^ (2 * terms + 1) +
              2 * x *
                (FormalPowerSeries.expCoeff (terms + 1) *
                  -((-1 : Rat) ^ terms) * x ^ (2 * (terms + 1))) := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ = 2 * (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
                x ^ (2 * terms + 1) +
              (((2 * (terms + 1) : Nat) : Rat)) *
                (FormalPowerSeries.expCoeff (terms + 1) *
                  -((-1 : Rat) ^ terms)) * x ^ (2 * terms + 1) +
              2 * x *
                (FormalPowerSeries.expCoeff (terms + 1) *
                  -((-1 : Rat) ^ terms) * x ^ (2 * (terms + 1))) := by
              rw [ih]
        _ = 2 * (FormalPowerSeries.expCoeff (terms + 1) *
                -((-1 : Rat) ^ terms)) *
              x ^ (2 * (terms + 1) + 1) := by
              push_cast
              grind [Rat.mul_add, Rat.add_mul,
                Rat.mul_assoc, Rat.mul_comm]

private theorem gaussian_neg_square_pow (x : Rat) (k : Nat) :
    (-(x * x)) ^ k = (-1 : Rat) ^ k * x ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Rat.pow_succ, ih]
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        Rat.pow_succ, Rat.pow_succ, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianEvenProfilePrefix_ode_boundary_eq
    (terms : Nat) (x : Rat) :
    (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
        x ^ (2 * terms + 1) =
      ExpProofs.powerSeriesTermAtTerms (-(x * x)) terms * x := by
  rw [ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial,
    gaussian_neg_square_pow, Rat.pow_succ]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- On the rational box `|x| <= C`, the exact finite Gaussian ODE defect is
bounded by one explicit factorial-tail term. -/
theorem gaussianEvenProfilePrefix_ode_residual_le
    (terms : Nat) {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) :
    qabs (gaussianEvenProfileFormalDerivativePrefix (terms + 1) x +
        2 * x * gaussianEvenProfilePrefix (terms + 1) x) <=
      2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
  rw [gaussianEvenProfilePrefix_ode_residual,
    show 2 * (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
          x ^ (2 * terms + 1) =
        2 * ((FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
          x ^ (2 * terms + 1)) by
      grind [Rat.mul_assoc],
    gaussianEvenProfilePrefix_ode_boundary_eq]
  have hbox : qabs (-(x * x)) <= C * C := by
    rw [qabs_neg, qabs_mul]
    exact rat_mul_le_mul_of_nonneg
      (qabs_nonneg x) hx (qabs_nonneg x) hx
  have hterm :=
    FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
      (Rat.mul_nonneg hC hC) hbox terms
  have hterm' :
      qabs (ExpProofs.powerSeriesTermAtTerms (-(x * x)) terms) <=
        RationalMajorant.factorialTailTerm (C * C) terms := by
    rw [ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial]
    exact hterm
  rw [qabs_mul, qabs_mul]
  have htwo : qabs (2 : Rat) = 2 := by decide +kernel
  rw [htwo]
  have hscaled := Rat.mul_le_mul_of_nonneg_left hterm'
    (by decide +kernel : (0 : Rat) <= 2)
  have hscaled' := Rat.mul_le_mul_of_nonneg_right hscaled (qabs_nonneg x)
  have htailNonneg :
      0 <= RationalMajorant.factorialTailTerm (C * C) terms :=
    RationalMajorant.factorialTailTerm_nonneg
      (Rat.mul_nonneg hC hC) terms
  have hright := Rat.mul_le_mul_of_nonneg_left hx
    (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 2) htailNonneg)
  have hright' :
      2 * RationalMajorant.factorialTailTerm (C * C) terms * qabs x <=
        2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
    calc
      2 * RationalMajorant.factorialTailTerm (C * C) terms * qabs x <=
          2 * RationalMajorant.factorialTailTerm (C * C) terms * C := hright
      _ = 2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  exact Rat.le_trans (by simpa [Rat.mul_assoc] using hscaled') hright'

/-- Executable Taylor term count making the Gaussian ODE defect smaller than
`eps` on the symmetric rational box of radius `C`. -/
def gaussianODETermsForPrecision (C : Rat) (eps : QPos) : Nat :=
  let start := RationalMajorant.factorialTailStart (C * C)
  start + RationalMajorant.halfDecayShift
    (2 * C * RationalMajorant.factorialTailTerm (C * C) start) eps

theorem gaussianEvenProfilePrefix_scheduled_ode_residual_le
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) (eps : QPos) :
    qabs
        (gaussianEvenProfileFormalDerivativePrefix
            (gaussianODETermsForPrecision C eps + 1) x +
          2 * x *
            gaussianEvenProfilePrefix
              (gaussianODETermsForPrecision C eps + 1) x) <=
      eps.val := by
  let start := RationalMajorant.factorialTailStart (C * C)
  let coefficient :=
    2 * C * RationalMajorant.factorialTailTerm (C * C) start
  let shift := RationalMajorant.halfDecayShift coefficient eps
  have hCC : 0 <= C * C := Rat.mul_nonneg hC hC
  have hstart := RationalMajorant.factorialTailStart_satisfies (C * C)
  have hterm :=
    RationalMajorant.factorialTailTerm_le_geometric_from_start
      hCC hstart shift
  have hfactorNonneg : 0 <= 2 * C :=
    Rat.mul_nonneg (by decide +kernel) hC
  have hscaled := Rat.mul_le_mul_of_nonneg_left hterm hfactorNonneg
  have hcoefficientNonneg : 0 <= coefficient := by
    dsimp [coefficient]
    exact Rat.mul_nonneg hfactorNonneg
      (RationalMajorant.factorialTailTerm_nonneg hCC start)
  have hdecay := RationalMajorant.halfDecayShift_spec
    hcoefficientNonneg eps
  have hresidual := gaussianEvenProfilePrefix_ode_residual_le
    (gaussianODETermsForPrecision C eps) hC hx
  calc
    qabs
        (gaussianEvenProfileFormalDerivativePrefix
            (gaussianODETermsForPrecision C eps + 1) x +
          2 * x *
            gaussianEvenProfilePrefix
              (gaussianODETermsForPrecision C eps + 1) x) <=
        2 * C * RationalMajorant.factorialTailTerm (C * C)
          (gaussianODETermsForPrecision C eps) := hresidual
    _ <= 2 * C *
          (RationalMajorant.factorialTailTerm (C * C) start *
            ((1 : Rat) / 2) ^ shift) := by
      simpa [gaussianODETermsForPrecision, start, shift] using hscaled
    _ = coefficient * ((1 : Rat) / 2) ^ shift := by
      dsimp [coefficient]
      grind [Rat.mul_assoc]
    _ <= eps.val := by
      simpa [shift] using hdecay

/-- The sparse even derivative polynomial is exactly the executable finite
factorial center evaluated at `-x^2`. -/
theorem gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms
    (terms : Nat) (x : Rat) :
    gaussianEvenProfilePrefix terms x =
      ExpProofs.powerSeriesCenterAtTerms (-(x * x)) terms := by
  induction terms with
  | zero =>
      change 0 = 0
      rfl
  | succ terms ih =>
      unfold gaussianEvenProfilePrefix
      rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega]
      simp only [FinitePolynomial.taylorDerivativePrefix]
      rw [gaussianEvenTaylorCoeff_odd, Rat.zero_mul, Rat.add_zero]
      rw [gaussianEvenTaylorCoeff_even]
      change gaussianEvenProfilePrefix terms x +
          (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
            x ^ (2 * terms) = _
      rw [ih, ExpProofs.powerSeriesCenterAtTerms_succ,
        ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial,
        gaussian_neg_square_pow]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite termwise integration: doubling the primitive increment on
`[0,1]` gives the symmetric Gaussian prefix already used by the alternating
raw-real construction. -/
theorem two_mul_gaussianEvenPrimitivePrefix_endpointDifference
    (terms : Nat) :
    2 * (gaussianEvenPrimitivePrefix terms 1 -
      gaussianEvenPrimitivePrefix terms 0) =
        gaussianEvenIntegralPrefix terms 1 := by
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
      rw [gaussianEvenTaylorCoeff_even]
      rw [gaussianEvenIntegralPrefix_succ]
      have hpowPos : 0 < 2 * terms + 1 := by omega
      have honePow : forall n : Nat, (1 : Rat) ^ n = 1 := by
        intro n
        induction n with
        | zero => rfl
        | succ n ihPow => rw [Rat.pow_succ, ihPow, Rat.one_mul]
      have hzeroPow : (0 : Rat) ^ (2 * terms + 1) = 0 := by
        rw [show 2 * terms + 1 = 2 * terms + 1 by rfl,
          Rat.pow_succ, Rat.mul_zero]
      have ih' :
          2 *
              (FinitePolynomial.integratedTaylorPrefix
                  gaussianEvenTaylorCoeff (2 * terms) 1 -
                FinitePolynomial.integratedTaylorPrefix
                  gaussianEvenTaylorCoeff (2 * terms) 0) =
            gaussianEvenIntegralPrefix terms 1 := by
        simpa [gaussianEvenPrimitivePrefix] using ih
      rw [honePow, hzeroPow]
      grind [Rat.div_def, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

/-- The explicit secant certificate carried by the sparse Gaussian
primitive.  Its coefficient is a computable rational finite sum. -/
def gaussianEvenPrimitiveSecantBound (terms : Nat) :
    FinitePolynomial.SecantDerivativeBound 1
      (gaussianEvenPrimitivePrefix terms)
      (gaussianEvenProfilePrefix terms) := by
  change FinitePolynomial.SecantDerivativeBound 1
    (FinitePolynomial.integratedTaylorPrefix gaussianEvenTaylorCoeff
      (2 * terms))
    (FinitePolynomial.taylorDerivativePrefix gaussianEvenTaylorCoeff
      (2 * terms))
  exact FinitePolynomial.integratedTaylorPrefixSecantBound
    1 gaussianEvenTaylorCoeff (by decide +kernel) (2 * terms)

theorem gaussianEvenPrimitiveSecantBound_errorCoefficient_eq
    (terms : Nat) :
    (gaussianEvenPrimitiveSecantBound terms).errorCoefficient =
      FinitePolynomial.integratedTaylorPrefixSecantCoefficient
        1 gaussianEvenTaylorCoeff (2 * terms) := by
  change
    (FinitePolynomial.integratedTaylorPrefixSecantBound
      1 gaussianEvenTaylorCoeff (by decide +kernel)
      (2 * terms)).errorCoefficient = _
  exact FinitePolynomial.integratedTaylorPrefixSecantBound_errorCoefficient
    1 gaussianEvenTaylorCoeff (by decide +kernel) (2 * terms)

private theorem gaussianEvenPrimitiveSecantBound_errorCoefficient_succ
    (terms : Nat) :
    (gaussianEvenPrimitiveSecantBound (terms + 1)).errorCoefficient =
      (gaussianEvenPrimitiveSecantBound terms).errorCoefficient +
        qabs (FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms) *
          FinitePolynomial.powerSecantErrorBound 1 (2 * terms + 1) := by
  rw [gaussianEvenPrimitiveSecantBound_errorCoefficient_eq,
    gaussianEvenPrimitiveSecantBound_errorCoefficient_eq]
  rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega,
    FinitePolynomial.integratedTaylorPrefixSecantCoefficient,
    FinitePolynomial.integratedTaylorPrefixSecantCoefficient,
    gaussianEvenTaylorCoeff_odd, gaussianEvenTaylorCoeff_even]
  rw [qabs_eq_self_of_nonneg (show (0 : Rat) <= 0 by decide +kernel),
    Rat.zero_mul, Rat.add_zero]

private theorem powerSecantErrorBound_one_odd_closed (k : Nat) :
    FinitePolynomial.powerSecantErrorBound 1 (2 * k + 1) =
      (k : Rat) * ((2 * k + 1 : Nat) : Rat) := by
  have honePow : forall n : Nat, (1 : Rat) ^ n = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ, ih, Rat.one_mul]
  induction k with
  | zero => decide +kernel
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        FinitePolynomial.powerSecantErrorBound,
        FinitePolynomial.powerSecantErrorBound,
        honePow, honePow, Rat.mul_one, Rat.one_mul, ih]
      have hk1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
        exact_mod_cast (by omega : k + 1 = k + 1)
      have htwoKOne : (((2 * k + 1 : Nat) : Rat)) = 2 * (k : Rat) + 1 := by
        exact_mod_cast (by omega : 2 * k + 1 = 2 * k + 1)
      have htwoKTwo : (((2 * k + 2 : Nat) : Rat)) = 2 * (k : Rat) + 2 := by
        exact_mod_cast (by omega : 2 * k + 2 = 2 * k + 2)
      have htwoKTwoOne : (((2 * k + 2 + 1 : Nat) : Rat)) =
          2 * (k : Rat) + 3 := by
        exact_mod_cast (by omega : 2 * k + 2 + 1 = 2 * k + 3)
      rw [hk1, htwoKOne, htwoKTwo, htwoKTwoOne]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem qabs_neg_one_pow_gaussian (k : Nat) :
    qabs ((-1 : Rat) ^ k) = 1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
      rw [Rat.pow_succ, qabs_mul, ih]
      decide +kernel

private theorem qabs_expCoeff_mul_neg_one_pow_gaussian (k : Nat) :
    qabs (FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k) =
      FormalPowerSeries.expCoeff k := by
  rw [qabs_mul, qabs_neg_one_pow_gaussian, Rat.mul_one]
  apply qabs_eq_self_of_nonneg
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2
    (RationalMajorant.factorialRat_pos k))

private theorem gaussianEvenSecantCoefficient_summand (k : Nat) :
    qabs (FormalPowerSeries.expCoeff (k + 2) * (-1 : Rat) ^ (k + 2)) *
        FinitePolynomial.powerSecantErrorBound 1 (2 * (k + 2) + 1) =
      2 * RationalMajorant.factorialTailTerm 1 k +
        3 * RationalMajorant.factorialTailTerm 1 (k + 1) := by
  rw [qabs_expCoeff_mul_neg_one_pow_gaussian,
    powerSecantErrorBound_one_odd_closed]
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
  have honePow : forall n : Nat, (1 : Rat) ^ n = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ, ih, Rat.one_mul]
  rw [honePow, honePow, Rat.one_mul]
  have hleft :
      (factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          ((k : Rat) + 2)⁻¹ *
            (((k : Rat) + 2) * (2 * (k : Rat) + 5)) =
        (factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          (2 * (k : Rat) + 5) := by
    rw [show
      (factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          ((k : Rat) + 2)⁻¹ *
            (((k : Rat) + 2) * (2 * (k : Rat) + 5)) =
        (factorialRat k)⁻¹ * ((k : Rat) + 1)⁻¹ *
          (((k : Rat) + 2)⁻¹ * ((k : Rat) + 2)) *
            (2 * (k : Rat) + 5) by
        grind [Rat.mul_assoc, Rat.mul_comm], hcancel2', Rat.mul_one]
  rw [hleft]
  have hsplit : 2 * (k : Rat) + 5 = 2 * ((k : Rat) + 1) + 3 := by
    grind [Rat.mul_add]
  rw [hsplit, Rat.mul_add]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem gaussianEvenPrimitiveSecantBound_errorCoefficient_eq_factorialPartials
    (n : Nat) :
    (gaussianEvenPrimitiveSecantBound (n + 2)).errorCoefficient =
      3 + 2 * RationalMajorant.factorialTailPartial 1 0 n +
        3 * RationalMajorant.factorialTailPartial 1 1 n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        gaussianEvenPrimitiveSecantBound_errorCoefficient_succ, ih,
        gaussianEvenSecantCoefficient_summand,
        RationalMajorant.factorialTailPartial,
        RationalMajorant.factorialTailPartial]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem factorialTailPartial_one_one_le_two (n : Nat) :
    RationalMajorant.factorialTailPartial 1 1 n <= 2 := by
  have h := RationalMajorant.factorialTailPartial_bound
    (C := (1 : Rat)) (N := 1) (by decide +kernel) (by decide +kernel) n
  have hterm : RationalMajorant.factorialTailTerm 1 1 = 1 := by
    decide +kernel
  rw [hterm, Rat.mul_one] at h
  exact h

private theorem factorialTailPartial_one_zero_le_three (n : Nat) :
    RationalMajorant.factorialTailPartial 1 0 n <= 3 := by
  cases n with
  | zero => decide +kernel
  | succ n =>
      have hsplit := RationalMajorant.factorialTailPartial_add 1 0 1 n
      have hone : RationalMajorant.factorialTailPartial 1 0 1 = 1 := by
        decide +kernel
      have htail := factorialTailPartial_one_one_le_two n
      rw [show n + 1 = 1 + n by omega, hsplit, hone]
      grind

/-- Every sparse Gaussian Taylor primitive on the unit box carries the same
rational secant-error coefficient bound.  The constant `15` comes from two
finite factorial-tail estimates, not from a completed exponential value. -/
theorem gaussianEvenPrimitiveSecantBound_errorCoefficient_le_fifteen
    (terms : Nat) :
    (gaussianEvenPrimitiveSecantBound terms).errorCoefficient <= 15 := by
  cases terms with
  | zero => decide +kernel
  | succ terms =>
      cases terms with
      | zero => decide +kernel
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega,
            gaussianEvenPrimitiveSecantBound_errorCoefficient_eq_factorialPartials]
          have hzero := factorialTailPartial_one_zero_le_three n
          have hone := factorialTailPartial_one_one_le_two n
          calc
            3 + 2 * RationalMajorant.factorialTailPartial 1 0 n +
                3 * RationalMajorant.factorialTailPartial 1 1 n <=
              3 + 2 * 3 + 3 * 2 := by
                apply rat_add_le_add
                · apply rat_add_le_add
                  · exact Rat.le_refl
                  · exact Rat.mul_le_mul_of_nonneg_left hzero
                      (by decide +kernel)
                · exact Rat.mul_le_mul_of_nonneg_left hone
                    (by decide +kernel)
            _ = 15 := by decide +kernel

theorem gaussianEvenProfilePrefix_uniformStage (stage : Nat) (x : Rat) :
    gaussianEvenProfilePrefix (ExpProofs.uniformExpTailTerms stage) x =
      ExpProofs.uniformExpCenter (-(x * x)) stage := by
  rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
  rfl

/-- The generic finite midpoint theorem specialized to a Gaussian factorial
prefix on `[0,1]`. -/
theorem gaussianEvenPrimitive_uniformMidpoint_error_le
    (terms pieces : Nat) (hpieces : 0 < pieces) :
    let P := RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)
    qabs ((gaussianEvenPrimitivePrefix terms 1 -
        gaussianEvenPrimitivePrefix terms 0) -
      P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <=
        (mesh 0 1 pieces * (1 - 0)) *
          (gaussianEvenPrimitiveSecantBound terms).errorCoefficient := by
  exact FinitePolynomial.SecantDerivativeBound.qabs_uniform_midpointRectangleAction_error_le
      (gaussianEvenPrimitiveSecantBound terms)
      pieces hpieces (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem gaussianEvenPrimitive_uniformMidpoint_error_le_fifteen
    (terms pieces : Nat) (hpieces : 0 < pieces) :
    let P := RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)
    qabs ((gaussianEvenPrimitivePrefix terms 1 -
        gaussianEvenPrimitivePrefix terms 0) -
      P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <=
        15 * mesh 0 1 pieces := by
  have hbase := gaussianEvenPrimitive_uniformMidpoint_error_le
    terms pieces hpieces
  have hcoeff :=
    gaussianEvenPrimitiveSecantBound_errorCoefficient_le_fifteen terms
  have hmesh : 0 <= mesh 0 1 pieces :=
    mesh_nonneg_of_le hpieces (by decide +kernel)
  have hscaled :
      (mesh 0 1 pieces * (1 - 0)) *
          (gaussianEvenPrimitiveSecantBound terms).errorCoefficient <=
        (mesh 0 1 pieces * (1 - 0)) * 15 :=
    Rat.mul_le_mul_of_nonneg_left hcoeff
      (Rat.mul_nonneg hmesh (by decide +kernel))
  exact Rat.le_trans hbase (by
    calc
      (mesh 0 1 pieces * (1 - 0)) *
          (gaussianEvenPrimitiveSecantBound terms).errorCoefficient <=
          (mesh 0 1 pieces * (1 - 0)) * 15 := hscaled
      _ = 15 * mesh 0 1 pieces := by
        grind [Rat.mul_assoc, Rat.mul_comm])

private theorem gaussian_unit_uniform_cell_width_pos
    (pieces : Nat) (hpieces : 0 < pieces) (k : Nat) (hk : k < pieces) :
    0 < ((RationalPartition.uniform 0 1 pieces hpieces
      (by decide +kernel)).cell k hk).width := by
  rw [RationalPartition.uniform_cell_width]
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hpieces)]
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide +kernel)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hpieces))

private theorem gaussian_neg_square_cell_bounds
    {C : RationalSubinterval (0 : Rat) 1}
    (hwidth : 0 < C.width) (x : Rat) (hx : C.contains x) :
    (-1 : Rat) <= -(C.upper * C.upper) /\
      -(C.lower * C.lower) <= 1 /\
      -(C.upper * C.upper) < -(C.lower * C.lower) /\
      -(C.upper * C.upper) <= -(x * x) /\
      -(x * x) <= -(C.lower * C.lower) := by
  have hl0 : 0 <= C.lower := C.lower_mem
  have hxu : x <= C.upper := hx.2
  have hlx : C.lower <= x := hx.1
  have hx0 : 0 <= x := Rat.le_trans hl0 hlx
  have hu1 : C.upper <= 1 := C.upper_mem
  have hu0 : 0 <= C.upper := Rat.le_trans hx0 hxu
  have hlu : C.lower < C.upper := by
    apply (Rat.lt_iff_sub_pos _ _).mpr
    simpa [RationalSubinterval.width] using hwidth
  have hu2 : C.upper * C.upper <= 1 := by
    have h := rat_mul_le_mul_of_nonneg hu0 hu1 hu0 hu1
    simpa using h
  have hl2x2 : C.lower * C.lower <= x * x :=
    rat_mul_le_mul_of_nonneg hl0 hlx hl0 hlx
  have hx2u2 : x * x <= C.upper * C.upper :=
    rat_mul_le_mul_of_nonneg hx0 hxu hx0 hxu
  have hsqStrict : C.lower * C.lower < C.upper * C.upper := by
    have hdiff : 0 < (C.upper - C.lower) * (C.upper + C.lower) := by
      apply Rat.mul_pos
      · grind [Rat.sub_eq_add_neg]
      · grind
    apply (Rat.lt_iff_sub_pos _ _).mpr
    have hid : C.upper * C.upper - C.lower * C.lower =
        (C.upper - C.lower) * (C.upper + C.lower) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    rw [hid]
    exact hdiff
  constructor
  · grind
  constructor
  · have hsquare := rat_square_nonneg_basic C.lower
    grind
  constructor
  · grind
  constructor <;> grind

/-- A finite sampled rule for the true exponential Gaussian on `[0,1]`.
The mesh size and the common exponential evaluator stage remain independent,
so later constructions can balance spatial and factorial-tail errors. -/
def gaussianExponentialHalfRule (pieces stage : Nat)
    (hpieces : 0 < pieces) :
    SampledRawDarbouxPartition gaussianExponentialRaw
      (RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)) where
  evalStage := stage
  sample := fun k hk =>
    gaussianCellMidpoint
      ((RationalPartition.uniform 0 1 pieces hpieces
        (by decide +kernel)).cell k hk)
  sample_mem := by
    intro k hk
    exact QInterval.midpoint_mem
      ((RationalPartition.uniform 0 1 pieces hpieces
        (by decide +kernel)).cell k hk).ordered
  sampleValue := fun k hk =>
    gaussianExponentialSampleValue
      ((RationalPartition.uniform 0 1 pieces hpieces
        (by decide +kernel)).cell k hk) stage
  sampleValue_mem := by
    intro k hk
    change (ExpProofs.uniformExpRaw
        (-(gaussianCellMidpoint
          ((RationalPartition.uniform 0 1 pieces hpieces
            (by decide +kernel)).cell k hk) *
          gaussianCellMidpoint
          ((RationalPartition.uniform 0 1 pieces hpieces
            (by decide +kernel)).cell k hk)))).compute stage |>.ContainsInterval
      (QInterval.pointInterval
        (gaussianExponentialSampleValue
          ((RationalPartition.uniform 0 1 pieces hpieces
            (by decide +kernel)).cell k hk) stage))
    rw [ExpProofs.uniformExpRaw_compute]
    unfold gaussianExponentialSampleValue
    unfold ExpProofs.uniformExpBox ExpProofs.intervalAround
      QInterval.ContainsInterval QInterval.pointInterval
    have htail : 0 <= ExpProofs.uniformExpTailRadius stage := by
      unfold ExpProofs.uniformExpTailRadius ExpProofs.uniformExpTailMagnitude
      exact Rat.mul_nonneg (by decide +kernel)
        (RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) _)
    grind
  range := fun k hk => gaussianExponentialCellRange
    ((RationalPartition.uniform 0 1 pieces hpieces
      (by decide +kernel)).cell k hk) stage
  range_contains := by
    intro k hk x hx
    let C := (RationalPartition.uniform 0 1 pieces hpieces
      (by decide +kernel)).cell k hk
    have hbounds := gaussian_neg_square_cell_bounds
      (C := C) (gaussian_unit_uniform_cell_width_pos pieces hpieces k hk) x hx
    change (gaussianExponentialCellRange C stage).ContainsInterval
      ((gaussianExponentialRaw x).compute stage)
    unfold gaussianExponentialCellRange gaussianExponentialRaw
    exact ExpProofs.uniformExpSymmetricCellRange_contains stage
      hbounds.1 hbounds.2.1 hbounds.2.2.1
      hbounds.2.2.2.1 hbounds.2.2.2.2

/-- At a common exponential stage, the polynomial midpoint action and the
raw Gaussian rule's sampled action are the same finite rational rectangles. -/
theorem gaussianUniformMidpointAction_eq_halfRuleSampledAction
    (pieces stage : Nat) (hpieces : 0 < pieces) :
    let P := RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)
    P.midpointRectangleAction
        (gaussianEvenProfilePrefix (ExpProofs.uniformExpTailTerms stage)) =
      (gaussianExponentialHalfRule pieces stage hpieces).sampledAction := by
  dsimp only
  let P := RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)
  let R := gaussianExponentialHalfRule pieces stage hpieces
  have hterm : forall k : Nat,
      P.midpointRectangleTerm
          (gaussianEvenProfilePrefix
            (ExpProofs.uniformExpTailTerms stage)) k =
        R.sampleTerm k := by
    intro k
    unfold RationalPartition.midpointRectangleTerm
      SampledRawDarbouxPartition.sampleTerm
    by_cases hk : k < P.pieces
    · have hkR : k < (RationalPartition.uniform 0 1 pieces hpieces
          (by decide +kernel)).pieces := by simpa [P] using hk
      simp only [hk, hkR, dite_true]
      rw [gaussianEvenProfilePrefix_uniformStage]
      simp [P, R, gaussianExponentialHalfRule,
        gaussianExponentialSampleValue, gaussianCellMidpoint,
        SampledDarbouxCell.cellInterval, QInterval.midpoint]
    · have hkR : ¬ (k < (RationalPartition.uniform 0 1 pieces hpieces
          (by decide +kernel)).pieces) := by simpa [P] using hk
      simp [hk, hkR]
  unfold RationalPartition.midpointRectangleAction
    SampledRawDarbouxPartition.sampledAction
  have hstep :
      (fun total k => total +
          P.midpointRectangleTerm
            (gaussianEvenProfilePrefix
              (ExpProofs.uniformExpTailTerms stage)) k) =
        (fun total k => total + R.sampleTerm k) := by
    funext total k
    rw [hterm]
  rw [hstep]

/-- Uniform finite comparison between the alternating Gaussian anchor prefix
and the common-stage exponential midpoint samples.  Every quantity is a
rational finite computation; the displayed coefficient comes from the sparse
polynomial secant certificate. -/
theorem gaussianEvenIntegralPrefix_sub_exponentialSampledAction_le
    (pieces stage : Nat) (hpieces : 0 < pieces) :
    let terms := ExpProofs.uniformExpTailTerms stage
    qabs (gaussianEvenIntegralPrefix terms 1 -
        2 * (gaussianExponentialHalfRule pieces stage hpieces).sampledAction) <=
      2 * ((mesh 0 1 pieces * (1 - 0)) *
        (gaussianEvenPrimitiveSecantBound terms).errorCoefficient) := by
  dsimp only
  let terms := ExpProofs.uniformExpTailTerms stage
  let P := RationalPartition.uniform 0 1 pieces hpieces (by decide +kernel)
  have hfinite := gaussianEvenPrimitive_uniformMidpoint_error_le
    terms pieces hpieces
  change qabs ((gaussianEvenPrimitivePrefix terms 1 -
      gaussianEvenPrimitivePrefix terms 0) -
        P.midpointRectangleAction (gaussianEvenProfilePrefix terms)) <= _
    at hfinite
  have haction := gaussianUniformMidpointAction_eq_halfRuleSampledAction
    pieces stage hpieces
  change P.midpointRectangleAction (gaussianEvenProfilePrefix terms) =
      (gaussianExponentialHalfRule pieces stage hpieces).sampledAction
    at haction
  rw [haction] at hfinite
  have hprefix :=
    two_mul_gaussianEvenPrimitivePrefix_endpointDifference terms
  have hdecomp :
      gaussianEvenIntegralPrefix terms 1 -
          2 * (gaussianExponentialHalfRule pieces stage hpieces).sampledAction =
        2 * ((gaussianEvenPrimitivePrefix terms 1 -
            gaussianEvenPrimitivePrefix terms 0) -
          (gaussianExponentialHalfRule pieces stage hpieces).sampledAction) := by
    rw [← hprefix]
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hdecomp, qabs_mul]
  have htwo : qabs (2 : Rat) = 2 := by decide +kernel
  rw [htwo]
  exact Rat.mul_le_mul_of_nonneg_left hfinite (by decide +kernel)

/-- The all-stage bridge now has a stage-independent spatial constant.  With
`pieces` midpoint cells, the symmetric finite Gaussian prefix and the common
exponential sampled action differ by at most `30 * mesh`. -/
theorem gaussianEvenIntegralPrefix_sub_exponentialSampledAction_le_thirty_mesh
    (pieces stage : Nat) (hpieces : 0 < pieces) :
    let terms := ExpProofs.uniformExpTailTerms stage
    qabs (gaussianEvenIntegralPrefix terms 1 -
        2 * (gaussianExponentialHalfRule pieces stage hpieces).sampledAction) <=
      30 * mesh 0 1 pieces := by
  dsimp only
  have hbase := gaussianEvenIntegralPrefix_sub_exponentialSampledAction_le
    pieces stage hpieces
  have hcoeff := gaussianEvenPrimitiveSecantBound_errorCoefficient_le_fifteen
    (ExpProofs.uniformExpTailTerms stage)
  have hmesh : 0 <= mesh 0 1 pieces :=
    mesh_nonneg_of_le hpieces (by decide +kernel)
  have hfactor : 0 <= mesh 0 1 pieces * (1 - 0) :=
    Rat.mul_nonneg hmesh (by decide +kernel)
  have hscaled :
      (mesh 0 1 pieces * (1 - 0)) *
          (gaussianEvenPrimitiveSecantBound
            (ExpProofs.uniformExpTailTerms stage)).errorCoefficient <=
        (mesh 0 1 pieces * (1 - 0)) * 15 :=
    Rat.mul_le_mul_of_nonneg_left hcoeff hfactor
  calc
    qabs (gaussianEvenIntegralPrefix
        (ExpProofs.uniformExpTailTerms stage) 1 -
          2 * (gaussianExponentialHalfRule pieces stage hpieces).sampledAction) <=
        2 * ((mesh 0 1 pieces * (1 - 0)) *
          (gaussianEvenPrimitiveSecantBound
            (ExpProofs.uniformExpTailTerms stage)).errorCoefficient) := hbase
    _ <= 2 * ((mesh 0 1 pieces * (1 - 0)) * 15) :=
      Rat.mul_le_mul_of_nonneg_left hscaled (by decide +kernel)
    _ = 30 * mesh 0 1 pieces := by
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianExponentialCellRange_width
    (C : RationalSubinterval (0 : Rat) 1) (stage : Nat) :
    (gaussianExponentialCellRange C stage).width =
      2 * (9 * (-(C.lower * C.lower) - -(C.upper * C.upper)) +
        34 * (-(C.lower * C.lower) - -(C.upper * C.upper)) ^ 2 +
        2 * ExpProofs.uniformExpTailMagnitude stage +
        ExpProofs.uniformExpTailRadius stage) := by
  unfold gaussianExponentialCellRange
  rw [ExpProofs.uniformExpSymmetricCellRange_width]

/-- A Gaussian cell pays separately for spatial variation and for the common
factorial tail.  The deliberately round constant `308` comes from the public
symmetric exponential range estimate after the `-x^2` pullback. -/
theorem gaussianExponentialCellRange_width_le
    (C : RationalSubinterval (0 : Rat) 1) (stage : Nat) :
    (gaussianExponentialCellRange C stage).width <=
      308 * C.width + 8 * ExpProofs.uniformExpTailMagnitude stage := by
  let w : Rat := C.width
  let d : Rat := -(C.lower * C.lower) - -(C.upper * C.upper)
  have hw0 : 0 <= w := by
    dsimp [w, RationalSubinterval.width]
    grind [C.ordered]
  have hw1 : w <= 1 := by
    dsimp [w, RationalSubinterval.width]
    grind [C.lower_mem, C.upper_mem, Rat.sub_eq_add_neg]
  have hsum0 : 0 <= C.upper + C.lower := by
    grind [C.lower_mem, C.ordered]
  have hsum2 : C.upper + C.lower <= 2 := by
    grind [C.lower_mem, C.ordered, C.upper_mem]
  have hd_eq : d = w * (C.upper + C.lower) := by
    dsimp [d, w, RationalSubinterval.width]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hd0 : 0 <= d := by
    rw [hd_eq]
    exact Rat.mul_nonneg hw0 hsum0
  have hd_le_two_w : d <= 2 * w := by
    rw [hd_eq]
    have h := Rat.mul_le_mul_of_nonneg_left hsum2 hw0
    grind [Rat.mul_comm]
  have hd2 : d <= 2 := by
    have h := Rat.mul_le_mul_of_nonneg_left hw1
      (by decide +kernel : (0 : Rat) <= 2)
    exact Rat.le_trans hd_le_two_w (by
      simpa [Rat.mul_comm] using h)
  have hdsq : d ^ 2 <= 4 * w := by
    have hfirst := Rat.mul_le_mul_of_nonneg_left hd2 hd0
    have hsecond := Rat.mul_le_mul_of_nonneg_left hd_le_two_w
      (by decide +kernel : (0 : Rat) <= 2)
    calc
      d ^ 2 = d * d := by
        rw [show 2 = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
        simp
      _ <= d * 2 := hfirst
      _ = 2 * d := by rw [Rat.mul_comm]
      _ <= 2 * (2 * w) := hsecond
      _ = 4 * w := by grind [Rat.mul_assoc]
  have htail : 0 <= ExpProofs.uniformExpTailMagnitude stage := by
    unfold ExpProofs.uniformExpTailMagnitude
    exact RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) _
  rw [gaussianExponentialCellRange_width]
  change 2 * (9 * d + 34 * d ^ 2 +
      2 * ExpProofs.uniformExpTailMagnitude stage +
      ExpProofs.uniformExpTailRadius stage) <= _
  unfold ExpProofs.uniformExpTailRadius
  have hlin := Rat.mul_le_mul_of_nonneg_left hd_le_two_w
    (by decide +kernel : (0 : Rat) <= 9)
  have hquad := Rat.mul_le_mul_of_nonneg_left hdsq
    (by decide +kernel : (0 : Rat) <= 34)
  grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul]

theorem gaussianExponentialHalfRule_range_width_le
    (pieces stage k : Nat) (hpieces : 0 < pieces) (hk : k < pieces) :
    ((gaussianExponentialHalfRule pieces stage hpieces).range k hk).width <=
      308 * mesh 0 1 pieces +
        8 * ExpProofs.uniformExpTailMagnitude stage := by
  have h := gaussianExponentialCellRange_width_le
    ((RationalPartition.uniform 0 1 pieces hpieces
      (by decide +kernel)).cell k hk) stage
  rw [RationalPartition.uniform_cell_width 0 1 pieces hpieces
    (by decide +kernel) k hk] at h
  exact h

/-- The finite half-Gaussian Darboux box has an explicit two-budget rate:
`308/pieces` for the spatial mesh and eight times the factorial tail at the
selected common evaluator stage. -/
theorem gaussianExponentialHalfRule_darbouxSum_width_le
    (pieces stage : Nat) (hpieces : 0 < pieces) :
    (gaussianExponentialHalfRule pieces stage hpieces).darbouxSum.width <=
      308 * mesh 0 1 pieces +
        8 * ExpProofs.uniformExpTailMagnitude stage := by
  change ((RationalPartition.uniform 0 1 pieces hpieces
    (by decide +kernel)).boundIntegralSum
      (gaussianExponentialHalfRule pieces stage hpieces).range).width <= _
  have h := RationalPartition.uniform_boundIntegralSum_width_le
    (a := (0 : Rat)) (b := (1 : Rat)) pieces hpieces (by decide +kernel)
    (gaussianExponentialHalfRule pieces stage hpieces).range
    (308 * mesh 0 1 pieces +
      8 * ExpProofs.uniformExpTailMagnitude stage)
    (fun k hk =>
      gaussianExponentialHalfRule_range_width_le
        pieces stage k hpieces hk)
  exact Rat.le_trans h (by grind)

/-- Public geometric decay of the particular factorial tail used by the
Gaussian rule.  This restates the finite majorant theorem at the Gaussian
module boundary without exposing any private exponential proof helper. -/
theorem gaussianUniformExpTailMagnitude_le_geometric (stage : Nat) :
    ExpProofs.uniformExpTailMagnitude stage <=
      ExpProofs.uniformExpTailMagnitude 0 * ((1 : Rat) / 2) ^ stage := by
  have hstart :
      (2 : Rat) <=
        (((ExpProofs.uniformExpTailTerms 0 + 1 : Nat) : Rat) / 2) := by
    simpa [ExpProofs.uniformExpTailTerms, ExpProofs.uniformExpTailStart] using
      RationalMajorant.factorialTailStart_satisfies (2 : Rat)
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := ExpProofs.uniformExpTailTerms 0)
    (by decide +kernel) hstart stage
  change RationalMajorant.factorialTailTerm 2
      (ExpProofs.uniformExpTailTerms stage) <= _
  have hterms : ExpProofs.uniformExpTailTerms stage =
      ExpProofs.uniformExpTailTerms 0 + stage := by
    unfold ExpProofs.uniformExpTailTerms
    omega
  rw [hterms]
  simpa [ExpProofs.uniformExpTailMagnitude] using htail

/-- Balance `stage+1` spatial cells with exponential common-prefix stage
`stage`.  Both displayed error terms now visibly converge by finite rational
schedules. -/
def gaussianExponentialHalfBalancedRule (stage : Nat) :=
  gaussianExponentialHalfRule (stage + 1) stage (Nat.succ_pos stage)

theorem gaussianExponentialHalfBalancedRule_darbouxSum_width_le
    (stage : Nat) :
    (gaussianExponentialHalfBalancedRule stage).darbouxSum.width <=
      308 / ((stage + 1 : Nat) : Rat) +
        8 * (ExpProofs.uniformExpTailMagnitude 0 *
          ((1 : Rat) / 2) ^ stage) := by
  have hbase := gaussianExponentialHalfRule_darbouxSum_width_le
    (stage + 1) stage (Nat.succ_pos stage)
  have htail := gaussianUniformExpTailMagnitude_le_geometric stage
  have htailScaled := Rat.mul_le_mul_of_nonneg_left htail
    (by decide +kernel : (0 : Rat) <= 8)
  change (gaussianExponentialHalfBalancedRule stage).darbouxSum.width <= _
  unfold gaussianExponentialHalfBalancedRule at hbase
  have hmesh : mesh 0 1 (stage + 1) =
      1 / ((stage + 1 : Nat) : Rat) := by
    unfold mesh
    rw [if_neg (Nat.succ_ne_zero stage)]
    grind
  rw [hmesh] at hbase
  have hspatial :
      308 * (1 / ((stage + 1 : Nat) : Rat)) <=
        308 / ((stage + 1 : Nat) : Rat) := by
    grind [Rat.div_def]
  exact Rat.le_trans hbase (rat_add_le_add hspatial htailScaled)

theorem gaussianExponentialHalfBalancedRule_contains_sampledAction
    (stage : Nat) :
    (gaussianExponentialHalfBalancedRule stage).darbouxSum.ContainsInterval
      (QInterval.pointInterval
        (gaussianExponentialHalfBalancedRule stage).sampledAction) :=
  SampledRawDarbouxPartition.darbouxSum_contains_sampledAction _

/-! Reflecting the half-rule uses the evenness of the intended Gaussian
profile only at the level of its finite candidate: the full symmetric box is
twice the `[0,1]` Darboux box.  This remains a finite rational enclosure. -/

def gaussianExponentialSymmetricBalancedBox (stage : Nat) : QInterval :=
  QInterval.scaleByRat 2
    (gaussianExponentialHalfBalancedRule stage).darbouxSum

def gaussianExponentialSymmetricBalancedSampledAction (stage : Nat) : Rat :=
  2 * (gaussianExponentialHalfBalancedRule stage).sampledAction

/-- On the balanced schedule, the reflected midpoint action is within the
explicit rational distance `30 / (stage + 1)` of the integrated even Taylor
prefix chosen by the common exponential evaluator. -/
theorem gaussianEvenIntegralPrefix_sub_exponentialSymmetricBalancedSampledAction_le
    (stage : Nat) :
    qabs (gaussianEvenIntegralPrefix
        (ExpProofs.uniformExpTailTerms stage) 1 -
      gaussianExponentialSymmetricBalancedSampledAction stage) <=
        30 / ((stage + 1 : Nat) : Rat) := by
  have hbase :=
    gaussianEvenIntegralPrefix_sub_exponentialSampledAction_le_thirty_mesh
      (stage + 1) stage (Nat.succ_pos stage)
  have hmesh : mesh 0 1 (stage + 1) =
      1 / ((stage + 1 : Nat) : Rat) := by
    unfold mesh
    rw [if_neg (Nat.succ_ne_zero stage)]
    grind
  rw [hmesh] at hbase
  simpa [gaussianExponentialSymmetricBalancedSampledAction,
    gaussianExponentialHalfBalancedRule, Rat.div_def,
    Rat.mul_assoc] using hbase

/-! ## A direct quadrature raw equivalent to the alternating anchor

At raw stage `n`, quadrature stage `2*n` uses `2*n+1` midpoint cells.  Its
common exponential prefix has `2*n+5` terms, exactly the upper endpoint of
alternating-anchor stage `n+2`.  Thus all overlap proofs below have a literal
rational witness; the anchor is never read by the executable candidate. -/

def gaussianExponentialQuadratureRadius (stage : Nat) : Rat :=
  30 / (((2 * stage + 1 : Nat) : Rat))

def gaussianExponentialQuadratureCandidateRaw : RealCompute where
  compute := fun stage =>
    QInterval.expand
      (QInterval.pointInterval
        (gaussianExponentialSymmetricBalancedSampledAction (2 * stage)))
      (gaussianExponentialQuadratureRadius stage)

theorem gaussianExponentialQuadratureCandidateRaw_contains_prefix
    (stage : Nat) :
    (gaussianExponentialQuadratureCandidateRaw.compute stage).ContainsInterval
      (QInterval.pointInterval
        (gaussianEvenIntegralPrefix (2 * stage + 5) 1)) := by
  have hclose :=
    gaussianEvenIntegralPrefix_sub_exponentialSymmetricBalancedSampledAction_le
      (2 * stage)
  have hterms : ExpProofs.uniformExpTailTerms (2 * stage) =
      2 * stage + 5 := by
    have hstart : ExpProofs.uniformExpTailStart = 5 := by decide +kernel
    unfold ExpProofs.uniformExpTailTerms
    rw [hstart]
    omega
  rw [hterms] at hclose
  unfold gaussianExponentialQuadratureCandidateRaw
    gaussianExponentialQuadratureRadius QInterval.expand
    QInterval.pointInterval QInterval.ContainsInterval
  constructor
  · have hneg := neg_qabs_le_self
      (gaussianEvenIntegralPrefix (2 * stage + 5) 1 -
        gaussianExponentialSymmetricBalancedSampledAction (2 * stage))
    grind
  · have hself := self_le_qabs
      (gaussianEvenIntegralPrefix (2 * stage + 5) 1 -
        gaussianExponentialSymmetricBalancedSampledAction (2 * stage))
    grind

theorem gaussianUnitIntegralRaw_contains_quadraturePrefix
    (stage : Nat) :
    (gaussianUnitIntegralRaw.compute stage).ContainsInterval
      (QInterval.pointInterval
        (gaussianEvenIntegralPrefix (2 * stage + 5) 1)) := by
  rw [gaussianUnitIntegralRaw_compute_eq_prefix_interval]
  have hnest := gaussianUnitIntegralRaw_valid.2.1
    stage (stage + 2) (by omega)
  rw [gaussianUnitIntegralRaw_compute_eq_prefix_interval,
    gaussianUnitIntegralRaw_compute_eq_prefix_interval] at hnest
  unfold QInterval.ContainsInterval QInterval.pointInterval
  constructor
  · exact Rat.le_trans hnest.1 hnest.2.1
  · simpa only [show 2 * (stage + 2) + 1 = 2 * stage + 5 by omega]
      using hnest.2.2

theorem gaussianExponentialQuadratureCandidateRaw_equiv_anchor :
    gaussianExponentialQuadratureCandidateRaw.Equiv
      gaussianUnitIntegralRaw := by
  intro stage
  apply (RealCompute.compareAt_overlap_iff
    gaussianExponentialQuadratureCandidateRaw gaussianUnitIntegralRaw
      stage stage).2
  have hc := gaussianExponentialQuadratureCandidateRaw_contains_prefix stage
  have ha := gaussianUnitIntegralRaw_contains_quadraturePrefix stage
  unfold QInterval.ContainsInterval QInterval.pointInterval at hc ha
  exact ⟨Rat.le_trans hc.1 ha.2, Rat.le_trans ha.1 hc.2⟩

theorem gaussianExponentialQuadratureCandidateRaw_width
    (stage : Nat) :
    (gaussianExponentialQuadratureCandidateRaw.compute stage).width =
      60 / (((2 * stage + 1 : Nat) : Rat)) := by
  unfold gaussianExponentialQuadratureCandidateRaw
    gaussianExponentialQuadratureRadius
  rw [QInterval.expand_width, QInterval.pointInterval_width]
  grind [Rat.div_def, Rat.mul_assoc]

theorem gaussianExponentialQuadratureCandidateRaw_width_le_natRate
    (stage : Nat) :
    (gaussianExponentialQuadratureCandidateRaw.compute stage).width <=
      60 / (((stage + 1 : Nat) : Rat)) := by
  rw [gaussianExponentialQuadratureCandidateRaw_width]
  have hrecip := Series.one_div_nat_antitone_series
    (n := stage + 1) (m := 2 * stage + 1)
    (by omega) (by omega) (by omega)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
    (by decide +kernel : (0 : Rat) <= 60)
  simpa [Rat.div_def, Rat.mul_assoc] using hscaled

theorem gaussianExponentialQuadratureCandidateRaw_widths_shrink :
    RealCompute.WidthsShrinkToZero
      gaussianExponentialQuadratureCandidateRaw.compute :=
  shrinksToZero_of_natOverSuccBound
    gaussianExponentialQuadratureCandidateRaw_width_le_natRate

/-- A public radius covering the alternating anchor at the same raw stage.
It is proof data for stabilization; the stabilized computation itself only
reads quadrature candidates and this rational schedule. -/
def gaussianExponentialQuadratureStabilizationRadius (stage : Nat) : Rat :=
  2 / (((stage + 1 : Nat) : Rat))

theorem gaussianUnitIntegralRaw_width_le_quadratureStabilizationRadius
    (stage : Nat) :
    (gaussianUnitIntegralRaw.compute stage).width <=
      gaussianExponentialQuadratureStabilizationRadius stage := by
  have hbase := gaussianUnitIntegralRaw_width_le_natRate stage
  have hrecip := Series.one_div_nat_antitone_series
    (n := stage + 1) (m := 2 * stage + 1)
    (by omega) (by omega) (by omega)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
    (by decide +kernel : (0 : Rat) <= 2)
  exact Rat.le_trans hbase (by
    unfold gaussianExponentialQuadratureStabilizationRadius
    simpa [Rat.div_def, Rat.mul_assoc] using hscaled)

theorem gaussianExponentialQuadratureStabilizationRadius_shrinks :
    ShrinksToZero gaussianExponentialQuadratureStabilizationRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 2)
  intro stage
  exact Rat.le_refl

/-- A nested raw evaluator computed solely from finite rational Gaussian
quadratures.  Prefix stabilization intersects the finitely many widened
quadrature intervals seen so far; the alternating raw appears only in the
proof that these explicit intersections remain nonempty. -/
def gaussianExponentialQuadratureIntegralRaw : RealCompute :=
  RealCompute.prefixStabilize gaussianExponentialQuadratureCandidateRaw
    gaussianExponentialQuadratureStabilizationRadius

theorem gaussianExponentialQuadratureIntegralRaw_valid :
    gaussianExponentialQuadratureIntegralRaw.Valid := by
  unfold gaussianExponentialQuadratureIntegralRaw
  exact RealCompute.prefixStabilize_valid
    gaussianExponentialQuadratureCandidateRaw_widths_shrink
    gaussianUnitIntegralRaw_valid
    gaussianExponentialQuadratureCandidateRaw_equiv_anchor
    gaussianUnitIntegralRaw_width_le_quadratureStabilizationRadius
    gaussianExponentialQuadratureStabilizationRadius_shrinks

theorem gaussianExponentialQuadratureIntegralRaw_equiv_gaussianUnitIntegralRaw :
    gaussianExponentialQuadratureIntegralRaw.Equiv
      gaussianUnitIntegralRaw := by
  unfold gaussianExponentialQuadratureIntegralRaw
  exact RealCompute.prefixStabilize_equiv_anchor
    gaussianUnitIntegralRaw_valid
    gaussianExponentialQuadratureCandidateRaw_equiv_anchor
    gaussianUnitIntegralRaw_width_le_quadratureStabilizationRadius

theorem gaussianExponentialQuadratureIntegralRaw_width_le_natRate
    (stage : Nat) :
    (gaussianExponentialQuadratureIntegralRaw.compute stage).width <=
      64 / (((stage + 1 : Nat) : Rat)) := by
  have hcontain := RealCompute.prefixStabilize_contained_in_current_expand
    gaussianExponentialQuadratureCandidateRaw
    gaussianExponentialQuadratureStabilizationRadius stage
  have hwidth := QInterval.width_le_of_contains hcontain
  rw [QInterval.expand_width] at hwidth
  have hcandidate :=
    gaussianExponentialQuadratureCandidateRaw_width_le_natRate stage
  calc
    (gaussianExponentialQuadratureIntegralRaw.compute stage).width <=
        (gaussianExponentialQuadratureCandidateRaw.compute stage).width +
          2 * gaussianExponentialQuadratureStabilizationRadius stage := by
      simpa [gaussianExponentialQuadratureIntegralRaw] using hwidth
    _ <= 60 / (((stage + 1 : Nat) : Rat)) +
          2 * gaussianExponentialQuadratureStabilizationRadius stage :=
      rat_add_le_add hcandidate Rat.le_refl
    _ = 64 / (((stage + 1 : Nat) : Rat)) := by
      unfold gaussianExponentialQuadratureStabilizationRadius
      grind [Rat.div_def, Rat.mul_assoc]

theorem gaussianExponentialSymmetricBalancedBox_contains_sampledAction
    (stage : Nat) :
    (gaussianExponentialSymmetricBalancedBox stage).ContainsInterval
      (QInterval.pointInterval
        (gaussianExponentialSymmetricBalancedSampledAction stage)) := by
  have hscaled := QInterval.scaleByRat_contains_of_nonneg
    (by decide +kernel : (0 : Rat) <= 2)
    (gaussianExponentialHalfBalancedRule_contains_sampledAction stage)
  simpa [gaussianExponentialSymmetricBalancedBox,
    gaussianExponentialSymmetricBalancedSampledAction,
    QInterval.scaleByRat, QInterval.pointInterval] using hscaled

theorem gaussianExponentialSymmetricBalancedBox_width_le
    (stage : Nat) :
    (gaussianExponentialSymmetricBalancedBox stage).width <=
      2 * (308 / ((stage + 1 : Nat) : Rat) +
        8 * (ExpProofs.uniformExpTailMagnitude 0 *
          ((1 : Rat) / 2) ^ stage)) := by
  rw [gaussianExponentialSymmetricBalancedBox,
    QInterval.scaleByRat_width_of_nonneg (by decide +kernel)]
  exact Rat.mul_le_mul_of_nonneg_left
    (gaussianExponentialHalfBalancedRule_darbouxSum_width_le stage)
    (by decide +kernel)

/-! A first literal common-stage bridge.  Both sides below are executable
rational boxes: the left is the nested alternating raw whose endpoints are
integrated Taylor prefixes, while the right is assembled from common-stage
exponential cell boxes. -/
theorem gaussianUnitIntegralRaw_stage_one_overlaps_exponentialBox_stage_four :
    QInterval.Overlaps ((gaussianUnitIntegralRaw).compute 1)
      (gaussianExponentialSymmetricBalancedBox 4) := by
  rw [gaussianUnitIntegralRaw_stage_one]
  unfold QInterval.Overlaps
  constructor <;> decide +kernel

/-- The literal overlap certificate yields a quantitative comparison between
the rational midpoint of the alternating anchor and the common-stage sampled
quadrature action.  The error budget is only the sum of the two displayed
finite box widths. -/
theorem gaussianAnchorMidpoint_sub_exponentialSample_stage_four_le :
    qabs (((gaussianUnitIntegralRaw.compute 1).midpoint) -
      gaussianExponentialSymmetricBalancedSampledAction 4) <=
      (gaussianUnitIntegralRaw.compute 1).width +
        (gaussianExponentialSymmetricBalancedBox 4).width := by
  let I := gaussianUnitIntegralRaw.compute 1
  let J := gaussianExponentialSymmetricBalancedBox 4
  have hI0 : 0 <= I.width := gaussianUnitIntegralRaw_valid.1 1
  have hIordered : I.lo <= I.hi := by
    change 0 <= I.hi - I.lo at hI0
    grind
  have hImid : I.ContainsInterval (QInterval.pointInterval I.midpoint) :=
    QInterval.midpoint_mem hIordered
  have hJsample : J.ContainsInterval
      (QInterval.pointInterval
        (gaussianExponentialSymmetricBalancedSampledAction 4)) :=
    gaussianExponentialSymmetricBalancedBox_contains_sampledAction 4
  have hJ0 : 0 <= J.width := by
    have h := hJsample
    unfold QInterval.ContainsInterval QInterval.pointInterval at h
    change 0 <= J.hi - J.lo
    grind
  have hHullMid := (QInterval.hull_contains_left I J).trans hImid
  have hHullSample := (QInterval.hull_contains_right I J).trans hJsample
  calc
    qabs (I.midpoint -
        gaussianExponentialSymmetricBalancedSampledAction 4) <=
        (QInterval.hull I J).width :=
      QInterval.qabs_sub_le_width_of_contains_points
        hHullMid hHullSample
    _ <= I.width + J.width :=
      QInterval.hull_width_le_add_of_overlaps hI0 hJ0
        gaussianUnitIntegralRaw_stage_one_overlaps_exponentialBox_stage_four

/-- One coarse but genuine range certificate for the Gaussian quadratic
profile on `[-1,1]`.  It is deliberately finite and rational. -/
def gaussianQuadraticWholeCell :
    SampledDarbouxCell gaussianQuadraticProfile (-1) 1 where
  cell := RationalSubinterval.whole (-1) 1 (by decide +kernel)
  sample := 0
  sample_mem := by
    change (-1 : Rat) <= 0 /\ (0 : Rat) <= 1
    constructor <;> decide +kernel
  range := { lo := 0, hi := 1 }
  range_contains := by
    intro x hx
    have hqabs : qabs x <= 1 := by
      apply qabs_le_of_neg_le_le
      · exact hx.1
      · exact hx.2
    have hsquareNonnegative := rat_square_nonneg_basic x
    have hsquareAbs : qabs (x * x) <= 1 := by
      rw [qabs_mul]
      simpa using rat_mul_le_mul_of_nonneg (qabs_nonneg x) hqabs
        (qabs_nonneg x) hqabs
    rw [qabs_eq_self_of_nonneg hsquareNonnegative] at hsquareAbs
    unfold gaussianQuadraticProfile
    constructor <;> grind [Rat.sub_eq_add_neg]

theorem gaussianQuadraticWholeCell_sampledAction :
    SampledDarbouxCells.sampledAction [gaussianQuadraticWholeCell] = 2 := by
  decide +kernel

theorem gaussianQuadraticWholeCell_oscillationBudget :
    SampledDarbouxCells.oscillationBudget [gaussianQuadraticWholeCell] = 2 := by
  decide +kernel

theorem gaussianEvenIntegralPrefix_two_one :
    gaussianEvenIntegralPrefix 2 1 = 4 / 3 := by
  decide +kernel

/-- The exactly term-integrated quadratic Gaussian prefix and its one-cell
sampled rectangle lie in the same Darboux enclosure.  The conclusion is an
instance of the generic finite comparison, not an appeal to an integral
functional. -/
theorem gaussianQuadraticPrefix_candidate_sub_sampledAction_le :
    qabs (gaussianEvenIntegralPrefix 2 1 -
      SampledDarbouxCells.sampledAction [gaussianQuadraticWholeCell]) <=
      SampledDarbouxCells.oscillationBudget [gaussianQuadraticWholeCell] := by
  apply SampledDarbouxCells.qabs_candidate_sub_sampledAction_le
  rw [gaussianEvenIntegralPrefix_two_one]
  simp [SampledDarbouxCells.darbouxSum, gaussianQuadraticWholeCell,
    SampledDarbouxCell.darbouxBox, RationalSubinterval.scaleBound,
    RationalSubinterval.width, QInterval.scaleByRat, QInterval.addInterval,
    QInterval.pointInterval, QInterval.ContainsInterval]
  constructor <;> decide +kernel

/-- The positive rational exponential-box weight used at the two outer
nodes. -/
def gaussianStencilOuterWeight : Rat := gaussianTailBoxUpper 1 20

/-- The positive rational exponential-box weight at the central node. -/
def gaussianStencilCenterWeight : Rat := gaussianTailBoxUpper 0 20

theorem gaussianStencilOuterWeight_positive :
    0 < gaussianStencilOuterWeight := by decide +kernel

theorem gaussianStencilCenterWeight_positive :
    0 < gaussianStencilCenterWeight := by decide +kernel

/-- Unnormalized three-node Gaussian-shaped data at one scale. -/
def gaussianThreePointData (stage : Nat) : FinitePositiveKernelData where
  samples :=
    [ { point := 0, weight := gaussianStencilCenterWeight },
      { point := -reciprocalStageRadius stage,
        weight := gaussianStencilOuterWeight },
      { point := reciprocalStageRadius stage,
        weight := gaussianStencilOuterWeight } ]
  weights_nonnegative := by
    intro sample hsample
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsample
    rcases hsample with hsample | hsample | hsample
    · rw [hsample]
      exact Rat.le_of_lt gaussianStencilCenterWeight_positive
    · rw [hsample]
      exact Rat.le_of_lt gaussianStencilOuterWeight_positive
    · rw [hsample]
      exact Rat.le_of_lt gaussianStencilOuterWeight_positive
  totalWeight_positive := by
    simp only [WeightedPoint.totalWeight]
    have houter := gaussianStencilOuterWeight_positive
    have hcenter := gaussianStencilCenterWeight_positive
    grind

/-- Exact rational normalization of the three Gaussian-shaped weights. -/
def gaussianThreePointKernel (stage : Nat) : FiniteProbabilityKernel :=
  (gaussianThreePointData stage).normalized

theorem gaussianThreePointKernel_action (stage : Nat) (f : Rat -> Rat) :
    (gaussianThreePointKernel stage).action f =
      (WeightedPoint.totalWeight (gaussianThreePointData stage).samples)⁻¹ *
        WeightedPoint.action (gaussianThreePointData stage).samples f :=
  FinitePositiveKernelData.normalized_action _ _

theorem gaussianThreePointData_support
    (stage : Nat) (sample : WeightedPoint)
    (hsample : sample ∈ (gaussianThreePointData stage).samples) :
    qabs sample.point <= reciprocalStageRadius stage := by
  have hradius : 0 <= reciprocalStageRadius stage :=
    Rat.le_of_lt (reciprocalStageRadius_positive stage)
  simp only [gaussianThreePointData, List.mem_cons,
    List.not_mem_nil, or_false] at hsample
  rcases hsample with hsample | hsample | hsample
  · rw [hsample]
    simp [qabs]
    exact hradius
  · rw [hsample, qabs_neg, qabs_eq_self_of_nonneg hradius]
    exact Rat.le_refl
  · rw [hsample, qabs_eq_self_of_nonneg hradius]
    exact Rat.le_refl

theorem gaussianThreePointData_totalWeight_eq (stage : Nat) :
    WeightedPoint.totalWeight (gaussianThreePointData stage).samples =
      gaussianStencilCenterWeight + 2 * gaussianStencilOuterWeight := by
  unfold gaussianThreePointData
  simp only [WeightedPoint.totalWeight]
  grind

theorem gaussianThreePointKernel_support
    (stage : Nat) (sample : WeightedPoint)
    (hsample : sample ∈ (gaussianThreePointKernel stage).samples) :
    qabs sample.point <= reciprocalStageRadius stage :=
  (gaussianThreePointData stage).normalized_support
    (reciprocalStageRadius stage)
    (gaussianThreePointData_support stage) sample hsample

/-- The normalized central node of the three-point stencil. -/
def gaussianThreePointCentralSamples (stage : Nat) : List WeightedPoint :=
  WeightedPoint.scaleWeights
    (WeightedPoint.totalWeight (gaussianThreePointData stage).samples)⁻¹
    [ { point := 0, weight := gaussianStencilCenterWeight } ]

/-- The two normalized outer nodes, regarded as the finite tail. -/
def gaussianThreePointTailSamples (stage : Nat) : List WeightedPoint :=
  WeightedPoint.scaleWeights
    (WeightedPoint.totalWeight (gaussianThreePointData stage).samples)⁻¹
    [ { point := -reciprocalStageRadius stage,
        weight := gaussianStencilOuterWeight },
      { point := reciprocalStageRadius stage,
        weight := gaussianStencilOuterWeight } ]

theorem gaussianThreePointKernel_samples_split (stage : Nat) :
    (gaussianThreePointKernel stage).samples =
      gaussianThreePointCentralSamples stage ++
        gaussianThreePointTailSamples stage := by
  rfl

/-- Exact normalized mass assigned to the two outer nodes. -/
def gaussianThreePointTailMass (stage : Nat) : Rat :=
  WeightedPoint.totalWeight (gaussianThreePointTailSamples stage)

theorem gaussianThreePointTailMass_eq (stage : Nat) :
    gaussianThreePointTailMass stage =
      (2 * gaussianStencilOuterWeight) /
        (gaussianStencilCenterWeight + 2 * gaussianStencilOuterWeight) := by
  unfold gaussianThreePointTailMass gaussianThreePointTailSamples
    gaussianThreePointData
  simp only [WeightedPoint.scaleWeights, WeightedPoint.totalWeight]
  grind [Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.mul_comm,
    Rat.mul_assoc]

/-- For the three-point family, only the two outer nodes contribute to the
error around `f 0`; their exact normalized mass multiplies the supplied outer
node error. -/
theorem gaussianThreePointKernel_action_central_tail_le
    (stage : Nat) (f : Rat -> Rat) (tailError : Rat)
    (outer_error : forall sample,
      sample ∈ gaussianThreePointTailSamples stage ->
        qabs (f sample.point - f 0) <= tailError) :
    qabs ((gaussianThreePointKernel stage).action f - f 0) <=
      tailError * gaussianThreePointTailMass stage := by
  have hsplit := (gaussianThreePointKernel stage).action_approximates_center_of_split
    f (f 0) 0 tailError
    (gaussianThreePointCentralSamples stage)
    (gaussianThreePointTailSamples stage)
    (gaussianThreePointKernel_samples_split stage)
    (by
      intro sample hsample
      simp only [gaussianThreePointCentralSamples,
        WeightedPoint.scaleWeights, List.mem_cons,
        List.not_mem_nil, or_false] at hsample
      rw [hsample]
      change qabs (f 0 - f 0) <= 0
      grind [qabs])
    outer_error
  unfold gaussianThreePointTailMass
  grind

/-! ## Stability between two stencil scales -/

/-- A single explicitly paired source/target sample. -/
def coupledWeightedPoint
    (sourcePoint sourceWeight targetPoint targetWeight : Rat) :
    WeightedPointCoupling :=
  { source := { point := sourcePoint, weight := sourceWeight }
    target := { point := targetPoint, weight := targetWeight } }

/-- Explicit pairing of the center and two outer nodes at two stages. -/
def gaussianThreePointStageCoupling
    (sourceStage targetStage : Nat) : List WeightedPointCoupling :=
  let sourceScale :=
    (WeightedPoint.totalWeight (gaussianThreePointData sourceStage).samples)⁻¹
  let targetScale :=
    (WeightedPoint.totalWeight (gaussianThreePointData targetStage).samples)⁻¹
  [ coupledWeightedPoint 0
      (sourceScale * gaussianStencilCenterWeight) 0
      (targetScale * gaussianStencilCenterWeight),
    coupledWeightedPoint (-reciprocalStageRadius sourceStage)
      (sourceScale * gaussianStencilOuterWeight)
      (-reciprocalStageRadius targetStage)
      (targetScale * gaussianStencilOuterWeight),
    coupledWeightedPoint (reciprocalStageRadius sourceStage)
      (sourceScale * gaussianStencilOuterWeight)
      (reciprocalStageRadius targetStage)
      (targetScale * gaussianStencilOuterWeight) ]

theorem gaussianThreePointStageCoupling_sourceSamples
    (sourceStage targetStage : Nat) :
    WeightedPointCoupling.sourceSamples
        (gaussianThreePointStageCoupling sourceStage targetStage) =
      (gaussianThreePointKernel sourceStage).samples := by
  rfl

theorem gaussianThreePointStageCoupling_targetSamples
    (sourceStage targetStage : Nat) :
    WeightedPointCoupling.targetSamples
        (gaussianThreePointStageCoupling sourceStage targetStage) =
      (gaussianThreePointKernel targetStage).samples := by
  rfl

theorem gaussianThreePointStageCoupling_weights_eq
    (sourceStage targetStage : Nat) (pair : WeightedPointCoupling)
    (hpair : pair ∈ gaussianThreePointStageCoupling sourceStage targetStage) :
    pair.target.weight = pair.source.weight := by
  simp only [gaussianThreePointStageCoupling, List.mem_cons,
    List.not_mem_nil, or_false] at hpair
  rcases hpair with hpair | hpair | hpair
  · rw [hpair]
    unfold coupledWeightedPoint
    rw [gaussianThreePointData_totalWeight_eq sourceStage,
      gaussianThreePointData_totalWeight_eq targetStage]
  · rw [hpair]
    unfold coupledWeightedPoint
    rw [gaussianThreePointData_totalWeight_eq sourceStage,
      gaussianThreePointData_totalWeight_eq targetStage]
  · rw [hpair]
    unfold coupledWeightedPoint
    rw [gaussianThreePointData_totalWeight_eq sourceStage,
      gaussianThreePointData_totalWeight_eq targetStage]

/-- Two stages of the normalized Gaussian-shaped stencil differ only by the
supplied errors for transporting the center and the two outer nodes.  Exact
normalization makes the common positive weights sum to one. -/
theorem gaussianThreePointKernel_action_stage_stable
    (sourceStage targetStage : Nat)
    (sourceFunction targetFunction : Rat -> Rat) (pointError : Rat)
    (center_error :
      qabs (targetFunction 0 - sourceFunction 0) <= pointError)
    (negative_outer_error :
      qabs (targetFunction (-reciprocalStageRadius targetStage) -
        sourceFunction (-reciprocalStageRadius sourceStage)) <= pointError)
    (positive_outer_error :
      qabs (targetFunction (reciprocalStageRadius targetStage) -
        sourceFunction (reciprocalStageRadius sourceStage)) <= pointError) :
    qabs ((gaussianThreePointKernel targetStage).action targetFunction -
      (gaussianThreePointKernel sourceStage).action sourceFunction) <=
        pointError := by
  let pairs := gaussianThreePointStageCoupling sourceStage targetStage
  have hsourceWeights : forall pair, pair ∈ pairs ->
      0 <= pair.source.weight := by
    intro pair hpair
    apply (gaussianThreePointKernel sourceStage).weights_nonnegative pair.source
    rw [← gaussianThreePointStageCoupling_sourceSamples
      sourceStage targetStage]
    exact List.mem_map_of_mem hpair
  have htransport : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point -
        sourceFunction pair.source.point) <= pointError := by
    intro pair hpair
    simp only [pairs, gaussianThreePointStageCoupling, List.mem_cons,
      List.not_mem_nil, or_false] at hpair
    rcases hpair with hpair | hpair | hpair
    · rw [hpair]
      exact center_error
    · rw [hpair]
      exact negative_outer_error
    · rw [hpair]
      exact positive_outer_error
  have h :=
    WeightedPointCoupling.qabs_action_targetSamples_sub_action_sourceSamples_le_of_weights_eq
      pairs sourceFunction targetFunction pointError hsourceWeights
      (gaussianThreePointStageCoupling_weights_eq sourceStage targetStage)
      htransport
  rw [gaussianThreePointStageCoupling_sourceSamples,
    gaussianThreePointStageCoupling_targetSamples,
    (gaussianThreePointKernel sourceStage).totalWeight_eq_one] at h
  unfold FiniteProbabilityKernel.action
  grind

/-- Lipschitz specialization of stage stability.  Because normalization is
stage-independent, moving from one scale to another costs only the distance
between their two outer radii. -/
theorem gaussianThreePointKernel_action_stage_stable_of_lipschitz
    (sourceStage targetStage : Nat) (f : Rat -> Rat) (lipschitz : Rat)
    (lipschitz_bound : forall x y : Rat,
      qabs (f x - f y) <= lipschitz * qabs (x - y)) :
    qabs ((gaussianThreePointKernel targetStage).action f -
      (gaussianThreePointKernel sourceStage).action f) <=
        lipschitz * qabs (reciprocalStageRadius targetStage -
          reciprocalStageRadius sourceStage) := by
  have hpositive := lipschitz_bound
    (reciprocalStageRadius targetStage)
    (reciprocalStageRadius sourceStage)
  apply gaussianThreePointKernel_action_stage_stable
    sourceStage targetStage f f
    (lipschitz * qabs (reciprocalStageRadius targetStage -
      reciprocalStageRadius sourceStage))
  · have hnonnegative :
        0 <= lipschitz * qabs (reciprocalStageRadius targetStage -
          reciprocalStageRadius sourceStage) :=
      Rat.le_trans (qabs_nonneg _) hpositive
    grind [qabs]
  · have hnegative := lipschitz_bound
      (-reciprocalStageRadius targetStage)
      (-reciprocalStageRadius sourceStage)
    have hdifference :
        -reciprocalStageRadius targetStage -
            -reciprocalStageRadius sourceStage =
          -(reciprocalStageRadius targetStage -
            reciprocalStageRadius sourceStage) := by
      grind
    rw [hdifference, qabs_neg] at hnegative
    exact hnegative
  · exact hpositive

/-- The normalized Gaussian-shaped stencil, equipped with the same explicit
denominator schedule as the two-point regression family. -/
def gaussianThreePointApproximateIdentity : FiniteApproximateIdentity where
  kernel := gaussianThreePointKernel
  radius := reciprocalStageRadius
  radius_nonnegative := fun stage =>
    Rat.le_of_lt (reciprocalStageRadius_positive stage)
  support_radius := gaussianThreePointKernel_support
  schedule := fun requested => requested.den
  schedule_spec := by
    intro requested hrequested
    exact one_div_den_succ_le_of_pos hrequested

theorem gaussianThreePointApproximateIdentity_action_rate
    (f : Rat -> Rat) (lipschitz requestedError : Rat)
    (lipschitz_positive : 0 < lipschitz)
    (requestedError_positive : 0 < requestedError)
    (lipschitz_at_selected_nodes : forall sample,
      sample ∈ (gaussianThreePointKernel
        ((requestedError / lipschitz).den)).samples ->
      qabs (f sample.point - f 0) <=
        lipschitz * qabs sample.point) :
    qabs
      ((gaussianThreePointKernel
        ((requestedError / lipschitz).den)).action f - f 0) <=
          requestedError :=
  gaussianThreePointApproximateIdentity.action_rate
    f lipschitz requestedError lipschitz_positive requestedError_positive
    lipschitz_at_selected_nodes

end ComputableAnalysis


