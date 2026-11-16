-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GaussianDifferential
-- name    : liuyao_ca_fd889115_k1_Analysis_GaussianDifferential
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:38:01.070084+00:00
-- url     : https://prove2.me/theorems/4ec2acbf-a7ae-4b84-8a96-60aafb2adbf3
-- title:
--   Computable analysis · GaussianDifferential · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GaussianDifferential.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianRadiusQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteDerivativeLimit

set_option autoImplicit true

/-!
# The represented Gaussian ODE

This file packages the normalized full-line Gaussian as a rational-input
interval function and defines its concrete derivative candidate.  The
candidate is chosen by the Gaussian ODE itself, so the represented identity

`D G(x) + 2 x G(x) = 0`

is exact up to `RealCompute.Equiv`.  Identifying this candidate with the analytic
derivative is a separate, quantitative obligation: it will be discharged by
passing the finite Taylor-prefix derivative certificates and their scheduled
ODE residual bounds to the represented limit.
-/

namespace ComputableAnalysis

/-! ## Positive factorial models for the reciprocal Gaussian -/

/-- The positive factorial coefficients inserted in even degrees.  Their
finite Taylor prefix is the literal polynomial `sum (x^2)^k/k!` whose
reciprocal is used by `reciprocalGaussianRaw`. -/
def gaussianPositiveEvenTaylorCoeff (n : Nat) : Rat :=
  if n % 2 = 0 then FormalPowerSeries.expCoeff (n / 2) else 0

theorem gaussianPositiveEvenTaylorCoeff_even (k : Nat) :
    gaussianPositiveEvenTaylorCoeff (2 * k) =
      FormalPowerSeries.expCoeff k := by
  simp [gaussianPositiveEvenTaylorCoeff]

theorem gaussianPositiveEvenTaylorCoeff_odd (k : Nat) :
    gaussianPositiveEvenTaylorCoeff (2 * k + 1) = 0 := by
  simp [gaussianPositiveEvenTaylorCoeff]

def gaussianPositiveProfilePrefix (terms : Nat) (x : Rat) : Rat :=
  FinitePolynomial.taylorDerivativePrefix gaussianPositiveEvenTaylorCoeff
    (2 * terms) x

/-- Literal formal derivative of the positive even factorial prefix. -/
def gaussianPositiveProfileFormalDerivativePrefix : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 => fun x =>
      gaussianPositiveProfileFormalDerivativePrefix terms x +
        ((2 * terms : Nat) : Rat) *
          FormalPowerSeries.expCoeff terms * x ^ (2 * terms - 1)

theorem gaussianPositiveProfilePrefix_succ (terms : Nat) (x : Rat) :
    gaussianPositiveProfilePrefix (terms + 1) x =
      gaussianPositiveProfilePrefix terms x +
        FormalPowerSeries.expCoeff terms * x ^ (2 * terms) := by
  unfold gaussianPositiveProfilePrefix
  rw [show 2 * (terms + 1) = (2 * terms + 1) + 1 by omega]
  simp only [FinitePolynomial.taylorDerivativePrefix]
  rw [gaussianPositiveEvenTaylorCoeff_odd, Rat.zero_mul, Rat.add_zero,
    gaussianPositiveEvenTaylorCoeff_even]

theorem gaussianPositiveProfileFormalDerivativePrefix_succ
    (terms : Nat) (x : Rat) :
    gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x =
      gaussianPositiveProfileFormalDerivativePrefix terms x +
        ((2 * terms : Nat) : Rat) *
          FormalPowerSeries.expCoeff terms * x ^ (2 * terms - 1) := by
  rfl

theorem gaussianPositiveProfilePrefix_eq_taylorPrefix
    (terms : Nat) (x : Rat) :
    gaussianPositiveProfilePrefix terms x =
      FinitePolynomial.taylorPrefix gaussianPositiveEvenTaylorCoeff
        (2 * terms) x := by
  unfold gaussianPositiveProfilePrefix
  exact (FinitePolynomial.taylorPrefix_eq_taylorDerivativePrefix
    gaussianPositiveEvenTaylorCoeff (2 * terms) x).symm

theorem gaussianPositiveProfileFormalDerivativePrefix_eq_taylorPrefixShift :
    forall terms x,
      gaussianPositiveProfileFormalDerivativePrefix terms x =
        FinitePolynomial.taylorPrefixShift gaussianPositiveEvenTaylorCoeff
          (2 * terms) x
  | 0, _x => rfl
  | terms + 1, x => by
      rw [gaussianPositiveProfileFormalDerivativePrefix_succ,
        gaussianPositiveProfileFormalDerivativePrefix_eq_taylorPrefixShift
          terms x]
      cases terms with
      | zero =>
          simp [FinitePolynomial.taylorPrefixShift,
            FinitePolynomial.taylorDerivativePrefix,
            FormalPowerSeries.coefficientShift,
            gaussianPositiveEvenTaylorCoeff]
      | succ terms =>
          unfold FinitePolynomial.taylorPrefixShift
          rw [show 2 * (terms + 1 + 1) =
              ((2 * (terms + 1) + 1) + 1) by omega]
          simp only [FinitePolynomial.taylorDerivativePrefix]
          rw [show 2 * (terms + 1) =
              ((2 * terms + 1) + 1) by omega]
          simp only [FinitePolynomial.taylorDerivativePrefix]
          unfold FormalPowerSeries.coefficientShift
          rw [gaussianPositiveEvenTaylorCoeff_odd]
          rw [show 2 * terms + 1 + 1 = 2 * (terms + 1) by omega,
            gaussianPositiveEvenTaylorCoeff_even]
          rw [gaussianPositiveEvenTaylorCoeff_odd]
          push_cast
          grind [Rat.mul_assoc, Rat.mul_comm]

private theorem gaussian_square_pow (x : Rat) (k : Nat) :
    (x * x) ^ k = x ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Rat.pow_succ, ih,
        show 2 * (k + 1) = 2 * k + 2 by omega,
        Rat.pow_succ, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The sparse positive even Taylor polynomial is exactly the executable
positive factorial center used before reciprocal enclosure. -/
theorem gaussianPositiveProfilePrefix_eq_factorialPrefix
    (terms : Nat) (x : Rat) :
    gaussianPositiveProfilePrefix terms x =
      FiniteExponentialProduct.factorialPrefix terms (x * x) := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [gaussianPositiveProfilePrefix_succ, ih,
        FiniteExponentialProduct.factorialPrefix_succ,
        gaussian_square_pow]

/-- Exact derivative identity for the finite positive exponential model.
The derivative loses precisely the final factorial term. -/
theorem gaussianPositiveProfileFormalDerivativePrefix_eq
    (terms : Nat) (x : Rat) :
    gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x =
      2 * x * FiniteExponentialProduct.factorialPrefix terms (x * x) := by
  induction terms with
  | zero =>
      rw [FiniteExponentialProduct.factorialPrefix_zero]
      simp [gaussianPositiveProfileFormalDerivativePrefix]
      grind
  | succ terms ih =>
      rw [gaussianPositiveProfileFormalDerivativePrefix_succ, ih,
        FiniteExponentialProduct.factorialPrefix_succ]
      have hcoeff := congrFun FormalPowerSeries.expCoeff_derivative terms
      change (((terms + 1 : Nat) : Rat)) *
          FormalPowerSeries.expCoeff (terms + 1) =
        FormalPowerSeries.expCoeff terms at hcoeff
      rw [show 2 * (terms + 1) - 1 = 2 * terms + 1 by omega,
        show x ^ (2 * terms + 1) = x ^ (2 * terms) * x by
          rw [Rat.pow_succ]]
      rw [gaussian_square_pow]
      push_cast
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- Every positive factorial model containing its constant term is at least
one.  The slightly stronger two-term hypothesis matches the executable
Gaussian schedules and reuses their published `1+x^2` lower bound. -/
theorem gaussianPositiveProfilePrefix_one_le
    {terms : Nat} (hterms : 2 <= terms) (x : Rat) :
    1 <= gaussianPositiveProfilePrefix terms x := by
  rw [gaussianPositiveProfilePrefix_eq_factorialPrefix]
  have hlower := FiniteExponentialProduct.factorialPrefix_ge_one_add
    (rat_square_nonneg_basic x) terms hterms
  exact Rat.le_trans (by
    have hsquare := rat_square_nonneg_basic x
    grind) hlower

/-- Explicit derivative majorant for a finite positive Gaussian prefix on a
symmetric rational box. -/
theorem gaussianPositiveProfileFormalDerivativePrefix_qabs_le
    (terms : Nat) {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) :
    qabs (gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x) <=
      2 * C * FiniteExponentialProduct.factorialPrefix terms (C * C) := by
  rw [gaussianPositiveProfileFormalDerivativePrefix_eq]
  have hxx0 : 0 <= x * x := rat_square_nonneg_basic x
  have hCC0 : 0 <= C * C := Rat.mul_nonneg hC hC
  have hxxCC : x * x <= C * C := by
    have hleft : x <= C := Rat.le_trans (self_le_qabs x) hx
    have hright : -C <= x := by
      have hneg := neg_qabs_le_self x
      grind
    by_cases hx0 : 0 <= x
    · exact rat_mul_le_mul_of_nonneg hx0 hleft hx0 hleft
    · have hxneg : x <= 0 := by grind
      have hnegx : 0 <= -x := by grind
      have hnegxC : -x <= C := by grind
      have hsquare : (-x) * (-x) <= C * C :=
        rat_mul_le_mul_of_nonneg hnegx hnegxC hnegx hnegxC
      grind [Rat.neg_mul, Rat.mul_neg]
  have hprefix := FiniteExponentialProduct.factorialPrefix_mono_input
    hxx0 hxxCC terms
  have hprefix0 := FiniteExponentialProduct.factorialPrefix_nonneg hxx0 terms
  have hprefixC0 := FiniteExponentialProduct.factorialPrefix_nonneg hCC0 terms
  rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg (by decide +kernel),
    qabs_eq_self_of_nonneg hprefix0]
  calc
    2 * qabs x * FiniteExponentialProduct.factorialPrefix terms (x * x) <=
        2 * C * FiniteExponentialProduct.factorialPrefix terms (x * x) := by
          exact Rat.mul_le_mul_of_nonneg_right
            (Rat.mul_le_mul_of_nonneg_left hx (by decide +kernel)) hprefix0
    _ <= 2 * C * FiniteExponentialProduct.factorialPrefix terms (C * C) := by
          exact Rat.mul_le_mul_of_nonneg_left hprefix
            (Rat.mul_nonneg (by decide +kernel) hC)

/-- The positive even factorial model inherits the generic finite Taylor
secant certificate. -/
def gaussianPositiveProfileSecantBound
    (C : Rat) (terms : Nat) (hC1 : 1 <= C) :
    FinitePolynomial.SecantDerivativeBound C
      (gaussianPositiveProfilePrefix terms)
      (gaussianPositiveProfileFormalDerivativePrefix terms) := by
  rw [show gaussianPositiveProfilePrefix terms =
      FinitePolynomial.taylorPrefix gaussianPositiveEvenTaylorCoeff
        (2 * terms) by
    funext x
    exact gaussianPositiveProfilePrefix_eq_taylorPrefix terms x]
  rw [show gaussianPositiveProfileFormalDerivativePrefix terms =
      FinitePolynomial.taylorPrefixShift gaussianPositiveEvenTaylorCoeff
        (2 * terms) by
    funext x
    exact gaussianPositiveProfileFormalDerivativePrefix_eq_taylorPrefixShift
      terms x]
  exact FinitePolynomial.taylorPrefixSecantBound C
    gaussianPositiveEvenTaylorCoeff hC1 (2 * terms)

/-- The same positive-prefix secant certificate presented by factorial-term
recursion.  Its coefficient recurrence is transparent enough for the uniform
majorant proof used by the represented Gaussian schedule. -/
private structure GaussianPositiveProfileSecantData
    (C : Rat) (terms : Nat) where
  coefficient : Rat
  coefficient_nonneg : 0 <= coefficient
  error_bound : forall x h : Rat, h ≠ 0 ->
    qabs x <= C -> qabs (x + h) <= C ->
    qabs (((gaussianPositiveProfilePrefix terms (x + h) -
      gaussianPositiveProfilePrefix terms x) / h) -
      gaussianPositiveProfileFormalDerivativePrefix terms x) <=
      qabs h * coefficient

private def GaussianPositiveProfileSecantData.toBound
    {C : Rat} {terms : Nat} (D : GaussianPositiveProfileSecantData C terms) :
    FinitePolynomial.SecantDerivativeBound C
      (gaussianPositiveProfilePrefix terms)
      (gaussianPositiveProfileFormalDerivativePrefix terms) where
  errorCoefficient := D.coefficient
  errorCoefficient_nonneg := D.coefficient_nonneg
  error_bound := D.error_bound

private def gaussianPositiveProfileRecursiveSecantData
    (C : Rat) (hC1 : 1 <= C) : (terms : Nat) ->
    GaussianPositiveProfileSecantData C terms
  | 0 =>
      { coefficient := 0
        coefficient_nonneg := by decide +kernel
        error_bound :=
          (FinitePolynomial.SecantDerivativeBound.constant C 0).error_bound }
  | 1 => by
      have hcoeff : FormalPowerSeries.expCoeff 0 = 1 := by decide +kernel
      have hf : gaussianPositiveProfilePrefix 1 = fun _x => 1 := by
        funext x
        rw [show 1 = 0 + 1 by omega, gaussianPositiveProfilePrefix_succ,
          hcoeff]
        have hzero : gaussianPositiveProfilePrefix 0 x = 0 := rfl
        rw [hzero]
        rw [Rat.pow_zero, Rat.one_mul]
        exact Rat.zero_add 1
      have hdf : gaussianPositiveProfileFormalDerivativePrefix 1 =
          fun _x => 0 := by
        funext x
        change 0 + 0 * FormalPowerSeries.expCoeff 0 * x ^ 0 = 0
        grind
      refine
        { coefficient := 0
          coefficient_nonneg := by decide +kernel
          error_bound := ?_ }
      intro x h hh hx hxh
      have hbound :=
        (FinitePolynomial.SecantDerivativeBound.constant C 1).error_bound
          x h hh hx hxh
      rw [hf, hdf]
      exact hbound
  | terms + 2 => by
      let D := gaussianPositiveProfileRecursiveSecantData C hC1 (terms + 1)
      let F := D.toBound
      let G := FinitePolynomial.SecantDerivativeBound.scaleRat
        (FormalPowerSeries.expCoeff (terms + 1))
        (FinitePolynomial.monomialSecantDerivativeBound C
          (2 * terms + 1) hC1)
      let H := FinitePolynomial.SecantDerivativeBound.add F G
      have hf : gaussianPositiveProfilePrefix (terms + 2) =
          fun x => gaussianPositiveProfilePrefix (terms + 1) x +
            FormalPowerSeries.expCoeff (terms + 1) *
              x ^ (2 * terms + 1 + 1) := by
        funext x
        rw [show terms + 2 = (terms + 1) + 1 by omega,
          gaussianPositiveProfilePrefix_succ]
        rw [show 2 * (terms + 1) = 2 * terms + 1 + 1 by omega]
      have hdf : gaussianPositiveProfileFormalDerivativePrefix (terms + 2) =
          fun x => gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x +
            FormalPowerSeries.expCoeff (terms + 1) *
              (((2 * terms + 1 + 1 : Nat) : Rat) * x ^ (2 * terms + 1)) := by
        funext x
        rw [show terms + 2 = (terms + 1) + 1 by omega,
          gaussianPositiveProfileFormalDerivativePrefix_succ]
        rw [show 2 * (terms + 1) = 2 * terms + 1 + 1 by omega,
          show 2 * terms + 1 + 1 - 1 = 2 * terms + 1 by omega]
        grind [Rat.mul_assoc, Rat.mul_comm]
      refine {
        coefficient := D.coefficient +
          qabs (FormalPowerSeries.expCoeff (terms + 1)) *
            (qabs (((2 * terms + 1 + 1 : Nat) : Rat)) *
              FinitePolynomial.powerSecantErrorBound C (2 * terms + 1 + 1))
        coefficient_nonneg := Rat.add_nonneg D.coefficient_nonneg
          (Rat.mul_nonneg (qabs_nonneg _)
            (Rat.mul_nonneg (qabs_nonneg _)
              (FinitePolynomial.powerSecantErrorBound_nonneg
                (Rat.le_trans (by decide +kernel) hC1) _)))
        error_bound := ?_ }
      intro x h hh hx hxh
      have hbound := H.error_bound x h hh hx hxh
      rw [hf, hdf]
      simpa [H, F, G, D,
        GaussianPositiveProfileSecantData.toBound,
        FinitePolynomial.SecantDerivativeBound.add,
        FinitePolynomial.SecantDerivativeBound.scaleRat,
        FinitePolynomial.monomialSecantDerivativeBound,
        FinitePolynomial.normalizedMonomialSecantBound] using hbound

/-- The literal finite coefficient accumulated by the recursive positive
factorial-prefix certificate. -/
def gaussianPositiveProfileSecantCoefficient
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) : Rat :=
  (gaussianPositiveProfileRecursiveSecantData C hC1 terms).coefficient

theorem gaussianPositiveProfileSecantCoefficient_nonneg
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) :
    0 <= gaussianPositiveProfileSecantCoefficient C hC1 terms :=
  (gaussianPositiveProfileRecursiveSecantData C hC1 terms).coefficient_nonneg

theorem gaussianPositiveProfileSecantCoefficient_succ_succ
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) :
    gaussianPositiveProfileSecantCoefficient C hC1 (terms + 2) =
      gaussianPositiveProfileSecantCoefficient C hC1 (terms + 1) +
        qabs (FormalPowerSeries.expCoeff (terms + 1)) *
          (qabs (((2 * terms + 1 + 1 : Nat) : Rat)) *
            FinitePolynomial.powerSecantErrorBound C (2 * terms + 1 + 1)) := by
  unfold gaussianPositiveProfileSecantCoefficient
  rw [gaussianPositiveProfileRecursiveSecantData]

private theorem powerSecantErrorBound_even_closed (C : Rat) (k : Nat) :
    FinitePolynomial.powerSecantErrorBound C (2 * k) =
      (k : Rat) * (((2 * k - 1 : Nat) : Rat)) * C ^ (2 * k - 1) := by
  induction k with
  | zero => simp [FinitePolynomial.powerSecantErrorBound]
  | succ k ih =>
      cases k with
      | zero =>
          simp [FinitePolynomial.powerSecantErrorBound]
          grind
      | succ k =>
          rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 by omega,
            FinitePolynomial.powerSecantErrorBound,
            FinitePolynomial.powerSecantErrorBound, ih]
          rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
            show 2 * (k + 1) + 1 + 1 - 1 = 2 * (k + 1) + 1 by omega,
            show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
            Rat.pow_succ, Rat.pow_succ]
          push_cast
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem qabs_expCoeff_eq (k : Nat) :
    qabs (FormalPowerSeries.expCoeff k) =
      FormalPowerSeries.expCoeff k := by
  apply qabs_eq_self_of_nonneg
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2
    (RationalMajorant.factorialRat_pos k))

private theorem gaussianPositiveProfileSecantCoefficient_tail_summand
    (C : Rat) (n : Nat) :
    qabs (FormalPowerSeries.expCoeff (n + 3)) *
        (qabs ((((2 * (n + 2) + 1 + 1 : Nat) : Rat))) *
          FinitePolynomial.powerSecantErrorBound C
            (2 * (n + 2) + 1 + 1)) =
      4 * C ^ 5 * RationalMajorant.factorialTailTerm (C * C) n +
        10 * C ^ 3 * RationalMajorant.factorialTailTerm (C * C) (n + 1) +
        2 * C * RationalMajorant.factorialTailTerm (C * C) (n + 2) := by
  rw [show n + 3 = n + 2 + 1 by omega, qabs_expCoeff_eq,
    show 2 * (n + 2) + 1 + 1 = 2 * (n + 3) by omega,
    powerSecantErrorBound_even_closed]
  have hcast0 : (0 : Rat) <= (((2 * (n + 3) : Nat) : Rat)) := by
    exact_mod_cast (Nat.zero_le (2 * (n + 3)))
  rw [qabs_eq_self_of_nonneg hcast0]
  unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
  rw [FormalPowerSeries.factorialRat_succ,
    FormalPowerSeries.factorialRat_succ,
    FormalPowerSeries.factorialRat_succ]
  have hn1 : (((n + 1 : Nat) : Rat)) = (n : Rat) + 1 := by
    exact_mod_cast (by omega : n + 1 = n + 1)
  have hn2 : (((n + 2 : Nat) : Rat)) = (n : Rat) + 2 := by
    exact_mod_cast (by omega : n + 2 = n + 2)
  have hn3 : (((n + 3 : Nat) : Rat)) = (n : Rat) + 3 := by
    exact_mod_cast (by omega : n + 3 = n + 3)
  have htwo : (((2 * (n + 3) : Nat) : Rat)) = 2 * (n : Rat) + 6 := by
    exact_mod_cast (by omega : 2 * (n + 3) = 2 * n + 6)
  have hodd : (((2 * (n + 3) - 1 : Nat) : Rat)) = 2 * (n : Rat) + 5 := by
    exact_mod_cast (by omega : 2 * (n + 3) - 1 = 2 * n + 5)
  rw [hn1, hn2, hn3, htwo, hodd, Rat.div_def, Rat.div_def,
    Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.inv_mul_rev,
    Rat.inv_mul_rev]
  have hn1ne : (n : Rat) + 1 ≠ 0 := by
    exact Rat.ne_of_gt (by exact_mod_cast (Nat.succ_pos n))
  have hn2ne : (n : Rat) + 2 ≠ 0 := by
    exact Rat.ne_of_gt (by exact_mod_cast (show 0 < n + 2 by omega))
  have hn3ne : (n : Rat) + 3 ≠ 0 := by
    exact Rat.ne_of_gt (by exact_mod_cast (show 0 < n + 3 by omega))
  have hc1 : ((n : Rat) + 1) * ((n : Rat) + 1)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hn1ne
  have hc2 : ((n : Rat) + 2) * ((n : Rat) + 2)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hn2ne
  have hc3 : ((n : Rat) + 3) * ((n : Rat) + 3)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hn3ne
  have hsquarePow : forall m : Nat, (C * C) ^ m = C ^ (2 * m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Rat.pow_succ, ih,
          show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          Rat.pow_succ, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hsquarePow n, hsquarePow (n + 1), hsquarePow (n + 2)]
  rw [show 2 * (n + 3) - 1 = 2 * n + 5 by omega,
    show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    show 2 * (n + 2) = (((2 * n + 1) + 1) + 1) + 1 by omega,
    Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, Rat.pow_succ,
    Rat.pow_succ]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem gaussianPositiveProfileSecantCoefficient_eq_factorialPartials
    (C : Rat) (hC1 : 1 <= C) (n : Nat) :
    let A := C * C
    gaussianPositiveProfileSecantCoefficient C hC1 (n + 3) =
      2 * C + 12 * C ^ 3 +
        4 * C ^ 5 * RationalMajorant.factorialTailPartial A 0 n +
        10 * C ^ 3 * RationalMajorant.factorialTailPartial A 1 n +
        2 * C * RationalMajorant.factorialTailPartial A 2 n := by
  let A := C * C
  induction n with
  | zero =>
      rw [show 0 + 3 = 1 + 2 by omega,
        gaussianPositiveProfileSecantCoefficient_succ_succ,
        show 1 + 1 = 0 + 2 by omega,
        gaussianPositiveProfileSecantCoefficient_succ_succ]
      have hone : gaussianPositiveProfileSecantCoefficient C hC1 1 = 0 := by
        rfl
      rw [hone]
      simp [RationalMajorant.factorialTailPartial,
        FinitePolynomial.powerSecantErrorBound,
        FormalPowerSeries.expCoeff, factorialRat, factorial]
      have hq1 : qabs ((1 : Rat) / 1) = 1 := by decide +kernel
      have hq2 : qabs (2 : Rat) = 2 := by decide +kernel
      have hq4 : qabs (4 : Rat) = 4 := by decide +kernel
      have hqhalf : qabs ((1 : Rat) / 2) = (2 : Rat)⁻¹ := by decide +kernel
      rw [hq1, hq2, hq4, hqhalf]
      have hhalf : (2 : Rat)⁻¹ * 4 = 2 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm]
  | succ n ih =>
      rw [show n + 1 + 3 = (n + 2) + 2 by omega,
        gaussianPositiveProfileSecantCoefficient_succ_succ,
        show n + 2 + 1 = n + 3 by omega, ih,
        gaussianPositiveProfileSecantCoefficient_tail_summand]
      change
        2 * C + 12 * C ^ 3 +
              4 * C ^ 5 * RationalMajorant.factorialTailPartial A 0 n +
            10 * C ^ 3 * RationalMajorant.factorialTailPartial A 1 n +
          2 * C * RationalMajorant.factorialTailPartial A 2 n +
            (4 * C ^ 5 * RationalMajorant.factorialTailTerm A n +
              10 * C ^ 3 * RationalMajorant.factorialTailTerm A (n + 1) +
              2 * C * RationalMajorant.factorialTailTerm A (n + 2)) =
          2 * C + 12 * C ^ 3 +
              4 * C ^ 5 *
                (RationalMajorant.factorialTailPartial A 0 n +
                  RationalMajorant.factorialTailTerm A (0 + n)) +
            10 * C ^ 3 *
              (RationalMajorant.factorialTailPartial A 1 n +
                RationalMajorant.factorialTailTerm A (1 + n)) +
          2 * C *
            (RationalMajorant.factorialTailPartial A 2 n +
              RationalMajorant.factorialTailTerm A (2 + n))
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- A prefix-independent coefficient for the positive factorial polynomial
on `[-C,C]`.  It is a finite rational expression built from the explicit
factorial-series majorant at `C^2`. -/
def gaussianPositiveProfileSecantUniformBound (C : Rat) : Rat :=
  let A := C * C
  2 * C + 12 * C ^ 3 +
    (4 * C ^ 5 + 10 * C ^ 3 + 2 * C) *
      RationalMajorant.factorialSeriesFiniteBound A

/-- A prefix-independent majorant for the formal derivatives of all positive
Gaussian factorial prefixes on `[-C,C]`. -/
def gaussianPositiveProfileDerivativeUniformBound (C : Rat) : Rat :=
  2 * C * RationalMajorant.factorialSeriesFiniteBound (C * C)

theorem gaussianPositiveProfileSecantUniformBound_nonneg
    (C : Rat) (hC1 : 1 <= C) :
    0 <= gaussianPositiveProfileSecantUniformBound C := by
  have hC : 0 <= C := Rat.le_trans (by decide +kernel) hC1
  have hA : 0 <= C * C := Rat.mul_nonneg hC hC
  unfold gaussianPositiveProfileSecantUniformBound
  exact Rat.add_nonneg
    (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
      (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC)))
    (Rat.mul_nonneg
      (Rat.add_nonneg
        (Rat.add_nonneg
          (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC))
          (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC)))
        (Rat.mul_nonneg (by decide +kernel) hC))
      (RationalMajorant.factorialSeriesFiniteBound_nonneg hA))

theorem gaussianPositiveProfileDerivativeUniformBound_nonneg
    (C : Rat) (hC1 : 1 <= C) :
    0 <= gaussianPositiveProfileDerivativeUniformBound C := by
  have hC : 0 <= C := Rat.le_trans (by decide +kernel) hC1
  unfold gaussianPositiveProfileDerivativeUniformBound
  exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
    (RationalMajorant.factorialSeriesFiniteBound_nonneg
      (Rat.mul_nonneg hC hC))

theorem gaussianPositiveProfileSecantCoefficient_le_uniform
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) :
    gaussianPositiveProfileSecantCoefficient C hC1 terms <=
      gaussianPositiveProfileSecantUniformBound C := by
  have hC : 0 <= C := Rat.le_trans (by decide +kernel) hC1
  have hA : 0 <= C * C := Rat.mul_nonneg hC hC
  cases terms with
  | zero =>
      exact gaussianPositiveProfileSecantUniformBound_nonneg C hC1
  | succ terms => cases terms with
    | zero =>
        exact gaussianPositiveProfileSecantUniformBound_nonneg C hC1
    | succ terms => cases terms with
      | zero =>
          have hcoeff : gaussianPositiveProfileSecantCoefficient C hC1 2 =
              2 * C := by
            rw [show 2 = 0 + 2 by omega,
              gaussianPositiveProfileSecantCoefficient_succ_succ]
            have hone : gaussianPositiveProfileSecantCoefficient C hC1 1 = 0 := by
              rfl
            rw [hone]
            simp [FinitePolynomial.powerSecantErrorBound,
              FormalPowerSeries.expCoeff, factorialRat, factorial]
            have hq1 : qabs ((1 : Rat) / 1) = 1 := by decide +kernel
            have hq2 : qabs (2 : Rat) = 2 := by decide +kernel
            rw [hq1, hq2]
            grind
          rw [hcoeff]
          unfold gaussianPositiveProfileSecantUniformBound
          have hrest : 0 <= 12 * C ^ 3 +
              (4 * C ^ 5 + 10 * C ^ 3 + 2 * C) *
                RationalMajorant.factorialSeriesFiniteBound (C * C) := by
            exact Rat.add_nonneg
              (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC))
              (Rat.mul_nonneg
                (Rat.add_nonneg
                  (Rat.add_nonneg
                    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC))
                    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC)))
                  (Rat.mul_nonneg (by decide +kernel) hC))
                (RationalMajorant.factorialSeriesFiniteBound_nonneg hA))
          grind
      | succ n =>
          rw [show n + 1 + 1 + 1 = n + 3 by omega,
            gaussianPositiveProfileSecantCoefficient_eq_factorialPartials]
          have hzero := RationalMajorant.factorialTailPartial_le_finiteBound
            hA 0 n
          have hone := RationalMajorant.factorialTailPartial_le_finiteBound
            hA 1 n
          have htwo := RationalMajorant.factorialTailPartial_le_finiteBound
            hA 2 n
          have hC5 : 0 <= C ^ 5 := Rat.pow_nonneg hC
          have hC3 : 0 <= C ^ 3 := Rat.pow_nonneg hC
          have hfour : 0 <= (4 : Rat) := by decide +kernel
          have hten : 0 <= (10 : Rat) := by decide +kernel
          have htwoRat : 0 <= (2 : Rat) := by decide +kernel
          unfold gaussianPositiveProfileSecantUniformBound
          have h4 := Rat.mul_le_mul_of_nonneg_left hzero
            (Rat.mul_nonneg hfour hC5)
          have h10 := Rat.mul_le_mul_of_nonneg_left hone
            (Rat.mul_nonneg hten hC3)
          have h2 := Rat.mul_le_mul_of_nonneg_left htwo
            (Rat.mul_nonneg htwoRat hC)
          calc
            2 * C + 12 * C ^ 3 +
                    4 * C ^ 5 * RationalMajorant.factorialTailPartial (C * C) 0 n +
                  10 * C ^ 3 * RationalMajorant.factorialTailPartial (C * C) 1 n +
                2 * C * RationalMajorant.factorialTailPartial (C * C) 2 n <=
              2 * C + 12 * C ^ 3 +
                    4 * C ^ 5 * RationalMajorant.factorialSeriesFiniteBound (C * C) +
                  10 * C ^ 3 * RationalMajorant.factorialSeriesFiniteBound (C * C) +
                2 * C * RationalMajorant.factorialSeriesFiniteBound (C * C) :=
              rat_add_le_add (rat_add_le_add
                (rat_add_le_add (Rat.le_refl) h4) h10) h2
            _ = 2 * C + 12 * C ^ 3 +
                (4 * C ^ 5 + 10 * C ^ 3 + 2 * C) *
                  RationalMajorant.factorialSeriesFiniteBound (C * C) := by
              grind [Rat.add_mul, Rat.mul_assoc]

def gaussianPositiveProfileRecursiveSecantBound
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) :
    FinitePolynomial.SecantDerivativeBound C
      (gaussianPositiveProfilePrefix terms)
      (gaussianPositiveProfileFormalDerivativePrefix terms) :=
  (gaussianPositiveProfileRecursiveSecantData C hC1 terms).toBound

theorem gaussianPositiveProfileRecursiveSecantBound_errorCoefficient
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) :
    (gaussianPositiveProfileRecursiveSecantBound C hC1 terms).errorCoefficient =
      gaussianPositiveProfileSecantCoefficient C hC1 terms := by
  rfl

/-- Quantitative secant certificate for the reciprocal of a positive finite
Gaussian factorial prefix. -/
def gaussianReciprocalPositiveProfileSecantBound
    (C : Rat) (terms : Nat) (hC1 : 1 <= C) (hterms : 1 <= terms) :
    FinitePolynomial.SecantDerivativeBound C
      (fun x => 1 / gaussianPositiveProfilePrefix (terms + 1) x)
      (fun x =>
        -(gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x /
          (gaussianPositiveProfilePrefix (terms + 1) x *
            gaussianPositiveProfilePrefix (terms + 1) x))) := by
  let derivativeMajorant : Rat :=
    2 * C * FiniteExponentialProduct.factorialPrefix terms (C * C)
  apply FinitePolynomial.SecantDerivativeBound.reciprocalOfOneLe
    (gaussianPositiveProfileRecursiveSecantBound C hC1 (terms + 1))
    derivativeMajorant
  · intro x hx
    dsimp [derivativeMajorant]
    exact gaussianPositiveProfileFormalDerivativePrefix_qabs_le
      terms (Rat.le_trans (by decide +kernel) hC1) hx
  · dsimp [derivativeMajorant]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel)
        (Rat.le_trans (by decide +kernel) hC1))
      (FiniteExponentialProduct.factorialPrefix_nonneg
        (Rat.mul_nonneg (Rat.le_trans (by decide +kernel) hC1)
          (Rat.le_trans (by decide +kernel) hC1)) terms)
  · exact Rat.le_trans (by decide +kernel) hC1
  · intro x _hx
    exact gaussianPositiveProfilePrefix_one_le (by omega) x

/-- The explicit reciprocal-closure coefficient obtained from the two
prefix-independent positive-factorial bounds. -/
def gaussianReciprocalPositiveProfileSecantUniformBound (C : Rat) : Rat :=
  let F := gaussianPositiveProfileSecantUniformBound C
  let D := gaussianPositiveProfileDerivativeUniformBound C
  F + D * (D + 2 * C * F)

theorem gaussianReciprocalPositiveProfileSecantUniformBound_nonneg
    (C : Rat) (hC1 : 1 <= C) :
    0 <= gaussianReciprocalPositiveProfileSecantUniformBound C := by
  let F := gaussianPositiveProfileSecantUniformBound C
  let D := gaussianPositiveProfileDerivativeUniformBound C
  have hF : 0 <= F := gaussianPositiveProfileSecantUniformBound_nonneg C hC1
  have hD : 0 <= D :=
    gaussianPositiveProfileDerivativeUniformBound_nonneg C hC1
  have hC : 0 <= C := Rat.le_trans (by decide +kernel) hC1
  unfold gaussianReciprocalPositiveProfileSecantUniformBound
  exact Rat.add_nonneg hF
    (Rat.mul_nonneg hD (Rat.add_nonneg hD
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) hF)))

theorem gaussianReciprocalPositiveProfileSecantBound_errorCoefficient_le_uniform
    (C : Rat) (hC1 : 1 <= C) (terms : Nat) (hterms : 1 <= terms) :
    (gaussianReciprocalPositiveProfileSecantBound
      C terms hC1 hterms).errorCoefficient <=
        gaussianReciprocalPositiveProfileSecantUniformBound C := by
  let F : Rat :=
    (gaussianPositiveProfileRecursiveSecantBound C hC1 (terms + 1)).errorCoefficient
  let D : Rat :=
    2 * C * FiniteExponentialProduct.factorialPrefix terms (C * C)
  let FU : Rat := gaussianPositiveProfileSecantUniformBound C
  let DU : Rat := gaussianPositiveProfileDerivativeUniformBound C
  have hC : 0 <= C := Rat.le_trans (by decide +kernel) hC1
  have hA : 0 <= C * C := Rat.mul_nonneg hC hC
  have hF0 : 0 <= F :=
    (gaussianPositiveProfileRecursiveSecantBound
      C hC1 (terms + 1)).errorCoefficient_nonneg
  have hD0 : 0 <= D := by
    dsimp [D]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
      (FiniteExponentialProduct.factorialPrefix_nonneg hA terms)
  have hFU0 : 0 <= FU :=
    gaussianPositiveProfileSecantUniformBound_nonneg C hC1
  have hDU0 : 0 <= DU :=
    gaussianPositiveProfileDerivativeUniformBound_nonneg C hC1
  have hF : F <= FU := by
    dsimp [F, FU]
    rw [gaussianPositiveProfileRecursiveSecantBound_errorCoefficient]
    exact gaussianPositiveProfileSecantCoefficient_le_uniform
      C hC1 (terms + 1)
  have hprefix := RationalMajorant.factorialTailPartial_zero_le_finiteBound
    hA terms
  have hD : D <= DU := by
    dsimp [D, DU, gaussianPositiveProfileDerivativeUniformBound]
    rw [FiniteExponentialProduct.factorialPrefix_eq_factorialTailPartial]
    exact Rat.mul_le_mul_of_nonneg_left hprefix
      (Rat.mul_nonneg (by decide +kernel) hC)
  have hscale : 2 * C * F <= 2 * C * FU :=
    Rat.mul_le_mul_of_nonneg_left hF
      (Rat.mul_nonneg (by decide +kernel) hC)
  have hinner : D + 2 * C * F <= DU + 2 * C * FU :=
    rat_add_le_add hD hscale
  have hinner0 : 0 <= D + 2 * C * F :=
    Rat.add_nonneg hD0
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) hF0)
  have hinnerU0 : 0 <= DU + 2 * C * FU :=
    Rat.add_nonneg hDU0
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) hFU0)
  have hproduct : D * (D + 2 * C * F) <= DU * (DU + 2 * C * FU) :=
    calc
      D * (D + 2 * C * F) <= D * (DU + 2 * C * FU) :=
        Rat.mul_le_mul_of_nonneg_left hinner hD0
      _ <= DU * (DU + 2 * C * FU) :=
        Rat.mul_le_mul_of_nonneg_right hD hinnerU0
  change F + D * (D + 2 * C * F) <= _
  unfold gaussianReciprocalPositiveProfileSecantUniformBound
  exact rat_add_le_add hF hproduct

/-- Exact finite defect between the derivative of the reciprocal prefix and
the Gaussian ODE candidate.  Only the last positive factorial monomial
remains. -/
theorem gaussianReciprocalPositiveProfile_derivative_sub_candidate
    (terms : Nat) (hterms : 1 <= terms) (x : Rat) :
    -(gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x /
        (gaussianPositiveProfilePrefix (terms + 1) x *
          gaussianPositiveProfilePrefix (terms + 1) x)) -
        (-(2 * x / gaussianPositiveProfilePrefix (terms + 1) x)) =
      (2 * x *
        (FormalPowerSeries.expCoeff terms * x ^ (2 * terms))) /
        (gaussianPositiveProfilePrefix (terms + 1) x *
          gaussianPositiveProfilePrefix (terms + 1) x) := by
  let P := gaussianPositiveProfilePrefix (terms + 1) x
  let Q := FiniteExponentialProduct.factorialPrefix terms (x * x)
  let T := FormalPowerSeries.expCoeff terms * x ^ (2 * terms)
  have hPone : 1 <= P := by
    dsimp [P]
    exact gaussianPositiveProfilePrefix_one_le (by omega) x
  have hPpos : 0 < P := by grind
  have hPne : P ≠ 0 := Rat.ne_of_gt hPpos
  have hderivative :
      gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x =
        2 * x * Q := by
    exact gaussianPositiveProfileFormalDerivativePrefix_eq terms x
  have hprefix : P = Q + T := by
    dsimp [P, Q, T]
    rw [gaussianPositiveProfilePrefix_succ,
      gaussianPositiveProfilePrefix_eq_factorialPrefix]
  change
    -(gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x /
        (P * P)) - (-(2 * x / P)) =
      (2 * x * T) / (P * P)
  rw [hderivative, Rat.div_def, Rat.div_def, Rat.div_def,
    Rat.inv_mul_rev]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

/-- The derivative mismatch of the reciprocal finite model is bounded by the
first omitted factorial term, uniformly on a rational box. -/
theorem gaussianReciprocalPositiveProfile_derivative_sub_candidate_qabs_le
    (terms : Nat) (hterms : 1 <= terms)
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) :
    qabs
      (-(gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x /
          (gaussianPositiveProfilePrefix (terms + 1) x *
            gaussianPositiveProfilePrefix (terms + 1) x)) -
        (-(2 * x / gaussianPositiveProfilePrefix (terms + 1) x))) <=
      2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
  rw [gaussianReciprocalPositiveProfile_derivative_sub_candidate
    terms hterms x]
  let P := gaussianPositiveProfilePrefix (terms + 1) x
  let T := FormalPowerSeries.expCoeff terms * x ^ (2 * terms)
  have hPone : 1 <= P := by
    dsimp [P]
    exact gaussianPositiveProfilePrefix_one_le (by omega) x
  have hPpos : 0 < P := by grind
  have hPPpos : 0 < P * P := Rat.mul_pos hPpos hPpos
  have hPPone : 1 <= P * P := by
    calc
      (1 : Rat) = 1 * 1 := by decide +kernel
      _ <= P * P := rat_mul_le_mul_of_nonneg
        (by decide +kernel) hPone (by decide +kernel) hPone
  have hinv0 : 0 <= (P * P)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hPPpos)
  have hinvle : (P * P)⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := P * P)
    · calc
        (P * P)⁻¹ * (P * P) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hPPpos)
        _ <= 1 * (P * P) := by simpa using hPPone
    · exact hPPpos
  have hbox : qabs (x * x) <= C * C := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg
      (qabs_nonneg x) hx (qabs_nonneg x) hx
  have hterm : qabs T <=
      RationalMajorant.factorialTailTerm (C * C) terms := by
    dsimp [T]
    rw [show x ^ (2 * terms) = (x * x) ^ terms by
      symm
      exact gaussian_square_pow x terms]
    exact FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
      (Rat.mul_nonneg hC hC) hbox terms
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_mul,
    qabs_eq_self_of_nonneg (by decide +kernel),
    qabs_eq_self_of_nonneg hinv0]
  calc
    2 * qabs x * qabs T * (P * P)⁻¹ <=
        2 * C * RationalMajorant.factorialTailTerm (C * C) terms *
          (P * P)⁻¹ := by
      have hxscaled : 2 * qabs x <= 2 * C :=
        Rat.mul_le_mul_of_nonneg_left hx (by decide +kernel)
      have hmid : 2 * qabs x * qabs T <=
          2 * C * RationalMajorant.factorialTailTerm (C * C) terms :=
        calc
          2 * qabs x * qabs T <= 2 * C * qabs T :=
            Rat.mul_le_mul_of_nonneg_right hxscaled (qabs_nonneg T)
          _ <= 2 * C *
              RationalMajorant.factorialTailTerm (C * C) terms :=
            Rat.mul_le_mul_of_nonneg_left hterm
              (Rat.mul_nonneg (by decide +kernel) hC)
      exact Rat.mul_le_mul_of_nonneg_right hmid hinv0
    _ <= 2 * C * RationalMajorant.factorialTailTerm (C * C) terms * 1 :=
      Rat.mul_le_mul_of_nonneg_left hinvle
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
          (RationalMajorant.factorialTailTerm_nonneg
            (Rat.mul_nonneg hC hC) terms))
    _ = 2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
      rw [Rat.mul_one]

/-- Complete finite reciprocal-prefix secant estimate against the Gaussian
ODE candidate.  The first summand is the ordinary polynomial secant error;
the second is the one omitted factorial boundary term. -/
theorem gaussianReciprocalPositiveProfile_secant_sub_candidate_qabs_le
    (C : Rat) (terms : Nat) (hC1 : 1 <= C) (hterms : 1 <= terms)
    {x h : Rat} (hh : h ≠ 0)
    (hx : qabs x <= C) (hxh : qabs (x + h) <= C) :
    qabs
      (((1 / gaussianPositiveProfilePrefix (terms + 1) (x + h) -
          1 / gaussianPositiveProfilePrefix (terms + 1) x) / h) -
        (-(2 * x / gaussianPositiveProfilePrefix (terms + 1) x))) <=
      qabs h *
          (gaussianReciprocalPositiveProfileSecantBound
            C terms hC1 hterms).errorCoefficient +
        2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
  let secant : Rat :=
    (1 / gaussianPositiveProfilePrefix (terms + 1) (x + h) -
      1 / gaussianPositiveProfilePrefix (terms + 1) x) / h
  let modelDerivative : Rat :=
    -(gaussianPositiveProfileFormalDerivativePrefix (terms + 1) x /
      (gaussianPositiveProfilePrefix (terms + 1) x *
        gaussianPositiveProfilePrefix (terms + 1) x))
  let candidate : Rat :=
    -(2 * x / gaussianPositiveProfilePrefix (terms + 1) x)
  have hsecant :=
    (gaussianReciprocalPositiveProfileSecantBound
      C terms hC1 hterms).error_bound x h hh hx hxh
  have hresidual :=
    gaussianReciprocalPositiveProfile_derivative_sub_candidate_qabs_le
      terms hterms (Rat.le_trans (by decide +kernel) hC1) hx
  have htriangle : qabs (secant - candidate) <=
      qabs (secant - modelDerivative) +
        qabs (modelDerivative - candidate) := by
    calc
      qabs (secant - candidate) =
          qabs ((secant - modelDerivative) +
            (modelDerivative - candidate)) := by
              congr 1
              grind [Rat.sub_eq_add_neg]
      _ <= qabs (secant - modelDerivative) +
          qabs (modelDerivative - candidate) := qabs_add_le _ _
  change qabs (secant - candidate) <= _
  exact Rat.le_trans htriangle (rat_add_le_add
    (by simpa [secant, modelDerivative] using hsecant)
    (by simpa [modelDerivative, candidate] using hresidual))

/-! ## Synchronized finite witnesses inside exponential boxes -/

/-- A later exact factorial-series center lies inside every earlier nested
exponential box.  This publishes the finite witness fact needed by derivative
limits; it is stronger than merely knowing that the raw is valid. -/
theorem expPowerSeries_future_center_mem
    (x : Rat) {stage futureStage : Nat} (hstage : stage <= futureStage) :
    ((expPowerSeries x).compute stage).lo <=
        ExpProofs.powerSeriesCenterAtTerms x
          (expPowerSeriesTerms x futureStage) /\
      ExpProofs.powerSeriesCenterAtTerms x
          (expPowerSeriesTerms x futureStage) <=
        ((expPowerSeries x).compute stage).hi := by
  have hfuture :
      ((expPowerSeries x).compute futureStage).lo <=
          ExpProofs.powerSeriesCenterAtTerms x
            (expPowerSeriesTerms x futureStage) /\
        ExpProofs.powerSeriesCenterAtTerms x
            (expPowerSeriesTerms x futureStage) <=
          ((expPowerSeries x).compute futureStage).hi := by
    rw [ExpProofs.expPowerSeries_compute_eq,
      ExpProofs.powerSeriesCenter_stage_eq]
    have hradius := ExpProofs.powerSeriesTailRadius_nonneg_of_ratioBound
      x (ExpProofs.expPowerSeries_ratio_bound x) futureStage
    unfold ExpProofs.intervalAround
    constructor <;> grind [Rat.sub_eq_add_neg]
  have hnested := (ExpProofs.expPowerSeries_valid x).2.1
    stage futureStage hstage
  exact
    ⟨Rat.le_trans hnested.1 hfuture.1,
      Rat.le_trans hfuture.2 hnested.2.2⟩

/-- A reciprocal of a later positive factorial center lies inside every
earlier positive-reciprocal box.  This is the rational witness theorem for
the actual executable presentation of `exp (-a)`. -/
theorem reciprocalNegativeExpRaw_future_inversePrefix_mem
    (a : Rat) (ha : 0 <= a) {stage futureStage : Nat}
    (hstage : stage <= futureStage) :
    ((reciprocalNegativeExpRaw a).compute stage).lo <=
        1 / FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms a futureStage) a /\
      1 / FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms a futureStage) a <=
        ((reciprocalNegativeExpRaw a).compute stage).hi := by
  let terms := expPowerSeriesTerms a futureStage
  let p := FiniteExponentialProduct.factorialPrefix terms a
  have hterms : 2 <= terms := by
    dsimp [terms]
    unfold expPowerSeriesTerms
    omega
  have hpLower : 1 + a <= p := by
    dsimp [p]
    exact FiniteExponentialProduct.factorialPrefix_ge_one_add ha terms hterms
  have hpPos : 0 < p := by grind
  have hpMem :
      ((expPowerSeries a).compute stage).lo <= p /\
        p <= ((expPowerSeries a).compute stage).hi := by
    dsimp [p, terms]
    change
      ((expPowerSeries a).compute stage).lo <=
          ExpProofs.powerSeriesCenterAtTerms a
            (expPowerSeriesTerms a futureStage) /\
        ExpProofs.powerSeriesCenterAtTerms a
            (expPowerSeriesTerms a futureStage) <=
          ((expPowerSeries a).compute stage).hi
    exact expPowerSeries_future_center_mem a hstage
  have hmaxLe :
      maxRat2 ((expPowerSeries a).compute stage).lo (1 + a) <= p := by
    unfold maxRat2
    by_cases h : ((expPowerSeries a).compute stage).lo <= 1 + a
    · simp [h, hpLower]
    · simp [h, hpMem.1]
  have hmaxPos :
      0 < maxRat2 ((expPowerSeries a).compute stage).lo (1 + a) := by
    unfold maxRat2
    by_cases h : ((expPowerSeries a).compute stage).lo <= 1 + a
    · simp [h]
      grind
    · simp [h]
      grind
  have hhiPos : 0 < ((expPowerSeries a).compute stage).hi := by
    grind
  unfold reciprocalNegativeExpRaw
  rw [RealCompute.positiveReciprocal_compute
    (expPowerSeries a) (1 + a) (by grind) stage]
  dsimp [p, terms]
  constructor
  · exact RealCompute.one_div_antitone_of_pos hpPos hpMem.2
  · exact RealCompute.one_div_antitone_of_pos hmaxPos hmaxLe

/-- Future stage for the base endpoint.  Its extra offset is the step
endpoint's input-dependent exponential offset, forcing both endpoints to use
one common finite term count. -/
def gaussianDerivativeBaseFutureStage
    (x h : Rat) (stage : Nat) : Nat :=
  stage + 8 + 2 * (-( (x + h) * (x + h))).num.natAbs

/-- Symmetric future stage for the step endpoint. -/
def gaussianDerivativeStepFutureStage
    (x _h : Rat) (stage : Nat) : Nat :=
  stage + 8 + 2 * (-(x * x)).num.natAbs

/-- The two synchronized future stages expose exactly the same number of
factorial-series terms. -/
theorem gaussianDerivative_future_terms_eq
    (x h : Rat) (stage : Nat) :
    expPowerSeriesTerms (-(x * x))
        (gaussianDerivativeBaseFutureStage x h stage) =
      expPowerSeriesTerms (-((x + h) * (x + h)))
        (gaussianDerivativeStepFutureStage x h stage) := by
  unfold gaussianDerivativeBaseFutureStage
    gaussianDerivativeStepFutureStage expPowerSeriesTerms
  omega

theorem expPowerSeriesTerms_square_eq_neg_square
    (x : Rat) (stage : Nat) :
    expPowerSeriesTerms (x * x) stage =
      expPowerSeriesTerms (-(x * x)) stage := by
  simp [expPowerSeriesTerms]

/-- The common Gaussian Taylor term count used at both secant endpoints. -/
def gaussianDerivativeCommonTerms (x h : Rat) (stage : Nat) : Nat :=
  expPowerSeriesTerms (-(x * x))
    (gaussianDerivativeBaseFutureStage x h stage)

theorem gaussianDerivativeCommonTerms_ge_two
    (x h : Rat) (stage : Nat) :
    2 <= gaussianDerivativeCommonTerms x h stage := by
  unfold gaussianDerivativeCommonTerms gaussianDerivativeBaseFutureStage
    expPowerSeriesTerms
  omega

/-- Index of the last included positive factorial monomial. -/
def gaussianDerivativeCommonTailIndex
    (x h : Rat) (stage : Nat) : Nat :=
  gaussianDerivativeCommonTerms x h stage - 1

theorem gaussianDerivativeCommonTerms_eq_tailIndex_succ
    (x h : Rat) (stage : Nat) :
    gaussianDerivativeCommonTerms x h stage =
      gaussianDerivativeCommonTailIndex x h stage + 1 := by
  unfold gaussianDerivativeCommonTailIndex
  have hterms := gaussianDerivativeCommonTerms_ge_two x h stage
  omega

theorem gaussianDerivativeCommonTailIndex_pos
    (x h : Rat) (stage : Nat) :
    1 <= gaussianDerivativeCommonTailIndex x h stage := by
  unfold gaussianDerivativeCommonTailIndex
  have hterms := gaussianDerivativeCommonTerms_ge_two x h stage
  omega

/-- The synchronized common prefix contains at least as many nonconstant
factorial terms as the requested evaluator stage. -/
theorem gaussianDerivativeCommonTailIndex_ge_stage
    (x h : Rat) (stage : Nat) :
    stage <= gaussianDerivativeCommonTailIndex x h stage := by
  unfold gaussianDerivativeCommonTailIndex gaussianDerivativeCommonTerms
    gaussianDerivativeBaseFutureStage expPowerSeriesTerms
  omega

theorem gaussianDerivative_stage_le_baseFuture
    (x h : Rat) (stage : Nat) :
    stage <= gaussianDerivativeBaseFutureStage x h stage := by
  unfold gaussianDerivativeBaseFutureStage
  omega

theorem gaussianDerivative_stage_le_stepFuture
    (x h : Rat) (stage : Nat) :
    stage <= gaussianDerivativeStepFutureStage x h stage := by
  unfold gaussianDerivativeStepFutureStage
  omega

/-- The common finite Gaussian prefix at the base endpoint lies inside the
earlier represented exponential box. -/
theorem gaussianDerivativeCommonPrefix_base_mem
    (x h : Rat) (stage : Nat) :
    ((expPowerSeries (-(x * x))).compute stage).lo <=
        gaussianEvenProfilePrefix
          (gaussianDerivativeCommonTerms x h stage) x /\
      gaussianEvenProfilePrefix
          (gaussianDerivativeCommonTerms x h stage) x <=
        ((expPowerSeries (-(x * x))).compute stage).hi := by
  rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
  exact expPowerSeries_future_center_mem (-(x * x))
    (gaussianDerivative_stage_le_baseFuture x h stage)

/-- The same common prefix, now evaluated at the step endpoint, lies inside
that endpoint's represented exponential box. -/
theorem gaussianDerivativeCommonPrefix_step_mem
    (x h : Rat) (stage : Nat) :
    ((expPowerSeries (-((x + h) * (x + h)))).compute stage).lo <=
        gaussianEvenProfilePrefix
          (gaussianDerivativeCommonTerms x h stage) (x + h) /\
      gaussianEvenProfilePrefix
          (gaussianDerivativeCommonTerms x h stage) (x + h) <=
        ((expPowerSeries (-((x + h) * (x + h)))).compute stage).hi := by
  rw [gaussianEvenProfilePrefix_eq_powerSeriesCenterAtTerms]
  rw [gaussianDerivativeCommonTerms,
    gaussianDerivative_future_terms_eq x h stage]
  exact expPowerSeries_future_center_mem (-((x + h) * (x + h)))
    (gaussianDerivative_stage_le_stepFuture x h stage)

/-- The reciprocal-prefix witness belonging to the executable Gaussian raw. -/
def gaussianReciprocalDerivativeCommonPrefix
    (x h : Rat) (stage : Nat) : Rat :=
  1 / FiniteExponentialProduct.factorialPrefix
    (gaussianDerivativeCommonTerms x h stage) (x * x)

theorem gaussianDerivativeCommonTerms_reverse
    (x h : Rat) (stage : Nat) :
    gaussianDerivativeCommonTerms (x + h) (-h) stage =
      gaussianDerivativeCommonTerms x h stage := by
  have hcancel : x + h + -h = x := by
    grind [Rat.add_assoc]
  unfold gaussianDerivativeCommonTerms gaussianDerivativeBaseFutureStage
    expPowerSeriesTerms
  rw [hcancel]
  omega

/-- The synchronized reciprocal-prefix value at the step endpoint. -/
def gaussianReciprocalDerivativeCommonStepValue
    (x h : Rat) (stage : Nat) : Rat :=
  1 / FiniteExponentialProduct.factorialPrefix
    (gaussianDerivativeCommonTerms x h stage) ((x + h) * (x + h))

/-- The synchronized reciprocal-prefix value at the base endpoint lies in
the executable reciprocal-Gaussian box. -/
theorem gaussianReciprocalDerivativeCommonPrefix_base_mem
    (x h : Rat) (stage : Nat) :
    ((reciprocalGaussianRaw x).compute stage).lo <=
        gaussianReciprocalDerivativeCommonPrefix x h stage /\
      gaussianReciprocalDerivativeCommonPrefix x h stage <=
        ((reciprocalGaussianRaw x).compute stage).hi := by
  unfold gaussianReciprocalDerivativeCommonPrefix reciprocalGaussianRaw
  have hmem := reciprocalNegativeExpRaw_future_inversePrefix_mem
    (x * x) (rat_square_nonneg_basic x)
    (gaussianDerivative_stage_le_baseFuture x h stage)
  rw [expPowerSeriesTerms_square_eq_neg_square] at hmem
  exact hmem

/-- The same synchronized reciprocal-prefix model at the step endpoint lies
in that endpoint's executable reciprocal-Gaussian box. -/
theorem gaussianReciprocalDerivativeCommonPrefix_step_mem
    (x h : Rat) (stage : Nat) :
    ((reciprocalGaussianRaw (x + h)).compute stage).lo <=
        gaussianReciprocalDerivativeCommonStepValue x h stage /\
      gaussianReciprocalDerivativeCommonStepValue x h stage <=
        ((reciprocalGaussianRaw (x + h)).compute stage).hi := by
  have hmem := gaussianReciprocalDerivativeCommonPrefix_base_mem
    (x + h) (-h) stage
  simpa [gaussianReciprocalDerivativeCommonPrefix,
    gaussianReciprocalDerivativeCommonStepValue,
    gaussianDerivativeCommonTerms_reverse x h stage] using hmem

/-! ## Lifting the synchronized witnesses through normalization -/

/-- A canonical exact rational witness inside the normalization-factor box. -/
def gaussianMassReciprocalMidpoint (stage : Nat) : Rat :=
  (gaussianFullLineMassReciprocalRaw.compute stage).midpoint

theorem gaussianMassReciprocalMidpoint_mem (stage : Nat) :
    (gaussianFullLineMassReciprocalRaw.compute stage).lo <=
        gaussianMassReciprocalMidpoint stage /\
      gaussianMassReciprocalMidpoint stage <=
        (gaussianFullLineMassReciprocalRaw.compute stage).hi := by
  exact QInterval.midpoint_mem
    (RealCompute.interval_order_of_valid
      gaussianFullLineMassReciprocalRaw
      gaussianFullLineMassReciprocalRaw_valid stage)

theorem gaussianMassReciprocalMidpoint_nonneg (stage : Nat) :
    0 <= gaussianMassReciprocalMidpoint stage := by
  have hlo := (gaussianFullLineMassReciprocalRaw_nonneg_bounded stage).1
  have hmem := gaussianMassReciprocalMidpoint_mem stage
  grind

theorem gaussianMassReciprocalMidpoint_le (stage : Nat) :
    gaussianMassReciprocalMidpoint stage <=
      1 / gaussianFullLineMassLower := by
  exact Rat.le_trans (gaussianMassReciprocalMidpoint_mem stage).2
    (gaussianFullLineMassReciprocalRaw_nonneg_bounded stage).2

/-- Width of the normalized Gaussian product is controlled by the
normalization width plus the reciprocal-Gaussian width scaled by the uniform
normalization bound. -/
theorem gaussianNormalizedProfileRaw_width_le
    (x : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileRaw x).compute stage).width <=
      (gaussianFullLineMassReciprocalRaw.compute stage).width +
        (1 / gaussianFullLineMassLower) *
          ((reciprocalGaussianRaw x).compute stage).width := by
  let A := gaussianFullLineMassReciprocalRaw.compute stage
  let G := (reciprocalGaussianRaw x).compute stage
  have hA0 : 0 <= A.lo := by
    dsimp [A]
    exact (gaussianFullLineMassReciprocalRaw_nonneg_bounded stage).1
  have hAM : A.hi <= 1 / gaussianFullLineMassLower := by
    dsimp [A]
    exact (gaussianFullLineMassReciprocalRaw_nonneg_bounded stage).2
  have hAorder : A.lo <= A.hi := by
    dsimp [A]
    exact RealCompute.interval_order_of_valid gaussianFullLineMassReciprocalRaw
      gaussianFullLineMassReciprocalRaw_valid stage
  have hG0 : 0 <= G.lo := by
    dsimp [G]
    exact (reciprocalGaussianRaw_nonneg_bounded_by_one x stage).1
  have hG1 : G.hi <= 1 := by
    dsimp [G]
    exact (reciprocalGaussianRaw_nonneg_bounded_by_one x stage).2
  have hGorder : G.lo <= G.hi := by
    dsimp [G]
    exact RealCompute.interval_order_of_valid (reciprocalGaussianRaw x)
      (reciprocalGaussianRaw_valid x) stage
  have hAwidth0 : 0 <= A.width := by
    unfold QInterval.width
    grind
  have hGwidth0 : 0 <= G.width := by
    unfold QInterval.width
    grind
  unfold gaussianNormalizedProfileRaw RealCompute.mul RealCompute.mulCompute
  change (QBox.mulRealInterval A.lo A.hi G.lo G.hi).width <= _
  rw [QBox.mulRealInterval_of_nonneg hA0 hAorder hG0 hGorder]
  unfold QInterval.width
  have hfirst : G.hi * (A.hi - A.lo) <= 1 * (A.hi - A.lo) :=
    Rat.mul_le_mul_of_nonneg_right hG1 hAwidth0
  have hsecond : A.lo * (G.hi - G.lo) <=
      (1 / gaussianFullLineMassLower) * (G.hi - G.lo) := by
    exact Rat.mul_le_mul_of_nonneg_right
      (Rat.le_trans hAorder hAM) hGwidth0
  calc
    A.hi * G.hi - A.lo * G.lo =
        G.hi * (A.hi - A.lo) + A.lo * (G.hi - G.lo) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    _ <= 1 * (A.hi - A.lo) +
        (1 / gaussianFullLineMassLower) * (G.hi - G.lo) :=
      rat_add_le_add hfirst hsecond
    _ = (A.hi - A.lo) +
        (1 / gaussianFullLineMassLower) * (G.hi - G.lo) := by
      rw [Rat.one_mul]

/-- Fully explicit pointwise width majorant for the normalized Gaussian. -/
theorem gaussianNormalizedProfileRaw_width_le_explicit
    (x : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileRaw x).compute stage).width <=
      (16 / (gaussianFullLineMassLower * gaussianFullLineMassLower)) /
          (((stage + 1 : Nat) : Rat)) +
        (1 / gaussianFullLineMassLower) *
          (((4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
              (expPowerSeriesTerms (x * x) 0))) /
            ((1 + x * x) * (1 + x * x))) *
              ((1 : Rat) / 2) ^ stage) := by
  have hproduct := gaussianNormalizedProfileRaw_width_le x stage
  have hmass := gaussianFullLineMassReciprocalRaw_width_le_natRate stage
  have hgaussian := reciprocalGaussianRaw_compute_width_le_geometric x stage
  have hnormalization0 : 0 <= 1 / gaussianFullLineMassLower := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 gaussianFullLineMassLower_pos)
  exact Rat.le_trans hproduct
    (rat_add_le_add hmass
      (Rat.mul_le_mul_of_nonneg_left hgaussian hnormalization0))

/-- Executable pointwise width budget for the normalized Gaussian.  The
first summand is the normalization uncertainty and the second is the
reciprocal-exponential uncertainty. -/
def gaussianNormalizedProfileWidthBudget (x : Rat) (stage : Nat) : Rat :=
  (16 / (gaussianFullLineMassLower * gaussianFullLineMassLower)) /
      (((stage + 1 : Nat) : Rat)) +
    (1 / gaussianFullLineMassLower) *
      (((4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
          (expPowerSeriesTerms (x * x) 0))) /
        ((1 + x * x) * (1 + x * x))) *
          ((1 : Rat) / 2) ^ stage)

/-- The inverse-linear coefficient in the normalized Gaussian width budget. -/
def gaussianNormalizedProfileNatWidthCoefficient : Rat :=
  16 / (gaussianFullLineMassLower * gaussianFullLineMassLower)

/-- The pointwise dyadic coefficient in the normalized Gaussian width
budget. -/
def gaussianNormalizedProfileGeometricWidthCoefficient (x : Rat) : Rat :=
  (1 / gaussianFullLineMassLower) *
    ((4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
        (expPowerSeriesTerms (x * x) 0))) /
      ((1 + x * x) * (1 + x * x)))

theorem gaussianNormalizedProfileNatWidthCoefficient_nonneg :
    0 <= gaussianNormalizedProfileNatWidthCoefficient := by
  unfold gaussianNormalizedProfileNatWidthCoefficient
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt ((Rat.inv_pos).2
      (Rat.mul_pos gaussianFullLineMassLower_pos
        gaussianFullLineMassLower_pos)))

theorem gaussianNormalizedProfileGeometricWidthCoefficient_nonneg
    (x : Rat) :
    0 <= gaussianNormalizedProfileGeometricWidthCoefficient x := by
  have hmassInv : 0 <= 1 / gaussianFullLineMassLower := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 gaussianFullLineMassLower_pos)
  have hsquare : 0 <= x * x := rat_square_nonneg_basic x
  have hdenPos : 0 < (1 + x * x) * (1 + x * x) := by
    exact Rat.mul_pos (by grind) (by grind)
  have hquot : 0 <=
      (4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
          (expPowerSeriesTerms (x * x) 0))) /
        ((1 + x * x) * (1 + x * x)) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
      (Rat.le_of_lt ((Rat.inv_pos).2 hdenPos))
  unfold gaussianNormalizedProfileGeometricWidthCoefficient
  exact Rat.mul_nonneg hmassInv hquot

theorem gaussianNormalizedProfileWidthBudget_eq_mixed
    (x : Rat) (stage : Nat) :
    gaussianNormalizedProfileWidthBudget x stage =
      gaussianNormalizedProfileNatWidthCoefficient /
          (((stage + 1 : Nat) : Rat)) +
        gaussianNormalizedProfileGeometricWidthCoefficient x *
          ((1 : Rat) / 2) ^ stage := by
  unfold gaussianNormalizedProfileWidthBudget
    gaussianNormalizedProfileNatWidthCoefficient
    gaussianNormalizedProfileGeometricWidthCoefficient
  grind [Rat.mul_assoc]

/-- Executable pointwise stage for a requested normalized-Gaussian width. -/
def gaussianNormalizedProfileWidthStage (x : Rat) (eps : QPos) : Nat :=
  RationalMajorant.mixedNatGeometricStage
    gaussianNormalizedProfileNatWidthCoefficient
    (gaussianNormalizedProfileGeometricWidthCoefficient x) eps

theorem gaussianNormalizedProfileWidthBudget_at_stage_le
    (x : Rat) (eps : QPos) {stage : Nat}
    (hstage : gaussianNormalizedProfileWidthStage x eps <= stage) :
    gaussianNormalizedProfileWidthBudget x stage <= eps.val := by
  rw [gaussianNormalizedProfileWidthBudget_eq_mixed]
  exact RationalMajorant.mixedNatGeometricStage_spec_of_le
    gaussianNormalizedProfileNatWidthCoefficient_nonneg
    (gaussianNormalizedProfileGeometricWidthCoefficient_nonneg x)
    eps hstage

/-- Each endpoint of a nonzero difference quotient receives half of the
output precision after multiplication by `|h|`. -/
def gaussianNormalizedProfileQuotientWidthTolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val * qabs h / 2
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (Rat.mul_pos (precisionAtStage n).property (qabs_pos_of_ne hh))
        ((Rat.inv_pos).2 (by decide +kernel)) }

/-- The profile tolerance which, after multiplication by `2*C`, gives the
requested derivative-candidate precision. -/
def gaussianNormalizedProfileDerivativeWidthTolerance
    (C : Rat) (hC : 0 < C) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val / (2 * C)
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos (precisionAtStage n).property
        ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) hC)) }

/-- One total width stage for the two quotient endpoints and the Gaussian
ODE candidate.  The zero-step branch is arbitrary because derivative
certificates always supply `h != 0`. -/
def gaussianNormalizedProfileWidthEvalPrecision
    (C : Rat) (hC : 0 < C) (x h : Rat) (n : Nat) : Nat :=
  let derivativeStage := gaussianNormalizedProfileWidthStage x
    (gaussianNormalizedProfileDerivativeWidthTolerance C hC n)
  if hh : h = 0 then derivativeStage else
    let quotientTolerance :=
      gaussianNormalizedProfileQuotientWidthTolerance h hh n
    Nat.max derivativeStage
      (Nat.max
        (gaussianNormalizedProfileWidthStage x quotientTolerance)
        (gaussianNormalizedProfileWidthStage (x + h) quotientTolerance))

theorem gaussianNormalizedProfileWidthEvalPrecision_derivative_budget_of_le
    (C : Rat) (hC : 0 < C) (x h : Rat) (n : Nat) {stage : Nat}
    (hstage : gaussianNormalizedProfileWidthEvalPrecision C hC x h n <= stage) :
    (2 * C) * gaussianNormalizedProfileWidthBudget x
        stage <=
      (precisionAtStage n).val := by
  let tolerance :=
    gaussianNormalizedProfileDerivativeWidthTolerance C hC n
  have hbaseStage : gaussianNormalizedProfileWidthStage x tolerance <=
      gaussianNormalizedProfileWidthEvalPrecision C hC x h n := by
    unfold gaussianNormalizedProfileWidthEvalPrecision
    by_cases hh : h = 0
    · rw [dif_pos hh]
      simpa [tolerance]
    · rw [dif_neg hh]
      exact Nat.le_max_left _ _
  have hwidthStage : gaussianNormalizedProfileWidthStage x tolerance <= stage :=
    Nat.le_trans hbaseStage hstage
  have hwidth := gaussianNormalizedProfileWidthBudget_at_stage_le
    x tolerance hwidthStage
  have hscale0 : 0 <= 2 * C :=
    Rat.le_of_lt (Rat.mul_pos (by decide +kernel) hC)
  calc
    (2 * C) * gaussianNormalizedProfileWidthBudget x
        stage <=
        (2 * C) * tolerance.val :=
      Rat.mul_le_mul_of_nonneg_left hwidth hscale0
    _ = (precisionAtStage n).val := by
      dsimp [tolerance, gaussianNormalizedProfileDerivativeWidthTolerance]
      rw [Rat.div_def]
      have hne : 2 * C ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (by decide +kernel) hC)
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem gaussianNormalizedProfileWidthEvalPrecision_derivative_budget
    (C : Rat) (hC : 0 < C) (x h : Rat) (n : Nat) :
    (2 * C) * gaussianNormalizedProfileWidthBudget x
        (gaussianNormalizedProfileWidthEvalPrecision C hC x h n) <=
      (precisionAtStage n).val :=
  gaussianNormalizedProfileWidthEvalPrecision_derivative_budget_of_le
    C hC x h n (Nat.le_refl _)

theorem gaussianNormalizedProfileWidthEvalPrecision_quotient_budget_of_le
    (C : Rat) (hC : 0 < C) (x h : Rat) (hh : h ≠ 0) (n : Nat)
    {stage : Nat}
    (hstage : gaussianNormalizedProfileWidthEvalPrecision C hC x h n <= stage) :
    qabs (1 / h) *
        (gaussianNormalizedProfileWidthBudget (x + h)
            stage +
          gaussianNormalizedProfileWidthBudget x
            stage) <=
      (precisionAtStage n).val := by
  let tolerance := gaussianNormalizedProfileQuotientWidthTolerance h hh n
  have hxBase : gaussianNormalizedProfileWidthStage x tolerance <=
      gaussianNormalizedProfileWidthEvalPrecision C hC x h n := by
    unfold gaussianNormalizedProfileWidthEvalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hxhBase : gaussianNormalizedProfileWidthStage (x + h) tolerance <=
      gaussianNormalizedProfileWidthEvalPrecision C hC x h n := by
    unfold gaussianNormalizedProfileWidthEvalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hxStage : gaussianNormalizedProfileWidthStage x tolerance <= stage :=
    Nat.le_trans hxBase hstage
  have hxhStage : gaussianNormalizedProfileWidthStage (x + h) tolerance <=
      stage := Nat.le_trans hxhBase hstage
  have hxWidth := gaussianNormalizedProfileWidthBudget_at_stage_le
    x tolerance hxStage
  have hxhWidth := gaussianNormalizedProfileWidthBudget_at_stage_le
    (x + h) tolerance hxhStage
  have hsum :
      gaussianNormalizedProfileWidthBudget (x + h) stage +
          gaussianNormalizedProfileWidthBudget x stage <=
        tolerance.val + tolerance.val :=
    rat_add_le_add hxhWidth hxWidth
  have hcancel : qabs (1 / h) * qabs h = 1 := by
    have hmul : (1 / h) * h = 1 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
    have habs := qabs_mul (1 / h) h
    rw [hmul] at habs
    have hone : qabs (1 : Rat) = 1 := by decide +kernel
    rw [hone] at habs
    exact habs.symm
  calc
    qabs (1 / h) *
        (gaussianNormalizedProfileWidthBudget (x + h) stage +
          gaussianNormalizedProfileWidthBudget x stage) <=
        qabs (1 / h) * (tolerance.val + tolerance.val) :=
      Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg _)
    _ = (precisionAtStage n).val := by
      dsimp [tolerance, gaussianNormalizedProfileQuotientWidthTolerance]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianNormalizedProfileWidthEvalPrecision_quotient_budget
    (C : Rat) (hC : 0 < C) (x h : Rat) (hh : h ≠ 0) (n : Nat) :
    qabs (1 / h) *
        (gaussianNormalizedProfileWidthBudget (x + h)
            (gaussianNormalizedProfileWidthEvalPrecision C hC x h n) +
          gaussianNormalizedProfileWidthBudget x
            (gaussianNormalizedProfileWidthEvalPrecision C hC x h n)) <=
      (precisionAtStage n).val :=
  gaussianNormalizedProfileWidthEvalPrecision_quotient_budget_of_le
    C hC x h hh n (Nat.le_refl _)

theorem gaussianNormalizedProfileRaw_width_le_budget
    (x : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileRaw x).compute stage).width <=
      gaussianNormalizedProfileWidthBudget x stage := by
  simpa [gaussianNormalizedProfileWidthBudget] using
    gaussianNormalizedProfileRaw_width_le_explicit x stage

/-- The represented Gaussian difference quotient has a completely explicit
endpoint-width budget. -/
theorem gaussianNormalizedProfile_differenceQuotient_width_le
    (x h : Rat) (stage : Nat) :
    (QInterval.differenceQuotient
      ((gaussianNormalizedProfileRaw (x + h)).compute stage)
      ((gaussianNormalizedProfileRaw x).compute stage) h).width <=
        qabs (1 / h) *
          (gaussianNormalizedProfileWidthBudget (x + h) stage +
            gaussianNormalizedProfileWidthBudget x stage) := by
  rw [QInterval.differenceQuotient_width]
  exact Rat.mul_le_mul_of_nonneg_left
    (rat_add_le_add
      (gaussianNormalizedProfileRaw_width_le_budget (x + h) stage)
      (gaussianNormalizedProfileRaw_width_le_budget x stage))
    (qabs_nonneg _)

/-- Exact normalized finite-model value at the secant base point. -/
def gaussianNormalizedDerivativeBaseValue
    (x h : Rat) (stage : Nat) : Rat :=
  gaussianMassReciprocalMidpoint stage *
    gaussianReciprocalDerivativeCommonPrefix x h stage

/-- Exact normalized finite-model value at the secant step point. -/
def gaussianNormalizedDerivativeStepValue
    (x h : Rat) (stage : Nat) : Rat :=
  gaussianMassReciprocalMidpoint stage *
    gaussianReciprocalDerivativeCommonStepValue x h stage

/-- The normalized base witness lies inside the actual executable normalized
Gaussian product box. -/
theorem gaussianNormalizedDerivativeBaseValue_mem
    (x h : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileRaw x).compute stage).lo <=
        gaussianNormalizedDerivativeBaseValue x h stage /\
      gaussianNormalizedDerivativeBaseValue x h stage <=
        ((gaussianNormalizedProfileRaw x).compute stage).hi := by
  have hm := gaussianMassReciprocalMidpoint_mem stage
  have hg := gaussianReciprocalDerivativeCommonPrefix_base_mem x h stage
  have hm0 := gaussianMassReciprocalMidpoint_nonneg stage
  have hglo0 := (reciprocalGaussianRaw_nonneg_bounded_by_one x stage).1
  have hg0 : 0 <= gaussianReciprocalDerivativeCommonPrefix x h stage := by
    grind
  unfold gaussianNormalizedProfileRaw gaussianNormalizedDerivativeBaseValue
    RealCompute.mul RealCompute.mulCompute
  change
    (QBox.mulRealInterval
      (gaussianFullLineMassReciprocalRaw.compute stage).lo
      (gaussianFullLineMassReciprocalRaw.compute stage).hi
      ((reciprocalGaussianRaw x).compute stage).lo
      ((reciprocalGaussianRaw x).compute stage).hi).lo <=
        gaussianMassReciprocalMidpoint stage *
          gaussianReciprocalDerivativeCommonPrefix x h stage /\
      gaussianMassReciprocalMidpoint stage *
          gaussianReciprocalDerivativeCommonPrefix x h stage <=
        (QBox.mulRealInterval
          (gaussianFullLineMassReciprocalRaw.compute stage).lo
          (gaussianFullLineMassReciprocalRaw.compute stage).hi
          ((reciprocalGaussianRaw x).compute stage).lo
          ((reciprocalGaussianRaw x).compute stage).hi).hi
  rw [QBox.mulRealInterval_of_nonneg
    (gaussianFullLineMassReciprocalRaw_nonneg_bounded stage).1
    (RealCompute.interval_order_of_valid gaussianFullLineMassReciprocalRaw
      gaussianFullLineMassReciprocalRaw_valid stage)
    hglo0
    (RealCompute.interval_order_of_valid (reciprocalGaussianRaw x)
      (reciprocalGaussianRaw_valid x) stage)]
  constructor
  · calc
      (gaussianFullLineMassReciprocalRaw.compute stage).lo *
          ((reciprocalGaussianRaw x).compute stage).lo <=
          gaussianMassReciprocalMidpoint stage *
            ((reciprocalGaussianRaw x).compute stage).lo :=
        Rat.mul_le_mul_of_nonneg_right hm.1 hglo0
      _ <= gaussianMassReciprocalMidpoint stage *
          gaussianReciprocalDerivativeCommonPrefix x h stage :=
        Rat.mul_le_mul_of_nonneg_left hg.1 hm0
  · calc
      gaussianMassReciprocalMidpoint stage *
          gaussianReciprocalDerivativeCommonPrefix x h stage <=
          (gaussianFullLineMassReciprocalRaw.compute stage).hi *
            gaussianReciprocalDerivativeCommonPrefix x h stage :=
        Rat.mul_le_mul_of_nonneg_right hm.2 hg0
      _ <= (gaussianFullLineMassReciprocalRaw.compute stage).hi *
          ((reciprocalGaussianRaw x).compute stage).hi := by
        have hmhi0 : 0 <=
            (gaussianFullLineMassReciprocalRaw.compute stage).hi := by
          exact Rat.le_trans hm0 hm.2
        exact Rat.mul_le_mul_of_nonneg_left hg.2 hmhi0

/-- The normalized step witness lies inside the actual executable normalized
Gaussian box at `x+h`. -/
theorem gaussianNormalizedDerivativeStepValue_mem
    (x h : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileRaw (x + h)).compute stage).lo <=
        gaussianNormalizedDerivativeStepValue x h stage /\
      gaussianNormalizedDerivativeStepValue x h stage <=
        ((gaussianNormalizedProfileRaw (x + h)).compute stage).hi := by
  have hbase := gaussianNormalizedDerivativeBaseValue_mem
    (x + h) (-h) stage
  simpa [gaussianNormalizedDerivativeBaseValue,
    gaussianNormalizedDerivativeStepValue,
    gaussianReciprocalDerivativeCommonPrefix,
    gaussianReciprocalDerivativeCommonStepValue,
    gaussianDerivativeCommonTerms_reverse x h stage] using hbase

/-- Exact finite-model value for the represented derivative candidate. -/
def gaussianNormalizedDerivativeCandidateValue
    (x h : Rat) (stage : Nat) : Rat :=
  -(2 * x * gaussianNormalizedDerivativeBaseValue x h stage)

/-- The normalized Gaussian as an everywhere-defined rational-input raw
function. -/
def gaussianNormalizedProfileFunRaw : RealFunRaw where
  domain := RealFunRaw.entire
  compute := fun x => (gaussianNormalizedProfileRaw x).compute

theorem gaussianNormalizedProfileFunRaw_valid :
    gaussianNormalizedProfileFunRaw.Valid := by
  intro x _hx
  exact gaussianNormalizedProfileRaw_valid x

/-- The concrete represented derivative candidate `-2 x G(x)`.  Its
definition uses interval negation after nonnegative-or-negative rational
scaling, so no sign case is hidden in the validity certificate. -/
def gaussianNormalizedProfileDerivativeCandidateRaw (x : Rat) : RealCompute :=
  -(RealCompute.scaleRat (2 * x) (gaussianNormalizedProfileRaw x))

theorem gaussianNormalizedProfileDerivativeCandidateRaw_valid (x : Rat) :
    (gaussianNormalizedProfileDerivativeCandidateRaw x).Valid := by
  unfold gaussianNormalizedProfileDerivativeCandidateRaw
  exact RealCompute.neg_valid
    (RealCompute.scaleRat_valid (gaussianNormalizedProfileRaw_valid x))

/-- The packaged Gaussian ODE candidate has exactly the expected scaled
profile width. -/
theorem gaussianNormalizedProfileDerivativeCandidateRaw_width
    (x : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute stage).width =
      qabs (2 * x) *
        ((gaussianNormalizedProfileRaw x).compute stage).width := by
  unfold gaussianNormalizedProfileDerivativeCandidateRaw
  change
    (QInterval.neg
      (QInterval.scaleRat (2 * x)
        ((gaussianNormalizedProfileRaw x).compute stage))).width = _
  rw [QInterval.neg_width, QInterval.scaleRat_width]

/-- On a rational box `|x| <= C`, the derivative candidate width is bounded
by `2 C` times the executable profile-width budget. -/
theorem gaussianNormalizedProfileDerivativeCandidateRaw_width_le
    (C x : Rat) (hx : qabs x <= C) (stage : Nat) :
    ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute stage).width <=
      (2 * C) * gaussianNormalizedProfileWidthBudget x stage := by
  rw [gaussianNormalizedProfileDerivativeCandidateRaw_width, qabs_mul]
  have htwo : qabs (2 : Rat) = 2 := by decide +kernel
  rw [htwo]
  have hscale : 2 * qabs x <= 2 * C :=
    Rat.mul_le_mul_of_nonneg_left hx (by decide +kernel)
  have hC0 : 0 <= C := Rat.le_trans (qabs_nonneg x) hx
  calc
    2 * qabs x * ((gaussianNormalizedProfileRaw x).compute stage).width <=
        2 * C * ((gaussianNormalizedProfileRaw x).compute stage).width :=
      Rat.mul_le_mul_of_nonneg_right hscale
        ((gaussianNormalizedProfileRaw_valid x).1 stage)
    _ <= 2 * C * gaussianNormalizedProfileWidthBudget x stage :=
      Rat.mul_le_mul_of_nonneg_left
        (gaussianNormalizedProfileRaw_width_le_budget x stage)
        (Rat.mul_nonneg (by decide +kernel) hC0)

/-- Scaling and negating the normalized base witness places the exact model
derivative inside the packaged `-2xG(x)` candidate box. -/
theorem gaussianNormalizedDerivativeCandidateValue_mem
    (x h : Rat) (stage : Nat) :
    ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute stage).lo <=
        gaussianNormalizedDerivativeCandidateValue x h stage /\
      gaussianNormalizedDerivativeCandidateValue x h stage <=
        ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute stage).hi := by
  have hbase := gaussianNormalizedDerivativeBaseValue_mem x h stage
  have hscaled := QInterval.scaleRat_mem (r := 2 * x) hbase
  have hneg := QInterval.neg_mem hscaled
  change
    (QInterval.neg
      (QInterval.scaleRat (2 * x)
        ((gaussianNormalizedProfileRaw x).compute stage))).lo <=
        -(2 * x * gaussianNormalizedDerivativeBaseValue x h stage) /\
      -(2 * x * gaussianNormalizedDerivativeBaseValue x h stage) <=
        (QInterval.neg
          (QInterval.scaleRat (2 * x)
            ((gaussianNormalizedProfileRaw x).compute stage))).hi
  exact hneg

/-- The derivative candidate as an everywhere-defined rational-input raw
function. -/
def gaussianNormalizedProfileDerivativeCandidateFunRaw : RealFunRaw where
  domain := RealFunRaw.entire
  compute := fun x =>
    (gaussianNormalizedProfileDerivativeCandidateRaw x).compute

theorem gaussianNormalizedProfileDerivativeCandidateFunRaw_valid :
    gaussianNormalizedProfileDerivativeCandidateFunRaw.Valid := by
  intro x _hx
  exact gaussianNormalizedProfileDerivativeCandidateRaw_valid x

/-- Stagewise normalized secant estimate for the exact witnesses already
placed inside the executable Gaussian boxes.  This is the analytic model
bound before choosing the final precision schedule. -/
theorem gaussianNormalizedDerivativeFiniteSecantError_le
    (C : Rat) (hC1 : 1 <= C) {x h : Rat} (hh : h ≠ 0)
    (hx : qabs x <= C) (hxh : qabs (x + h) <= C) (stage : Nat) :
    qabs
      (((gaussianNormalizedDerivativeStepValue x h stage -
          gaussianNormalizedDerivativeBaseValue x h stage) / h) -
        gaussianNormalizedDerivativeCandidateValue x h stage) <=
      (1 / gaussianFullLineMassLower) *
        (qabs h *
            (gaussianReciprocalPositiveProfileSecantBound C
              (gaussianDerivativeCommonTailIndex x h stage)
              hC1
              (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient +
          2 * C * RationalMajorant.factorialTailTerm (C * C)
            (gaussianDerivativeCommonTailIndex x h stage)) := by
  let terms := gaussianDerivativeCommonTailIndex x h stage
  let count := gaussianDerivativeCommonTerms x h stage
  let mass := gaussianMassReciprocalMidpoint stage
  let base : Rat :=
    1 / FiniteExponentialProduct.factorialPrefix count (x * x)
  let step : Rat :=
    1 / FiniteExponentialProduct.factorialPrefix count
      ((x + h) * (x + h))
  let candidate : Rat := -(2 * x / gaussianPositiveProfilePrefix (terms + 1) x)
  have hterms : 1 <= terms := by
    dsimp [terms]
    exact gaussianDerivativeCommonTailIndex_pos x h stage
  have hcount : count = terms + 1 := by
    dsimp [count, terms]
    exact gaussianDerivativeCommonTerms_eq_tailIndex_succ x h stage
  have hraw :=
    gaussianReciprocalPositiveProfile_secant_sub_candidate_qabs_le
      C terms hC1 hterms hh hx hxh
  have hraw' :
      qabs (((step - base) / h) - candidate) <=
        qabs h *
            (gaussianReciprocalPositiveProfileSecantBound
              C terms hC1 hterms).errorCoefficient +
          2 * C * RationalMajorant.factorialTailTerm (C * C) terms := by
    simpa [step, base, candidate,
      gaussianPositiveProfilePrefix_eq_factorialPrefix, hcount] using hraw
  have hmass0 : 0 <= mass := by
    dsimp [mass]
    exact gaussianMassReciprocalMidpoint_nonneg stage
  have hmass : mass <= 1 / gaussianFullLineMassLower := by
    dsimp [mass]
    exact gaussianMassReciprocalMidpoint_le stage
  let error : Rat :=
    qabs h *
        (gaussianReciprocalPositiveProfileSecantBound
          C terms hC1 hterms).errorCoefficient +
      2 * C * RationalMajorant.factorialTailTerm (C * C) terms
  have herror0 : 0 <= error := by
    dsimp [error]
    exact Rat.add_nonneg
      (Rat.mul_nonneg (qabs_nonneg _)
        (gaussianReciprocalPositiveProfileSecantBound
          C terms hC1 hterms).errorCoefficient_nonneg)
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by decide +kernel)
          (Rat.le_trans (by decide +kernel) hC1))
        (RationalMajorant.factorialTailTerm_nonneg
          (Rat.mul_nonneg
            (Rat.le_trans (by decide +kernel) hC1)
            (Rat.le_trans (by decide +kernel) hC1)) terms))
  have hfactor :
      (((mass * step - mass * base) / h) - mass * candidate) =
        mass * (((step - base) / h) - candidate) := by
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hbaseValue : gaussianNormalizedDerivativeBaseValue x h stage =
      mass * base := by
    rfl
  have hstepValue : gaussianNormalizedDerivativeStepValue x h stage =
      mass * step := by
    rfl
  have hcandidateValue :
      gaussianNormalizedDerivativeCandidateValue x h stage =
        mass * candidate := by
    unfold gaussianNormalizedDerivativeCandidateValue
    rw [hbaseValue]
    dsimp [candidate, base]
    rw [gaussianPositiveProfilePrefix_eq_factorialPrefix, ← hcount]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  rw [hbaseValue, hstepValue, hcandidateValue]
  rw [hfactor, qabs_mul, qabs_eq_self_of_nonneg hmass0]
  calc
    mass * qabs (((step - base) / h) - candidate) <= mass * error :=
      Rat.mul_le_mul_of_nonneg_left (by simpa [error] using hraw') hmass0
    _ <= (1 / gaussianFullLineMassLower) * error :=
      Rat.mul_le_mul_of_nonneg_right hmass herror0
    _ = (1 / gaussianFullLineMassLower) *
        (qabs h *
            (gaussianReciprocalPositiveProfileSecantBound C
              (gaussianDerivativeCommonTailIndex x h stage)
              hC1
              (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient +
          2 * C * RationalMajorant.factorialTailTerm (C * C)
            (gaussianDerivativeCommonTailIndex x h stage)) := by
      rfl

/-- Tolerance assigned to the first omitted factorial term.  After
multiplication by `2*C` and the normalization upper bound, it spends half of
the requested derivative precision. -/
def gaussianNormalizedDerivativeTailTolerance
    (C : Rat) (hC : 0 < C) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val * gaussianFullLineMassLower / (4 * C)
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (Rat.mul_pos (precisionAtStage n).property
          gaussianFullLineMassLower_pos)
        ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) hC)) }

/-- Explicit stage making the first omitted factorial monomial small enough
for the normalized Gaussian derivative budget. -/
def gaussianNormalizedDerivativeTailPrecision
    (C : Rat) (hC : 0 < C) (n : Nat) : Nat :=
  let A := C * C
  let start := RationalMajorant.factorialTailStart A
  start + RationalMajorant.halfDecayShift
    (RationalMajorant.factorialTailTerm A start)
    (gaussianNormalizedDerivativeTailTolerance C hC n)

theorem gaussianNormalizedDerivativeTailTerm_le_tolerance
    (C : Rat) (hC : 0 < C) (x h : Rat) (n : Nat) {stage : Nat}
    (hstage : gaussianNormalizedDerivativeTailPrecision C hC n <= stage) :
    RationalMajorant.factorialTailTerm (C * C)
        (gaussianDerivativeCommonTailIndex x h stage) <=
      (gaussianNormalizedDerivativeTailTolerance C hC n).val := by
  let A : Rat := C * C
  let start : Nat := RationalMajorant.factorialTailStart A
  let shift : Nat := RationalMajorant.halfDecayShift
    (RationalMajorant.factorialTailTerm A start)
    (gaussianNormalizedDerivativeTailTolerance C hC n)
  let index : Nat := gaussianDerivativeCommonTailIndex x h stage
  have hprecision : start + shift <= stage := by
    simpa [gaussianNormalizedDerivativeTailPrecision, A, start, shift] using hstage
  have hstageIndex : stage <= index := by
    dsimp [index]
    exact gaussianDerivativeCommonTailIndex_ge_stage x h stage
  have hstartIndex : start <= index := by omega
  have hshiftIndex : shift <= index - start := by omega
  have hindex : start + (index - start) = index := Nat.add_sub_of_le hstartIndex
  have hA0 : 0 <= A := by
    dsimp [A]
    exact Rat.mul_nonneg (Rat.le_of_lt hC) (Rat.le_of_lt hC)
  have hgeom := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hA0 (RationalMajorant.factorialTailStart_satisfies A) (index - start)
  have hdecay := RationalMajorant.halfDecayShift_spec_of_le
    (RationalMajorant.factorialTailTerm_nonneg hA0 start)
    (gaussianNormalizedDerivativeTailTolerance C hC n) hshiftIndex
  calc
    RationalMajorant.factorialTailTerm (C * C) index =
        RationalMajorant.factorialTailTerm A (start + (index - start)) := by
      rw [hindex]
    _ <= RationalMajorant.factorialTailTerm A start *
        ((1 : Rat) / 2) ^ (index - start) := hgeom
    _ <= (gaussianNormalizedDerivativeTailTolerance C hC n).val := hdecay

theorem gaussianNormalizedDerivativeTailBudget_le_half_precision
    (C : Rat) (hC : 0 < C) (x h : Rat) (n : Nat) {stage : Nat}
    (hstage : gaussianNormalizedDerivativeTailPrecision C hC n <= stage) :
    (1 / gaussianFullLineMassLower) *
        (2 * C * RationalMajorant.factorialTailTerm (C * C)
          (gaussianDerivativeCommonTailIndex x h stage)) <=
      (precisionAtStage n).val / 2 := by
  have htail := gaussianNormalizedDerivativeTailTerm_le_tolerance
    C hC x h n hstage
  have hscale0 : 0 <= (1 / gaussianFullLineMassLower) * (2 * C) := by
    exact Rat.mul_nonneg
      (by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 gaussianFullLineMassLower_pos))
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hC))
  calc
    (1 / gaussianFullLineMassLower) *
        (2 * C * RationalMajorant.factorialTailTerm (C * C)
          (gaussianDerivativeCommonTailIndex x h stage)) =
        ((1 / gaussianFullLineMassLower) * (2 * C)) *
          RationalMajorant.factorialTailTerm (C * C)
            (gaussianDerivativeCommonTailIndex x h stage) := by
      grind [Rat.mul_assoc]
    _ <= ((1 / gaussianFullLineMassLower) * (2 * C)) *
        (gaussianNormalizedDerivativeTailTolerance C hC n).val :=
      Rat.mul_le_mul_of_nonneg_left htail hscale0
    _ = (precisionAtStage n).val / 2 := by
      change
        ((1 / gaussianFullLineMassLower) * (2 * C)) *
            ((precisionAtStage n).val * gaussianFullLineMassLower / (4 * C)) =
          (precisionAtStage n).val / 2
      rw [Rat.div_def, Rat.div_def]
      have hmassNe : gaussianFullLineMassLower ≠ 0 :=
        Rat.ne_of_gt gaussianFullLineMassLower_pos
      have hCNe : C ≠ 0 := Rat.ne_of_gt hC
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The pointwise represented Gaussian ODE.  This is already exact at the
raw-real level; the remaining calculus theorem is that the first summand is
indeed the derivative of the represented Gaussian. -/
theorem gaussianNormalizedProfile_candidate_add_drift_equiv_zero (x : Rat) :
    (gaussianNormalizedProfileDerivativeCandidateRaw x +
      RealCompute.scaleRat (2 * x) (gaussianNormalizedProfileRaw x)).Equiv
        RealCompute.zero := by
  let drift : RealCompute :=
    RealCompute.scaleRat (2 * x) (gaussianNormalizedProfileRaw x)
  have hdrift : drift.Valid :=
    RealCompute.scaleRat_valid (gaussianNormalizedProfileRaw_valid x)
  have hcandidate : (-drift).Valid := RealCompute.neg_valid hdrift
  intro n
  have horder := RealCompute.interval_order_of_valid drift hdrift n
  apply (RealCompute.compareAt_overlap_iff ((-drift) + drift) RealCompute.zero n n).2
  change QInterval.Overlaps
    { lo := -(drift.compute n).hi + (drift.compute n).lo,
      hi := -(drift.compute n).lo + (drift.compute n).hi }
    { lo := 0, hi := 0 }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The normalized Gaussian restricted to a closed rational chart. -/
def gaussianNormalizedProfileOn (a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun _ => True
      compute := fun x => (gaussianNormalizedProfileRaw x).compute }
    a b (fun _ _ => trivial)
    (fun x _ => gaussianNormalizedProfileRaw_valid x)

/-- The represented derivative candidate restricted to the same chart. -/
def gaussianNormalizedProfileDerivativeCandidateOn
    (a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun _ => True
      compute := fun x =>
        (gaussianNormalizedProfileDerivativeCandidateRaw x).compute }
    a b (fun _ _ => trivial)
    (fun x _ => gaussianNormalizedProfileDerivativeCandidateRaw_valid x)

/-- The exact finite certificate still required to identify the represented
Gaussian derivative.  Naming this specialization makes the remaining proof
obligations inspectable: rational Taylor witnesses, their memberships in the
runtime boxes, one secant-error estimate, and two width budgets. -/
abbrev GaussianNormalizedProfileFiniteDerivativeCertificate (a b : Rat) :=
  FiniteModelDerivativeOnInterval
    (gaussianNormalizedProfileOn a b)
    (gaussianNormalizedProfileDerivativeCandidateOn a b)

/-- The three genuinely analytic schedules left after the exact finite
witness-membership layer has been discharged. -/
structure GaussianNormalizedProfileDerivativeBounds (a b : Rat) where
  stepPrecision : Nat -> Nat
  evalPrecision : Rat -> Rat -> Nat -> Nat
  secant_error : forall x h n,
    inDomainInterval a b x -> inDomainInterval a b (x + h) -> h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    qabs
      (((gaussianNormalizedDerivativeStepValue x h
            (evalPrecision x h n) -
          gaussianNormalizedDerivativeBaseValue x h
            (evalPrecision x h n)) / h) -
        gaussianNormalizedDerivativeCandidateValue x h
          (evalPrecision x h n)) <=
      (precisionAtStage n).val
  quotient_width : forall x h n,
    inDomainInterval a b x -> inDomainInterval a b (x + h) -> h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    (QInterval.differenceQuotient
      ((gaussianNormalizedProfileRaw (x + h)).compute
        (evalPrecision x h n))
      ((gaussianNormalizedProfileRaw x).compute
        (evalPrecision x h n)) h).width <=
      (precisionAtStage n).val
  derivative_width : forall x h n, inDomainInterval a b x ->
    ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute
      (evalPrecision x h n)).width <=
        (precisionAtStage n).val

/-- Fully explicit chart data from which the specialized Gaussian bounds are
assembled.  The secant field now asks only for the displayed rational budget;
the reciprocal-prefix calculus above proves that this budget controls the
actual normalized witnesses. -/
structure GaussianNormalizedProfileDerivativeSchedules (a b : Rat) where
  radius : Rat
  radius_one : 1 <= radius
  lower_in_box : -radius <= a
  upper_in_box : b <= radius
  stepPrecision : Nat -> Nat
  evalPrecision : Rat -> Rat -> Nat -> Nat
  model_error_budget : forall x h n,
    inDomainInterval a b x -> inDomainInterval a b (x + h) -> h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    (1 / gaussianFullLineMassLower) *
        (qabs h *
            (gaussianReciprocalPositiveProfileSecantBound radius
              (gaussianDerivativeCommonTailIndex x h
                (evalPrecision x h n))
              radius_one
              (gaussianDerivativeCommonTailIndex_pos x h
                (evalPrecision x h n))).errorCoefficient +
          2 * radius * RationalMajorant.factorialTailTerm
            (radius * radius)
            (gaussianDerivativeCommonTailIndex x h
              (evalPrecision x h n))) <=
      (precisionAtStage n).val
  quotient_width_budget : forall x h n,
    inDomainInterval a b x -> inDomainInterval a b (x + h) -> h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    qabs (1 / h) *
        (gaussianNormalizedProfileWidthBudget (x + h)
            (evalPrecision x h n) +
          gaussianNormalizedProfileWidthBudget x
            (evalPrecision x h n)) <=
      (precisionAtStage n).val
  derivative_width_budget : forall x h n, inDomainInterval a b x ->
    (2 * radius) * gaussianNormalizedProfileWidthBudget x
      (evalPrecision x h n) <=
        (precisionAtStage n).val

/-- A reduced Gaussian derivative schedule.  Callers choose only the
finite-model secant stage and the step schedule; the evaluator stage
automatically takes the maximum with the explicit runtime-width and omitted
factorial-tail stages. -/
structure GaussianNormalizedProfileDerivativeModelSchedule (a b : Rat) where
  radius : Rat
  radius_one : 1 <= radius
  radius_pos : 0 < radius
  lower_in_box : -radius <= a
  upper_in_box : b <= radius
  stepPrecision : Nat -> Nat
  modelPrecision : Rat -> Rat -> Nat -> Nat
  secant_error_budget : forall x h n,
    inDomainInterval a b x -> inDomainInterval a b (x + h) -> h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    let evalPrecision := Nat.max (modelPrecision x h n)
      (Nat.max
        (gaussianNormalizedProfileWidthEvalPrecision
          radius radius_pos x h n)
        (gaussianNormalizedDerivativeTailPrecision radius radius_pos n))
    (1 / gaussianFullLineMassLower) *
      (qabs h *
        (gaussianReciprocalPositiveProfileSecantBound radius
          (gaussianDerivativeCommonTailIndex x h evalPrecision)
          radius_one
          (gaussianDerivativeCommonTailIndex_pos x h
            evalPrecision)).errorCoefficient) <=
      (precisionAtStage n).val / 2

/-- A stage-independent rational majorant for all reciprocal positive
Gaussian-prefix secant coefficients on one symmetric chart.  Supplying this
finite coefficient inequality is now the sole remaining analytic input to
the automatic Gaussian derivative schedule. -/
structure GaussianReciprocalPositiveProfileUniformSecantBound
    (C : Rat) (hC1 : 1 <= C) where
  coefficient : Rat
  coefficient_nonneg : 0 <= coefficient
  errorCoefficient_le : forall (terms : Nat) (hterms : 1 <= terms),
    (gaussianReciprocalPositiveProfileSecantBound
      C terms hC1 hterms).errorCoefficient <= coefficient

/-- The computable factorial-series estimate supplies the formerly abstract
uniform reciprocal-prefix coefficient on every symmetric chart. -/
def gaussianReciprocalPositiveProfileUniformSecantCertificate
    (C : Rat) (hC1 : 1 <= C) :
    GaussianReciprocalPositiveProfileUniformSecantBound C hC1 where
  coefficient := gaussianReciprocalPositiveProfileSecantUniformBound C
  coefficient_nonneg :=
    gaussianReciprocalPositiveProfileSecantUniformBound_nonneg C hC1
  errorCoefficient_le := by
    intro terms hterms
    exact
      gaussianReciprocalPositiveProfileSecantBound_errorCoefficient_le_uniform
        C hC1 terms hterms

/-- Normalize a uniform reciprocal-prefix secant coefficient by the computed
full-line Gaussian mass lower bound. -/
def GaussianReciprocalPositiveProfileUniformSecantBound.normalizedCoefficient
    {C : Rat} {hC1 : 1 <= C}
    (U : GaussianReciprocalPositiveProfileUniformSecantBound C hC1) : Rat :=
  (1 / gaussianFullLineMassLower) * U.coefficient

theorem GaussianReciprocalPositiveProfileUniformSecantBound.normalizedCoefficient_nonneg
    {C : Rat} {hC1 : 1 <= C}
    (U : GaussianReciprocalPositiveProfileUniformSecantBound C hC1) :
    0 <= U.normalizedCoefficient := by
  exact Rat.mul_nonneg
    (by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 gaussianFullLineMassLower_pos))
    U.coefficient_nonneg

/-- A uniform reciprocal-prefix coefficient constructs the complete reduced
model schedule.  Widths and factorial tails are selected automatically. -/
def GaussianReciprocalPositiveProfileUniformSecantBound.toModelSchedule
    {a b C : Rat} (hC1 : 1 <= C) (hCpos : 0 < C)
    (hleft : -C <= a) (hright : b <= C)
    (U : GaussianReciprocalPositiveProfileUniformSecantBound C hC1) :
    GaussianNormalizedProfileDerivativeModelSchedule a b where
  radius := C
  radius_one := hC1
  radius_pos := hCpos
  lower_in_box := hleft
  upper_in_box := hright
  stepPrecision := fun n => RationalMajorant.dyadicStepPrecision
    (2 * U.normalizedCoefficient) (precisionAtStage n)
  modelPrecision := fun _x _h _n => 0
  secant_error_budget := by
    intro x h n hx hxh hh hsmall
    let stage := Nat.max 0
      (Nat.max
        (gaussianNormalizedProfileWidthEvalPrecision C hCpos x h n)
        (gaussianNormalizedDerivativeTailPrecision C hCpos n))
    let terms := gaussianDerivativeCommonTailIndex x h stage
    have hcoeff := U.errorCoefficient_le terms
      (gaussianDerivativeCommonTailIndex_pos x h stage)
    have hnorm0 := U.normalizedCoefficient_nonneg
    have hbound0 : 0 <= 2 * U.normalizedCoefficient :=
      Rat.mul_nonneg (by decide +kernel) hnorm0
    have hstep := RationalMajorant.dyadicStepPrecision_spec
      hbound0 (precisionAtStage n) hsmall
    have hhalf : qabs h * U.normalizedCoefficient <=
        (precisionAtStage n).val / 2 := by
      apply Rat.le_of_mul_le_mul_left (c := (2 : Rat))
      · calc
          2 * (qabs h * U.normalizedCoefficient) =
              qabs h * (2 * U.normalizedCoefficient) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ <= (precisionAtStage n).val := hstep
          _ = 2 * ((precisionAtStage n).val / 2) := by grind
      · decide +kernel
    have hinv0 : 0 <= 1 / gaussianFullLineMassLower := by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 gaussianFullLineMassLower_pos)
    have hnormalized :
        (1 / gaussianFullLineMassLower) *
            (gaussianReciprocalPositiveProfileSecantBound C terms hC1
              (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient <=
          U.normalizedCoefficient := by
      unfold GaussianReciprocalPositiveProfileUniformSecantBound.normalizedCoefficient
      exact Rat.mul_le_mul_of_nonneg_left hcoeff hinv0
    change
      (1 / gaussianFullLineMassLower) *
          (qabs h *
            (gaussianReciprocalPositiveProfileSecantBound C terms hC1
              (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient) <=
        (precisionAtStage n).val / 2
    calc
      (1 / gaussianFullLineMassLower) *
          (qabs h *
            (gaussianReciprocalPositiveProfileSecantBound C terms hC1
              (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient) =
          qabs h *
            ((1 / gaussianFullLineMassLower) *
              (gaussianReciprocalPositiveProfileSecantBound C terms hC1
                (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= qabs h * U.normalizedCoefficient :=
        Rat.mul_le_mul_of_nonneg_left hnormalized (qabs_nonneg _)
      _ <= (precisionAtStage n).val / 2 := hhalf

/-- The reduced model schedule supplies both runtime width budgets by the
mixed inverse-linear/geometric evaluator schedule. -/
def GaussianNormalizedProfileDerivativeModelSchedule.toSchedules
    {a b : Rat} (S : GaussianNormalizedProfileDerivativeModelSchedule a b) :
    GaussianNormalizedProfileDerivativeSchedules a b where
  radius := S.radius
  radius_one := S.radius_one
  lower_in_box := S.lower_in_box
  upper_in_box := S.upper_in_box
  stepPrecision := S.stepPrecision
  evalPrecision := fun x h n => Nat.max (S.modelPrecision x h n)
    (Nat.max
      (gaussianNormalizedProfileWidthEvalPrecision
        S.radius S.radius_pos x h n)
      (gaussianNormalizedDerivativeTailPrecision
        S.radius S.radius_pos n))
  model_error_budget := by
    intro x h n hx hxh hh hsmall
    let stage := Nat.max (S.modelPrecision x h n)
      (Nat.max
        (gaussianNormalizedProfileWidthEvalPrecision
          S.radius S.radius_pos x h n)
        (gaussianNormalizedDerivativeTailPrecision
          S.radius S.radius_pos n))
    have hsec := S.secant_error_budget x h n hx hxh hh hsmall
    have htailStage :
        gaussianNormalizedDerivativeTailPrecision
            S.radius S.radius_pos n <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have htail := gaussianNormalizedDerivativeTailBudget_le_half_precision
      S.radius S.radius_pos x h n htailStage
    change
      (1 / gaussianFullLineMassLower) *
          (qabs h *
              (gaussianReciprocalPositiveProfileSecantBound S.radius
                (gaussianDerivativeCommonTailIndex x h stage)
                S.radius_one
                (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient +
            2 * S.radius * RationalMajorant.factorialTailTerm
              (S.radius * S.radius)
              (gaussianDerivativeCommonTailIndex x h stage)) <=
        (precisionAtStage n).val
    have hsplit :
        (1 / gaussianFullLineMassLower) *
            (qabs h *
                (gaussianReciprocalPositiveProfileSecantBound S.radius
                  (gaussianDerivativeCommonTailIndex x h stage)
                  S.radius_one
                  (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient +
              2 * S.radius * RationalMajorant.factorialTailTerm
                (S.radius * S.radius)
                (gaussianDerivativeCommonTailIndex x h stage)) =
          (1 / gaussianFullLineMassLower) *
              (qabs h *
                (gaussianReciprocalPositiveProfileSecantBound S.radius
                  (gaussianDerivativeCommonTailIndex x h stage)
                  S.radius_one
                  (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient) +
            (1 / gaussianFullLineMassLower) *
              (2 * S.radius * RationalMajorant.factorialTailTerm
                (S.radius * S.radius)
                (gaussianDerivativeCommonTailIndex x h stage)) := by
      rw [Rat.mul_add]
    rw [hsplit]
    calc
      (1 / gaussianFullLineMassLower) *
            (qabs h *
              (gaussianReciprocalPositiveProfileSecantBound S.radius
                (gaussianDerivativeCommonTailIndex x h stage)
                S.radius_one
                (gaussianDerivativeCommonTailIndex_pos x h stage)).errorCoefficient) +
          (1 / gaussianFullLineMassLower) *
            (2 * S.radius * RationalMajorant.factorialTailTerm
              (S.radius * S.radius)
              (gaussianDerivativeCommonTailIndex x h stage)) <=
          (precisionAtStage n).val / 2 +
            (precisionAtStage n).val / 2 :=
        rat_add_le_add hsec htail
      _ = (precisionAtStage n).val := by grind
  quotient_width_budget := by
    intro x h n hx hxh hh hsmall
    exact gaussianNormalizedProfileWidthEvalPrecision_quotient_budget_of_le
      S.radius S.radius_pos x h hh n
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  derivative_width_budget := by
    intro x h n hx
    exact gaussianNormalizedProfileWidthEvalPrecision_derivative_budget_of_le
      S.radius S.radius_pos x h n
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))

/-- The finite reciprocal-prefix estimate discharges the semantic secant
field; only executable budget and width schedules remain. -/
def GaussianNormalizedProfileDerivativeSchedules.toBounds
    {a b : Rat} (S : GaussianNormalizedProfileDerivativeSchedules a b) :
    GaussianNormalizedProfileDerivativeBounds a b where
  stepPrecision := S.stepPrecision
  evalPrecision := S.evalPrecision
  secant_error := by
    intro x h n hx hxh hh hsmall
    have hxC : qabs x <= S.radius := by
      apply qabs_le_of_neg_le_le
      · exact Rat.le_trans S.lower_in_box hx.1
      · exact Rat.le_trans hx.2 S.upper_in_box
    have hxhC : qabs (x + h) <= S.radius := by
      apply qabs_le_of_neg_le_le
      · exact Rat.le_trans S.lower_in_box hxh.1
      · exact Rat.le_trans hxh.2 S.upper_in_box
    exact Rat.le_trans
      (gaussianNormalizedDerivativeFiniteSecantError_le
        S.radius S.radius_one hh hxC hxhC (S.evalPrecision x h n))
      (S.model_error_budget x h n hx hxh hh hsmall)
  quotient_width := by
    intro x h n hx hxh hh hsmall
    exact Rat.le_trans
      (gaussianNormalizedProfile_differenceQuotient_width_le
        x h (S.evalPrecision x h n))
      (S.quotient_width_budget x h n hx hxh hh hsmall)
  derivative_width := by
    intro x h n hx
    have hxC : qabs x <= S.radius := by
      apply qabs_le_of_neg_le_le
      · exact Rat.le_trans S.lower_in_box hx.1
      · exact Rat.le_trans hx.2 S.upper_in_box
    exact Rat.le_trans
      (gaussianNormalizedProfileDerivativeCandidateRaw_width_le
        S.radius x hxC (S.evalPrecision x h n))
      (S.derivative_width_budget x h n hx)

/-- All representation-membership fields of the finite Gaussian derivative
certificate are now automatic; only the three explicit analytic bounds above
must be supplied. -/
def GaussianNormalizedProfileDerivativeBounds.toFiniteCertificate
    {a b : Rat} (B : GaussianNormalizedProfileDerivativeBounds a b) :
    GaussianNormalizedProfileFiniteDerivativeCertificate a b where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := B.stepPrecision
  evalPrecision := B.evalPrecision
  baseValue := fun x h n =>
    gaussianNormalizedDerivativeBaseValue x h (B.evalPrecision x h n)
  stepValue := fun x h n =>
    gaussianNormalizedDerivativeStepValue x h (B.evalPrecision x h n)
  derivativeValue := fun x h n =>
    gaussianNormalizedDerivativeCandidateValue x h (B.evalPrecision x h n)
  base_mem := by
    intro x h n hx hxh
    change
      ((gaussianNormalizedProfileRaw x).compute
          (B.evalPrecision x h n)).lo <=
            gaussianNormalizedDerivativeBaseValue x h
              (B.evalPrecision x h n) /\
        gaussianNormalizedDerivativeBaseValue x h
            (B.evalPrecision x h n) <=
          ((gaussianNormalizedProfileRaw x).compute
            (B.evalPrecision x h n)).hi
    exact gaussianNormalizedDerivativeBaseValue_mem x h
      (B.evalPrecision x h n)
  step_mem := by
    intro x h n hx hxh
    change
      ((gaussianNormalizedProfileRaw (x + h)).compute
          (B.evalPrecision x h n)).lo <=
            gaussianNormalizedDerivativeStepValue x h
              (B.evalPrecision x h n) /\
        gaussianNormalizedDerivativeStepValue x h
            (B.evalPrecision x h n) <=
          ((gaussianNormalizedProfileRaw (x + h)).compute
            (B.evalPrecision x h n)).hi
    exact gaussianNormalizedDerivativeStepValue_mem x h
      (B.evalPrecision x h n)
  derivative_mem := by
    intro x h n hdx
    change
      ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute
          (B.evalPrecision x h n)).lo <=
            gaussianNormalizedDerivativeCandidateValue x h
              (B.evalPrecision x h n) /\
        gaussianNormalizedDerivativeCandidateValue x h
            (B.evalPrecision x h n) <=
          ((gaussianNormalizedProfileDerivativeCandidateRaw x).compute
            (B.evalPrecision x h n)).hi
    exact gaussianNormalizedDerivativeCandidateValue_mem x h
      (B.evalPrecision x h n)
  secant_error := by
    intro x h n hx hxh hh hsmall
    exact B.secant_error x h n hx hxh hh hsmall
  quotient_width := by
    intro x h n hx hxh hh hsmall
    exact B.quotient_width x h n hx hxh hh hsmall
  derivative_width := by
    intro x h n hdx
    exact B.derivative_width x h n hdx

/-- The final represented Gaussian derivative follows from the three
function-specific rational bounds, with no remaining representation
membership obligations. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval_of_bounds
    {a b : Rat} (B : GaussianNormalizedProfileDerivativeBounds a b) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  B.toFiniteCertificate.toHasDerivativeOnInterval

/-- Chart schedules with the explicit finite Gaussian budgets imply the full
represented derivative theorem directly. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval_of_schedules
    {a b : Rat} (S : GaussianNormalizedProfileDerivativeSchedules a b) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  gaussianNormalizedProfile_hasDerivativeOnInterval_of_bounds S.toBounds

/-- A finite-model schedule alone proves the represented Gaussian derivative;
all runtime interval widths are selected by the library. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval_of_modelSchedule
    {a b : Rat}
    (S : GaussianNormalizedProfileDerivativeModelSchedule a b) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  gaussianNormalizedProfile_hasDerivativeOnInterval_of_schedules S.toSchedules

/-- A single uniform finite reciprocal-prefix secant coefficient now implies
the full represented Gaussian derivative on the chart. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval_of_uniformSecantBound
    {a b C : Rat} (hC1 : 1 <= C) (hCpos : 0 < C)
    (hleft : -C <= a) (hright : b <= C)
    (U : GaussianReciprocalPositiveProfileUniformSecantBound C hC1) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  gaussianNormalizedProfile_hasDerivativeOnInterval_of_modelSchedule
    (U.toModelSchedule hC1 hCpos hleft hright)

/-- The normalized represented Gaussian has a public finite derivative model
on every closed rational chart contained in a computable symmetric box.
Keeping the rational witnesses is essential for later nonlinear composition
and represented-constant scaling. -/
def gaussianNormalizedProfileFiniteModel
    {a b C : Rat} (hC1 : 1 <= C)
    (hleft : -C <= a) (hright : b <= C) :
    GaussianNormalizedProfileFiniteDerivativeCertificate a b :=
  (((gaussianReciprocalPositiveProfileUniformSecantCertificate C hC1).toModelSchedule
    hC1 (by grind) hleft hright).toSchedules.toBounds).toFiniteCertificate

/-- The normalized represented Gaussian satisfies its analytic derivative
certificate on every closed rational chart contained in a computable
symmetric box.  All precision schedules are generated internally. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval
    {a b C : Rat} (hC1 : 1 <= C)
    (hleft : -C <= a) (hright : b <= C) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  (gaussianNormalizedProfileFiniteModel hC1 hleft hright).toHasDerivativeOnInterval

/-- Once the finite Gaussian model certificate is supplied, the generic
completeness-free bridge produces the full represented derivative theorem. -/
def gaussianNormalizedProfile_hasDerivativeOnInterval_of_finiteModel
    {a b : Rat}
    (M : GaussianNormalizedProfileFiniteDerivativeCertificate a b) :
    HasDerivativeOnInterval
      (gaussianNormalizedProfileOn a b)
      (gaussianNormalizedProfileDerivativeCandidateOn a b) :=
  M.toHasDerivativeOnInterval

/-- The Gaussian drift term `2 x G(x)` on a closed rational chart. -/
def gaussianNormalizedProfileDriftOn (a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun _ => True
      compute := fun x =>
        (RealCompute.scaleRat (2 * x) (gaussianNormalizedProfileRaw x)).compute }
    a b (fun _ _ => trivial)
    (fun x _ =>
      RealCompute.scaleRat_valid (gaussianNormalizedProfileRaw_valid x))

/-- The candidate derivative plus the Gaussian drift represents the zero
function on every rational chart. -/
theorem gaussianNormalizedProfile_ode_equivalent_zeroOn (a b : Rat) :
    FunctionOnInterval.Equivalent
      (FunctionOnInterval.add
        (gaussianNormalizedProfileDerivativeCandidateOn a b)
        (gaussianNormalizedProfileDriftOn a b) rfl rfl)
      (FunctionOnInterval.exactRat (fun _ => 0) a b) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x hxLeft hxZero
  change
    (gaussianNormalizedProfileDerivativeCandidateRaw x +
      RealCompute.scaleRat (2 * x) (gaussianNormalizedProfileRaw x)).Equiv
        RealCompute.zero
  exact gaussianNormalizedProfile_candidate_add_drift_equiv_zero x

end ComputableAnalysis


