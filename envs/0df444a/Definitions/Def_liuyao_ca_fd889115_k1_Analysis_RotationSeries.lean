-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RotationSeries
-- name    : liuyao_ca_fd889115_k1_Analysis_RotationSeries
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:08.387728+00:00
-- url     : https://prove2.me/theorems/d4451066-e0b3-4d11-825f-625b2f449e69
-- title:
--   Computable analysis · RotationSeries · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RotationSeries.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PeanoBaker
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FinitePolynomialCalculus

set_option autoImplicit true

/-!
# Finite complex rotation-series algebra

This module joins two already finite calculations: rational complex exponential
prefixes and constant-coefficient Peano--Baker rotation prefixes.  It
constructs a valid factorial-tail complex raw exponential on rational
imaginary-axis inputs; extending that evaluator to represented inputs and
identifying it with geometry remain separate work.
-/

namespace ComputableAnalysis

namespace RotationSeries

/-- Coordinate equality for the local rational-complex structure. -/
theorem qcomplex_ext {z w : QComplex}
    (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z
  cases w
  simp at hre him ⊢
  exact ⟨hre, him⟩

/-- The rational complex unit on the positive imaginary axis. -/
def imaginaryUnit : QComplex := { re := 0, im := 1 }

/-- The imaginary-axis input used by the rotation exponential prefix. -/
def imaginaryAxis (T : Rat) : QComplex :=
  QComplex.mul imaginaryUnit (QComplex.ofRat T)

theorem imaginaryAxis_coordinates (T : Rat) :
    imaginaryAxis T = { re := 0, im := T } := by
  unfold imaginaryAxis imaginaryUnit QComplex.mul QComplex.ofRat
  change ({ re := 0 * T - 1 * 0, im := 0 * 0 + 1 * T } : QComplex) =
    { re := 0, im := T }
  simp only [Rat.zero_mul, Rat.one_mul, Rat.sub_self, Rat.zero_add]

theorem imaginaryAxis_mul_real (T r : Rat) :
    QComplex.mul (imaginaryAxis T) { re := r, im := 0 } =
      { re := 0, im := T * r } := by
  rw [imaginaryAxis_coordinates]
  change ({ re := 0 * r - T * 0, im := 0 * 0 + T * r } : QComplex) =
    { re := 0, im := T * r }
  simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_self, Rat.zero_add]

theorem imaginaryAxis_mul_imaginary (T r : Rat) :
    QComplex.mul (imaginaryAxis T) { re := 0, im := r } =
      { re := -(T * r), im := 0 } := by
  rw [imaginaryAxis_coordinates]
  change ({ re := 0 * 0 - T * r, im := 0 * r + T * 0 } : QComplex) =
    { re := -(T * r), im := 0 }
  simp only [Rat.zero_mul, Rat.mul_zero, Rat.sub_eq_add_neg, Rat.add_zero]
  rw [Rat.zero_add]

/-- Even powers of the imaginary-axis input are real alternating powers. -/
theorem imaginaryAxis_pow_even (T : Rat) (k : Nat) :
    QComplex.pow (imaginaryAxis T) (2 * k) =
      { re := ((-1 : Rat) ^ k) * T ^ (2 * k), im := 0 } := by
  induction k with
  | zero =>
      simp [QComplex.pow, QComplex.one]
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [QComplex.pow]
      rw [show 2 * k + 1 = (2 * k) + 1 by omega]
      rw [QComplex.pow, ih]
      rw [imaginaryAxis_mul_real, imaginaryAxis_mul_imaginary]
      apply qcomplex_ext
      · simp
        simp only [Rat.pow_succ]
        grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_assoc, Rat.mul_comm]
      · rfl

/-- Odd powers of the imaginary-axis input are imaginary alternating powers. -/
theorem imaginaryAxis_pow_odd (T : Rat) (k : Nat) :
    QComplex.pow (imaginaryAxis T) (2 * k + 1) =
      { re := 0, im := ((-1 : Rat) ^ k) * T ^ (2 * k + 1) } := by
  rw [show 2 * k + 1 = (2 * k) + 1 by omega]
  rw [QComplex.pow, imaginaryAxis_pow_even]
  rw [imaginaryAxis_mul_real]
  apply qcomplex_ext
  · rfl
  · simp only [Rat.pow_succ]
    grind [Rat.mul_assoc, Rat.mul_comm]

/-- The even exponential term at an imaginary-axis input is the matching
cosine-type rational coefficient. -/
theorem expTerm_imaginary_even (T : Rat) (k : Nat) :
    ComplexSeries.expTerm (imaginaryAxis T) (2 * k) =
      { re := LinearODE.RotationSystem.cosineCoefficient T k, im := 0 } := by
  unfold ComplexSeries.expTerm
  rw [imaginaryAxis_pow_even]
  apply qcomplex_ext
  · change ((-1 : Rat) ^ k * T ^ (2 * k)) / factorialRat (2 * k) =
      T ^ (2 * k) / factorialRat (2 * k) * (-1 : Rat) ^ k
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  · change 0 / factorialRat (2 * k) = 0
    rw [Rat.div_def, Rat.zero_mul]

/-- The odd exponential term at an imaginary-axis input is the matching
sine-type rational coefficient on the imaginary axis. -/
theorem expTerm_imaginary_odd (T : Rat) (k : Nat) :
    ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1) =
      { re := 0, im := LinearODE.RotationSystem.sineCoefficient T k } := by
  unfold ComplexSeries.expTerm
  rw [imaginaryAxis_pow_odd]
  apply qcomplex_ext
  · change 0 / factorialRat (2 * k + 1) = 0
    rw [Rat.div_def, Rat.zero_mul]
  · change ((-1 : Rat) ^ k * T ^ (2 * k + 1)) /
      factorialRat (2 * k + 1) =
        T ^ (2 * k + 1) / factorialRat (2 * k + 1) * (-1 : Rat) ^ k
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- The alternating sign used by the formal sine and cosine coefficient
streams is the ordinary integer power of `-1`. -/
theorem altSign_eq_negOnePow (k : Nat) :
    FormalPowerSeries.altSign k = (-1 : Rat) ^ k := by
  have hsign_period (n : Nat) :
      FormalPowerSeries.altSign (n + 2) = FormalPowerSeries.altSign n := by
    unfold FormalPowerSeries.altSign
    have hmod : (n + 2) % 2 = n % 2 := by omega
    rw [hmod]
  have hpow_period (n : Nat) :
      (-1 : Rat) ^ (n + 2) = (-1 : Rat) ^ n := by
    rw [show n + 2 = (n + 1) + 1 by omega, Rat.pow_succ, Rat.pow_succ]
    have htwo : (-1 : Rat) * (-1) = 1 := by decide +kernel
    rw [Rat.mul_assoc, htwo, Rat.mul_one]
  have hpair : forall n,
      FormalPowerSeries.altSign n = (-1 : Rat) ^ n /\
      FormalPowerSeries.altSign (n + 1) = (-1 : Rat) ^ (n + 1) := by
    intro n
    induction n with
    | zero => constructor <;> rfl
    | succ n ih =>
        constructor
        · exact ih.2
        · calc
            FormalPowerSeries.altSign (n + 2) =
                FormalPowerSeries.altSign n := hsign_period n
            _ = (-1 : Rat) ^ n := ih.1
            _ = (-1 : Rat) ^ (n + 2) := (hpow_period n).symm
  exact (hpair k).1

/-- The even sine and odd cosine coefficients vanish. -/
theorem sineCosine_wrongParity (k : Nat) :
    FormalPowerSeries.sinCoeff (2 * k) = 0 /\
      FormalPowerSeries.cosCoeff (2 * k + 1) = 0 := by
  induction k with
  | zero =>
      constructor
      · simp [FormalPowerSeries.sinCoeff]
      · simp [FormalPowerSeries.cosCoeff, FormalPowerSeries.sinCoeff,
          Rat.div_def]
  | succ k ih =>
      have hs : FormalPowerSeries.sinCoeff (2 * (k + 1)) = 0 := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          FormalPowerSeries.sinCoeff, ih.2]
        simp [Rat.div_def]
      have hc : FormalPowerSeries.cosCoeff (2 * (k + 1) + 1) = 0 := by
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
          FormalPowerSeries.cosCoeff, hs]
        simp [Rat.div_def]
      exact ⟨hs, hc⟩

/-- The nonzero sine and cosine coefficients have their factorial formulas. -/
theorem sineCosine_factorialParity (k : Nat) :
    FormalPowerSeries.cosCoeff (2 * k) =
        FormalPowerSeries.altSign k / factorialRat (2 * k) /\
      FormalPowerSeries.sinCoeff (2 * k + 1) =
        FormalPowerSeries.altSign k / factorialRat (2 * k + 1) := by
  have hpair : forall k,
      FormalPowerSeries.cosCoeff (2 * k) =
          FormalPowerSeries.altSign k / factorialRat (2 * k) /\
        FormalPowerSeries.sinCoeff (2 * k + 1) =
          FormalPowerSeries.altSign k / factorialRat (2 * k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor <;> simp [FormalPowerSeries.cosCoeff,
          FormalPowerSeries.sinCoeff, FormalPowerSeries.altSign,
          factorialRat, factorial] <;> decide +kernel
    | succ k ih =>
        have hsign : FormalPowerSeries.altSign (k + 1) =
            -FormalPowerSeries.altSign k := by
          unfold FormalPowerSeries.altSign
          by_cases hk : k % 2 = 0
          · have hn : (k + 1) % 2 ≠ 0 := by omega
            simp [hk, hn]
          · have hn : (k + 1) % 2 = 0 := by omega
            simp [hk, hn]
        have hfact : factorialRat (2 * k + 2) =
            (((2 * k + 2 : Nat) : Rat) *
              factorialRat (2 * k + 1)) := by
          rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega,
          FormalPowerSeries.factorialRat_succ]
        have hcos : FormalPowerSeries.cosCoeff (2 * (k + 1)) =
            FormalPowerSeries.altSign (k + 1) /
              factorialRat (2 * (k + 1)) := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
            FormalPowerSeries.cosCoeff, ih.2, hfact, hsign]
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
        have hsin : FormalPowerSeries.sinCoeff (2 * (k + 1) + 1) =
            FormalPowerSeries.altSign (k + 1) /
              factorialRat (2 * (k + 1) + 1) := by
          rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
            FormalPowerSeries.sinCoeff, hcos,
            show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
            FormalPowerSeries.factorialRat_succ]
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
        exact ⟨hcos, hsin⟩
  exact hpair k

/-- The finite Peano--Baker cosine coefficient is the corresponding formal
Taylor cosine coefficient evaluated at the rational input. -/
theorem cosineCoefficient_eq_cosineTaylorTerm (T : Rat) (k : Nat) :
    LinearODE.RotationSystem.cosineCoefficient T k =
      FormalPowerSeries.cosineTaylorTerm T k := by
  unfold LinearODE.RotationSystem.cosineCoefficient
    FormalPowerSeries.cosineTaylorTerm
  rw [← altSign_eq_negOnePow k]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The finite Peano--Baker sine coefficient is the corresponding formal
Taylor sine coefficient evaluated at the rational input. -/
theorem sineCoefficient_eq_sineTaylorTerm (T : Rat) (k : Nat) :
    LinearODE.RotationSystem.sineCoefficient T k =
      FormalPowerSeries.sineTaylorTerm T k := by
  unfold LinearODE.RotationSystem.sineCoefficient
    FormalPowerSeries.sineTaylorTerm
  rw [← altSign_eq_negOnePow k]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The Peano--Baker cosine prefix is exactly the finite formal Taylor
cosine sum at every rational input. -/
theorem cosinePrefix_eq_cosineTaylorPartial (T : Rat) :
    forall n,
      LinearODE.RotationSystem.cosinePrefix T n =
        FormalPowerSeries.cosineTaylorPartial T n
  | 0 => rfl
  | n + 1 => by
      rw [LinearODE.RotationSystem.cosinePrefix,
        FormalPowerSeries.cosineTaylorPartial,
        cosinePrefix_eq_cosineTaylorPartial T n,
        cosineCoefficient_eq_cosineTaylorTerm]

/-- The Peano--Baker sine prefix is exactly the finite formal Taylor sine
sum at every rational input. -/
theorem sinePrefix_eq_sineTaylorPartial (T : Rat) :
    forall n,
      LinearODE.RotationSystem.sinePrefix T n =
        FormalPowerSeries.sineTaylorPartial T n
  | 0 => rfl
  | n + 1 => by
      rw [LinearODE.RotationSystem.sinePrefix,
        FormalPowerSeries.sineTaylorPartial,
        sinePrefix_eq_sineTaylorPartial T n,
        sineCoefficient_eq_sineTaylorTerm]

/-- The formal coefficient presentation used by the finite FTC calculus has
the same cosine polynomial as the alternating rotation prefix. -/
theorem cosineTaylorPrefix_eq_cosinePartial (T : Rat) :
    forall n,
      FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n) T =
        FormalPowerSeries.cosineTaylorPartial T n
  | 0 => rfl
  | n + 1 => by
      have ih := cosineTaylorPrefix_eq_cosinePartial T n
      have hstep := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.cosCoeff (2 * n) T
      have hstep' := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.cosCoeff (2 * n + 1) T
      have hzero := (sineCosine_wrongParity n).2
      have hformula := (sineCosine_factorialParity n).1
      have hterm : FormalPowerSeries.cosCoeff (2 * n) * T ^ (2 * n) =
          FormalPowerSeries.cosineTaylorTerm T n := by
        rw [hformula, FormalPowerSeries.cosineTaylorTerm,
          Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      calc
        FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
            (2 * (n + 1)) T =
            FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
              (2 * n + 1 + 1) T := by congr 2 <;> omega
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
              (2 * n + 1) T +
              FormalPowerSeries.cosCoeff (2 * n + 1) * T ^ (2 * n + 1) := hstep'
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
              (2 * n + 1) T := by
          rw [hzero, Rat.zero_mul, Rat.add_zero]
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
              (2 * n) T + FormalPowerSeries.cosCoeff (2 * n) * T ^ (2 * n) := hstep
        _ = FormalPowerSeries.cosineTaylorPartial T n +
              FormalPowerSeries.cosineTaylorTerm T n := by rw [ih, hterm]
        _ = FormalPowerSeries.cosineTaylorPartial T (n + 1) := by
              rw [FormalPowerSeries.cosineTaylorPartial]

/-- The formal coefficient presentation used by the finite FTC calculus has
the same sine polynomial as the alternating rotation prefix. -/
theorem sineTaylorPrefix_eq_sinePartial (T : Rat) :
    forall n,
      FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff (2 * n + 1) T =
        FormalPowerSeries.sineTaylorPartial T n
  | 0 => by
      simp [FinitePolynomial.taylorPrefix, FormalPowerSeries.sinCoeff,
        FinitePolynomial.integratedTaylorPrefix,
        FormalPowerSeries.sineTaylorPartial, Rat.zero_add]
  | n + 1 => by
      have ih := sineTaylorPrefix_eq_sinePartial T n
      have hstep := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.sinCoeff (2 * n + 1) T
      have hstep' := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.sinCoeff (2 * n + 2) T
      have hzero := (sineCosine_wrongParity (n + 1)).1
      have hzero' : FormalPowerSeries.sinCoeff (2 * n + 2) = 0 := by
        simpa only [Nat.mul_add, Nat.mul_one] using hzero
      have hformula := (sineCosine_factorialParity n).2
      have hterm : FormalPowerSeries.sinCoeff (2 * n + 1) * T ^ (2 * n + 1) =
          FormalPowerSeries.sineTaylorTerm T n := by
        rw [hformula, FormalPowerSeries.sineTaylorTerm,
          Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      calc
        FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
            (2 * (n + 1) + 1) T =
            FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
              (2 * n + 2 + 1) T := by congr 2 <;> omega
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
              (2 * n + 2) T +
              FormalPowerSeries.sinCoeff (2 * n + 2) * T ^ (2 * n + 2) := hstep'
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
              (2 * n + 2) T := by
          rw [hzero', Rat.zero_mul, Rat.add_zero]
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
              (2 * n + 1) T +
              FormalPowerSeries.sinCoeff (2 * n + 1) * T ^ (2 * n + 1) := hstep
        _ = FormalPowerSeries.sineTaylorPartial T n +
              FormalPowerSeries.sineTaylorTerm T n := by rw [ih, hterm]
        _ = FormalPowerSeries.sineTaylorPartial T (n + 1) := by
              rw [FormalPowerSeries.sineTaylorPartial]

/-- The negative coefficient stream gives the negative of the geometric sine
prefix. This is the finite companion needed for the cosine derivative
certificate. -/
theorem negSineTaylorPrefix_eq_negSinePartial (T : Rat) :
    forall n,
      FinitePolynomial.taylorPrefix
          (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) (2 * n + 1) T =
        -FormalPowerSeries.sineTaylorPartial T n
  | 0 => by
      simp [FinitePolynomial.taylorPrefix, FormalPowerSeries.neg,
        FormalPowerSeries.sinCoeff, FinitePolynomial.integratedTaylorPrefix,
        FormalPowerSeries.sineTaylorPartial]
      exact Rat.zero_add 0
  | n + 1 => by
      have ih := negSineTaylorPrefix_eq_negSinePartial T n
      have hstep := FinitePolynomial.taylorPrefix_succ
        (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) (2 * n + 1) T
      have hstep' := FinitePolynomial.taylorPrefix_succ
        (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) (2 * n + 2) T
      have hzero := (sineCosine_wrongParity (n + 1)).1
      have hsinZero : FormalPowerSeries.sinCoeff (2 * n + 2) = 0 := by
        simpa only [Nat.mul_add, Nat.mul_one] using hzero
      have hzero' : (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
          (2 * n + 2) = 0 := by
        simp [FormalPowerSeries.neg, hsinZero]
      have hformula := (sineCosine_factorialParity n).2
      have hterm : (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
            (2 * n + 1) * T ^ (2 * n + 1) =
          -FormalPowerSeries.sineTaylorTerm T n := by
        simp only [FormalPowerSeries.neg]
        rw [hformula, FormalPowerSeries.sineTaylorTerm,
          Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      have hindex : 2 * (n + 1) + 1 = 2 * n + 2 + 1 := by omega
      rw [hindex]
      calc
        FinitePolynomial.taylorPrefix
            (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
            (2 * n + 2 + 1) T =
            FinitePolynomial.taylorPrefix
              (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
              (2 * n + 2) T +
            (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
              (2 * n + 2) * T ^ (2 * n + 2) := hstep'
        _ = FinitePolynomial.taylorPrefix
              (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
              (2 * n + 2) T := by
          rw [hzero', Rat.zero_mul, Rat.add_zero]
        _ = FinitePolynomial.taylorPrefix
              (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
              (2 * n + 1) T +
            (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
              (2 * n + 1) * T ^ (2 * n + 1) := hstep
        _ = -FormalPowerSeries.sineTaylorPartial T (n + 1) := by
          rw [ih, hterm, FormalPowerSeries.sineTaylorPartial]
          rw [← Rat.neg_add]

/-- Finite geometric rotation cosine prefixes also have the full interval
derivative certificate from the FTC Taylor calculus. The derivative is the
negative of the preceding geometric sine prefix. -/
def rotationCosinePrefix_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (fun x => LinearODE.RotationSystem.cosinePrefix x (terms + 1)) a b)
      (FunctionOnInterval.exactRat
        (fun x => -LinearODE.RotationSystem.sinePrefix x terms) a b) := by
  have h := FinitePolynomial.cosineTaylorPrefix_hasDerivativeOnInterval
    (2 * terms + 1) a b C hleft hright hC1
  have hf : (fun x => LinearODE.RotationSystem.cosinePrefix x (terms + 1)) =
      FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (2 * terms + 2) := by
    funext x
    rw [cosinePrefix_eq_cosineTaylorPartial,
      ← cosineTaylorPrefix_eq_cosinePartial]
    congr 2 <;> omega
  have hdf : (fun x => -LinearODE.RotationSystem.sinePrefix x terms) =
      FinitePolynomial.taylorPrefix
        (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
        (2 * terms + 1) := by
    funext x
    rw [sinePrefix_eq_sineTaylorPartial,
      ← negSineTaylorPrefix_eq_negSinePartial]
  change HasDerivativeOnInterval
    (FunctionOnInterval.exactRat
      (FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (2 * terms + 2)) a b)
    (FunctionOnInterval.exactRat
      (FinitePolynomial.taylorPrefix
        (FormalPowerSeries.neg FormalPowerSeries.sinCoeff)
        (2 * terms + 1)) a b)
    at h
  rw [hf, hdf]
  exact h

/-- Every finite geometric rotation sine prefix carries the full interval
derivative certificate supplied by the finite FTC Taylor calculus, with the
matching geometric cosine prefix as derivative.  This concerns finite
prefixes only; passing to the factorial-tail raw evaluator still requires a
separate limit argument. -/
def rotationSinePrefix_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (fun x => LinearODE.RotationSystem.sinePrefix x terms) a b)
      (FunctionOnInterval.exactRat
        (fun x => LinearODE.RotationSystem.cosinePrefix x terms) a b) := by
  have h := FinitePolynomial.sineTaylorPrefix_hasDerivativeOnInterval
    (2 * terms) a b C hleft hright hC1
  have hf : (fun x => LinearODE.RotationSystem.sinePrefix x terms) =
      FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
        (2 * terms + 1) := by
    funext x
    rw [sinePrefix_eq_sineTaylorPartial, sineTaylorPrefix_eq_sinePartial]
  have hdf : (fun x => LinearODE.RotationSystem.cosinePrefix x terms) =
      FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (2 * terms) := by
    funext x
    rw [cosinePrefix_eq_cosineTaylorPartial, cosineTaylorPrefix_eq_cosinePartial]
  change HasDerivativeOnInterval
    (FunctionOnInterval.exactRat
      (FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
        (2 * terms + 1)) a b)
    (FunctionOnInterval.exactRat
      (FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (2 * terms)) a b)
    at h
  rw [hf, hdf]
  exact h

private theorem finOne_eq_zero (i : Fin 1) : i = 0 := by
  apply Fin.ext
  have hi := i.isLt
  omega

private theorem finTwo_one : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by
  decide +kernel

/-- Bundle the finite geometric rotation prefixes as a two-coordinate
interval function. The real coordinate includes one extra cosine term; this
aligns both coordinate derivative certificates with the same rational
rotation state up to one factorial-bounded defect. -/
def rotationPrefixFunctionVector (terms : Nat) (a b : Rat) :
    LinearODE.FunctionVectorOnInterval 2 a b where
  component := fun i => Fin.cases
    (FunctionOnInterval.exactRat
      (fun x => LinearODE.RotationSystem.cosinePrefix x (terms + 1)) a b)
    (fun _ => FunctionOnInterval.exactRat
      (fun x => LinearODE.RotationSystem.sinePrefix x terms) a b) i
  component_lower := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      have hj := finOne_eq_zero j
      subst j
      rfl
  component_upper := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      have hj := finOne_eq_zero j
      subst j
      rfl

/-- The exact finite derivative vector paired with the rotation prefix
state. -/
def rotationPrefixDerivativeVector (terms : Nat) (a b : Rat) :
    LinearODE.FunctionVectorOnInterval 2 a b where
  component := fun i => Fin.cases
    (FunctionOnInterval.exactRat
      (fun x => -LinearODE.RotationSystem.sinePrefix x terms) a b)
    (fun _ => FunctionOnInterval.exactRat
      (fun x => LinearODE.RotationSystem.cosinePrefix x terms) a b) i
  component_lower := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      have hj := finOne_eq_zero j
      subst j
      rfl
  component_upper := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      have hj := finOne_eq_zero j
      subst j
      rfl

/-- The bundled finite rotation vector has checked derivative evidence in
both coordinates, ready to be passed to `LinearODESolutionMeshData`. -/
def rotationPrefixFunctionVector_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    forall i : Fin 2,
      HasDerivativeOnInterval
        ((rotationPrefixFunctionVector terms a b).component i)
        ((rotationPrefixDerivativeVector terms a b).component i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact rotationCosinePrefix_hasDerivativeOnInterval
      terms a b C hleft hright hC1
  · intro j
    have hj := finOne_eq_zero j
    subst j
    exact rotationSinePrefix_hasDerivativeOnInterval
      terms a b C hleft hright hC1

/-- The finite rotation state uses one extra cosine term so its sine
derivative is the cosine prefix at the same index. -/
def rotationPrefixState (T : Rat) (terms : Nat) : LinearODE.RatVector 2 :=
  fun i => if i.val = 0 then
    LinearODE.RotationSystem.cosinePrefix T (terms + 1)
    else LinearODE.RotationSystem.sinePrefix T terms

/-- The derivative state certified by the two finite FTC derivative
theorems. -/
def rotationPrefixDerivativeState (T : Rat) (terms : Nat) : LinearODE.RatVector 2 :=
  fun i => if i.val = 0 then
    -LinearODE.RotationSystem.sinePrefix T terms
    else LinearODE.RotationSystem.cosinePrefix T terms

theorem rotationPrefixFunctionVector_lowerSample_eq_state
    (terms : Nat) (a b x : Rat)
    (hx : inDomainInterval a b x) (stages : Fin 2 -> Nat) :
    (rotationPrefixFunctionVector terms a b).lowerSample x hx stages =
      rotationPrefixState x terms := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    have hj := finOne_eq_zero j
    subst j
    rfl

theorem rotationPrefixDerivativeVector_lowerSample_eq_state
    (terms : Nat) (a b x : Rat)
    (hx : inDomainInterval a b x) (stages : Fin 2 -> Nat) :
    (rotationPrefixDerivativeVector terms a b).lowerSample x hx stages =
      rotationPrefixDerivativeState x terms := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    have hj := finOne_eq_zero j
    subst j
    rfl

/-- An explicit two-coordinate finite sum rule used to expose the rotation
matrix action without hiding its coordinates in `Fin` recursion. -/
private theorem finiteSum_two (f : Fin 2 -> Rat) :
    LinearODE.finiteSum f = f 0 + f 1 := by
  change f 0 + (f 1 + 0) = f 0 + f 1
  rw [Rat.add_zero]

/-- The rational rotation generator acts by `(-v, u)` on every two-coordinate
state. -/
theorem rotationGenerator_apply (x : LinearODE.RatVector 2) :
    LinearODE.matrixApply LinearODE.RotationSystem.generator x =
      (fun i => if i.val = 0 then -x 1 else x 0) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · change LinearODE.finiteSum
      (fun j => LinearODE.RotationSystem.generator 0 j * x j) = -x 1
    rw [finiteSum_two]
    change (0 : Rat) * x 0 + (-1 : Rat) *
      x (Fin.succ (0 : Fin 1)) = -x (Fin.succ (0 : Fin 1))
    grind [Rat.mul_assoc, Rat.mul_comm]
  · intro j
    have hj := finOne_eq_zero j
    subst j
    change LinearODE.finiteSum
      (fun k => LinearODE.RotationSystem.generator 1 k * x k) = x 0
    rw [finiteSum_two]
    change (1 : Rat) * x 0 + (0 : Rat) *
      x (Fin.succ (0 : Fin 1)) = x 0
    rw [Rat.zero_mul, Rat.one_mul, Rat.add_zero]

/-- The only defect in the paired finite rotation state is the last omitted
cosine term. The first coordinate satisfies the rotation equation exactly. -/
def rotationPrefixResidual (T : Rat) (terms : Nat) : LinearODE.RatVector 2 :=
  fun i => if i.val = 0 then 0
    else -LinearODE.RotationSystem.cosineCoefficient T terms

theorem rotationPrefixDerivativeState_eq_generator_state_add_residual
    (T : Rat) (terms : Nat) :
    rotationPrefixDerivativeState T terms =
      LinearODE.vectorAdd
        (LinearODE.matrixApply LinearODE.RotationSystem.generator
          (rotationPrefixState T terms))
        (rotationPrefixResidual T terms) := by
  rw [rotationGenerator_apply]
  funext i
  refine Fin.cases ?_ ?_ i
  · change -LinearODE.RotationSystem.sinePrefix T terms =
      -(rotationPrefixState T terms (Fin.succ (0 : Fin 1))) +
        rotationPrefixResidual T terms 0
    simp [rotationPrefixState, rotationPrefixResidual]
    exact (Rat.add_zero _).symm
  · intro j
    have hj := finOne_eq_zero j
    subst j
    change LinearODE.RotationSystem.cosinePrefix T terms =
      rotationPrefixState T terms 0 +
        rotationPrefixResidual T terms (Fin.succ (0 : Fin 1))
    simp [rotationPrefixState, rotationPrefixResidual,
      LinearODE.RotationSystem.cosinePrefix]
    grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]


/-- Rational absolute value commutes with a natural power.  This local lemma
keeps the complex-tail certificate below entirely in rational arithmetic. -/
private theorem qabs_pow (x : Rat) : forall n : Nat, qabs (x ^ n) = qabs x ^ n
  | 0 => by
      have hnot : ¬ ((1 : Rat) < 0) := by decide +kernel
      simp [Rat.pow_zero, qabs, hnot]
  | n + 1 => by
      rw [Rat.pow_succ, qabs_mul, qabs_pow, Rat.pow_succ]

private theorem qabs_neg_one_pow (n : Nat) : qabs ((-1 : Rat) ^ n) = 1 := by
  rw [qabs_pow]
  have hneg : (-1 : Rat) < 0 := by decide +kernel
  have habs : qabs (-1 : Rat) = 1 := by
    unfold qabs
    simp [hneg]
  rw [habs]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Rat.pow_succ, ih, Rat.one_mul]

private theorem qabs_inv_factorialRat (n : Nat) :
    qabs ((factorialRat n)⁻¹) = (factorialRat n)⁻¹ := by
  apply qabs_eq_self_of_nonneg
  exact Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos n))

/-- On a bounded rational input interval, every cosine term has an explicit
factorial majorant. This is the coefficient defect bound needed when finite
rotation prefixes are supplied to the linear-system mesh comparison. -/
theorem cosineCoefficient_qabs_le_factorialMajorant
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) (n : Nat) :
    qabs (LinearODE.RotationSystem.cosineCoefficient x n) <=
      RationalMajorant.factorialTailTerm C (2 * n) := by
  have hpow : forall m : Nat, qabs x ^ m <= C ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Rat.pow_succ, Rat.pow_succ]
        calc
          qabs x ^ m * qabs x <= C ^ m * qabs x :=
            Rat.mul_le_mul_of_nonneg_right ih (qabs_nonneg x)
          _ <= C ^ m * C :=
            Rat.mul_le_mul_of_nonneg_left hx (Rat.pow_nonneg hC)
  rw [cosineCoefficient_eq_cosineTaylorTerm]
  unfold FormalPowerSeries.cosineTaylorTerm
    RationalMajorant.factorialTailTerm
  simp only [Rat.div_def, qabs_mul, qabs_pow, qabs_inv_factorialRat]
  rw [altSign_eq_negOnePow, qabs_neg_one_pow]
  simp only [Rat.one_mul]
  exact Rat.mul_le_mul_of_nonneg_right (hpow (2 * n))
    (Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos (2 * n))))

/-- The residual vector for a finite rotation prefix has an explicit
factorial-tail norm bound on every rational interval bounded by `C`. -/
theorem rotationPrefixResidual_norm_le_factorialMajorant
    {C T : Rat} (hC : 0 <= C) (hT : qabs T <= C) (terms : Nat) :
    LinearODE.vectorAbsSum (rotationPrefixResidual T terms) <=
      RationalMajorant.factorialTailTerm C (2 * terms) := by
  have hcoef := cosineCoefficient_qabs_le_factorialMajorant hC hT terms
  calc
    LinearODE.vectorAbsSum (rotationPrefixResidual T terms) =
        qabs (LinearODE.RotationSystem.cosineCoefficient T terms) := by
      unfold LinearODE.vectorAbsSum
      rw [finiteSum_two]
      simp [rotationPrefixResidual, qabs_neg]
      rw [show qabs (0 : Rat) = 0 by decide +kernel, Rat.zero_add]
    _ <= RationalMajorant.factorialTailTerm C (2 * terms) := hcoef

/-- A fully explicit finite-stage certificate that the rotation Taylor
prefix is an approximate solution of the constant-coefficient rotation
system. It contains the interval derivative evidence, the exact rational
state sampled by the mesh, the linear-system residual identity, and its
factorial error bound. -/
structure RotationPrefixODEApproximation
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) where
  value : LinearODE.FunctionVectorOnInterval 2 a b
  derivative : LinearODE.FunctionVectorOnInterval 2 a b
  derivative_evidence : forall i : Fin 2,
    HasDerivativeOnInterval (value.component i) (derivative.component i)
  value_sample : forall T (hx : inDomainInterval a b T) (stages : Fin 2 -> Nat),
    value.lowerSample T hx stages = rotationPrefixState T terms
  derivative_sample : forall T (hx : inDomainInterval a b T)
      (stages : Fin 2 -> Nat),
    derivative.lowerSample T hx stages = rotationPrefixDerivativeState T terms
  state_equation : forall T,
    rotationPrefixDerivativeState T terms =
      LinearODE.vectorAdd
        (LinearODE.matrixApply LinearODE.RotationSystem.generator
          (rotationPrefixState T terms))
        (rotationPrefixResidual T terms)
  defect_bound : forall T, qabs T <= C ->
    LinearODE.vectorAbsSum (rotationPrefixResidual T terms) <=
      RationalMajorant.factorialTailTerm C (2 * terms)

/-- Construct the complete finite rotation approximation certificate from
the checked coefficient identities and FTC polynomial derivative estimates. -/
def rotationPrefixODEApproximation
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    RotationPrefixODEApproximation terms a b C hleft hright hC1 where
  value := rotationPrefixFunctionVector terms a b
  derivative := rotationPrefixDerivativeVector terms a b
  derivative_evidence := rotationPrefixFunctionVector_hasDerivativeOnInterval
    terms a b C hleft hright hC1
  value_sample := rotationPrefixFunctionVector_lowerSample_eq_state terms a b
  derivative_sample := rotationPrefixDerivativeVector_lowerSample_eq_state
    terms a b
  state_equation := fun T =>
    rotationPrefixDerivativeState_eq_generator_state_add_residual T terms
  defect_bound := fun T hT =>
    rotationPrefixResidual_norm_le_factorialMajorant
      (Rat.le_trans (by decide : (0 : Rat) <= 1) hC1) hT terms

/-- The real coordinate of each even imaginary-axis exponential term has the
standard factorial majorant exactly, rather than merely asymptotically. -/
theorem expTerm_imaginary_even_re_abs (T : Rat) (k : Nat) :
    qabs (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re =
      RationalMajorant.factorialTailTerm (qabs T) (2 * k) := by
  rw [expTerm_imaginary_even]
  unfold LinearODE.RotationSystem.cosineCoefficient
    RationalMajorant.factorialTailTerm
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_pow, qabs_inv_factorialRat,
    qabs_neg_one_pow]
  grind [Rat.div_def, Rat.mul_assoc]

/-- The imaginary coordinate of each odd imaginary-axis exponential term has
the standard factorial majorant exactly. -/
theorem expTerm_imaginary_odd_im_abs (T : Rat) (k : Nat) :
    qabs (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im =
      RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) := by
  rw [expTerm_imaginary_odd]
  unfold LinearODE.RotationSystem.sineCoefficient
    RationalMajorant.factorialTailTerm
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_pow, qabs_inv_factorialRat,
    qabs_neg_one_pow]
  grind [Rat.div_def, Rat.mul_assoc]

/-- The literal finite complex exponential prefix advances by its next
rational term. -/
theorem expPartial_succ (z : QComplex) (terms : Nat) :
    ComplexSeries.expPartial z (terms + 1) =
      QComplex.add (ComplexSeries.expPartial z terms) (ComplexSeries.expTerm z terms) := by
  unfold ComplexSeries.expPartial
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The complex form of the executable rotation prefix. -/
def complexPrefix (T : Rat) (n : Nat) : QComplex :=
  { re := LinearODE.RotationSystem.cosinePrefix T n,
    im := LinearODE.RotationSystem.sinePrefix T n }

/-- The certified factorial-tail start for the imaginary-axis exponential
input.  Its magnitude is purely rational. -/
def rotationTailStart (T : Rat) : Nat :=
  RationalMajorant.factorialTailStart (qabs T)

/-- Each stage advances by an even pair of complex exponential terms, so its
center remains exactly a cosine--sine rotation prefix. -/
def rotationTailTerms (T : Rat) (n : Nat) : Nat :=
  2 * (rotationTailStart T + n)

def rotationTailMagnitude (T : Rat) (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n)

/-- A deliberately slack radius: four times the first omitted term.  The
slack makes consecutive certified boxes nest while their centers advance by
one even--odd term pair. -/
def rotationTailRadius (T : Rat) (n : Nat) : Rat :=
  4 * rotationTailMagnitude T n

/-- The center stored at each stage of the certified complex rotation
evaluator. -/
def rotationCenter (T : Rat) (n : Nat) : QComplex :=
  complexPrefix T (rotationTailStart T + n)

/-- A symmetric rational complex box around a rotation-series center. -/
def rotationBox (T : Rat) (n : Nat) : QBox :=
  let c := rotationCenter T n
  let r := rotationTailRadius T n
  { lo := { re := c.re - r, im := c.im - r },
    hi := { re := c.re + r, im := c.im + r } }

/-- At every finite even truncation, the rational complex exponential at
`i*T` is exactly the cosine--sine rotation prefix. -/
theorem expPartial_imaginary_even_split (T : Rat) (n : Nat) :
    ComplexSeries.expPartial (imaginaryAxis T) (2 * n) = complexPrefix T n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [expPartial_succ]
      rw [show 2 * n + 1 = (2 * n) + 1 by omega]
      rw [expPartial_succ, ih]
      rw [expTerm_imaginary_even, expTerm_imaginary_odd]
      apply qcomplex_ext
      · change
          (LinearODE.RotationSystem.cosinePrefix T n +
              LinearODE.RotationSystem.cosineCoefficient T n) + 0 =
            LinearODE.RotationSystem.cosinePrefix T n +
              LinearODE.RotationSystem.cosineCoefficient T n
        exact Rat.add_zero _
      · change
          (LinearODE.RotationSystem.sinePrefix T n + 0) +
              LinearODE.RotationSystem.sineCoefficient T n =
            LinearODE.RotationSystem.sinePrefix T n +
              LinearODE.RotationSystem.sineCoefficient T n
        rw [Rat.add_zero]

/-- The even-stage centers of the complex evaluator are literally the finite
complex exponential prefixes, not a separately postulated rotation value. -/
theorem rotationCenter_eq_expPartial (T : Rat) (n : Nat) :
    rotationCenter T n =
      ComplexSeries.expPartial (imaginaryAxis T) (rotationTailTerms T n) := by
  unfold rotationCenter rotationTailTerms
  symm
  exact expPartial_imaginary_even_split T (rotationTailStart T + n)

private theorem rotation_tail_start (T : Rat) (n : Nat) :
    qabs T <= (((rotationTailTerms T n + 1 : Nat) : Rat) / 2) := by
  let s := RationalMajorant.factorialTailStart (qabs T)
  have hs := RationalMajorant.factorialTailStart_satisfies (qabs T)
  have hmono := RationalMajorant.factorialTailStart_mono (qabs T) s (s + 2 * n)
    (by simpa [s] using hs)
  change qabs T <= (((2 * (s + n) + 1 : Nat) : Rat) / 2)
  have hterms : s + (s + 2 * n) + 1 = 2 * (s + n) + 1 := by omega
  rw [hterms] at hmono
  exact hmono

theorem rotationTailMagnitude_nonneg (T : Rat) (n : Nat) :
    0 <= rotationTailMagnitude T n := by
  unfold rotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (qabs_nonneg T) _

private theorem rotationTailMagnitude_next_le_quarter (T : Rat) (n : Nat) :
    rotationTailMagnitude T (n + 1) <= rotationTailMagnitude T n * ((1 : Rat) / 2) ^ 2 := by
  have h := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := qabs T) (N := rotationTailTerms T n)
    (qabs_nonneg T) (rotation_tail_start T n) 2
  change RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T (n + 1)) <=
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n) *
      ((1 : Rat) / 2) ^ 2
  have hterms : rotationTailTerms T (n + 1) = rotationTailTerms T n + 2 := by
    unfold rotationTailTerms
    omega
  rw [hterms]
  exact h

private theorem rotationTailRadius_drop_majorizes (T : Rat) (n : Nat) :
    rotationTailMagnitude T n <=
      rotationTailRadius T n - rotationTailRadius T (n + 1) := by
  have hnext := rotationTailMagnitude_next_le_quarter T n
  have hmag0 := rotationTailMagnitude_nonneg T n
  have hquarter : ((1 : Rat) / 2) ^ 2 = (1 : Rat) / 4 := by decide +kernel
  rw [hquarter] at hnext
  have hfour : 4 * rotationTailMagnitude T (n + 1) <= rotationTailMagnitude T n := by
    calc
      4 * rotationTailMagnitude T (n + 1) <=
          4 * (rotationTailMagnitude T n * ((1 : Rat) / 4)) :=
        Rat.mul_le_mul_of_nonneg_left hnext (by decide +kernel)
      _ = rotationTailMagnitude T n := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold rotationTailRadius
  grind [Rat.sub_eq_add_neg]

private theorem rotationCenter_succ (T : Rat) (n : Nat) :
    rotationCenter T (n + 1) =
      QComplex.add
        (QComplex.add (rotationCenter T n)
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)))
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)) := by
  rw [rotationCenter_eq_expPartial, rotationCenter_eq_expPartial]
  unfold rotationTailTerms
  rw [show 2 * (rotationTailStart T + (n + 1)) =
      (2 * (rotationTailStart T + n) + 1) + 1 by omega]
  rw [expPartial_succ]
  rw [show 2 * (rotationTailStart T + n) + 1 =
      2 * (rotationTailStart T + n) + 1 by rfl]
  rw [expPartial_succ]

private theorem even_term_coordinate_bounds (T : Rat) (k : Nat) :
    -RationalMajorant.factorialTailTerm (qabs T) (2 * k) <=
        (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re /\
      (ComplexSeries.expTerm (imaginaryAxis T) (2 * k)).re <=
        RationalMajorant.factorialTailTerm (qabs T) (2 * k) := by
  have habs := expTerm_imaginary_even_re_abs T k
  constructor
  · rw [← habs]
    exact neg_qabs_le_self _
  · rw [← habs]
    exact self_le_qabs _

private theorem odd_term_coordinate_bounds (T : Rat) (k : Nat) :
    -RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) <=
        (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im /\
      (ComplexSeries.expTerm (imaginaryAxis T) (2 * k + 1)).im <=
        RationalMajorant.factorialTailTerm (qabs T) (2 * k + 1) := by
  have habs := expTerm_imaginary_odd_im_abs T k
  constructor
  · rw [← habs]
    exact neg_qabs_le_self _
  · rw [← habs]
    exact self_le_qabs _

private theorem rotationTailMagnitude_middle_le (T : Rat) (n : Nat) :
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
      rotationTailMagnitude T n := by
  have hhalf := RationalMajorant.factorialTailTerm_succ_le_half
    (qabs_nonneg T) (rotationTailTerms T n)
    (RationalMajorant.factorialTailRatio_le_half_from_start
      (qabs T) (rotationTailTerms T n) 0 (rotation_tail_start T n))
  have hmag0 := rotationTailMagnitude_nonneg T n
  change RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n) *
      ((1 : Rat) / 2) at hhalf
  calc
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T n + 1) <=
        rotationTailMagnitude T n * ((1 : Rat) / 2) := by
      simpa [rotationTailMagnitude] using hhalf
    _ <= rotationTailMagnitude T n := by
      have hhalf_le_one : (1 : Rat) / 2 <= 1 := by decide +kernel
      calc
        rotationTailMagnitude T n * ((1 : Rat) / 2) <=
            rotationTailMagnitude T n * 1 :=
          Rat.mul_le_mul_of_nonneg_left hhalf_le_one hmag0
        _ = rotationTailMagnitude T n := by rw [Rat.mul_one]

private theorem rotation_even_term_coordinate_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re /\
      (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re <=
        rotationTailMagnitude T n := by
  simpa [rotationTailMagnitude, rotationTailTerms] using
    even_term_coordinate_bounds T (rotationTailStart T + n)

private theorem rotation_odd_term_coordinate_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im /\
      (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im <=
        rotationTailMagnitude T n := by
  have hterm := odd_term_coordinate_bounds T (rotationTailStart T + n)
  have hmiddle := rotationTailMagnitude_middle_le T n
  have hterms : rotationTailTerms T n + 1 = 2 * (rotationTailStart T + n) + 1 := by
    unfold rotationTailTerms
    rfl
  constructor
  · rw [hterms]
    calc
      -rotationTailMagnitude T n <=
          -RationalMajorant.factorialTailTerm (qabs T) (2 * (rotationTailStart T + n) + 1) :=
        Rat.neg_le_neg (by simpa [rotationTailMagnitude, rotationTailTerms] using hmiddle)
      _ <= (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).im := hterm.1
  · rw [hterms]
    calc
      (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).im <=
          RationalMajorant.factorialTailTerm (qabs T) (2 * (rotationTailStart T + n) + 1) :=
        hterm.2
      _ <= rotationTailMagnitude T n := by
        simpa [rotationTailMagnitude, rotationTailTerms] using hmiddle

private theorem rotation_even_term_im_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (rotationTailStart T + n))).im = 0
  rw [expTerm_imaginary_even]

private theorem rotation_odd_term_re_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (rotationTailStart T + n) + 1)).re = 0
  rw [expTerm_imaginary_odd]

private theorem rotationCenter_step_re_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (rotationCenter T (n + 1)).re - (rotationCenter T n).re /\
      (rotationCenter T (n + 1)).re - (rotationCenter T n).re <=
        rotationTailMagnitude T n := by
  have hcenter := rotationCenter_succ T n
  have heven := rotation_even_term_coordinate_bounds T n
  have hoddzero := rotation_odd_term_re_eq_zero T n
  rw [hcenter]
  change -rotationTailMagnitude T n <=
      ((rotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re) -
        (rotationCenter T n).re /\
    ((rotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).re) -
        (rotationCenter T n).re <= rotationTailMagnitude T n
  rw [hoddzero]
  grind [Rat.sub_eq_add_neg]

private theorem rotationCenter_step_im_bounds (T : Rat) (n : Nat) :
    -rotationTailMagnitude T n <=
        (rotationCenter T (n + 1)).im - (rotationCenter T n).im /\
      (rotationCenter T (n + 1)).im - (rotationCenter T n).im <=
        rotationTailMagnitude T n := by
  have hcenter := rotationCenter_succ T n
  have hodd := rotation_odd_term_coordinate_bounds T n
  have hevenzero := rotation_even_term_im_eq_zero T n
  rw [hcenter]
  change -rotationTailMagnitude T n <=
      ((rotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im) -
        (rotationCenter T n).im /\
    ((rotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (rotationTailTerms T n + 1)).im) -
        (rotationCenter T n).im <= rotationTailMagnitude T n
  rw [hevenzero]
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_width (T : Rat) (n : Nat) :
    (rotationBox T n).width = 2 * rotationTailRadius T n := by
  unfold rotationBox QBox.width
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_height (T : Rat) (n : Nat) :
    (rotationBox T n).height = 2 * rotationTailRadius T n := by
  unfold rotationBox QBox.height
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem rotationBox_ordered (T : Rat) (n : Nat) :
    0 <= (rotationBox T n).width /\ 0 <= (rotationBox T n).height := by
  have hmag0 := rotationTailMagnitude_nonneg T n
  rw [rotationBox_width, rotationBox_height]
  unfold rotationTailRadius
  constructor <;> exact Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg (by decide +kernel) hmag0)

private theorem rotationBox_nested_step (T : Rat) (n : Nat) :
    QBox.NestedIn (rotationBox T (n + 1)) (rotationBox T n) := by
  have hre := rotationCenter_step_re_bounds T n
  have him := rotationCenter_step_im_bounds T n
  have hdrop := rotationTailRadius_drop_majorizes T n
  unfold QBox.NestedIn rotationBox
  dsimp
  constructor
  · constructor
    · grind [Rat.sub_eq_add_neg]
    · grind [Rat.sub_eq_add_neg]
  · constructor
    · grind [Rat.sub_eq_add_neg]
    · grind [Rat.sub_eq_add_neg]

private theorem qbox_nested_trans {A B C : QBox}
    (hAB : QBox.NestedIn A B) (hBC : QBox.NestedIn B C) :
    QBox.NestedIn A C := by
  exact ⟨QComplex.le_trans hBC.1 hAB.1, QComplex.le_trans hAB.2 hBC.2⟩

private theorem rotationBox_nested (T : Rat) :
    forall n m : Nat, n <= m -> QBox.NestedIn (rotationBox T m) (rotationBox T n)
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
      · have hnm' : n <= m := by omega
        exact qbox_nested_trans (rotationBox_nested_step T m) (rotationBox_nested T n m hnm')

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem half_pow_twice_le (n : Nat) :
    ((1 : Rat) / 2) ^ (2 * n) <= ((1 : Rat) / 2) ^ n := by
  rw [show 2 * n = n + n by omega, rat_pow_add]
  have hhalf0 : (0 : Rat) <= 1 / 2 := by decide +kernel
  have hhalf1 : (1 : Rat) / 2 <= 1 := by decide +kernel
  have hpow0 : 0 <= ((1 : Rat) / 2) ^ n := Rat.pow_nonneg hhalf0
  have hpow1 : ((1 : Rat) / 2) ^ n <= 1 := by
    induction n with
    | zero =>
        rw [Rat.pow_zero]
        exact Rat.le_refl
    | succ n ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ n * 1 :=
            Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]
          _ <= 1 := ih (Rat.pow_nonneg hhalf0)
  calc
    ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) ^ n <=
        ((1 : Rat) / 2) ^ n * 1 :=
      Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
    _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]

/-- The ratio-one-half schedule decreases with its natural stage. -/
theorem half_pow_antitone {n m : Nat} (hnm : n <= m) :
    ((1 : Rat) / 2) ^ m <= ((1 : Rat) / 2) ^ n := by
  have hdecomp : m = n + (m - n) := by omega
  rw [hdecomp, rat_pow_add]
  have hhalf0 : (0 : Rat) <= 1 / 2 := by decide +kernel
  have hhalf1 : (1 : Rat) / 2 <= 1 := by decide +kernel
  have hbase : 0 <= ((1 : Rat) / 2) ^ n := Rat.pow_nonneg hhalf0
  have hfactor : ((1 : Rat) / 2) ^ (m - n) <= 1 := by
    induction m - n with
    | zero =>
        rw [Rat.pow_zero]
        exact Rat.le_refl
    | succ k ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ k * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ k * 1 :=
            Rat.mul_le_mul_of_nonneg_left hhalf1
              (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
          _ <= 1 := ih
  calc
    ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) ^ (m - n) <=
        ((1 : Rat) / 2) ^ n * 1 :=
      Rat.mul_le_mul_of_nonneg_left hfactor hbase
    _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]

private theorem rotationTailMagnitude_le_geometric (T : Rat) (n : Nat) :
    rotationTailMagnitude T n <=
      rotationTailMagnitude T 0 * ((1 : Rat) / 2) ^ n := by
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := qabs T) (N := rotationTailTerms T 0)
    (qabs_nonneg T) (rotation_tail_start T 0) (2 * n)
  have hterms : rotationTailTerms T n = rotationTailTerms T 0 + 2 * n := by
    unfold rotationTailTerms
    omega
  unfold rotationTailMagnitude
  rw [hterms]
  calc
    RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0 + 2 * n) <=
        RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0) *
          ((1 : Rat) / 2) ^ (2 * n) := htail
    _ <= RationalMajorant.factorialTailTerm (qabs T) (rotationTailTerms T 0) *
          ((1 : Rat) / 2) ^ n :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_twice_le n)
        (RationalMajorant.factorialTailTerm_nonneg (qabs_nonneg T) _)

private theorem rotationBox_width_le_geometric (T : Rat) (n : Nat) :
    (rotationBox T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  have htail := rotationTailMagnitude_le_geometric T n
  rw [rotationBox_width]
  unfold rotationTailRadius
  calc
    2 * (4 * rotationTailMagnitude T n) = 8 * rotationTailMagnitude T n := by
      grind [Rat.mul_assoc]
    _ <= 8 * (rotationTailMagnitude T 0 * ((1 : Rat) / 2) ^ n) :=
      Rat.mul_le_mul_of_nonneg_left htail (by decide +kernel)
    _ = (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
      grind [Rat.mul_assoc]

private theorem rotationBox_height_le_geometric (T : Rat) (n : Nat) :
    (rotationBox T n).height <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  rw [rotationBox_height, ← rotationBox_width]
  exact rotationBox_width_le_geometric T n

private theorem rotationBox_widths_shrink (T : Rat) :
    ComplexCompute.WidthsShrinkToZero (rotationBox T) := by
  intro eps
  let bound : Rat := 8 * rotationTailMagnitude T 0
  let N : Nat := RationalMajorant.halfDecayShift bound eps
  refine ⟨N, ?_⟩
  intro n hn
  have hbound0 : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by decide +kernel) (rotationTailMagnitude_nonneg T 0)
  have hwidth := rotationBox_width_le_geometric T n
  have hheight := rotationBox_height_le_geometric T n
  have hfactor : ((1 : Rat) / 2) ^ n <= ((1 : Rat) / 2) ^ N := by
    let k := n - N
    have hNk : N + k = n := by
      dsimp [k]
      exact Nat.add_sub_of_le hn
    rw [← hNk, rat_pow_add]
    have hhalf0 : (0 : Rat) <= 1 / 2 := by decide +kernel
    have hhalf1 : (1 : Rat) / 2 <= 1 := by decide +kernel
    have hpow0 : 0 <= ((1 : Rat) / 2) ^ N := Rat.pow_nonneg hhalf0
    have hpow1 : ((1 : Rat) / 2) ^ k <= 1 := by
      induction k with
      | zero =>
          rw [Rat.pow_zero]
          exact Rat.le_refl
      | succ k ih =>
          rw [Rat.pow_succ]
          calc
            ((1 : Rat) / 2) ^ k * ((1 : Rat) / 2) <=
                ((1 : Rat) / 2) ^ k * 1 :=
              Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
            _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
            _ <= 1 := ih
    calc
      ((1 : Rat) / 2) ^ N * ((1 : Rat) / 2) ^ k <=
          ((1 : Rat) / 2) ^ N * 1 :=
        Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
      _ = ((1 : Rat) / 2) ^ N := by rw [Rat.mul_one]
  have hscaled : bound * ((1 : Rat) / 2) ^ n <=
      bound * ((1 : Rat) / 2) ^ N :=
    Rat.mul_le_mul_of_nonneg_left hfactor hbound0
  have hfinal := RationalMajorant.halfDecayShift_spec hbound0 eps
  dsimp [N] at hfactor hscaled hfinal ⊢
  dsimp [bound] at hwidth hheight hscaled hfinal
  exact ⟨Rat.le_trans hwidth (Rat.le_trans hscaled hfinal),
    Rat.le_trans hheight (Rat.le_trans hscaled hfinal)⟩

/-- Geometric width metadata for the imaginary-axis exponential evaluator.
Both coordinate widths are at most the displayed rational half-decay bound. -/
def rotationExpRate (T : Rat) : ComplexCompute.Rate (rotationBox T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by decide +kernel)
    (by decide +kernel)
    (fun n _ => ⟨rotationBox_width_le_geometric T n,
      rotationBox_height_le_geometric T n⟩)

/-- A certified complex raw evaluator for the exponential series at `i*T`.

Its finite centers are rotation prefixes and its symmetric rational boxes have
an explicit factorial-tail, half-geometric convergence rate. -/
def rotationExpRaw (T : Rat) : ComplexCompute where
  compute := rotationBox T
  rate := rotationExpRate T

theorem rotationExpRaw_compute (T : Rat) (n : Nat) :
    (rotationExpRaw T).compute n = rotationBox T n := rfl

/-- The public rate bound for the checked imaginary-axis exponential
evaluator. -/
theorem rotationExpRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationExpRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationBox_width_le_geometric T n

theorem rotationExpRaw_height_le_geometric (T : Rat) (n : Nat) :
    ((rotationExpRaw T).compute n).height <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationBox_height_le_geometric T n

/-- The factorial-tail boxes around the rotation prefixes form a valid raw
complex computation.  This establishes the complex convergence layer needed
before any Euler identity can connect it to geometric trigonometry. -/
theorem rotationExpRaw_valid (T : Rat) : (rotationExpRaw T).Valid := by
  unfold ComplexCompute.Valid ComplexCompute.ValidCompute rotationExpRaw
  constructor
  · exact rotationBox_ordered T
  · constructor
    · intro n m hnm
      have hnest := rotationBox_nested T n m hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact rotationBox_widths_shrink T

/-- The real coordinate boxes of the certified imaginary-axis exponential. -/
def rotationCosCompute (T : Rat) (n : Nat) : QInterval :=
  { lo := (rotationBox T n).lo.re, hi := (rotationBox T n).hi.re }

/-- The imaginary coordinate boxes of the certified imaginary-axis
exponential. -/
def rotationSinCompute (T : Rat) (n : Nat) : QInterval :=
  { lo := (rotationBox T n).lo.im, hi := (rotationBox T n).hi.im }

private theorem rotationCosCompute_width_le_geometric (T : Rat) (n : Nat) :
    (rotationCosCompute T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  change (rotationBox T n).width <=
    (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n
  exact rotationBox_width_le_geometric T n

private theorem rotationSinCompute_width_le_geometric (T : Rat) (n : Nat) :
    (rotationSinCompute T n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n := by
  change (rotationBox T n).height <=
    (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n
  exact rotationBox_height_le_geometric T n

def rotationCosRate (T : Rat) : RealCompute.Rate (rotationCosCompute T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by decide +kernel)
    (by decide +kernel)
    (fun n _ => rotationCosCompute_width_le_geometric T n)

def rotationSinRate (T : Rat) : RealCompute.Rate (rotationSinCompute T) :=
  .geometric 0
    (8 * rotationTailMagnitude T 0)
    ((1 : Rat) / 2)
    (by decide +kernel)
    (by decide +kernel)
    (fun n _ => rotationSinCompute_width_le_geometric T n)

/-- The power-series cosine coordinate at a rational input, as a certified
raw real computation. -/
def rotationCosRaw (T : Rat) : RealCompute where
  compute := rotationCosCompute T
  rate := rotationCosRate T

/-- The power-series sine coordinate at a rational input, as a certified raw
real computation. -/
def rotationSinRaw (T : Rat) : RealCompute where
  compute := rotationSinCompute T
  rate := rotationSinRate T

set_option maxHeartbeats 1000000 in
theorem rotationCosRaw_valid (T : Rat) : (rotationCosRaw T).Valid := by
  have hcompute : rotationCosCompute T = (fun n =>
      { lo := (rotationBox T n).lo.re, hi := (rotationBox T n).hi.re }) := by
    rfl
  change RealCompute.ValidCompute (rotationCosCompute T)
  rw [hcompute]
  exact ComplexCompute.realPart_valid (rotationExpRaw_valid T)

set_option maxHeartbeats 1000000 in
theorem rotationSinRaw_valid (T : Rat) : (rotationSinRaw T).Valid := by
  have hcompute : rotationSinCompute T = (fun n =>
      { lo := (rotationBox T n).lo.im, hi := (rotationBox T n).hi.im }) := by
    rfl
  change RealCompute.ValidCompute (rotationSinCompute T)
  rw [hcompute]
  exact ComplexCompute.imagPart_valid (rotationExpRaw_valid T)

theorem rotationCosRaw_compute (T : Rat) (n : Nat) :
    (rotationCosRaw T).compute n =
      { lo := LinearODE.RotationSystem.cosinePrefix T (rotationTailStart T + n) -
          rotationTailRadius T n,
        hi := LinearODE.RotationSystem.cosinePrefix T (rotationTailStart T + n) +
          rotationTailRadius T n } := rfl

theorem rotationSinRaw_compute (T : Rat) (n : Nat) :
    (rotationSinRaw T).compute n =
      { lo := LinearODE.RotationSystem.sinePrefix T (rotationTailStart T + n) -
          rotationTailRadius T n,
        hi := LinearODE.RotationSystem.sinePrefix T (rotationTailStart T + n) +
          rotationTailRadius T n } := rfl

theorem rotationCosRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationCosRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationCosCompute_width_le_geometric T n

theorem rotationSinRaw_width_le_geometric (T : Rat) (n : Nat) :
    ((rotationSinRaw T).compute n).width <=
      (8 * rotationTailMagnitude T 0) * ((1 : Rat) / 2) ^ n :=
  rotationSinCompute_width_le_geometric T n

/-!
## A uniform bounded-input rotation schedule

The preceding evaluator selects a factorial start from its particular rational
input.  For a represented parameter, such as the interval computation of
`pi/2`, it is more useful to have one schedule that works for every rational
sample in a fixed certified range.  The following construction fixes the
majorant at `2`; the later represented-input step need only control movement
of the rational samples, not a changing factorial start.
-/

/-- The common factorial start for every imaginary-axis input of absolute
value at most `2`. -/
def uniformRotationTailStart : Nat :=
  RationalMajorant.factorialTailStart 2

/-- Each uniform stage advances by an even pair of exponential terms. -/
def uniformRotationTailTerms (n : Nat) : Nat :=
  2 * (uniformRotationTailStart + n)

/-- The common scalar factorial majorant at the uniform stage. -/
def uniformRotationTailMagnitude (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n)

/-- Four times the common omitted-term bound, enough to absorb one paired
center update and keep the rational boxes nested. -/
def uniformRotationTailRadius (n : Nat) : Rat :=
  4 * uniformRotationTailMagnitude n

/-- The finite rotation prefix attached to the common bounded-input schedule. -/
def uniformRotationCenter (T : Rat) (n : Nat) : QComplex :=
  complexPrefix T (uniformRotationTailStart + n)

/- The change in a nonconstant cosine coefficient is controlled by the
shifted factorial majorant at radius two. -/
private theorem cosineCoefficient_succ_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (k : Nat) :
    qabs (LinearODE.RotationSystem.cosineCoefficient T (k + 1) -
        LinearODE.RotationSystem.cosineCoefficient U (k + 1)) <=
      qabs (T - U) * 2 *
        RationalMajorant.factorialTailTerm 2 (2 * k + 1) := by
  have hpower := RationalMajorant.qabs_power_div_factorial_sub_le_two
    hT hU (2 * k + 1)
  have hsign := qabs_neg_one_pow (k + 1)
  have hrewrite :
      LinearODE.RotationSystem.cosineCoefficient T (k + 1) -
          LinearODE.RotationSystem.cosineCoefficient U (k + 1) =
        (T ^ ((2 * k + 1) + 1) / factorialRat ((2 * k + 1) + 1) -
          U ^ ((2 * k + 1) + 1) / factorialRat ((2 * k + 1) + 1)) *
          ((-1 : Rat) ^ (k + 1)) := by
    unfold LinearODE.RotationSystem.cosineCoefficient
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  rw [hrewrite, qabs_mul, hsign, Rat.mul_one]
  exact hpower

/- The change in a sine coefficient is controlled by the preceding
factorial term at the same uniform radius. -/
private theorem sineCoefficient_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (k : Nat) :
    qabs (LinearODE.RotationSystem.sineCoefficient T k -
        LinearODE.RotationSystem.sineCoefficient U k) <=
      qabs (T - U) * 2 *
        RationalMajorant.factorialTailTerm 2 (2 * k) := by
  have hpower := RationalMajorant.qabs_power_div_factorial_sub_le_two
    hT hU (2 * k)
  have hsign := qabs_neg_one_pow k
  have hrewrite :
      LinearODE.RotationSystem.sineCoefficient T k -
          LinearODE.RotationSystem.sineCoefficient U k =
        (T ^ ((2 * k) + 1) / factorialRat ((2 * k) + 1) -
          U ^ ((2 * k) + 1) / factorialRat ((2 * k) + 1)) *
          ((-1 : Rat) ^ k) := by
    unfold LinearODE.RotationSystem.sineCoefficient
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  rw [hrewrite, qabs_mul, hsign, Rat.mul_one]
  exact hpower

/- The coordinatewise rational distance between two finite rotation
prefixes.  It is only a finite sum of rational absolute values. -/
def rotationPrefixDistance (T U : Rat) (m : Nat) : Rat :=
  qabs (LinearODE.RotationSystem.cosinePrefix T m -
      LinearODE.RotationSystem.cosinePrefix U m) +
    qabs (LinearODE.RotationSystem.sinePrefix T m -
      LinearODE.RotationSystem.sinePrefix U m)

/- The factorial budget for the first m rotation-prefix coefficient pairs. -/
def rotationPrefixSensitivity (m : Nat) : Rat :=
  2 * RationalMajorant.factorialTailPartial 2 0 (2 * m - 1)

private theorem rotationPrefixDistance_zero (T U : Rat) :
    rotationPrefixDistance T U 0 = 0 := by
  unfold rotationPrefixDistance
  change qabs ((0 : Rat) - 0) + qabs ((0 : Rat) - 0) = 0
  have hzero : qabs (0 : Rat) = 0 := by
    rw [qabs_eq_self_of_nonneg (by decide +kernel)]
  have hdiff : (0 : Rat) - 0 = 0 := by decide +kernel
  rw [hdiff, hzero]
  decide +kernel

private theorem rotationPrefixDistance_succ_le (T U : Rat) (m : Nat) :
    rotationPrefixDistance T U (m + 1) <=
      rotationPrefixDistance T U m +
        qabs (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) +
        qabs (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
  unfold rotationPrefixDistance
  simp only [LinearODE.RotationSystem.cosinePrefix,
    LinearODE.RotationSystem.sinePrefix]
  have hre :
      (LinearODE.RotationSystem.cosinePrefix T m +
          LinearODE.RotationSystem.cosineCoefficient T m) -
        (LinearODE.RotationSystem.cosinePrefix U m +
          LinearODE.RotationSystem.cosineCoefficient U m) =
        (LinearODE.RotationSystem.cosinePrefix T m -
          LinearODE.RotationSystem.cosinePrefix U m) +
        (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have him :
      (LinearODE.RotationSystem.sinePrefix T m +
          LinearODE.RotationSystem.sineCoefficient T m) -
        (LinearODE.RotationSystem.sinePrefix U m +
          LinearODE.RotationSystem.sineCoefficient U m) =
        (LinearODE.RotationSystem.sinePrefix T m -
          LinearODE.RotationSystem.sinePrefix U m) +
        (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  rw [hre, him]
  calc
    qabs (LinearODE.RotationSystem.cosinePrefix T m -
        LinearODE.RotationSystem.cosinePrefix U m +
        (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m)) +
      qabs (LinearODE.RotationSystem.sinePrefix T m -
        LinearODE.RotationSystem.sinePrefix U m +
        (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m)) <=
        (qabs (LinearODE.RotationSystem.cosinePrefix T m -
          LinearODE.RotationSystem.cosinePrefix U m) +
          qabs (LinearODE.RotationSystem.cosineCoefficient T m -
            LinearODE.RotationSystem.cosineCoefficient U m)) +
          (qabs (LinearODE.RotationSystem.sinePrefix T m -
            LinearODE.RotationSystem.sinePrefix U m) +
            qabs (LinearODE.RotationSystem.sineCoefficient T m -
              LinearODE.RotationSystem.sineCoefficient U m)) :=
      rat_add_le_add (qabs_add_le _ _) (qabs_add_le _ _)
    _ = rotationPrefixDistance T U m +
        qabs (LinearODE.RotationSystem.cosineCoefficient T m -
          LinearODE.RotationSystem.cosineCoefficient U m) +
        qabs (LinearODE.RotationSystem.sineCoefficient T m -
          LinearODE.RotationSystem.sineCoefficient U m) := by
      unfold rotationPrefixDistance
      grind [Rat.add_assoc, Rat.add_comm]

private theorem rotationPrefixSensitivity_succ_succ (m : Nat) :
    rotationPrefixSensitivity (m + 2) =
      rotationPrefixSensitivity (m + 1) +
        2 * RationalMajorant.factorialTailTerm 2 (2 * m + 1) +
        2 * RationalMajorant.factorialTailTerm 2 (2 * m + 2) := by
  unfold rotationPrefixSensitivity
  rw [show 2 * (m + 2) - 1 = (2 * m + 2) + 1 by omega,
    RationalMajorant.factorialTailPartial]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
    RationalMajorant.factorialTailPartial]
  have hindex : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [hindex]
  grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc, Rat.add_comm]

private theorem rotationPrefixDistance_le_sensitivity (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) :
    forall m : Nat,
      rotationPrefixDistance T U m <=
        qabs (T - U) * rotationPrefixSensitivity m
  | 0 => by
      rw [rotationPrefixDistance_zero]
      unfold rotationPrefixSensitivity
      change (0 : Rat) <= qabs (T - U) * (2 * 0)
      calc
        (0 : Rat) <= 0 := Rat.le_refl
        _ = qabs (T - U) * (2 * 0) := by
          rw [Rat.mul_zero]
          exact (Rat.mul_zero _).symm
  | 1 => by
      have hstep := rotationPrefixDistance_succ_le T U 0
      have hinvOne : ((1 : Rat)⁻¹) = 1 := by decide +kernel
      have hcosT : LinearODE.RotationSystem.cosineCoefficient T 0 = 1 := by
        simp [LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hcosU : LinearODE.RotationSystem.cosineCoefficient U 0 = 1 := by
        simp [LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hcos : qabs (LinearODE.RotationSystem.cosineCoefficient T 0 -
          LinearODE.RotationSystem.cosineCoefficient U 0) = 0 := by
        rw [hcosT, hcosU]
        have hzero : qabs (0 : Rat) = 0 := by
          rw [qabs_eq_self_of_nonneg (by decide +kernel)]
        rw [show (1 : Rat) - 1 = 0 by decide +kernel, hzero]
      have hsinT : LinearODE.RotationSystem.sineCoefficient T 0 = T := by
        simp [LinearODE.RotationSystem.sineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hsinU : LinearODE.RotationSystem.sineCoefficient U 0 = U := by
        simp [LinearODE.RotationSystem.sineCoefficient, factorialRat, factorial,
          Rat.div_def, hinvOne]
      have hsin : qabs (LinearODE.RotationSystem.sineCoefficient T 0 -
          LinearODE.RotationSystem.sineCoefficient U 0) = qabs (T - U) := by
        rw [hsinT, hsinU]
      rw [rotationPrefixDistance_zero, hcos, hsin, Rat.add_zero,
        Rat.zero_add] at hstep
      have hsens : rotationPrefixSensitivity 1 = 2 := by decide +kernel
      rw [hsens]
      calc
        rotationPrefixDistance T U 1 <= qabs (T - U) := hstep
        _ = qabs (T - U) * 1 := by rw [Rat.mul_one]
        _ <= qabs (T - U) * 2 :=
          Rat.mul_le_mul_of_nonneg_left (by decide +kernel) (qabs_nonneg _)
  | m + 2 => by
      have ih := rotationPrefixDistance_le_sensitivity T U hT hU (m + 1)
      have hstep := rotationPrefixDistance_succ_le T U (m + 1)
      have hcos := cosineCoefficient_succ_input_lipschitz T U hT hU m
      have hsin := sineCoefficient_input_lipschitz T U hT hU (m + 1)
      have hsens := rotationPrefixSensitivity_succ_succ m
      rw [hsens]
      calc
        rotationPrefixDistance T U (m + 2) <=
            rotationPrefixDistance T U (m + 1) +
              qabs (LinearODE.RotationSystem.cosineCoefficient T (m + 1) -
                LinearODE.RotationSystem.cosineCoefficient U (m + 1)) +
              qabs (LinearODE.RotationSystem.sineCoefficient T (m + 1) -
                LinearODE.RotationSystem.sineCoefficient U (m + 1)) := hstep
        _ <= qabs (T - U) * rotationPrefixSensitivity (m + 1) +
              (qabs (T - U) * 2 *
                RationalMajorant.factorialTailTerm 2 (2 * m + 1)) +
              (qabs (T - U) * 2 *
                RationalMajorant.factorialTailTerm 2 (2 * m + 2)) :=
          rat_add_le_add (rat_add_le_add ih hcos) hsin
        _ = qabs (T - U) *
            (rotationPrefixSensitivity (m + 1) +
              2 * RationalMajorant.factorialTailTerm 2 (2 * m + 1) +
              2 * RationalMajorant.factorialTailTerm 2 (2 * m + 2)) := by
          grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc]

/- The finite sensitivity budget is uniformly bounded by sixteen on the
fixed input range.  It is intentionally coarse: it buys one simple rational
radius for a later represented-input construction. -/
private theorem rotationPrefixSensitivity_le_sixteen (m : Nat) :
    rotationPrefixSensitivity m <= 16 := by
  unfold rotationPrefixSensitivity
  calc
    2 * RationalMajorant.factorialTailPartial 2 0 (2 * m - 1) <= 2 * 8 :=
      Rat.mul_le_mul_of_nonneg_left
        (RationalMajorant.factorialTailPartial_two_le_eight (2 * m - 1))
        (by decide +kernel)
    _ = 16 := by decide +kernel

/- A common bounded-input factorial prefix is Lipschitz in its rational
input.  The statement is still entirely finite: both sides refer only to a
specified pair of rational prefixes. -/
theorem uniformRotationCenter_input_lipschitz (T U : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (n : Nat) :
    qabs ((uniformRotationCenter T n).re - (uniformRotationCenter U n).re) <=
        16 * qabs (T - U) /\
      qabs ((uniformRotationCenter T n).im - (uniformRotationCenter U n).im) <=
        16 * qabs (T - U) := by
  have hdistance := rotationPrefixDistance_le_sensitivity T U hT hU
    (uniformRotationTailStart + n)
  have hsensitivity := rotationPrefixSensitivity_le_sixteen
    (uniformRotationTailStart + n)
  have hsum : rotationPrefixDistance T U (uniformRotationTailStart + n) <=
      qabs (T - U) * 16 := by
    calc
      rotationPrefixDistance T U (uniformRotationTailStart + n) <=
          qabs (T - U) *
            rotationPrefixSensitivity (uniformRotationTailStart + n) := hdistance
      _ <= qabs (T - U) * 16 :=
        Rat.mul_le_mul_of_nonneg_left hsensitivity (qabs_nonneg _)
  have hre :
      qabs (LinearODE.RotationSystem.cosinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.cosinePrefix U
          (uniformRotationTailStart + n)) <=
        rotationPrefixDistance T U (uniformRotationTailStart + n) := by
    unfold rotationPrefixDistance
    have himnonneg : 0 <= qabs (LinearODE.RotationSystem.sinePrefix T
        (uniformRotationTailStart + n) -
      LinearODE.RotationSystem.sinePrefix U
        (uniformRotationTailStart + n)) := qabs_nonneg _
    grind
  have him :
      qabs (LinearODE.RotationSystem.sinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix U
          (uniformRotationTailStart + n)) <=
        rotationPrefixDistance T U (uniformRotationTailStart + n) := by
    unfold rotationPrefixDistance
    have hrenonneg : 0 <= qabs (LinearODE.RotationSystem.cosinePrefix T
        (uniformRotationTailStart + n) -
      LinearODE.RotationSystem.cosinePrefix U
        (uniformRotationTailStart + n)) := qabs_nonneg _
    grind
  constructor <;> unfold uniformRotationCenter complexPrefix
  · calc
      qabs (LinearODE.RotationSystem.cosinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.cosinePrefix U
          (uniformRotationTailStart + n)) <=
          rotationPrefixDistance T U (uniformRotationTailStart + n) := hre
      _ <= qabs (T - U) * 16 := hsum
      _ = 16 * qabs (T - U) := by grind [Rat.mul_comm]
  · calc
      qabs (LinearODE.RotationSystem.sinePrefix T
          (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix U
          (uniformRotationTailStart + n)) <=
          rotationPrefixDistance T U (uniformRotationTailStart + n) := him
      _ <= qabs (T - U) * 16 := hsum
      _ = 16 * qabs (T - U) := by grind [Rat.mul_comm]

/-- A symmetric complex box around the uniform bounded-input rotation
prefix. -/
def uniformRotationBox (T : Rat) (n : Nat) : QBox :=
  let c := uniformRotationCenter T n
  let r := uniformRotationTailRadius n
  { lo := { re := c.re - r, im := c.im - r },
    hi := { re := c.re + r, im := c.im + r } }

private theorem uniform_rotation_tail_start (n : Nat) :
    (2 : Rat) <= (((uniformRotationTailTerms n + 1 : Nat) : Rat) / 2) := by
  let s := uniformRotationTailStart
  have hs := RationalMajorant.factorialTailStart_satisfies (2 : Rat)
  have hmono := RationalMajorant.factorialTailStart_mono (2 : Rat) s (s + 2 * n)
    (by simpa [s, uniformRotationTailStart] using hs)
  change (2 : Rat) <= (((2 * (s + n) + 1 : Nat) : Rat) / 2)
  have hterms : s + (s + 2 * n) + 1 = 2 * (s + n) + 1 := by omega
  rw [hterms] at hmono
  exact hmono

private theorem uniformRotationTailMagnitude_nonneg (n : Nat) :
    0 <= uniformRotationTailMagnitude n := by
  unfold uniformRotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) _

private theorem uniformRotationTailMagnitude_next_le_quarter (n : Nat) :
    uniformRotationTailMagnitude (n + 1) <=
      uniformRotationTailMagnitude n * ((1 : Rat) / 2) ^ 2 := by
  have h := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformRotationTailTerms n)
    (by decide +kernel) (uniform_rotation_tail_start n) 2
  change RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms (n + 1)) <=
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n) *
      ((1 : Rat) / 2) ^ 2
  have hterms : uniformRotationTailTerms (n + 1) =
      uniformRotationTailTerms n + 2 := by
    unfold uniformRotationTailTerms
    omega
  rw [hterms]
  exact h

private theorem uniformRotationTailRadius_drop_majorizes (n : Nat) :
    uniformRotationTailMagnitude n <=
      uniformRotationTailRadius n - uniformRotationTailRadius (n + 1) := by
  have hnext := uniformRotationTailMagnitude_next_le_quarter n
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  have hquarter : ((1 : Rat) / 2) ^ 2 = (1 : Rat) / 4 := by decide +kernel
  rw [hquarter] at hnext
  have hfour : 4 * uniformRotationTailMagnitude (n + 1) <=
      uniformRotationTailMagnitude n := by
    calc
      4 * uniformRotationTailMagnitude (n + 1) <=
          4 * (uniformRotationTailMagnitude n * ((1 : Rat) / 4)) :=
        Rat.mul_le_mul_of_nonneg_left hnext (by decide +kernel)
      _ = uniformRotationTailMagnitude n := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  unfold uniformRotationTailRadius
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationCenter_succ (T : Rat) (n : Nat) :
    uniformRotationCenter T (n + 1) =
      QComplex.add
        (QComplex.add (uniformRotationCenter T n)
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)))
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)) := by
  unfold uniformRotationCenter uniformRotationTailTerms
  rw [← expPartial_imaginary_even_split T (uniformRotationTailStart + (n + 1)),
    ← expPartial_imaginary_even_split T (uniformRotationTailStart + n)]
  rw [show 2 * (uniformRotationTailStart + (n + 1)) =
      (2 * (uniformRotationTailStart + n) + 1) + 1 by omega]
  rw [expPartial_succ, expPartial_succ]

/-- The bounded-input center is still the literal even exponential prefix. -/
theorem uniformRotationCenter_eq_expPartial (T : Rat) (n : Nat) :
    uniformRotationCenter T n =
      ComplexSeries.expPartial (imaginaryAxis T) (uniformRotationTailTerms n) := by
  unfold uniformRotationCenter uniformRotationTailTerms
  symm
  exact expPartial_imaginary_even_split T (uniformRotationTailStart + n)

private theorem uniformRotationTailMagnitude_middle_le (n : Nat) :
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
      uniformRotationTailMagnitude n := by
  have hhalf := RationalMajorant.factorialTailTerm_succ_le_half
    (by decide +kernel : (0 : Rat) <= 2) (uniformRotationTailTerms n)
    (RationalMajorant.factorialTailRatio_le_half_from_start
      2 (uniformRotationTailTerms n) 0 (uniform_rotation_tail_start n))
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  change RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
      RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n) *
        ((1 : Rat) / 2)
    at hhalf
  calc
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n + 1) <=
        uniformRotationTailMagnitude n * ((1 : Rat) / 2) := by
      simpa [uniformRotationTailMagnitude] using hhalf
    _ <= uniformRotationTailMagnitude n := by
      have hhalf_le_one : (1 : Rat) / 2 <= 1 := by decide +kernel
      calc
        uniformRotationTailMagnitude n * ((1 : Rat) / 2) <=
            uniformRotationTailMagnitude n * 1 :=
          Rat.mul_le_mul_of_nonneg_left hhalf_le_one hmag0
        _ = uniformRotationTailMagnitude n := by rw [Rat.mul_one]

private theorem uniform_rotation_even_term_coordinate_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n)).re /\
      (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n)).re <=
        uniformRotationTailMagnitude n := by
  have hterm := even_term_coordinate_bounds T (uniformRotationTailStart + n)
  have hmono := RationalMajorant.factorialTailTerm_mono (qabs_nonneg T) hT
    (2 * (uniformRotationTailStart + n))
  constructor
  · change -RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n)) <=
      (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re
    calc
      -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) <=
        -RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n)) := Rat.neg_le_neg hmono
      _ <= (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re := hterm.1
  · change (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).re <=
      RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n))
    exact Rat.le_trans hterm.2 hmono

private theorem uniform_rotation_odd_term_coordinate_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im /\
      (ComplexSeries.expTerm
          (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im <=
        uniformRotationTailMagnitude n := by
  have hterm := odd_term_coordinate_bounds T (uniformRotationTailStart + n)
  have hmono := RationalMajorant.factorialTailTerm_mono (qabs_nonneg T) hT
    (2 * (uniformRotationTailStart + n) + 1)
  have hmiddle := uniformRotationTailMagnitude_middle_le n
  constructor
  · change -RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n)) <=
      (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im
    calc
      -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) <=
        -RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n) + 1) := by
            apply Rat.neg_le_neg
            simpa [uniformRotationTailMagnitude, uniformRotationTailTerms] using hmiddle
      _ <= -RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n) + 1) := Rat.neg_le_neg hmono
      _ <= (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im := hterm.1
  · change (ComplexSeries.expTerm
        (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im <=
      RationalMajorant.factorialTailTerm 2
        (2 * (uniformRotationTailStart + n))
    calc
      (ComplexSeries.expTerm
          (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).im <=
        RationalMajorant.factorialTailTerm (qabs T)
          (2 * (uniformRotationTailStart + n) + 1) := hterm.2
      _ <= RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n) + 1) := hmono
      _ <= RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n)) := by
        simpa [uniformRotationTailMagnitude, uniformRotationTailTerms] using hmiddle

private theorem uniform_rotation_even_term_im_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm
      (imaginaryAxis T) (uniformRotationTailTerms n)).im = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (uniformRotationTailStart + n))).im = 0
  rw [expTerm_imaginary_even]

private theorem uniform_rotation_odd_term_re_eq_zero (T : Rat) (n : Nat) :
    (ComplexSeries.expTerm
      (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re = 0 := by
  change (ComplexSeries.expTerm
    (imaginaryAxis T) (2 * (uniformRotationTailStart + n) + 1)).re = 0
  rw [expTerm_imaginary_odd]

private theorem uniformRotationCenter_step_re_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (uniformRotationCenter T (n + 1)).re - (uniformRotationCenter T n).re /\
      (uniformRotationCenter T (n + 1)).re - (uniformRotationCenter T n).re <=
        uniformRotationTailMagnitude n := by
  have hcenter := uniformRotationCenter_succ T n
  have heven := uniform_rotation_even_term_coordinate_bounds T hT n
  have hoddzero := uniform_rotation_odd_term_re_eq_zero T n
  rw [hcenter]
  change -uniformRotationTailMagnitude n <=
      ((uniformRotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re) -
        (uniformRotationCenter T n).re /\
    ((uniformRotationCenter T n).re +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).re +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).re) -
        (uniformRotationCenter T n).re <= uniformRotationTailMagnitude n
  rw [hoddzero]
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationCenter_step_im_bounds (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    -uniformRotationTailMagnitude n <=
        (uniformRotationCenter T (n + 1)).im - (uniformRotationCenter T n).im /\
      (uniformRotationCenter T (n + 1)).im - (uniformRotationCenter T n).im <=
        uniformRotationTailMagnitude n := by
  have hcenter := uniformRotationCenter_succ T n
  have hodd := uniform_rotation_odd_term_coordinate_bounds T hT n
  have hevenzero := uniform_rotation_even_term_im_eq_zero T n
  rw [hcenter]
  change -uniformRotationTailMagnitude n <=
      ((uniformRotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im) -
        (uniformRotationCenter T n).im /\
    ((uniformRotationCenter T n).im +
        (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n)).im +
          (ComplexSeries.expTerm (imaginaryAxis T) (uniformRotationTailTerms n + 1)).im) -
        (uniformRotationCenter T n).im <= uniformRotationTailMagnitude n
  rw [hevenzero]
  grind [Rat.sub_eq_add_neg]

theorem uniformRotationBox_width (T : Rat) (n : Nat) :
    (uniformRotationBox T n).width = 2 * uniformRotationTailRadius n := by
  unfold uniformRotationBox QBox.width
  dsimp
  grind [Rat.sub_eq_add_neg]

theorem uniformRotationBox_height (T : Rat) (n : Nat) :
    (uniformRotationBox T n).height = 2 * uniformRotationTailRadius n := by
  unfold uniformRotationBox QBox.height
  dsimp
  grind [Rat.sub_eq_add_neg]

private theorem uniformRotationBox_ordered (T : Rat) (n : Nat) :
    0 <= (uniformRotationBox T n).width /\
      0 <= (uniformRotationBox T n).height := by
  have hmag0 := uniformRotationTailMagnitude_nonneg n
  rw [uniformRotationBox_width, uniformRotationBox_height]
  unfold uniformRotationTailRadius
  constructor <;>
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.mul_nonneg (by decide +kernel) hmag0)

private theorem uniformRotationBox_nested_step (T : Rat)
    (hT : qabs T <= 2) (n : Nat) :
    QBox.NestedIn (uniformRotationBox T (n + 1)) (uniformRotationBox T n) := by
  have hre := uniformRotationCenter_step_re_bounds T hT n
  have him := uniformRotationCenter_step_im_bounds T hT n
  have hdrop := uniformRotationTailRadius_drop_majorizes n
  unfold QBox.NestedIn uniformRotationBox
  dsimp
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

private theorem uniformRotationBox_nested (T : Rat) (hT : qabs T <= 2) :
    forall n m : Nat, n <= m ->
      QBox.NestedIn (uniformRotationBox T m) (uniformRotationBox T n)
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
      · have hnm' : n <= m := by omega
        exact qbox_nested_trans
          (uniformRotationBox_nested_step T hT m)
          (uniformRotationBox_nested T hT n m hnm')

/-- At one common factorial stage, changing the rational input by at most
`eps` only widens the rotation box by `16 * eps` in each coordinate. -/
theorem uniformRotationBox_contained_expand_of_input_near (T U eps : Rat)
    (hT : qabs T <= 2) (hU : qabs U <= 2) (n : Nat)
    (hnear : qabs (T - U) <= eps) :
    QBox.NestedIn (uniformRotationBox T n)
      (QBox.expand (uniformRotationBox U n) (16 * eps)) := by
  have hcenter := uniformRotationCenter_input_lipschitz T U hT hU n
  have hfactor : 16 * qabs (T - U) <= 16 * eps :=
    Rat.mul_le_mul_of_nonneg_left hnear (by decide +kernel)
  have hreupper : (uniformRotationCenter T n).re -
      (uniformRotationCenter U n).re <= 16 * eps :=
    Rat.le_trans (self_le_qabs _) (Rat.le_trans hcenter.1 hfactor)
  have hrelower : -(16 * eps) <= (uniformRotationCenter T n).re -
      (uniformRotationCenter U n).re := by
    calc
      -(16 * eps) <= -qabs ((uniformRotationCenter T n).re -
          (uniformRotationCenter U n).re) := Rat.neg_le_neg
            (Rat.le_trans hcenter.1 hfactor)
      _ <= (uniformRotationCenter T n).re -
          (uniformRotationCenter U n).re := neg_qabs_le_self _
  have himupper : (uniformRotationCenter T n).im -
      (uniformRotationCenter U n).im <= 16 * eps :=
    Rat.le_trans (self_le_qabs _) (Rat.le_trans hcenter.2 hfactor)
  have himlower : -(16 * eps) <= (uniformRotationCenter T n).im -
      (uniformRotationCenter U n).im := by
    calc
      -(16 * eps) <= -qabs ((uniformRotationCenter T n).im -
          (uniformRotationCenter U n).im) := Rat.neg_le_neg
            (Rat.le_trans hcenter.2 hfactor)
      _ <= (uniformRotationCenter T n).im -
          (uniformRotationCenter U n).im := neg_qabs_le_self _
  unfold QBox.NestedIn QBox.expand uniformRotationBox
  dsimp
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

/-- A later finite rotation prefix at a nearby bounded rational input fits in
the earlier box after the same explicit input-error enlargement.  This is the
finite-prefix Cauchy certificate used for represented-angle evaluation. -/
theorem uniformRotationBox_future_contained_expand_of_input_near
    (T U eps : Rat) (hT : qabs T <= 2) (hU : qabs U <= 2)
    (k n : Nat) (hkn : k <= n) (hnear : qabs (T - U) <= eps) :
    QBox.NestedIn (uniformRotationBox T n)
      (QBox.expand (uniformRotationBox U k) (16 * eps)) := by
  apply QBox.nested_trans (uniformRotationBox_nested T hT k n hkn)
  exact uniformRotationBox_contained_expand_of_input_near T U eps hT hU k hnear

/-- Uniform bounded-input boxes have exactly the same coordinate widths as
the ordinary rational-input evaluator at the endpoint 2. This reuses the
already checked geometric width modulus while leaving the centers free to
vary with the bounded rational input. -/
private theorem uniformRotationBox_width_eq_rotationBox_two (T : Rat) (n : Nat) :
    (uniformRotationBox T n).width = (rotationBox 2 n).width := by
  rw [uniformRotationBox_width, rotationBox_width]
  unfold uniformRotationTailRadius rotationTailRadius
    uniformRotationTailMagnitude rotationTailMagnitude
    uniformRotationTailTerms rotationTailTerms
    uniformRotationTailStart rotationTailStart
  have hqabs : qabs (2 : Rat) = 2 := by decide +kernel
  rw [hqabs]

private theorem uniformRotationBox_height_eq_rotationBox_two (T : Rat) (n : Nat) :
    (uniformRotationBox T n).height = (rotationBox 2 n).height := by
  rw [uniformRotationBox_height, rotationBox_height]
  unfold uniformRotationTailRadius rotationTailRadius
    uniformRotationTailMagnitude rotationTailMagnitude
    uniformRotationTailTerms rotationTailTerms
    uniformRotationTailStart rotationTailStart
  have hqabs : qabs (2 : Rat) = 2 := by decide +kernel
  rw [hqabs]

/-- Effective geometric bound for both coordinate widths of every bounded
rational-input factorial rotation box. -/
theorem uniformRotationBox_width_le_geometric (T : Rat) (n : Nat) :
    (uniformRotationBox T n).width <=
      (8 * rotationTailMagnitude 2 0) * ((1 : Rat) / 2) ^ n := by
  rw [uniformRotationBox_width_eq_rotationBox_two]
  exact rotationBox_width_le_geometric 2 n

theorem uniformRotationBox_height_le_geometric (T : Rat) (n : Nat) :
    (uniformRotationBox T n).height <=
      (8 * rotationTailMagnitude 2 0) * ((1 : Rat) / 2) ^ n := by
  rw [uniformRotationBox_height_eq_rotationBox_two]
  exact rotationBox_height_le_geometric 2 n

theorem uniformRotationBox_widths_shrink (T : Rat) :
    ComplexCompute.WidthsShrinkToZero (uniformRotationBox T) := by
  intro eps
  obtain ⟨N, hN⟩ := rotationBox_widths_shrink 2 eps
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  constructor
  · rw [uniformRotationBox_width_eq_rotationBox_two]
    exact h.1
  · rw [uniformRotationBox_height_eq_rotationBox_two]
    exact h.2

/-- Every common-prefix rotation box is ordered in its real coordinate. -/
theorem uniformRotationBox_width_nonneg (T : Rat) (n : Nat) :
    0 <= (uniformRotationBox T n).width :=
  (uniformRotationBox_ordered T n).1

/-- Every common-prefix rotation box is ordered in its imaginary coordinate. -/
theorem uniformRotationBox_height_nonneg (T : Rat) (n : Nat) :
    0 <= (uniformRotationBox T n).height :=
  (uniformRotationBox_ordered T n).2

/-- One factorial stage works uniformly for the coordinate widths of every
bounded-input rotation prefix.  The centers depend on the input, but the
tail radius is the fixed radius-two majorant. -/
theorem uniformRotationBoxes_widths_shrink_uniform (eps : QPos) :
    Exists fun N : Nat => forall (T : Rat) (n : Nat), N <= n ->
      (uniformRotationBox T n).width <= eps.val /\
        (uniformRotationBox T n).height <= eps.val := by
  obtain ⟨N, hN⟩ := rotationBox_widths_shrink 2 eps
  refine ⟨N, ?_⟩
  intro T n hn
  have h := hN n hn
  constructor
  · rw [uniformRotationBox_width_eq_rotationBox_two]
    exact h.1
  · rw [uniformRotationBox_height_eq_rotationBox_two]
    exact h.2

/-- The rotation-series evaluator with one common tail schedule for all
rational inputs satisfying the bound qabs T <= 2. It is the rational
building block for represented-angle evaluation. -/
def uniformRotationExpRaw (T : Rat) : ComplexCompute where
  compute := uniformRotationBox T

theorem uniformRotationExpRaw_compute (T : Rat) (n : Nat) :
    (uniformRotationExpRaw T).compute n = uniformRotationBox T n := rfl

theorem uniformRotationExpRaw_valid (T : Rat) (hT : qabs T <= 2) :
    (uniformRotationExpRaw T).Valid := by
  unfold ComplexCompute.Valid ComplexCompute.ValidCompute uniformRotationExpRaw
  constructor
  · exact uniformRotationBox_ordered T
  · constructor
    · intro n m hnm
      have hnest := uniformRotationBox_nested T hT n m hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact uniformRotationBox_widths_shrink T

/-! ### Evaluating the rotation series at represented real inputs

For a represented input, use the midpoint of its stage-`n` interval as the
finite series center. The input Lipschitz bound gives a finite widening
radius, and `ComplexCompute.cauchyStabilize` turns the approximations into a valid
raw complex computation without choosing a real representative. -/

/-- Finite rational centers for the rotation series at a represented real
input. -/
def representedRotationCandidate (x : RealCompute) : ComplexCompute where
  compute n := uniformRotationBox (x.compute n).midpoint n

/-- The future-center motion allowance at stage `n`. -/
def representedRotationRadius (x : RealCompute) (n : Nat) : Rat :=
  32 * (x.compute n).width

/-- The computation-defined complex exponential of an imaginary represented
real input, when every rational input box stays in the radius-two chart. -/
def representedRotationExpRaw (x : RealCompute) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (representedRotationCandidate x)
    (representedRotationRadius x)

private theorem qbox_expand_preserves_nested {A B : QBox} (r : Rat)
    (h : QBox.NestedIn A B) :
    QBox.NestedIn (QBox.expand A r) (QBox.expand B r) := by
  unfold QBox.NestedIn QBox.expand at *
  simp only [QComplex.le_def] at *
  grind [Rat.sub_eq_add_neg]

private theorem representedRotationMidpoint_bound
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2)
    (n : Nat) : qabs (x.compute n).midpoint <= 2 := by
  have hord := RealCompute.interval_order_of_valid x hx n
  have hmid := QInterval.midpoint_mem hord
  exact qabs_le_of_neg_le_le
    (Rat.le_trans (hbound n).1 hmid.1)
    (Rat.le_trans hmid.2 (hbound n).2)

/-- Later finite rotation centers lie in the earlier center's explicit
input-motion enlargement. -/
theorem representedRotationCandidate_future
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2) :
    forall k n, k <= n ->
      ((representedRotationCandidate x).compute n).NestedIn
        (QBox.expand ((representedRotationCandidate x).compute k)
          (representedRotationRadius x k)) := by
  intro k n hkn
  have hknest := hx.2.1 k n hkn
  have hwidth : (x.compute n).width <= (x.compute k).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hover : (x.compute n).Overlaps (x.compute k) := by
    unfold QInterval.Overlaps
    exact ⟨Rat.le_trans hknest.2.1 hknest.2.2,
      Rat.le_trans hknest.1 hknest.2.1⟩
  have hmid := QInterval.qabs_midpoint_sub_midpoint_le_width_add_of_overlaps
    (RealCompute.interval_order_of_valid x hx n)
    (RealCompute.interval_order_of_valid x hx k) hover
  have hnear :
      qabs ((x.compute n).midpoint - (x.compute k).midpoint) <=
        2 * (x.compute k).width := by
    calc
      qabs ((x.compute n).midpoint - (x.compute k).midpoint) <=
          (x.compute n).width + (x.compute k).width := hmid
      _ <= (x.compute k).width + (x.compute k).width :=
        (Rat.add_le_add_right).2 hwidth
      _ = 2 * (x.compute k).width := by
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]
  have hseries := uniformRotationBox_future_contained_expand_of_input_near
    (x.compute n).midpoint (x.compute k).midpoint
    (2 * (x.compute k).width)
    (representedRotationMidpoint_bound x hx hbound n)
    (representedRotationMidpoint_bound x hx hbound k)
    k n hkn hnear
  have hrad : 16 * (2 * (x.compute k).width) =
      32 * (x.compute k).width := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hrad] at hseries
  simpa [representedRotationCandidate, representedRotationRadius] using hseries

/-- At each output stage, the represented-input evaluator retains the
unexpanded factorial box centered at that stage's rational input midpoint.
This gives explicit rational witnesses for finite composition certificates;
the Cauchy stabilization may narrow the output box, but it cannot discard
this current factorial approximation. -/
theorem representedRotationExpRaw_contains_midpoint_box
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2)
    (n : Nat) :
    (uniformRotationBox (x.compute n).midpoint n).NestedIn
      ((representedRotationExpRaw x).compute n) := by
  change ((representedRotationCandidate x).compute n).NestedIn
    (ComplexCompute.cauchyStabilizeCompute
      (representedRotationCandidate x).compute
      (representedRotationRadius x) n)
  exact ComplexCompute.cauchyStabilize_contains_current
    (representedRotationCandidate_future x hx hbound) n

private theorem cauchyStabilizeCompute_contains_prefix
    (candidate : Nat -> QBox) (radius : Nat -> Rat) (common : QBox)
    (N : Nat)
    (hcommon : forall k, k <= N ->
      common.NestedIn (QBox.expand (candidate k) (radius k))) :
    common.NestedIn (ComplexCompute.cauchyStabilizeCompute candidate radius N) := by
  induction N with
  | zero =>
      simpa [ComplexCompute.cauchyStabilizeCompute] using hcommon 0 (Nat.le_refl 0)
  | succ N ih =>
      rw [ComplexCompute.cauchyStabilizeCompute]
      apply QBox.intersection_contains
      · exact ih (fun k hk => hcommon k (Nat.le_trans hk (Nat.le_succ N)))
      · exact hcommon (N + 1) (Nat.le_refl _)

/-- A later rational input midpoint may be used as a finite series center
inside any earlier stabilized output box.  The input interval nesting and
the explicit `32 * width` motion allowance are what make the stage mismatch
safe; this is the form needed when a chain-rule certificate allocates
different inner, outer, and actual-output precisions. -/
theorem representedRotationExpRaw_contains_later_midpoint_box
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2)
    (outputStage inputStage : Nat) (hstage : outputStage <= inputStage) :
    (uniformRotationBox (x.compute inputStage).midpoint inputStage).NestedIn
      ((representedRotationExpRaw x).compute outputStage) := by
  unfold representedRotationExpRaw
  apply cauchyStabilizeCompute_contains_prefix
    (representedRotationCandidate x).compute (representedRotationRadius x)
    (uniformRotationBox (x.compute inputStage).midpoint inputStage)
    outputStage
  intro k hk
  have hkm : k <= inputStage := Nat.le_trans hk hstage
  have hfuture := representedRotationCandidate_future x hx hbound
    k inputStage hkm
  simpa [representedRotationCandidate] using hfuture

/-- A finite rotation box may use an input midpoint and factorial truncation
from two independent later stages. It remains inside every earlier
stabilization prefix as long as both stages are at least the output stage. -/
theorem representedRotationExpRaw_contains_midpoint_box_at
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2)
    (outputStage inputStage factorialStage : Nat)
    (hinput : outputStage <= inputStage)
    (hfactorial : outputStage <= factorialStage) :
    (uniformRotationBox (x.compute inputStage).midpoint factorialStage).NestedIn
      ((representedRotationExpRaw x).compute outputStage) := by
  unfold representedRotationExpRaw
  apply cauchyStabilizeCompute_contains_prefix
    (representedRotationCandidate x).compute (representedRotationRadius x)
    (uniformRotationBox (x.compute inputStage).midpoint factorialStage)
    outputStage
  intro k hk
  have hkm : k <= inputStage := Nat.le_trans hk hinput
  have hkr : k <= factorialStage := Nat.le_trans hk hfactorial
  have hinputNest := hx.2.1 k inputStage hkm
  have hwidth : (x.compute inputStage).width <= (x.compute k).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hoverlap : (x.compute inputStage).Overlaps (x.compute k) := by
    unfold QInterval.Overlaps
    exact ⟨Rat.le_trans hinputNest.2.1 hinputNest.2.2,
      Rat.le_trans hinputNest.1 hinputNest.2.1⟩
  have hmid := QInterval.qabs_midpoint_sub_midpoint_le_width_add_of_overlaps
    (RealCompute.interval_order_of_valid x hx inputStage)
    (RealCompute.interval_order_of_valid x hx k) hoverlap
  have hnear :
      qabs ((x.compute inputStage).midpoint - (x.compute k).midpoint) <=
        2 * (x.compute k).width := by
    calc
      qabs ((x.compute inputStage).midpoint - (x.compute k).midpoint) <=
          (x.compute inputStage).width + (x.compute k).width := hmid
      _ <= (x.compute k).width + (x.compute k).width :=
        (Rat.add_le_add_right).2 hwidth
      _ = 2 * (x.compute k).width := by
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]
  have hT := representedRotationMidpoint_bound x hx hbound inputStage
  have hU := representedRotationMidpoint_bound x hx hbound k
  have hnearBox := uniformRotationBox_contained_expand_of_input_near
    (x.compute inputStage).midpoint (x.compute k).midpoint
    (2 * (x.compute k).width) hT hU k hnear
  have htail := uniformRotationBox_nested
    (x.compute inputStage).midpoint hT k factorialStage hkr
  have hcontained := QBox.nested_trans htail hnearBox
  have hrad : 16 * (2 * (x.compute k).width) =
      32 * (x.compute k).width := by
    grind [Rat.mul_assoc]
  rw [hrad] at hcontained
  simpa [representedRotationCandidate, representedRotationRadius,
    representedRotationExpRaw] using hcontained

/-- Every stabilized represented-input box is contained in the current
expanded factorial candidate. This gives a direct width estimate at the
current rational precision stage. -/
theorem representedRotationExpRaw_nested_in_current_expand
    (x : RealCompute) (n : Nat) :
    ((representedRotationExpRaw x).compute n).NestedIn
      (QBox.expand ((representedRotationCandidate x).compute n)
        (representedRotationRadius x n)) := by
  change (ComplexCompute.cauchyStabilizeCompute
      (representedRotationCandidate x).compute
      (representedRotationRadius x) n).NestedIn _
  induction n with
  | zero =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ n ih =>
      rw [ComplexCompute.cauchyStabilizeCompute]
      exact QBox.intersection_contained_right
        (ComplexCompute.cauchyStabilizeCompute
          (representedRotationCandidate x).compute
          (representedRotationRadius x) n)
        (QBox.expand ((representedRotationCandidate x).compute (n + 1))
          (representedRotationRadius x (n + 1)))

/-- Coordinate widths of the stabilized represented rotation are bounded by
the current factorial box plus twice the input-motion radius. -/
theorem representedRotationExpRaw_width_bound
    (x : RealCompute) (n : Nat) :
    let B := uniformRotationBox (x.compute n).midpoint n
    ((representedRotationExpRaw x).compute n).width <=
        B.width + 2 * representedRotationRadius x n /\
      ((representedRotationExpRaw x).compute n).height <=
        B.height + 2 * representedRotationRadius x n := by
  let B := uniformRotationBox (x.compute n).midpoint n
  have hcontained := representedRotationExpRaw_nested_in_current_expand x n
  have hwidthHeight := QBox.width_height_le_of_nested hcontained
  rw [QBox.expand_width, QBox.expand_height] at hwidthHeight
  exact hwidthHeight

/-- Arbitrary represented real inputs in `[-2,2]` have a valid factorial
rotation-series value. The proof combines explicit input-motion and
factorial-tail bounds through finite complex-box stabilization. -/
theorem representedRotationExpRaw_valid
    (x : RealCompute) (hx : x.Valid)
    (hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2) :
    (representedRotationExpRaw x).Valid := by
  unfold representedRotationExpRaw
  apply ComplexCompute.cauchyStabilize_valid
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).2
      (uniformRotationBox_ordered _ n)
  · intro eps
    obtain ⟨N, hN⟩ := uniformRotationBoxes_widths_shrink_uniform eps
    exact ⟨N, fun n hn => hN ((x.compute n).midpoint) n hn⟩
  · exact representedRotationCandidate_future x hx hbound
  · intro eps
    have h32inv : 0 < (32 : Rat)⁻¹ :=
      Rat.inv_pos.mpr (by decide +kernel)
    let small : QPos := ⟨eps.val / 32, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property h32inv⟩
    obtain ⟨N, hN⟩ := hx.2.2 small
    refine ⟨N, ?_⟩
    intro n hn
    have hw := hN n hn
    have hscale := Rat.mul_le_mul_of_nonneg_left hw
      (by decide : (0 : Rat) <= 32)
    have hidentity : 32 * (eps.val / 32) = eps.val := by
      rw [Rat.div_def]
      have hinv := Rat.mul_inv_cancel (32 : Rat)
        (by decide : (32 : Rat) ≠ 0)
      grind [Rat.mul_assoc, Rat.mul_comm]
    simpa [representedRotationRadius, small, hidentity] using hscale

/-- The represented-input rotation series respects equivalence of raw real
input names. For each requested output stage, a midpoint of the two overlapping
input boxes supplies one rational series box contained in both finite-prefix
stabilizations. -/
theorem representedRotationExpRaw_congr
    (x y : RealCompute) (hx : x.Valid) (hy : y.Valid)
    (hboundX : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2)
    (hboundY : forall n, -2 <= (y.compute n).lo /\ (y.compute n).hi <= 2)
    (heq : x.Equiv y) :
    (representedRotationExpRaw x).Equiv
      (representedRotationExpRaw y) := by
  intro n
  have hover := (RealCompute.compareAt_overlap_iff x y n n).1 (heq n)
  have hxn := RealCompute.interval_order_of_valid x hx n
  have hyn := RealCompute.interval_order_of_valid y hy n
  have hcommonOrdered := QInterval.intersection_ordered_of_overlaps hxn hyn hover
  let I := QInterval.intersection (x.compute n) (y.compute n)
  let q := I.midpoint
  have hqmem := QInterval.midpoint_mem (show I.lo <= I.hi from hcommonOrdered)
  have hIleft := QInterval.intersection_contained_left (x.compute n) (y.compute n)
  have hIright := QInterval.intersection_contained_right (x.compute n) (y.compute n)
  have hqX : (x.compute n).lo <= q /\ q <= (x.compute n).hi := by
    exact ⟨Rat.le_trans hIleft.1 hqmem.1,
      Rat.le_trans hqmem.2 hIleft.2⟩
  have hqY : (y.compute n).lo <= q /\ q <= (y.compute n).hi := by
    exact ⟨Rat.le_trans hIright.1 hqmem.1,
      Rat.le_trans hqmem.2 hIright.2⟩
  have hqbound : qabs q <= 2 := by
    exact qabs_le_of_neg_le_le
      (Rat.le_trans (hboundX n).1 hqX.1)
      (Rat.le_trans hqX.2 (hboundX n).2)
  have hcommon : QBox.Ordered (uniformRotationBox q n) := by
    exact (QBox.ordered_iff_width_height_nonneg _).2
      (uniformRotationBox_ordered q n)
  have hprefixX :
      (uniformRotationBox q n).NestedIn
        (ComplexCompute.cauchyStabilizeCompute
          (representedRotationCandidate x).compute
          (representedRotationRadius x) n) := by
    apply cauchyStabilizeCompute_contains_prefix
    intro k hkn
    have hknest := hx.2.1 k n hkn
    have hqk : (x.compute k).lo <= q /\ q <= (x.compute k).hi := by
      exact ⟨Rat.le_trans hknest.1 hqX.1,
        Rat.le_trans hqX.2 hknest.2.2⟩
    have hnear := QInterval.qabs_sub_midpoint_le_width
      (RealCompute.interval_order_of_valid x hx k) hqk.1 hqk.2
    have hrot := uniformRotationBox_future_contained_expand_of_input_near
      q (x.compute k).midpoint (x.compute k).width
      hqbound (representedRotationMidpoint_bound x hx hboundX k)
      k n hkn hnear
    have hradius : 16 * (x.compute k).width <=
        representedRotationRadius x k := by
      dsimp [representedRotationRadius]
      exact Rat.mul_le_mul_of_nonneg_right
        (by decide : (16 : Rat) <= 32) (hx.1 k)
    exact QBox.nested_trans hrot
      (QBox.expand_mono_radius _ hradius)
  have hprefixY :
      (uniformRotationBox q n).NestedIn
        (ComplexCompute.cauchyStabilizeCompute
          (representedRotationCandidate y).compute
          (representedRotationRadius y) n) := by
    apply cauchyStabilizeCompute_contains_prefix
    intro k hkn
    have hknest := hy.2.1 k n hkn
    have hqk : (y.compute k).lo <= q /\ q <= (y.compute k).hi := by
      exact ⟨Rat.le_trans hknest.1 hqY.1,
        Rat.le_trans hqY.2 hknest.2.2⟩
    have hnear := QInterval.qabs_sub_midpoint_le_width
      (RealCompute.interval_order_of_valid y hy k) hqk.1 hqk.2
    have hrot := uniformRotationBox_future_contained_expand_of_input_near
      q (y.compute k).midpoint (y.compute k).width
      hqbound (representedRotationMidpoint_bound y hy hboundY k)
      k n hkn hnear
    have hradius : 16 * (y.compute k).width <=
        representedRotationRadius y k := by
      dsimp [representedRotationRadius]
      exact Rat.mul_le_mul_of_nonneg_right
        (by decide : (16 : Rat) <= 32) (hy.1 k)
    exact QBox.nested_trans hrot
      (QBox.expand_mono_radius _ hradius)
  have hcrossX : (representedRotationExpRaw x).compute n =
      ComplexCompute.cauchyStabilizeCompute
        (representedRotationCandidate x).compute
        (representedRotationRadius x) n := rfl
  have hcrossY : (representedRotationExpRaw y).compute n =
      ComplexCompute.cauchyStabilizeCompute
        (representedRotationCandidate y).compute
        (representedRotationRadius y) n := rfl
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  rw [hcrossX, hcrossY]
  exact ⟨QComplex.le_trans hprefixX.1
      (QComplex.le_trans hcommon hprefixY.2),
    QComplex.le_trans hprefixY.1
      (QComplex.le_trans hcommon hprefixX.2)⟩

/-- The represented-input series extends the rational-input evaluator
without changing its mathematical value. -/
theorem representedRotationExpRaw_ofRat_equiv (T : Rat) (hT : qabs T <= 2) :
    (representedRotationExpRaw (RealCompute.ofRat T)).Equiv
      (uniformRotationExpRaw T) := by
  let x : RealCompute := RealCompute.ofRat T
  have hx : x.Valid := RealCompute.ofRat_valid T
  have hbound : forall n, -2 <= (x.compute n).lo /\ (x.compute n).hi <= 2 := by
    intro n
    change -2 <= T /\ T <= 2
    exact ⟨Rat.le_trans (Rat.neg_le_neg hT) (neg_qabs_le_self T),
      Rat.le_trans (self_le_qabs T) hT⟩
  have hfuture := representedRotationCandidate_future x hx hbound
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (representedRotationExpRaw x) (uniformRotationExpRaw T) n n).2
  have hcurrent := ComplexCompute.cauchyStabilize_contains_current hfuture n
  have hbox : (representedRotationCandidate x).compute n =
      uniformRotationBox T n := by
    change uniformRotationBox ((T + T) / 2) n = uniformRotationBox T n
    congr 1
    rw [Rat.div_def]
    have hinv := Rat.mul_inv_cancel (2 : Rat) (by decide : (2 : Rat) ≠ 0)
    calc
      (T + T) * (2 : Rat)⁻¹ = T * (2 * (2 : Rat)⁻¹) := by
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
      _ = T := by rw [hinv, Rat.mul_one]
  rw [hbox] at hcurrent
  have hordered := (QBox.ordered_iff_width_height_nonneg
    (uniformRotationBox T n)).2 (uniformRotationBox_ordered T n)
  exact ⟨QComplex.le_trans hcurrent.1 hordered,
    QComplex.le_trans hordered hcurrent.2⟩

/-- Certified abstract real handles for the two rational-input rotation
coordinates. -/
def rotationCos (T : Rat) : RealCompute.Certified :=
  RealCompute.Certified.ofRaw (rotationCosRaw T) (rotationCosRaw_valid T)

def rotationSin (T : Rat) : RealCompute.Certified :=
  RealCompute.Certified.ofRaw (rotationSinRaw T) (rotationSinRaw_valid T)

end RotationSeries

end ComputableAnalysis


