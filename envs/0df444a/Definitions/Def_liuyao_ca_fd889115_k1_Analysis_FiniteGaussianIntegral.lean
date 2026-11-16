-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianIntegral
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteGaussianIntegral
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:21:31.206143+00:00
-- url     : https://prove2.me/theorems/32ad8b6d-dacf-4a32-a1e5-5870d4032fbc
-- title:
--   Computable analysis · FiniteGaussianIntegral · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteGaussianIntegral.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteNBallVolume
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialTaylor
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ExpProofs
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Series

set_option autoImplicit true

/-!
# Finite Gaussian integral prefixes

This is the bounded, finite layer of the Gaussian route.  The integrand is the
even Taylor prefix for `exp (-x^2)`, and each monomial is integrated exactly
over `[-radius,radius]`.  It is not yet an improper integral over the line.
-/

namespace ComputableAnalysis

def gaussianEvenIntegralPrefix (terms : Nat) (radius : Rat) : Rat :=
  (List.range terms).foldl
    (fun acc k =>
      acc + 2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)) 0

theorem gaussianEvenIntegralPrefix_zero (radius : Rat) :
    gaussianEvenIntegralPrefix 0 radius = 0 := by
  rfl

/-! ## A nested computable raw for the bounded unit Gaussian integral

At radius one, the absolute magnitude of the `k`th term obtained by
termwise integration is `2 / (k! (2k+1))`.  The following construction uses
that rational magnitude as an alternating-series algorithm.  Thus it names
the bounded Gaussian integral by nested rational intervals, without first
postulating an integral or an infinite sum in a completed real space. -/

def gaussianUnitIntegralMagnitude (k : Nat) : Rat :=
  2 * RationalMajorant.factorialTailTerm 1 k * Series.leibnizTerm k

theorem gaussianUnitFactorialTerm_nonneg (k : Nat) :
    0 <= RationalMajorant.factorialTailTerm 1 k :=
  RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) k

theorem gaussianUnitFactorialTerm_le_one (k : Nat) :
    RationalMajorant.factorialTailTerm 1 k <= 1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
      rw [RationalMajorant.factorialTailTerm_succ]
      have hratio :
          (1 : Rat) / (((k + 1 : Nat) : Rat)) <= 1 := by
        have h := Series.one_div_nat_antitone_series
          (n := 1) (m := k + 1) (by omega) (by omega) (by omega)
        exact Rat.le_trans h (by decide +kernel)
      calc
        RationalMajorant.factorialTailTerm 1 k *
            (1 / (((k + 1 : Nat) : Rat))) <=
            RationalMajorant.factorialTailTerm 1 k * 1 :=
          Rat.mul_le_mul_of_nonneg_left hratio
            (gaussianUnitFactorialTerm_nonneg k)
        _ <= 1 * 1 :=
          Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel)
        _ = 1 := by decide +kernel

theorem gaussianUnitFactorialTerm_decreasing (k : Nat) :
    RationalMajorant.factorialTailTerm 1 (k + 1) <=
      RationalMajorant.factorialTailTerm 1 k := by
  rw [RationalMajorant.factorialTailTerm_succ]
  have hratio : (1 : Rat) / (((k + 1 : Nat) : Rat)) <= 1 := by
    have h := Series.one_div_nat_antitone_series
      (n := 1) (m := k + 1) (by omega) (by omega) (by omega)
    exact Rat.le_trans h (by decide +kernel)
  simpa using Rat.mul_le_mul_of_nonneg_left hratio
    (gaussianUnitFactorialTerm_nonneg k)

theorem gaussianUnitIntegralMagnitude_nonneg (k : Nat) :
    0 <= gaussianUnitIntegralMagnitude k := by
  unfold gaussianUnitIntegralMagnitude
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel)
      (gaussianUnitFactorialTerm_nonneg k))
    (Series.leibnizTerm_nonneg k)

theorem gaussianUnitIntegralMagnitude_decreasing (k : Nat) :
    gaussianUnitIntegralMagnitude (k + 1) <=
      gaussianUnitIntegralMagnitude k := by
  unfold gaussianUnitIntegralMagnitude
  calc
    2 * RationalMajorant.factorialTailTerm 1 (k + 1) *
        Series.leibnizTerm (k + 1) <=
        2 * RationalMajorant.factorialTailTerm 1 k *
          Series.leibnizTerm (k + 1) := by
      exact Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left
          (gaussianUnitFactorialTerm_decreasing k) (by decide +kernel))
        (Series.leibnizTerm_nonneg (k + 1))
    _ <= 2 * RationalMajorant.factorialTailTerm 1 k *
          Series.leibnizTerm k := by
      exact Rat.mul_le_mul_of_nonneg_left
        (Series.leibnizTerm_decreasing k)
        (Rat.mul_nonneg (by decide +kernel)
          (gaussianUnitFactorialTerm_nonneg k))

theorem gaussianUnitIntegralMagnitude_le_natRate (k : Nat) :
    gaussianUnitIntegralMagnitude k <=
      (2 : Rat) / (((k + 1 : Nat) : Rat)) := by
  unfold gaussianUnitIntegralMagnitude
  calc
    2 * RationalMajorant.factorialTailTerm 1 k *
        Series.leibnizTerm k <= 2 * 1 * Series.leibnizTerm k := by
      exact Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left
          (gaussianUnitFactorialTerm_le_one k) (by decide +kernel))
        (Series.leibnizTerm_nonneg k)
    _ <= 2 * 1 * (1 / (((k + 1 : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left
        (Series.leibnizTerm_le_one_div_succ k) (by decide +kernel)
    _ = (2 : Rat) / (((k + 1 : Nat) : Rat)) := by
      grind [Rat.div_def, Rat.mul_assoc]

theorem gaussianUnitIntegralMagnitude_shrinks :
    ShrinksToZero gaussianUnitIntegralMagnitude := by
  exact shrinksToZero_of_natOverSuccBound
    gaussianUnitIntegralMagnitude_le_natRate

def gaussianUnitIntegralAlternatingRaw : Series.AlternatingRaw where
  term := gaussianUnitIntegralMagnitude
  term_nonneg := gaussianUnitIntegralMagnitude_nonneg
  term_decreasing := gaussianUnitIntegralMagnitude_decreasing
  term_shrinks := gaussianUnitIntegralMagnitude_shrinks

def gaussianUnitIntegralRaw : RealCompute :=
  gaussianUnitIntegralAlternatingRaw.toRealCompute

theorem gaussianUnitIntegralRaw_valid : gaussianUnitIntegralRaw.Valid :=
  gaussianUnitIntegralAlternatingRaw.toRealCompute_valid

private theorem gaussian_neg_one_pow_even (n : Nat) :
    (-1 : Rat) ^ (2 * n) = 1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        Rat.pow_succ, Rat.pow_succ, ih]
      decide +kernel

private theorem gaussian_neg_one_pow_odd (n : Nat) :
    (-1 : Rat) ^ (2 * n + 1) = -1 := by
  rw [Rat.pow_succ, gaussian_neg_one_pow_even]
  decide +kernel

private theorem gaussian_one_pow (n : Nat) : (1 : Rat) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rat.pow_succ, ih, Rat.one_mul]

private theorem gaussian_alternatingSign_eq_neg_one_pow (n : Nat) :
    Series.alternatingSign n = (-1 : Rat) ^ n := by
  by_cases hn : n % 2 = 0
  · have hnform : n = 2 * (n / 2) := by omega
    rw [hnform, gaussian_neg_one_pow_even]
    simp [Series.alternatingSign]
  · have hnform : n = 2 * (n / 2) + 1 := by omega
    rw [hnform, gaussian_neg_one_pow_odd]
    simp [Series.alternatingSign]

private theorem gaussian_square_pow_mul (radius : Rat) (n : Nat) :
    (radius * radius) ^ n * radius = radius ^ (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ,
        show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
        Rat.pow_succ, Rat.pow_succ]
      calc
        (radius * radius) ^ n * (radius * radius) * radius =
            ((radius * radius) ^ n * radius) * (radius * radius) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ = radius ^ (2 * n + 1) * (radius * radius) := by rw [ih]
        _ = radius ^ (2 * n + 1) * radius * radius := by
          rw [Rat.mul_assoc]

/- The finite Gaussian prefix is integrated term by term.  This recurrence is
   the algebraic interface used by any later tail certificate; it does not
   assert an improper integral or invoke a completed real number. -/
theorem gaussianEvenIntegralPrefix_succ (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius =
      gaussianEvenIntegralPrefix terms radius +
        2 * FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms *
          radius ^ (2 * terms + 1) / ((2 * terms + 1 : Nat) : Rat) := by
  unfold gaussianEvenIntegralPrefix
  rw [List.range_succ]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem gaussianEvenIntegralPrefix_term_difference (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius -
        gaussianEvenIntegralPrefix terms radius =
      2 * FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms *
        radius ^ (2 * terms + 1) / ((2 * terms + 1 : Nat) : Rat) := by
  rw [gaussianEvenIntegralPrefix_succ]
  grind

def gaussianEvenIntegralTerm (k : Nat) (radius : Rat) : Rat :=
  2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
    radius ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)

/-! ## Shifted alternating tails at an arbitrary nonnegative radius

For radius `R`, the absolute value of the integrated `k`th Gaussian Taylor
term is

`2 * R * (R^2)^k / k! * 1/(2k+1)`.

Starting after twice the standard factorial-tail start makes the start index
even and places every subsequent factorial ratio below one half.  Evenness is
important: the remaining alternating tail then starts with a positive term,
so it can be consumed directly by `Series.AlternatingRaw`. -/

def gaussianIntegralTermMagnitude (radius : Rat) (k : Nat) : Rat :=
  2 * radius *
    RationalMajorant.factorialTailTerm (radius * radius) k *
      Series.leibnizTerm k

def gaussianIntegralTailStart (radius : Rat) : Nat :=
  2 * RationalMajorant.factorialTailStart (radius * radius)

theorem gaussianIntegralTailStart_even (radius : Rat) :
    gaussianIntegralTailStart radius % 2 = 0 := by
  unfold gaussianIntegralTailStart
  omega

theorem gaussianIntegralTailStart_satisfies
    (radius : Rat) (_hradius : 0 <= radius) :
    radius * radius <=
      (((gaussianIntegralTailStart radius + 1 : Nat) : Rat) / 2) := by
  let C := radius * radius
  let start := RationalMajorant.factorialTailStart C
  have hbase := RationalMajorant.factorialTailStart_satisfies C
  have hlater := RationalMajorant.factorialTailStart_mono C start start hbase
  change C <= (((start + start + 1 : Nat) : Rat) / 2) at hlater
  change radius * radius <=
    (((2 * RationalMajorant.factorialTailStart (radius * radius) + 1 : Nat) : Rat) / 2)
  rw [show 2 * RationalMajorant.factorialTailStart (radius * radius) + 1 =
      RationalMajorant.factorialTailStart (radius * radius) +
        RationalMajorant.factorialTailStart (radius * radius) + 1 by omega]
  simpa [C, start] using hlater

theorem gaussianIntegralTermMagnitude_nonneg
    (radius : Rat) (hradius : 0 <= radius) (k : Nat) :
    0 <= gaussianIntegralTermMagnitude radius k := by
  unfold gaussianIntegralTermMagnitude
  exact Rat.mul_nonneg
    (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) hradius)
      (RationalMajorant.factorialTailTerm_nonneg
        (Rat.mul_nonneg hradius hradius) k))
    (Series.leibnizTerm_nonneg k)

def gaussianIntegralShiftedMagnitude (radius : Rat) (j : Nat) : Rat :=
  gaussianIntegralTermMagnitude radius (gaussianIntegralTailStart radius + j)

theorem gaussianIntegralShiftedMagnitude_nonneg
    (radius : Rat) (hradius : 0 <= radius) (j : Nat) :
    0 <= gaussianIntegralShiftedMagnitude radius j :=
  gaussianIntegralTermMagnitude_nonneg radius hradius _

theorem gaussianIntegralShiftedMagnitude_decreasing
    (radius : Rat) (hradius : 0 <= radius) (j : Nat) :
    gaussianIntegralShiftedMagnitude radius (j + 1) <=
      gaussianIntegralShiftedMagnitude radius j := by
  let C := radius * radius
  let start := gaussianIntegralTailStart radius
  have hC : 0 <= C := Rat.mul_nonneg hradius hradius
  have hstart : C <= (((start + 1 : Nat) : Rat) / 2) := by
    simpa [C, start] using gaussianIntegralTailStart_satisfies radius hradius
  have hratio := RationalMajorant.factorialTailRatio_le_half_from_start
    C start j hstart
  have hfactorial := RationalMajorant.factorialTailTerm_succ_le_half
    hC (start + j) hratio
  have hleibniz := Series.leibnizTerm_decreasing (start + j)
  have hfactorialNonneg := RationalMajorant.factorialTailTerm_nonneg
    hC (start + j)
  have hleibnizNextNonneg := Series.leibnizTerm_nonneg (start + j + 1)
  have hhalfLeOne : (1 : Rat) / 2 <= 1 := by decide +kernel
  unfold gaussianIntegralShiftedMagnitude gaussianIntegralTermMagnitude
  rw [show start + (j + 1) = start + j + 1 by omega]
  calc
    2 * radius * RationalMajorant.factorialTailTerm C (start + j + 1) *
        Series.leibnizTerm (start + j + 1) <=
      2 * radius *
          (RationalMajorant.factorialTailTerm C (start + j) * (1 / 2)) *
        Series.leibnizTerm (start + j + 1) := by
      exact Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left hfactorial
          (Rat.mul_nonneg (by decide +kernel) hradius))
        hleibnizNextNonneg
    _ <= 2 * radius * RationalMajorant.factorialTailTerm C (start + j) *
        Series.leibnizTerm (start + j + 1) := by
      have hhalfFactor :
          RationalMajorant.factorialTailTerm C (start + j) * (1 / 2) <=
            RationalMajorant.factorialTailTerm C (start + j) := by
        simpa using Rat.mul_le_mul_of_nonneg_left hhalfLeOne hfactorialNonneg
      exact Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left hhalfFactor
          (Rat.mul_nonneg (by decide +kernel) hradius))
        hleibnizNextNonneg
    _ <= 2 * radius * RationalMajorant.factorialTailTerm C (start + j) *
        Series.leibnizTerm (start + j) := by
      exact Rat.mul_le_mul_of_nonneg_left hleibniz
        (Rat.mul_nonneg
          (Rat.mul_nonneg (by decide +kernel) hradius) hfactorialNonneg)

theorem gaussianIntegralShiftedMagnitude_shrinks
    (radius : Rat) (hradius : 0 <= radius) :
    ShrinksToZero (gaussianIntegralShiftedMagnitude radius) := by
  intro eps
  let C : Rat := radius * radius
  let start : Nat := gaussianIntegralTailStart radius
  let bound : Rat :=
    2 * radius * RationalMajorant.factorialTailTerm C start
  let shift : Nat := RationalMajorant.halfDecayShift bound eps
  refine ⟨shift, ?_⟩
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hC : 0 <= C := by
    dsimp [C]
    exact Rat.mul_nonneg hradius hradius
  have hstart : C <= (((start + 1 : Nat) : Rat) / 2) := by
    simpa [C, start] using gaussianIntegralTailStart_satisfies radius hradius
  have hgeom := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC hstart (shift + d)
  have hpow : ((1 : Rat) / 2) ^ (shift + d) <=
      ((1 : Rat) / 2) ^ shift :=
    Series.halfPow_add_le_left shift d
  have hleibniz : Series.leibnizTerm (start + (shift + d)) <= 1 := by
    calc
      Series.leibnizTerm (start + (shift + d)) <=
          1 / (((start + (shift + d) + 1 : Nat) : Rat)) :=
        Series.leibnizTerm_le_one_div_succ _
      _ <= 1 / ((1 : Nat) : Rat) := by
        exact Series.one_div_nat_antitone_series (by omega) (by omega) (by omega)
      _ = 1 := by decide +kernel
  have hconst : 0 <= 2 * radius := Rat.mul_nonneg (by decide +kernel) hradius
  have hfactor : 0 <=
      RationalMajorant.factorialTailTerm C (start + (shift + d)) :=
    RationalMajorant.factorialTailTerm_nonneg hC _
  have hbound : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg hconst
      (RationalMajorant.factorialTailTerm_nonneg hC start)
  unfold gaussianIntegralShiftedMagnitude gaussianIntegralTermMagnitude
  change 2 * radius *
      RationalMajorant.factorialTailTerm C (start + (shift + d)) *
        Series.leibnizTerm (start + (shift + d)) <= eps.val
  calc
    2 * radius * RationalMajorant.factorialTailTerm C (start + (shift + d)) *
        Series.leibnizTerm (start + (shift + d)) <=
        2 * radius * RationalMajorant.factorialTailTerm C (start + (shift + d)) * 1 := by
      exact Rat.mul_le_mul_of_nonneg_left hleibniz
        (Rat.mul_nonneg hconst hfactor)
    _ = 2 * radius *
        RationalMajorant.factorialTailTerm C (start + (shift + d)) := by simp
    _ <= bound * ((1 : Rat) / 2) ^ (shift + d) := by
      dsimp [bound]
      simpa [Nat.add_assoc, Rat.mul_assoc] using
        (Rat.mul_le_mul_of_nonneg_left hgeom hconst)
    _ <= bound * ((1 : Rat) / 2) ^ shift :=
      Rat.mul_le_mul_of_nonneg_left hpow hbound
    _ <= eps.val := by
      dsimp [shift]
      exact RationalMajorant.halfDecayShift_spec hbound eps

/-- The computable alternating tail left after the explicit even cutoff.
This is purely a rational series object; its identification with an integral
is deliberately kept as a separate later theorem. -/
def gaussianIntegralShiftedAlternatingRaw
    (radius : Rat) (hradius : 0 <= radius) : Series.AlternatingRaw where
  term := gaussianIntegralShiftedMagnitude radius
  term_nonneg := gaussianIntegralShiftedMagnitude_nonneg radius hradius
  term_decreasing := gaussianIntegralShiftedMagnitude_decreasing radius hradius
  term_shrinks := gaussianIntegralShiftedMagnitude_shrinks radius hradius

def gaussianIntegralShiftedTailRaw
    (radius : Rat) (hradius : 0 <= radius) : RealCompute :=
  (gaussianIntegralShiftedAlternatingRaw radius hradius).toRealCompute

theorem gaussianIntegralShiftedTailRaw_valid
    (radius : Rat) (hradius : 0 <= radius) :
    (gaussianIntegralShiftedTailRaw radius hradius).Valid :=
  (gaussianIntegralShiftedAlternatingRaw radius hradius).toRealCompute_valid

theorem gaussianIntegralShifted_signedTerm_eq
    (radius : Rat) (j : Nat) :
    Series.signedTerm (gaussianIntegralShiftedMagnitude radius) j =
      gaussianEvenIntegralTerm (gaussianIntegralTailStart radius + j) radius := by
  let start := gaussianIntegralTailStart radius
  have hstartEven : start % 2 = 0 := by
    simpa [start] using gaussianIntegralTailStart_even radius
  have hstartForm : start = 2 * (start / 2) := by omega
  have hsign : Series.alternatingSign j =
      (-1 : Rat) ^ (start + j) := by
    rw [show Series.alternatingSign j =
        Series.alternatingSign start * Series.alternatingSign j by
      rw [hstartForm, Series.alternatingSign_even]
      simp]
    rw [← Series.alternatingSign_add,
      gaussian_alternatingSign_eq_neg_one_pow]
  unfold Series.signedTerm gaussianIntegralShiftedMagnitude
    gaussianIntegralTermMagnitude gaussianEvenIntegralTerm
    RationalMajorant.factorialTailTerm Series.leibnizTerm
    FormalPowerSeries.expCoeff
  rw [hsign]
  have hpow := gaussian_square_pow_mul radius (start + j)
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- At an even offset from the chosen alternating-tail start, the next
integrated Gaussian term is exactly the nonnegative shifted magnitude. -/
theorem gaussianEvenIntegralTerm_tailStart_add_even_eq_magnitude
    (radius : Rat) (j : Nat) :
    gaussianEvenIntegralTerm
        (gaussianIntegralTailStart radius + 2 * j) radius =
      gaussianIntegralShiftedMagnitude radius (2 * j) := by
  have h := gaussianIntegralShifted_signedTerm_eq radius (2 * j)
  unfold Series.signedTerm at h
  rw [Series.alternatingSign_even, Rat.one_mul] at h
  exact h.symm

/-- Consequently the odd endpoint immediately following an even shifted
prefix is obtained by adding precisely that nonnegative magnitude. -/
theorem gaussianEvenIntegralPrefix_tailStart_even_succ
    (radius : Rat) (j : Nat) :
    gaussianEvenIntegralPrefix
        (gaussianIntegralTailStart radius + 2 * j + 1) radius =
      gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + 2 * j) radius +
        gaussianIntegralShiftedMagnitude radius (2 * j) := by
  rw [gaussianEvenIntegralPrefix_succ]
  change gaussianEvenIntegralPrefix
        (gaussianIntegralTailStart radius + 2 * j) radius +
      gaussianEvenIntegralTerm
        (gaussianIntegralTailStart radius + 2 * j) radius = _
  rw [gaussianEvenIntegralTerm_tailStart_add_even_eq_magnitude]

theorem gaussianIntegralShifted_partialSum_eq_prefix_sub
    (radius : Rat) (terms : Nat) :
    Series.partialSum (gaussianIntegralShiftedMagnitude radius) terms =
      gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + terms) radius -
        gaussianEvenIntegralPrefix (gaussianIntegralTailStart radius) radius := by
  induction terms with
  | zero =>
      rw [Series.partialSum, Nat.add_zero]
      grind
  | succ terms ih =>
      rw [Series.partialSum, ih, gaussianIntegralShifted_signedTerm_eq]
      have hprefix := gaussianEvenIntegralPrefix_succ
        (gaussianIntegralTailStart radius + terms) radius
      change gaussianEvenIntegralPrefix
          ((gaussianIntegralTailStart radius + terms) + 1) radius =
        gaussianEvenIntegralPrefix
            (gaussianIntegralTailStart radius + terms) radius +
          gaussianEvenIntegralTerm
            (gaussianIntegralTailStart radius + terms) radius at hprefix
      rw [show gaussianIntegralTailStart radius + (terms + 1) =
          (gaussianIntegralTailStart radius + terms) + 1 by omega,
        hprefix]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The arbitrary-radius integrated Gaussian Taylor series, split into an
exact finite prefix and a certified alternating tail.  This construction is
a valid computable real independently of the later quadrature theorem that
will identify it with the bounded definite integral. -/
def gaussianRadiusIntegratedSeriesRaw
    (radius : Rat) (hradius : 0 <= radius) : RealCompute :=
  RealCompute.add
    (RealCompute.ofRat
      (gaussianEvenIntegralPrefix (gaussianIntegralTailStart radius) radius))
    (gaussianIntegralShiftedTailRaw radius hradius)

theorem gaussianRadiusIntegratedSeriesRaw_valid
    (radius : Rat) (hradius : 0 <= radius) :
    (gaussianRadiusIntegratedSeriesRaw radius hradius).Valid := by
  exact RealCompute.add_valid
    (RealCompute.ofRat_valid
      (gaussianEvenIntegralPrefix (gaussianIntegralTailStart radius) radius))
    (gaussianIntegralShiftedTailRaw_valid radius hradius)

theorem gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval
    (radius : Rat) (hradius : 0 <= radius) (stage : Nat) :
    (gaussianRadiusIntegratedSeriesRaw radius hradius).compute stage =
      { lo := gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + 2 * stage) radius,
        hi := gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + (2 * stage + 1)) radius } := by
  change RealCompute.addCompute
      (RealCompute.ofRat
        (gaussianEvenIntegralPrefix (gaussianIntegralTailStart radius) radius))
      ((gaussianIntegralShiftedAlternatingRaw radius hradius).toRealCompute)
      stage = _
  simp only [RealCompute.addCompute, RealCompute.ofRat,
    Series.AlternatingRaw.toRealCompute]
  rw [Series.AlternatingRaw.interval_eq_endpoints]
  simp only [gaussianIntegralShiftedAlternatingRaw]
  rw [gaussianIntegralShifted_partialSum_eq_prefix_sub,
    gaussianIntegralShifted_partialSum_eq_prefix_sub]
  congr <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Every even shifted prefix is a certified lower approximation to the
represented integrated Gaussian series, while the following odd prefix is a
certified upper approximation.  This is an exact raw-order statement, not a
limit theorem imported from an infinite-series library. -/
theorem gaussianRadiusIntegratedSeriesRaw_between_shifted_even_odd_prefixes
    (radius : Rat) (hradius : 0 <= radius) (j : Nat) :
    (RealCompute.ofRat
      (gaussianEvenIntegralPrefix
        (gaussianIntegralTailStart radius + 2 * j) radius)).Le
      (gaussianRadiusIntegratedSeriesRaw radius hradius) /\
    (gaussianRadiusIntegratedSeriesRaw radius hradius).Le
      (RealCompute.ofRat
        (gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + (2 * j + 1)) radius)) := by
  let raw := gaussianRadiusIntegratedSeriesRaw radius hradius
  have hraw : raw.Valid := by
    simpa [raw] using gaussianRadiusIntegratedSeriesRaw_valid radius hradius
  have hall := RealCompute.allStagesOverlap_refl raw hraw
  constructor
  · intro n m
    have hover := (RealCompute.compareAt_overlap_iff raw raw j m).1 (hall j m)
    rw [gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval]
      at hover
    rw [RealCompute.ofRat_compute]
    exact hover.1
  · intro n m
    have hover := (RealCompute.compareAt_overlap_iff raw raw n j).1 (hall n j)
    rw [RealCompute.ofRat_compute]
    have hj : (raw.compute j).hi =
        gaussianEvenIntegralPrefix
          (gaussianIntegralTailStart radius + (2 * j + 1)) radius := by
      dsimp [raw]
      rw [gaussianRadiusIntegratedSeriesRaw_compute_eq_prefix_interval]
    rw [← hj]
    exact hover.1

theorem gaussianUnitIntegral_signedTerm_eq (k : Nat) :
    Series.signedTerm gaussianUnitIntegralMagnitude k =
      gaussianEvenIntegralTerm k 1 := by
  have hsign : Series.alternatingSign k = (-1 : Rat) ^ k := by
    by_cases hk : k % 2 = 0
    · have hkform : k = 2 * (k / 2) := by omega
      rw [hkform, gaussian_neg_one_pow_even]
      simp [Series.alternatingSign]
    · have hkform : k = 2 * (k / 2) + 1 := by omega
      rw [hkform, gaussian_neg_one_pow_odd]
      simp [Series.alternatingSign]
  unfold Series.signedTerm gaussianUnitIntegralMagnitude
    gaussianEvenIntegralTerm Series.leibnizTerm
    RationalMajorant.factorialTailTerm FormalPowerSeries.expCoeff
  rw [hsign]
  rw [gaussian_one_pow, gaussian_one_pow]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

def gaussianEvenIntegralTailMajorant (radius : Rat) (start : Nat) : Nat → Rat
  | 0 => 0
  | terms + 1 =>
      gaussianEvenIntegralTailMajorant radius start terms +
        qabs (gaussianEvenIntegralTerm (start + terms) radius)

theorem gaussianEvenIntegralPrefix_succ_eq_term (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius =
      gaussianEvenIntegralPrefix terms radius +
        gaussianEvenIntegralTerm terms radius := by
  rw [gaussianEvenIntegralPrefix_succ]
  rfl

theorem gaussianUnitIntegral_partialSum_eq_prefix (terms : Nat) :
    Series.partialSum gaussianUnitIntegralMagnitude terms =
      gaussianEvenIntegralPrefix terms 1 := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [Series.partialSum, gaussianEvenIntegralPrefix_succ_eq_term,
        ih, gaussianUnitIntegral_signedTerm_eq]

theorem gaussianUnitIntegralRaw_compute_eq_prefix_interval (stage : Nat) :
    gaussianUnitIntegralRaw.compute stage =
      { lo := gaussianEvenIntegralPrefix (2 * stage) 1,
        hi := gaussianEvenIntegralPrefix (2 * stage + 1) 1 } := by
  change gaussianUnitIntegralAlternatingRaw.interval stage = _
  rw [Series.AlternatingRaw.interval_eq_endpoints]
  simp only [gaussianUnitIntegralAlternatingRaw]
  rw [gaussianUnitIntegral_partialSum_eq_prefix,
    gaussianUnitIntegral_partialSum_eq_prefix]

theorem gaussianUnitIntegralRaw_width_eq_magnitude (stage : Nat) :
    (gaussianUnitIntegralRaw.compute stage).width =
      gaussianUnitIntegralMagnitude (2 * stage) := by
  change (gaussianUnitIntegralAlternatingRaw.interval stage).width = _
  exact Series.AlternatingRaw.interval_width_eq
    gaussianUnitIntegralAlternatingRaw stage

theorem gaussianUnitIntegralRaw_width_le_natRate (stage : Nat) :
    (gaussianUnitIntegralRaw.compute stage).width <=
      (2 : Rat) / (((2 * stage + 1 : Nat) : Rat)) := by
  rw [gaussianUnitIntegralRaw_width_eq_magnitude]
  exact gaussianUnitIntegralMagnitude_le_natRate (2 * stage)

theorem gaussianUnitIntegralRaw_reaches_of_positive_tolerance (eps : QPos) :
    ∃ stage : Nat,
      (gaussianUnitIntegralRaw.compute stage).width <= eps.val := by
  rcases gaussianUnitIntegralRaw_valid.2.2 eps with ⟨stage, hstage⟩
  exact ⟨stage, hstage stage (Nat.le_refl stage)⟩

theorem gaussianUnitIntegralRaw_stage_one :
    gaussianUnitIntegralRaw.compute 1 = { lo := 4 / 3, hi := 23 / 15 } := by
  rw [gaussianUnitIntegralRaw_compute_eq_prefix_interval]
  decide +kernel

theorem gaussianEvenIntegralPrefix_remainder_abs_le
    (radius : Rat) (start terms : Nat) :
    qabs (gaussianEvenIntegralPrefix (start + terms) radius -
      gaussianEvenIntegralPrefix start radius) <=
      gaussianEvenIntegralTailMajorant radius start terms := by
  induction terms with
  | zero =>
      simp only [gaussianEvenIntegralTailMajorant, Nat.zero_eq, Nat.add_zero,
        Rat.sub_self]
      exact Rat.le_refl
  | succ terms ih =>
      rw [gaussianEvenIntegralTailMajorant]
      have hstep :
          gaussianEvenIntegralPrefix (start + (terms + 1)) radius =
            gaussianEvenIntegralPrefix (start + terms) radius +
              gaussianEvenIntegralTerm (start + terms) radius := by
        have hindex : start + (terms + 1) = (start + terms) + 1 := by omega
        rw [hindex, gaussianEvenIntegralPrefix_succ_eq_term]
      rw [hstep]
      have hrewrite :
          gaussianEvenIntegralPrefix (start + terms) radius +
              gaussianEvenIntegralTerm (start + terms) radius -
            gaussianEvenIntegralPrefix start radius =
            (gaussianEvenIntegralPrefix (start + terms) radius -
              gaussianEvenIntegralPrefix start radius) +
              gaussianEvenIntegralTerm (start + terms) radius := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hrewrite]
      exact Rat.le_trans
        (qabs_add_le _ _)
        (rat_add_le_add ih Rat.le_refl)

/- Package the finite Gaussian prefix together with its explicit rational tail
   allowance.  This is the interval-valued object consumed by later bounded
   or improper Gaussian constructions; no infinite integral is asserted here. -/
def gaussianEvenIntegralPrefix_interval
    (radius : Rat) (start terms : Nat) : QInterval :=
  { lo := gaussianEvenIntegralPrefix start radius -
      gaussianEvenIntegralTailMajorant radius start terms,
    hi := gaussianEvenIntegralPrefix start radius +
      gaussianEvenIntegralTailMajorant radius start terms }

theorem gaussianEvenIntegralPrefix_interval_contains
    (radius : Rat) (start terms : Nat) :
    (gaussianEvenIntegralPrefix_interval radius start terms).lo <=
        gaussianEvenIntegralPrefix (start + terms) radius /\
      gaussianEvenIntegralPrefix (start + terms) radius <=
        (gaussianEvenIntegralPrefix_interval radius start terms).hi := by
  have h := gaussianEvenIntegralPrefix_remainder_abs_le radius start terms
  unfold gaussianEvenIntegralPrefix_interval
  constructor
  · have hneg := neg_qabs_le_self
      (gaussianEvenIntegralPrefix (start + terms) radius -
        gaussianEvenIntegralPrefix start radius)
    have hlow := Rat.le_trans (Rat.neg_le_neg h) hneg
    grind [Rat.sub_eq_add_neg]
  · have hupper := self_le_qabs
      (gaussianEvenIntegralPrefix (start + terms) radius -
        gaussianEvenIntegralPrefix start radius)
    have hupp := Rat.le_trans hupper h
    grind [Rat.sub_eq_add_neg]

theorem gaussianEvenIntegralPrefix_interval_width
    (radius : Rat) (start terms : Nat) :
    (gaussianEvenIntegralPrefix_interval radius start terms).width =
      2 * gaussianEvenIntegralTailMajorant radius start terms := by
  unfold gaussianEvenIntegralPrefix_interval QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem gaussianEvenIntegralPrefix_stage_four :
    gaussianEvenIntegralPrefix 4 1 = 52 / 35 := by
  decide +kernel

theorem gaussianEvenIntegralPrefix_stage_six :
    gaussianEvenIntegralPrefix 6 1 = 31049 / 20790 := by
  decide +kernel

theorem gaussianEvenIntegralPrefix_stage_eight :
    gaussianEvenIntegralPrefix 8 1 = 1009219 / 675675 := by
  decide +kernel

theorem gaussianEvenIntegralPrefix_stage_six_minus_four :
    gaussianEvenIntegralPrefix 6 1 - gaussianEvenIntegralPrefix 4 1 =
      23 / 2970 := by
  rw [gaussianEvenIntegralPrefix_stage_six,
    gaussianEvenIntegralPrefix_stage_four]
  decide +kernel

theorem gaussianEvenIntegralPrefix_stage_four_nonnegative :
    0 <= gaussianEvenIntegralPrefix 4 1 := by
  rw [gaussianEvenIntegralPrefix_stage_four]
  decide +kernel

/-! A finite reciprocal-square tail, suitable for transporting a supplied
pointwise Gaussian domination certificate. -/

def reciprocalSquareTailPartial (cutoff : Rat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      reciprocalSquareTailPartial cutoff terms +
        1 / (cutoff + (terms + 1 : Nat)) ^ 2

theorem reciprocalSquareTailPartial_succ (cutoff : Rat) (terms : Nat) :
    reciprocalSquareTailPartial cutoff (terms + 1) =
      reciprocalSquareTailPartial cutoff terms +
        1 / (cutoff + (terms + 1 : Nat)) ^ 2 := by
  rfl

theorem reciprocalSquareTailPartial_stage_four :
    reciprocalSquareTailPartial 1 4 = 1669 / 3600 := by
  decide +kernel

theorem reciprocalSquareTailPartial_stage_four_below_one :
    reciprocalSquareTailPartial 1 4 < 1 := by
  rw [reciprocalSquareTailPartial_stage_four]
  decide +kernel

theorem reciprocalSquareTailPartial_stage_six :
    reciprocalSquareTailPartial 1 6 = 90281 / 176400 := by
  decide +kernel

theorem reciprocalSquareTailPartial_stage_eight :
    reciprocalSquareTailPartial 1 8 = 3427741 / 6350400 := by
  decide +kernel

theorem reciprocalSquareTailPartial_stage_eight_below_one :
    reciprocalSquareTailPartial 1 8 < 1 := by
  rw [reciprocalSquareTailPartial_stage_eight]
  decide +kernel

/-! A concrete pointwise Gaussian tail witness from the project's certified
power-series exponential box. -/

theorem expPowerSeries_neg_four_stage_twenty_upper :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 := by
  decide +kernel

theorem expPowerSeries_neg_nine_stage_twenty_upper :
    ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 := by
  decide +kernel

theorem expPowerSeries_neg_sixteen_stage_twenty_upper :
    ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  decide +kernel

theorem expPowerSeries_neg_twenty_five_stage_twenty_upper :
    ((expPowerSeries (-25 : Rat)).compute 20).hi <= 1 / 25 := by
  decide +kernel

theorem gaussianTailPointLadder_stage_twenty :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 /\
      ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 /\
      ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  exact ⟨expPowerSeries_neg_four_stage_twenty_upper,
    expPowerSeries_neg_nine_stage_twenty_upper,
    expPowerSeries_neg_sixteen_stage_twenty_upper⟩

def gaussianTailBoxUpper (x : Rat) (stage : Nat) : Rat :=
  ((expPowerSeries (-(x * x))).compute stage).hi

theorem gaussianTailBoxUpper_stage_twenty_ladder :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 := by
  decide +kernel

theorem gaussianTailBoxUpper_stage_twenty_ladder_four :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 := by
  decide +kernel

theorem gaussianTailBoxUpper_stage_twenty_ladder_eight :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 /\
      gaussianTailBoxUpper 6 100 <= 1 / 36 /\
      gaussianTailBoxUpper 7 100 <= 1 / 49 /\
      gaussianTailBoxUpper 8 100 <= 1 / 64 := by
  decide +kernel

theorem gaussianTailBoxUpper_stage_twenty_three_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 <= 61 / 144 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder
  grind

theorem gaussianTailBoxUpper_stage_twenty_four_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 <=
      1669 / 3600 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_four
  grind

theorem gaussianTailBoxUpper_stage_twenty_eight_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 +
        gaussianTailBoxUpper 6 100 + gaussianTailBoxUpper 7 100 +
        gaussianTailBoxUpper 8 100 <= 3349341 / 6350400 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_eight
  grind

theorem gaussianTailBoxUpper_stage_two_hundred_nine_ten_ladder :
    gaussianTailBoxUpper 9 200 <= 1 / 81 /\
      gaussianTailBoxUpper 10 200 <= 1 / 100 := by
  decide +kernel

theorem gaussianTailBoxUpper_stage_two_hundred_nine_ten_sum :
    gaussianTailBoxUpper 9 200 + gaussianTailBoxUpper 10 200 <=
      181 / 8100 := by
  have h := gaussianTailBoxUpper_stage_two_hundred_nine_ten_ladder
  grind

end ComputableAnalysis


