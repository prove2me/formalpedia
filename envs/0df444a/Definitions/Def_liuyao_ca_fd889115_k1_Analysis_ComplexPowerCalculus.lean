-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexPowerCalculus
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexPowerCalculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:44.811343+00:00
-- url     : https://prove2.me/theorems/f826b2c2-14dd-44a9-9c61-f43a3567a64d
-- title:
--   Computable analysis · ComplexPowerCalculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexPowerCalculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialApproximation

set_option autoImplicit true

/-!
# Quantitative finite complex power calculus

This module proves the finite Lipschitz estimate needed to evaluate analytic
power series on a moving represented complex input.  All bounds are rational
and all powers are finite.
-/

namespace ComputableAnalysis

namespace QComplex

theorem normBound_neg (z : QComplex) :
    normBound (neg z) = normBound z := by
  unfold normBound neg
  rw [qabs_neg, qabs_neg]

theorem normBound_sub_le (z w : QComplex) :
    normBound (sub z w) <= normBound z + normBound w := by
  unfold sub
  calc
    normBound (add z (neg w)) <=
        normBound z + normBound (neg w) := normBound_add_le _ _
    _ = normBound z + normBound w := by rw [normBound_neg]

/-- Exact product-difference decomposition. -/
theorem mul_sub_mul_decompose (z w a b : QComplex) :
    sub (mul z a) (mul w b) =
      add (mul z (sub a b)) (mul (sub z w) b) := by
  cases z
  cases w
  cases a
  cases b
  simp [sub, add, neg, mul]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm,
    Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem sub_add_sub (a b c d : QComplex) :
    sub (add a b) (add c d) = add (sub a c) (sub b d) := by
  cases a
  cases b
  cases c
  cases d
  simp [sub, add, neg]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.neg_add]

/-- On the norm ball of radius `C`, the difference of `(n+1)`st powers is
bounded by `(n+1) C^n` times the input difference. -/
theorem pow_succ_difference_normBound_le
    {z w : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : normBound z <= C) (hw : normBound w <= C) :
    forall n,
      normBound (sub (pow z (n + 1)) (pow w (n + 1))) <=
        (((n + 1 : Nat) : Rat) * C ^ n) * normBound (sub z w)
  | 0 => by
      change normBound (sub (mul z one) (mul w one)) <=
        (((1 : Nat) : Rat) * C ^ 0) * normBound (sub z w)
      rw [mul_one_cert, mul_one_cert, Rat.pow_zero]
      change normBound (sub z w) <=
        (1 : Rat) * 1 * normBound (sub z w)
      rw [Rat.one_mul, Rat.one_mul]
      exact Rat.le_refl
  | n + 1 => by
      change normBound
          (sub (mul z (pow z (n + 1))) (mul w (pow w (n + 1)))) <=
        ((((n + 1 + 1 : Nat) : Rat) * C ^ (n + 1)) *
          normBound (sub z w))
      rw [mul_sub_mul_decompose]
      have hprevious := pow_succ_difference_normBound_le hC hz hw n
      have hwpow := normBound_pow_le hC hw (n + 1)
      have hdist0 : 0 <= normBound (sub z w) := normBound_nonneg _
      have hpow0 : 0 <= C ^ (n + 1) := Rat.pow_nonneg hC
      have hfirst :
          normBound (mul z
            (sub (pow z (n + 1)) (pow w (n + 1)))) <=
            C * ((((n + 1 : Nat) : Rat) * C ^ n) *
              normBound (sub z w)) := by
        calc
          normBound (mul z
              (sub (pow z (n + 1)) (pow w (n + 1)))) <=
              normBound z *
                normBound (sub (pow z (n + 1)) (pow w (n + 1))) :=
            normBound_mul_le _ _
          _ <= C *
              normBound (sub (pow z (n + 1)) (pow w (n + 1))) :=
            Rat.mul_le_mul_of_nonneg_right hz (normBound_nonneg _)
          _ <= C * ((((n + 1 : Nat) : Rat) * C ^ n) *
              normBound (sub z w)) :=
            Rat.mul_le_mul_of_nonneg_left hprevious hC
      have hsecond :
          normBound (mul (sub z w) (pow w (n + 1))) <=
            normBound (sub z w) * C ^ (n + 1) := by
        exact Rat.le_trans (normBound_mul_le _ _)
          (Rat.mul_le_mul_of_nonneg_left hwpow hdist0)
      calc
        normBound
            (add
              (mul z (sub (pow z (n + 1)) (pow w (n + 1))))
              (mul (sub z w) (pow w (n + 1)))) <=
            normBound (mul z
              (sub (pow z (n + 1)) (pow w (n + 1)))) +
              normBound (mul (sub z w) (pow w (n + 1))) :=
          normBound_add_le _ _
        _ <= C * ((((n + 1 : Nat) : Rat) * C ^ n) *
              normBound (sub z w)) +
            normBound (sub z w) * C ^ (n + 1) :=
          rat_add_le_add hfirst hsecond
        _ = ((((n + 1 + 1 : Nat) : Rat) * C ^ (n + 1)) *
              normBound (sub z w)) := by
          rw [Rat.pow_succ]
          simp only [Rat.natCast_add]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
            Rat.add_assoc, Rat.add_comm]

end QComplex

namespace QComplex

theorem normBound_scaleRat (r : Rat) (z : QComplex) :
    normBound (scaleRat r z) = qabs r * normBound z := by
  unfold normBound scaleRat
  rw [qabs_mul, qabs_mul]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem sub_scaleRat (r : Rat) (z w : QComplex) :
    sub (scaleRat r z) (scaleRat r w) = scaleRat r (sub z w) := by
  cases z
  cases w
  simp [sub, scaleRat, add, neg]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add,
    Rat.neg_mul, Rat.mul_neg]

end QComplex

namespace ComplexExponentialApproximation

def termDerivativeMajorant (C : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => RationalMajorant.factorialTailTerm C n

def derivativeMajorantPartial (C : Rat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      derivativeMajorantPartial C terms +
        termDerivativeMajorant C terms

theorem expCoeff_nonneg (n : Nat) :
    0 <= FormalPowerSeries.expCoeff n := by
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2
    (RationalMajorant.factorialRat_pos n))

theorem expCoeff_succ_mul_natCast (n : Nat) :
    FormalPowerSeries.expCoeff (n + 1) * (((n + 1 : Nat) : Rat)) =
      FormalPowerSeries.expCoeff n := by
  have h := congrFun FormalPowerSeries.expCoeff_derivative n
  change (((n + 1 : Nat) : Rat)) *
      FormalPowerSeries.expCoeff (n + 1) =
        FormalPowerSeries.expCoeff n at h
  simpa [Rat.mul_comm] using h

theorem expCoeff_mul_power_eq_factorialTailTerm (C : Rat) (n : Nat) :
    FormalPowerSeries.expCoeff n * C ^ n =
      RationalMajorant.factorialTailTerm C n := by
  unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
  rw [Rat.div_def, Rat.div_def, Rat.one_mul]
  exact Rat.mul_comm _ _

theorem term_difference_normBound_le
    {z w : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C)
    (hw : QComplex.normBound w <= C) (n : Nat) :
    QComplex.normBound (QComplex.sub (term z n) (term w n)) <=
      termDerivativeMajorant C n *
        QComplex.normBound (QComplex.sub z w) := by
  cases n with
  | zero =>
      have hterm : forall u : QComplex, term u 0 = QComplex.one := by
        intro u
        unfold term ComplexSeries.expTerm QComplex.pow QComplex.divRat
          factorialRat factorial QComplex.one
        decide +kernel
      rw [hterm z, hterm w, termDerivativeMajorant, Rat.zero_mul]
      decide +kernel
  | succ n =>
      rw [term_eq_scaleRat, term_eq_scaleRat,
        QComplex.sub_scaleRat, QComplex.normBound_scaleRat,
        qabs_eq_self_of_nonneg (expCoeff_nonneg (n + 1))]
      have hpower := QComplex.pow_succ_difference_normBound_le hC hz hw n
      have hcoeff := expCoeff_nonneg (n + 1)
      calc
        FormalPowerSeries.expCoeff (n + 1) *
            QComplex.normBound
              (QComplex.sub (QComplex.pow z (n + 1))
                (QComplex.pow w (n + 1))) <=
            FormalPowerSeries.expCoeff (n + 1) *
              (((((n + 1 : Nat) : Rat) * C ^ n) *
                QComplex.normBound (QComplex.sub z w))) :=
          Rat.mul_le_mul_of_nonneg_left hpower hcoeff
        _ = termDerivativeMajorant C (n + 1) *
              QComplex.normBound (QComplex.sub z w) := by
          rw [termDerivativeMajorant]
          rw [← expCoeff_mul_power_eq_factorialTailTerm C n]
          rw [← expCoeff_succ_mul_natCast n]
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem derivativeMajorantPartial_nonneg {C : Rat} (hC : 0 <= C) :
    forall terms, 0 <= derivativeMajorantPartial C terms
  | 0 => Rat.le_refl
  | terms + 1 => by
      rw [derivativeMajorantPartial]
      exact Rat.add_nonneg (derivativeMajorantPartial_nonneg hC terms)
        (by
          cases terms with
          | zero => exact Rat.le_refl
          | succ terms =>
              exact RationalMajorant.factorialTailTerm_nonneg hC terms)

theorem derivativeMajorantPartial_succ_eq (C : Rat) (terms : Nat) :
    derivativeMajorantPartial C (terms + 1) =
      RationalMajorant.factorialTailPartial C 0 terms := by
  induction terms with
  | zero =>
      change (0 : Rat) + 0 = 0
      exact Rat.zero_add 0
  | succ terms ih =>
      rw [derivativeMajorantPartial, ih, termDerivativeMajorant,
        RationalMajorant.factorialTailPartial, Nat.zero_add]

/-- One finite rational Lipschitz constant controlling every exponential
prefix on the norm ball of radius `C`. -/
def derivativeMajorant (C : Rat) : Rat :=
  let start := RationalMajorant.factorialTailStart C
  RationalMajorant.factorialTailPartial C 0 start +
    2 * RationalMajorant.factorialTailTerm C start

theorem derivativeMajorant_nonneg {C : Rat} (hC : 0 <= C) :
    0 <= derivativeMajorant C := by
  have hpartial :
      0 <= RationalMajorant.factorialTailPartial C 0
        (RationalMajorant.factorialTailStart C) := by
    have hmono := RationalMajorant.factorialTailPartial_mono hC 0
      0 (RationalMajorant.factorialTailStart C) (Nat.zero_le _)
    simpa [RationalMajorant.factorialTailPartial] using hmono
  unfold derivativeMajorant
  exact Rat.add_nonneg
    hpartial
    (Rat.mul_nonneg (by decide +kernel)
      (RationalMajorant.factorialTailTerm_nonneg hC _))

private theorem factorialTailPartial_le_derivativeMajorant
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    RationalMajorant.factorialTailPartial C 0 terms <=
      derivativeMajorant C := by
  let start := RationalMajorant.factorialTailStart C
  by_cases hterms : terms <= start
  · have hmono := RationalMajorant.factorialTailPartial_mono
      hC 0 terms start hterms
    have htail0 :
        0 <= 2 * RationalMajorant.factorialTailTerm C start :=
      Rat.mul_nonneg (by decide +kernel)
        (RationalMajorant.factorialTailTerm_nonneg hC _)
    unfold derivativeMajorant
    dsimp [start] at hmono htail0 ⊢
    exact Rat.le_trans hmono (by grind)
  · have hstart : start <= terms := by omega
    let extra := terms - start
    have htermsEq : terms = start + extra := by
      dsimp [extra]
      omega
    rw [htermsEq, RationalMajorant.factorialTailPartial_add]
    have htail := RationalMajorant.factorialTailPartial_bound hC
      (RationalMajorant.factorialTailStart_satisfies C) extra
    unfold derivativeMajorant
    dsimp [start] at htail ⊢
    simpa only [Nat.zero_add] using Rat.add_le_add_left.mpr htail

theorem derivativeMajorantPartial_le
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    derivativeMajorantPartial C terms <= derivativeMajorant C := by
  cases terms with
  | zero =>
      rw [derivativeMajorantPartial]
      have hpartial :
          0 <= RationalMajorant.factorialTailPartial C 0
            (RationalMajorant.factorialTailStart C) := by
        have hmono := RationalMajorant.factorialTailPartial_mono hC 0
          0 (RationalMajorant.factorialTailStart C) (Nat.zero_le _)
        simpa [RationalMajorant.factorialTailPartial] using hmono
      have htail :
          0 <= 2 * RationalMajorant.factorialTailTerm C
            (RationalMajorant.factorialTailStart C) :=
        Rat.mul_nonneg (by decide +kernel)
          (RationalMajorant.factorialTailTerm_nonneg hC _)
      unfold derivativeMajorant
      grind
  | succ terms =>
      rw [derivativeMajorantPartial_succ_eq]
      exact factorialTailPartial_le_derivativeMajorant hC terms

/-- Every finite complex exponential prefix on a norm ball is bounded by the
same explicit rational majorant used for its Lipschitz estimate. -/
theorem expPrefix_normBound_le_derivativeMajorant
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (terms : Nat) :
    QComplex.normBound (ComplexExponentialApproximation.expPrefix z terms) <=
      derivativeMajorant C := by
  have hpartial := ComplexExponentialApproximation.tailPartial_normBound_le
    hC hz 0 terms
  have hprefix :
      QComplex.normBound (ComplexExponentialApproximation.expPrefix z terms) <=
        derivativeMajorantPartial C (terms + 1) := by
    simpa [ComplexExponentialApproximation.expPrefix,
      derivativeMajorantPartial_succ_eq] using hpartial
  exact Rat.le_trans hprefix (derivativeMajorantPartial_le hC (terms + 1))

/-- Finite complex exponential prefixes have an explicit rational Lipschitz
majorant on every supplied norm ball. -/
theorem expPrefix_difference_normBound_le
    {z w : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C)
    (hw : QComplex.normBound w <= C) :
    forall terms,
      QComplex.normBound
          (QComplex.sub (expPrefix z terms) (expPrefix w terms)) <=
        derivativeMajorantPartial C terms *
          QComplex.normBound (QComplex.sub z w)
  | 0 => by
      have hprefix : forall u : QComplex,
          expPrefix u 0 = QComplex.zero := by
        intro u
        rfl
      rw [hprefix z, hprefix w, derivativeMajorantPartial, Rat.zero_mul]
      decide +kernel
  | terms + 1 => by
      rw [expPrefix_succ, expPrefix_succ, QComplex.sub_add_sub]
      have hprefix := expPrefix_difference_normBound_le hC hz hw terms
      have hterm := term_difference_normBound_le hC hz hw terms
      calc
        QComplex.normBound
            (QComplex.add
              (QComplex.sub (expPrefix z terms) (expPrefix w terms))
              (QComplex.sub (term z terms) (term w terms))) <=
            QComplex.normBound
                (QComplex.sub (expPrefix z terms) (expPrefix w terms)) +
              QComplex.normBound
                (QComplex.sub (term z terms) (term w terms)) :=
          QComplex.normBound_add_le _ _
        _ <= derivativeMajorantPartial C terms *
              QComplex.normBound (QComplex.sub z w) +
            termDerivativeMajorant C terms *
              QComplex.normBound (QComplex.sub z w) :=
          rat_add_le_add hprefix hterm
        _ = derivativeMajorantPartial C (terms + 1) *
              QComplex.normBound (QComplex.sub z w) := by
          rw [derivativeMajorantPartial, Rat.add_mul]

/-- All finite exponential prefixes share one computable Lipschitz constant
on a rational norm ball. This is the composition modulus used when the input
box itself moves with a represented complex argument. -/
theorem expPrefix_difference_normBound_le_uniform
    {z w : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C)
    (hw : QComplex.normBound w <= C) (terms : Nat) :
    QComplex.normBound
        (QComplex.sub (expPrefix z terms) (expPrefix w terms)) <=
      derivativeMajorant C * QComplex.normBound (QComplex.sub z w) := by
  exact Rat.le_trans (expPrefix_difference_normBound_le hC hz hw terms)
    (Rat.mul_le_mul_of_nonneg_right
      (derivativeMajorantPartial_le hC terms)
      (QComplex.normBound_nonneg _))

end ComplexExponentialApproximation

end ComputableAnalysis


