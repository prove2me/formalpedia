-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialApproximation
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexExponentialApproximation
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:08.749252+00:00
-- url     : https://prove2.me/theorems/f08d315d-9c72-4ea5-9b60-601e79d9d124
-- title:
--   Computable analysis · ComplexExponentialApproximation · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexExponentialApproximation.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_HolomorphicJet
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialTaylor
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PolynomialHolomorphicChart

set_option autoImplicit true

/-!
# Finite complex exponential approximations

This module supplies the missing rational-complex majorant for exponential
Taylor prefixes.  Every statement concerns finite sums.  The scheduled
extension theorem is a potential-infinity certificate: every later finite
prefix differs from the scheduled prefix by an explicitly bounded rational
complex error.
-/

namespace ComputableAnalysis

namespace QComplex

theorem normBound_nonneg (z : QComplex) : 0 <= normBound z := by
  unfold normBound
  exact Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _)

theorem normBound_zero : normBound zero = 0 := by
  decide +kernel

theorem normBound_add_le (z w : QComplex) :
    normBound (add z w) <= normBound z + normBound w := by
  unfold normBound add
  have hre := qabs_add_le z.re w.re
  have him := qabs_add_le z.im w.im
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem normBound_mul_le (z w : QComplex) :
    normBound (mul z w) <= normBound z * normBound w := by
  unfold normBound mul
  have hre := qabs_sub_le (z.re * w.re) (z.im * w.im)
  have him := qabs_add_le (z.re * w.im) (z.im * w.re)
  rw [qabs_mul, qabs_mul] at hre
  rw [qabs_mul, qabs_mul] at him
  calc
    qabs (z.re * w.re - z.im * w.im) +
        qabs (z.re * w.im + z.im * w.re) <=
      (qabs z.re * qabs w.re + qabs z.im * qabs w.im) +
        (qabs z.re * qabs w.im + qabs z.im * qabs w.re) :=
      rat_add_le_add hre him
    _ = (qabs z.re + qabs z.im) * (qabs w.re + qabs w.im) := by
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.add_left_comm]

theorem normBound_pow_le {z : QComplex} {C : Rat}
    (hC : 0 <= C) (hz : normBound z <= C) :
    forall n, normBound (pow z n) <= C ^ n
  | 0 => by
      rw [Rat.pow_zero]
      change normBound one <= (1 : Rat)
      decide +kernel
  | n + 1 => by
      rw [pow]
      calc
        normBound (mul z (pow z n)) <=
            normBound z * normBound (pow z n) := normBound_mul_le _ _
        _ <= C * normBound (pow z n) :=
          Rat.mul_le_mul_of_nonneg_right hz (normBound_nonneg _)
        _ <= C * C ^ n :=
          Rat.mul_le_mul_of_nonneg_left
            (normBound_pow_le hC hz n) hC
        _ = C ^ (n + 1) := by
          rw [Rat.pow_succ]
          exact Rat.mul_comm _ _

theorem normBound_divRat_eq (z : QComplex) {q : Rat} (hq : 0 < q) :
    normBound (divRat z q) = normBound z * q⁻¹ := by
  have hinv : 0 <= q⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hq)
  unfold normBound divRat
  rw [Rat.div_def, Rat.div_def, qabs_mul, qabs_mul,
    qabs_eq_self_of_nonneg hinv]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

end QComplex

namespace ComplexExponentialApproximation

abbrev term := ComplexSeries.expTerm

/-- A finite complex exponential block with degrees
`start, ..., start + terms - 1`. -/
def tailPartial (z : QComplex) (start : Nat) : Nat -> QComplex
  | 0 => QComplex.zero
  | terms + 1 =>
      QComplex.add (tailPartial z start terms)
        (term z (start + terms))

/-- The first `terms` complex exponential monomials. -/
def expPrefix (z : QComplex) (terms : Nat) : QComplex :=
  tailPartial z 0 terms

theorem expPrefix_succ (z : QComplex) (terms : Nat) :
    expPrefix z (terms + 1) =
      QComplex.add (expPrefix z terms) (term z terms) := by
  unfold expPrefix
  simp only [tailPartial, Nat.zero_add]

theorem complexSeries_expPartial_succ (z : QComplex) (terms : Nat) :
    ComplexSeries.expPartial z (terms + 1) =
      QComplex.add (ComplexSeries.expPartial z terms) (term z terms) := by
  unfold ComplexSeries.expPartial
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The new recursive prefix is definitionally compatible with the existing
public finite complex exponential evaluator. -/
theorem expPrefix_eq_complexSeries_expPartial
    (z : QComplex) (terms : Nat) :
    expPrefix z terms = ComplexSeries.expPartial z terms := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [expPrefix_succ, complexSeries_expPartial_succ, ih]

/-! ## Uniform evaluation on rational complex boxes -/

def boxPow (input : QBox) : Nat -> QBox
  | 0 => QBox.point QComplex.one
  | n + 1 => QBox.mul input (boxPow input n)

theorem boxPow_contains {input : QBox} {z : QComplex}
    (hzlo : input.lo <= z) (hzhi : z <= input.hi) :
    forall n,
      (boxPow input n).lo <= QComplex.pow z n /\
        QComplex.pow z n <= (boxPow input n).hi
  | 0 => ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n + 1 => by
      rw [boxPow, QComplex.pow]
      exact QBox.mul_contains hzlo hzhi
        (boxPow_contains hzlo hzhi n).1
        (boxPow_contains hzlo hzhi n).2

def termBox (input : QBox) (n : Nat) : QBox :=
  QBox.scaleRat (FormalPowerSeries.expCoeff n) (boxPow input n)

theorem term_eq_scaleRat (z : QComplex) (n : Nat) :
    term z n = QComplex.scaleRat
      (FormalPowerSeries.expCoeff n) (QComplex.pow z n) := by
  cases hpow : QComplex.pow z n with
  | mk re im =>
      unfold term ComplexSeries.expTerm QComplex.divRat
        QComplex.scaleRat FormalPowerSeries.expCoeff
      simp only [hpow]
      congr <;> grind [Rat.div_def, Rat.mul_comm]

theorem termBox_contains {input : QBox} {z : QComplex}
    (hzlo : input.lo <= z) (hzhi : z <= input.hi) (n : Nat) :
    (termBox input n).lo <= term z n /\
      term z n <= (termBox input n).hi := by
  rw [term_eq_scaleRat]
  exact QBox.scaleRat_contains
    (boxPow_contains hzlo hzhi n).1
    (boxPow_contains hzlo hzhi n).2

def prefixBox (input : QBox) : Nat -> QBox
  | 0 => QBox.point QComplex.zero
  | terms + 1 => QBox.add (prefixBox input terms) (termBox input terms)

theorem prefixBox_contains {input : QBox} {z : QComplex}
    (hzlo : input.lo <= z) (hzhi : z <= input.hi) :
    forall terms,
      (prefixBox input terms).lo <= expPrefix z terms /\
        expPrefix z terms <= (prefixBox input terms).hi
  | 0 => ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | terms + 1 => by
      rw [prefixBox, expPrefix_succ]
      exact QBox.add_contains
        (prefixBox_contains hzlo hzhi terms).1
        (prefixBox_contains hzlo hzhi terms).2
        (termBox_contains hzlo hzhi terms).1
        (termBox_contains hzlo hzhi terms).2

theorem qabs_re_le_normBound (z : QComplex) :
    qabs z.re <= QComplex.normBound z := by
  unfold QComplex.normBound
  have h := qabs_nonneg z.im
  grind

theorem qabs_im_le_normBound (z : QComplex) :
    qabs z.im <= QComplex.normBound z := by
  unfold QComplex.normBound
  have h := qabs_nonneg z.re
  grind

theorem point_add_error_nested_expand_box
    {box : QBox} {center error : QComplex} {radius : Rat}
    (hcenterLo : box.lo <= center) (hcenterHi : center <= box.hi)
    (herror : QComplex.normBound error <= radius) :
    (QBox.point (QComplex.add center error)).NestedIn
      (QBox.expand box radius) := by
  have hre := Rat.le_trans (qabs_re_le_normBound error) herror
  have him := Rat.le_trans (qabs_im_le_normBound error) herror
  have hrelo := neg_qabs_le_self error.re
  have hrehi := self_le_qabs error.re
  have himlo := neg_qabs_le_self error.im
  have himhi := self_le_qabs error.im
  unfold QBox.NestedIn QBox.expand QBox.point QComplex.add
  simp only [QComplex.le_def] at hcenterLo hcenterHi ⊢
  constructor <;> constructor <;>
    grind [Rat.sub_eq_add_neg]

theorem term_normBound_le {z : QComplex} {C : Rat}
    (hC : 0 <= C) (hz : QComplex.normBound z <= C) (n : Nat) :
    QComplex.normBound (term z n) <=
      RationalMajorant.factorialTailTerm C n := by
  unfold term ComplexSeries.expTerm RationalMajorant.factorialTailTerm
  have hfactorial := RationalMajorant.factorialRat_pos n
  rw [QComplex.normBound_divRat_eq _ hfactorial]
  rw [Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right
    (QComplex.normBound_pow_le hC hz n)
    (Rat.le_of_lt ((Rat.inv_pos).2 hfactorial))

theorem tailPartial_normBound_le {z : QComplex} {C : Rat}
    (hC : 0 <= C) (hz : QComplex.normBound z <= C)
    (start terms : Nat) :
    QComplex.normBound (tailPartial z start terms) <=
      RationalMajorant.factorialTailPartial C start terms := by
  induction terms with
  | zero =>
      rw [tailPartial, RationalMajorant.factorialTailPartial,
        QComplex.normBound_zero]
      exact Rat.le_refl
  | succ terms ih =>
      rw [tailPartial, RationalMajorant.factorialTailPartial]
      exact Rat.le_trans (QComplex.normBound_add_le _ _)
        (rat_add_le_add ih (term_normBound_le hC hz (start + terms)))

theorem tailPartial_add (z : QComplex) (start first second : Nat) :
    tailPartial z start (first + second) =
      QComplex.add (tailPartial z start first)
        (tailPartial z (start + first) second) := by
  induction second with
  | zero =>
      rw [Nat.add_zero, tailPartial, QComplex.add_zero_cert]
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega,
        tailPartial, ih, tailPartial]
      have hindex : start + (first + second) = start + first + second := by
        omega
      rw [hindex, QComplex.add_assoc_cert]

theorem expPrefix_add (z : QComplex) (terms extra : Nat) :
    expPrefix z (terms + extra) =
      QComplex.add (expPrefix z terms) (tailPartial z terms extra) := by
  unfold expPrefix
  simpa using tailPartial_add z 0 terms extra

/-- Widening radius that contains every future prefix after a geometric
stage. -/
def stageRadius (C : Rat) (stage : Nat) : Rat :=
  2 * RationalMajorant.factorialTailTerm C
    (RationalMajorant.factorialTailStart C + stage)

/-- Uniform exponential enclosure over an input box at one geometric stage. -/
def uniformBox (input : QBox) (C : Rat) (stage : Nat) : QBox :=
  QBox.expand
    (prefixBox input (RationalMajorant.factorialTailStart C + stage))
    (stageRadius C stage)

/-- Every later exact prefix at every enclosed norm-bounded rational input is
contained in the uniform stage box. -/
theorem uniformBox_contains_future_prefix
    {input : QBox} {z : QComplex} {C : Rat}
    (hC : 0 <= C) (hzlo : input.lo <= z) (hzhi : z <= input.hi)
    (hzNorm : QComplex.normBound z <= C)
    {stage later : Nat} (hstage : stage <= later) :
    (QBox.point (expPrefix z
      (RationalMajorant.factorialTailStart C + later))).NestedIn
        (uniformBox input C stage) := by
  let extra := later - stage
  have hlater :
      RationalMajorant.factorialTailStart C + later =
        (RationalMajorant.factorialTailStart C + stage) + extra := by
    dsimp [extra]
    omega
  have hprefix := expPrefix_add z
    (RationalMajorant.factorialTailStart C + stage) extra
  rw [← hlater] at hprefix
  have hcenter := prefixBox_contains hzlo hzhi
    (RationalMajorant.factorialTailStart C + stage)
  have htail := tailPartial_normBound_le hC hzNorm
    (RationalMajorant.factorialTailStart C + stage) extra
  have hmajorant := RationalMajorant.factorialTailPartial_bound hC
    (RationalMajorant.factorialTailStart_mono C
      (RationalMajorant.factorialTailStart C) stage
      (RationalMajorant.factorialTailStart_satisfies C)) extra
  have herror :
      QComplex.normBound
          (tailPartial z
            (RationalMajorant.factorialTailStart C + stage) extra) <=
        stageRadius C stage :=
    Rat.le_trans htail (by simpa [stageRadius] using hmajorant)
  unfold uniformBox
  rw [hprefix]
  exact point_add_error_nested_expand_box
    hcenter.1 hcenter.2 herror

/-- Paired uniform boxes for the adjacent-prefix exponential first jet. -/
def uniformJetBox (input : QBox) (C : Rat) (stage : Nat) :
    QBox.FirstJetBox where
  value := uniformBox input C (stage + 1)
  derivative := uniformBox input C stage

/-- Both components of the uniform jet box contain the same sufficiently
late exponential prefix, expressing the finite enclosure form of
`exp' = exp`. -/
theorem uniformJetBox_contains_future_selfDerivative
    {input : QBox} {z : QComplex} {C : Rat}
    (hC : 0 <= C) (hzlo : input.lo <= z) (hzhi : z <= input.hi)
    (hzNorm : QComplex.normBound z <= C)
    {stage later : Nat} (hstage : stage + 1 <= later) :
    QBox.FirstJetBox.Contains (uniformJetBox input C stage)
      { value := expPrefix z
          (RationalMajorant.factorialTailStart C + later)
        derivative := expPrefix z
          (RationalMajorant.factorialTailStart C + later) } := by
  have hvalue := uniformBox_contains_future_prefix hC hzlo hzhi hzNorm hstage
  have hderivative := uniformBox_contains_future_prefix hC hzlo hzhi hzNorm
    (Nat.le_trans (Nat.le_succ stage) hstage)
  exact ⟨hvalue.1, hvalue.2, hderivative.1, hderivative.2⟩

/-- The common scheduled term count on the norm ball `normBound z <= C`. -/
def scheduledTerms (C : Rat) (eps : QPos) : Nat :=
  FiniteExponentialTaylor.scheduledTailStart C eps

/-- Every later finite prefix is the scheduled prefix plus a computably
bounded complex error. -/
theorem scheduled_prefix_extension
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (eps : QPos) (extra : Nat) :
    Exists fun error : QComplex =>
      expPrefix z (scheduledTerms C eps + extra) =
          QComplex.add (expPrefix z (scheduledTerms C eps)) error /\
        QComplex.normBound error <= eps.val := by
  refine ⟨tailPartial z (scheduledTerms C eps) extra,
    expPrefix_add z (scheduledTerms C eps) extra, ?_⟩
  exact Rat.le_trans (tailPartial_normBound_le hC hz _ _)
    (by
      simpa [scheduledTerms, FiniteExponentialTaylor.scheduledTailStart] using
        RationalMajorant.factorialTailPartial_shifted_le_eps hC eps extra)

/-- The formal first jet of an exponential prefix.  The value uses one more
term than the derivative, exactly as termwise polynomial differentiation
requires when the exponential coefficient stream shifts to itself. -/
def finiteJet (z : QComplex) (terms : Nat) : HolomorphicJet.FirstJet where
  value := expPrefix z (terms + 1)
  derivative := expPrefix z terms

theorem finiteJet_value_eq_derivative_add_term (z : QComplex) (terms : Nat) :
    (finiteJet z terms).value =
      QComplex.add (finiteJet z terms).derivative (term z terms) := by
  change expPrefix z (terms + 1) =
    QComplex.add (expPrefix z terms) (term z terms)
  rw [expPrefix_add]
  simp only [tailPartial, Nat.add_zero, QComplex.zero_add_cert]

theorem formal_exponential_coefficient_derivative :
    FormalPowerSeries.derivative FormalPowerSeries.expCoeff =
      FormalPowerSeries.expCoeff :=
  FormalPowerSeries.expCoeff_derivative

/-- At the scheduled stage, the finite value/derivative discrepancy is within
the requested norm budget. -/
theorem scheduled_finiteJet_gap_le
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (eps : QPos) :
    QComplex.normBound
      (term z (scheduledTerms C eps)) <= eps.val := by
  have hterm := term_normBound_le hC hz (scheduledTerms C eps)
  have htail := RationalMajorant.factorialTailPartial_shifted_le_eps
    hC eps 1
  simp only [RationalMajorant.factorialTailPartial, Nat.add_zero,
    Rat.zero_add] at htail
  exact Rat.le_trans hterm (by
    simpa [scheduledTerms, FiniteExponentialTaylor.scheduledTailStart] using
      htail)

/-- Precision-indexed exponential first-jet approximant on the norm ball of
radius `C`. -/
def scheduledJet (z : QComplex) (C : Rat) (eps : QPos) :
    HolomorphicJet.FirstJet :=
  finiteJet z (scheduledTerms C eps)

theorem scheduledJet_value_eq_derivative_add_error
    (z : QComplex) (C : Rat) (eps : QPos) :
    (scheduledJet z C eps).value =
      QComplex.add (scheduledJet z C eps).derivative
        (term z (scheduledTerms C eps)) :=
  finiteJet_value_eq_derivative_add_term z (scheduledTerms C eps)

/-- The exact value/derivative relation and the requested error bound packaged
together at one precision. -/
structure ScheduledJetCertificate
    (z : QComplex) (C : Rat) (eps : QPos) : Prop where
  relation :
    (scheduledJet z C eps).value =
      QComplex.add (scheduledJet z C eps).derivative
        (term z (scheduledTerms C eps))
  errorBound :
    QComplex.normBound (term z (scheduledTerms C eps)) <= eps.val

theorem scheduledJet_certificate
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (eps : QPos) :
    ScheduledJetCertificate z C eps where
  relation := scheduledJet_value_eq_derivative_add_error z C eps
  errorBound := scheduled_finiteJet_gap_le hC hz eps

/-! ## A valid raw complex exponential at a rational point -/

theorem point_add_error_nested_expand
    (center error : QComplex) {radius : Rat}
    (herror : QComplex.normBound error <= radius) :
    (QBox.point (QComplex.add center error)).NestedIn
      (QBox.expand (QBox.point center) radius) := by
  have hre := Rat.le_trans (qabs_re_le_normBound error) herror
  have him := Rat.le_trans (qabs_im_le_normBound error) herror
  have hrelo := neg_qabs_le_self error.re
  have hrehi := self_le_qabs error.re
  have himlo := neg_qabs_le_self error.im
  have himhi := self_le_qabs error.im
  unfold QBox.NestedIn QBox.expand QBox.point QComplex.add
  simp only [QComplex.le_def]
  constructor <;> constructor <;>
    grind [Rat.sub_eq_add_neg]

private theorem half_pow_nonneg (n : Nat) :
    0 <= ((1 : Rat) / 2) ^ n :=
  Rat.pow_nonneg (by decide +kernel)

private theorem half_pow_le_one (n : Nat) :
    ((1 : Rat) / 2) ^ n <= 1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [Rat.pow_succ]
      calc
        ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) <=
            1 * ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel)
        _ <= 1 := by decide +kernel

private theorem half_pow_antitone {n m : Nat} (hnm : n <= m) :
    ((1 : Rat) / 2) ^ m <= ((1 : Rat) / 2) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero =>
      rw [Nat.add_zero]
      exact Rat.le_refl
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega, Rat.pow_succ]
      have hstep :
          ((1 : Rat) / 2) ^ (n + k) * ((1 : Rat) / 2) <=
            ((1 : Rat) / 2) ^ (n + k) := by
        calc
          ((1 : Rat) / 2) ^ (n + k) * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ (n + k) * 1 :=
            Rat.mul_le_mul_of_nonneg_left (by decide +kernel)
              (half_pow_nonneg (n + k))
          _ = ((1 : Rat) / 2) ^ (n + k) := Rat.mul_one _
      exact Rat.le_trans hstep ih

/-- Direct point candidates before finite-prefix stabilization. -/
def directCandidate (z : QComplex) (C : Rat) : ComplexCompute where
  compute := fun stage =>
    QBox.point (expPrefix z
      (RationalMajorant.factorialTailStart C + stage))

/-- The nested raw exponential computation obtained by finite intersections
of widened Taylor-prefix point boxes. -/
def exponentialRawAt (z : QComplex) (C : Rat) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (directCandidate z C) (stageRadius C)

private theorem exponentialRawAt_contained_current_expand
    (z : QComplex) (C : Rat) (stage : Nat) :
    ((exponentialRawAt z C).compute stage).NestedIn
      (QBox.expand ((directCandidate z C).compute stage)
        (stageRadius C stage)) := by
  cases stage with
  | zero =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ stage =>
      change (QBox.intersection
        (ComplexCompute.cauchyStabilizeCompute
          (directCandidate z C).compute (stageRadius C) stage)
        (QBox.expand ((directCandidate z C).compute (stage + 1))
          (stageRadius C (stage + 1)))).NestedIn
        (QBox.expand ((directCandidate z C).compute (stage + 1))
          (stageRadius C (stage + 1)))
      exact QBox.intersection_contained_right _ _

private theorem directCandidate_ordered (z : QComplex) (C : Rat) :
    forall stage, ((directCandidate z C).compute stage).Ordered := by
  intro stage
  exact QComplex.le_refl _

private theorem directCandidate_shrinks (z : QComplex) (C : Rat) :
    ComplexCompute.WidthsShrinkToZero (directCandidate z C).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  constructor
  · simpa [directCandidate, QBox.point, QBox.width, Rat.sub_self] using
      (Rat.le_of_lt eps.property)
  · simpa [directCandidate, QBox.point, QBox.height, Rat.sub_self] using
      (Rat.le_of_lt eps.property)

private theorem directCandidate_future
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) :
    forall first later, first <= later ->
      ((directCandidate z C).compute later).NestedIn
        (QBox.expand ((directCandidate z C).compute first)
          (stageRadius C first)) := by
  intro first later hfl
  let extra := later - first
  have hlater :
      RationalMajorant.factorialTailStart C + later =
        (RationalMajorant.factorialTailStart C + first) + extra := by
    dsimp [extra]
    omega
  have hprefix := expPrefix_add z
    (RationalMajorant.factorialTailStart C + first) extra
  rw [← hlater] at hprefix
  have htail := tailPartial_normBound_le hC hz
    (RationalMajorant.factorialTailStart C + first) extra
  have hmajorant := RationalMajorant.factorialTailPartial_bound hC
    (RationalMajorant.factorialTailStart_mono C
      (RationalMajorant.factorialTailStart C) first
      (RationalMajorant.factorialTailStart_satisfies C)) extra
  have herror :
      QComplex.normBound
          (tailPartial z
            (RationalMajorant.factorialTailStart C + first) extra) <=
        stageRadius C first :=
    Rat.le_trans htail (by simpa [stageRadius] using hmajorant)
  change (QBox.point
      (expPrefix z (RationalMajorant.factorialTailStart C + later))).NestedIn
    (QBox.expand
      (QBox.point
        (expPrefix z (RationalMajorant.factorialTailStart C + first)))
      (stageRadius C first))
  rw [hprefix]
  exact point_add_error_nested_expand _ _ herror

/-- The stabilized stage contains its current exact Taylor prefix. -/
theorem exponentialRawAt_contains_prefix
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (stage : Nat) :
    (QBox.point (expPrefix z
      (RationalMajorant.factorialTailStart C + stage))).NestedIn
        ((exponentialRawAt z C).compute stage) := by
  exact ComplexCompute.cauchyStabilize_contains_current
    (directCandidate_future hC hz) stage

private theorem exponentialRawAt_width_height_le_radius
    (z : QComplex) (C : Rat) (stage : Nat) :
    ((exponentialRawAt z C).compute stage).width <=
        2 * stageRadius C stage /\
      ((exponentialRawAt z C).compute stage).height <=
        2 * stageRadius C stage := by
  have hnested := exponentialRawAt_contained_current_expand z C stage
  have hwidthHeight := QBox.width_height_le_of_nested hnested
  rw [QBox.expand_width, QBox.expand_height] at hwidthHeight
  simpa [directCandidate, QBox.point, QBox.width, QBox.height,
    Rat.sub_self, Rat.zero_add] using hwidthHeight

/-- Explicit geometric width bound for the valid stabilized exponential
boxes. -/
theorem exponentialRawAt_width_height_geometric
    {z : QComplex} {C : Rat} (hC : 0 <= C) (stage : Nat) :
    let bound := 4 * RationalMajorant.factorialTailTerm C
      (RationalMajorant.factorialTailStart C)
    ((exponentialRawAt z C).compute stage).width <=
        bound * ((1 : Rat) / 2) ^ stage /\
      ((exponentialRawAt z C).compute stage).height <=
        bound * ((1 : Rat) / 2) ^ stage := by
  dsimp
  have hbox := exponentialRawAt_width_height_le_radius z C stage
  have hterm := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC (RationalMajorant.factorialTailStart_satisfies C) stage
  have hscaled :
      2 * stageRadius C stage <=
        4 * RationalMajorant.factorialTailTerm C
          (RationalMajorant.factorialTailStart C) *
            ((1 : Rat) / 2) ^ stage := by
    unfold stageRadius
    calc
      2 * (2 * RationalMajorant.factorialTailTerm C
          (RationalMajorant.factorialTailStart C + stage)) <=
          2 * (2 * (RationalMajorant.factorialTailTerm C
            (RationalMajorant.factorialTailStart C) *
              ((1 : Rat) / 2) ^ stage)) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left hterm
            (by decide +kernel : (0 : Rat) <= 2))
          (by decide +kernel : (0 : Rat) <= 2)
      _ = 4 * RationalMajorant.factorialTailTerm C
          (RationalMajorant.factorialTailStart C) *
            ((1 : Rat) / 2) ^ stage := by
        grind [Rat.mul_assoc]
  exact ⟨Rat.le_trans hbox.1 hscaled, Rat.le_trans hbox.2 hscaled⟩

theorem stageRadius_shrinks {C : Rat} (hC : 0 <= C) :
    ShrinksToZero (stageRadius C) := by
  intro eps
  let bound : Rat :=
    2 * RationalMajorant.factorialTailTerm C
      (RationalMajorant.factorialTailStart C)
  have hbound : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by decide +kernel)
      (RationalMajorant.factorialTailTerm_nonneg hC _)
  let start := RationalMajorant.halfDecayShift bound eps
  refine ⟨start, ?_⟩
  intro stage hstage
  have hterm := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC (RationalMajorant.factorialTailStart_satisfies C) stage
  have hradius :
      stageRadius C stage <= bound * ((1 : Rat) / 2) ^ stage := by
    dsimp [stageRadius, bound]
    calc
      2 * RationalMajorant.factorialTailTerm C
          (RationalMajorant.factorialTailStart C + stage) <=
          2 * (RationalMajorant.factorialTailTerm C
            (RationalMajorant.factorialTailStart C) *
              ((1 : Rat) / 2) ^ stage) :=
        Rat.mul_le_mul_of_nonneg_left hterm
          (by decide +kernel : (0 : Rat) <= 2)
      _ = 2 * RationalMajorant.factorialTailTerm C
          (RationalMajorant.factorialTailStart C) *
            ((1 : Rat) / 2) ^ stage := by
        grind [Rat.mul_assoc]
  have hmono := half_pow_antitone hstage
  calc
    stageRadius C stage <= bound * ((1 : Rat) / 2) ^ stage := hradius
    _ <= bound * ((1 : Rat) / 2) ^ start :=
      Rat.mul_le_mul_of_nonneg_left hmono hbound
    _ <= eps.val := RationalMajorant.halfDecayShift_spec hbound eps

/-- The stabilized exponential Taylor computation is a valid raw complex
number for every supplied rational norm bound on its input. -/
theorem exponentialRawAt_valid
    {z : QComplex} {C : Rat} (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) :
    (exponentialRawAt z C).Valid := by
  apply ComplexCompute.cauchyStabilize_valid
  · exact directCandidate_ordered z C
  · exact directCandidate_shrinks z C
  · exact directCandidate_future hC hz
  · exact stageRadius_shrinks hC

end ComplexExponentialApproximation

end ComputableAnalysis


