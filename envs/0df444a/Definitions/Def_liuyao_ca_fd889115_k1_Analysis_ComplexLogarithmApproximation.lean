-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexLogarithmApproximation
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexLogarithmApproximation
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:59:38.383465+00:00
-- url     : https://prove2.me/theorems/038cbf38-36b1-4488-bc5f-32ca153015cc
-- title:
--   Computable analysis · ComplexLogarithmApproximation · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexLogarithmApproximation.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalCalculus

set_option autoImplicit true

/-!
# A computable local complex logarithm

This module constructs the branch

`log(1 + w) = w - w^2/2 + w^3/3 - ...`

on the closed rational `ℓ¹`-ball `normBound w <= 1/2`.  Runtime evaluation
uses only finite rational-complex Taylor prefixes and finite intersections of
explicitly widened boxes.  The validity proof uses the geometric majorant
obtained by discarding both the alternating signs and the divisors `n + 1`.

This is the first analytic evaluator needed by the boundary-value layer.  It
does not appeal to a completed complex field, a Lebesgue integral, or a
noncomputable choice of logarithm branch.
-/

namespace ComputableAnalysis
namespace ComplexLogarithmApproximation

private def half : Rat := (1 : Rat) / 2

/-- The `n`th term of the Taylor series for `log(1+w)`, indexed from zero. -/
def term (w : QComplex) (n : Nat) : QComplex :=
  QComplex.scaleRat (FormalPowerSeries.altSign n)
    (QComplex.divRat (QComplex.pow w (n + 1)) (((n + 1 : Nat) : Rat)))

/-- A finite block of logarithm terms beginning at `start`. -/
def tailPartial (w : QComplex) (start : Nat) : Nat -> QComplex
  | 0 => QComplex.zero
  | terms + 1 =>
      QComplex.add (tailPartial w start terms) (term w (start + terms))

/-- The first `terms` Taylor terms for `log(1+w)`. -/
def logPrefix (w : QComplex) (terms : Nat) : QComplex :=
  tailPartial w 0 terms

theorem tailPartial_add (w : QComplex) (start first later : Nat) :
    tailPartial w start (first + later) =
      QComplex.add (tailPartial w start first)
        (tailPartial w (start + first) later) := by
  induction later with
  | zero =>
      rw [Nat.add_zero]
      exact (QComplex.add_zero_cert _).symm
  | succ later ih =>
      rw [Nat.add_succ, tailPartial, ih, tailPartial]
      rw [show start + (first + later) = (start + first) + later by omega]
      exact QComplex.add_assoc_cert _ _ _

theorem logPrefix_add (w : QComplex) (first later : Nat) :
    logPrefix w (first + later) =
      QComplex.add (logPrefix w first) (tailPartial w first later) := by
  simpa [logPrefix, Nat.zero_add] using tailPartial_add w 0 first later

private theorem altSign_abs (n : Nat) :
    qabs (FormalPowerSeries.altSign n) = 1 := by
  unfold FormalPowerSeries.altSign
  split <;> decide +kernel

private theorem denominator_pos (n : Nat) :
    0 < (((n + 1 : Nat) : Rat)) :=
  Rat.natCast_pos.mpr (by omega)

private theorem denominator_inv_le_one (n : Nat) :
    (((n + 1 : Nat) : Rat))⁻¹ <= 1 := by
  have hone : (1 : Rat) <= (((n + 1 : Nat) : Rat)) := by
    exact_mod_cast (show 1 <= n + 1 by omega)
  have h := Rat.inv_antitone_of_pos (a := (1 : Rat))
    (b := (((n + 1 : Nat) : Rat))) (by decide +kernel) hone
  have hinvOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
  rw [hinvOne] at h
  exact h

/-- Each logarithm term is bounded by the corresponding geometric term on
the half-ball. -/
theorem term_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (n : Nat) :
    QComplex.normBound (term w n) <= half ^ (n + 1) := by
  have hhalf : 0 <= half := by decide +kernel
  have hpow := QComplex.normBound_pow_le hhalf hw (n + 1)
  have hpowNonneg : 0 <= QComplex.normBound (QComplex.pow w (n + 1)) :=
    QComplex.normBound_nonneg _
  unfold term
  rw [QComplex.normBound_scaleRat, altSign_abs, Rat.one_mul,
    QComplex.normBound_divRat_eq _ (denominator_pos n)]
  calc
    QComplex.normBound (QComplex.pow w (n + 1)) *
        (((n + 1 : Nat) : Rat))⁻¹ <=
      half ^ (n + 1) * (((n + 1 : Nat) : Rat))⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hpow
          (Rat.le_of_lt ((Rat.inv_pos).2 (denominator_pos n)))
    _ <= half ^ (n + 1) * 1 :=
      Rat.mul_le_mul_of_nonneg_left (denominator_inv_le_one n)
        (Rat.pow_nonneg hhalf)
    _ = half ^ (n + 1) := Rat.mul_one _

/-- The norm of a finite logarithm tail is bounded by its finite geometric
majorant. -/
theorem tailPartial_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (start terms : Nat) :
    QComplex.normBound (tailPartial w start terms) <=
      RationalMajorant.geomTailPartial 1 half (start + 1) terms := by
  induction terms with
  | zero =>
      change QComplex.normBound QComplex.zero <= 0
      rw [QComplex.normBound_zero]
      exact Rat.le_refl
  | succ terms ih =>
      rw [tailPartial, RationalMajorant.geomTailPartial]
      calc
        QComplex.normBound
            (QComplex.add (tailPartial w start terms)
              (term w (start + terms))) <=
          QComplex.normBound (tailPartial w start terms) +
            QComplex.normBound (term w (start + terms)) :=
              QComplex.normBound_add_le _ _
        _ <= RationalMajorant.geomTailPartial 1 half (start + 1) terms +
            half ^ (start + terms + 1) :=
          rat_add_le_add ih (term_normBound_le hw (start + terms))
        _ = RationalMajorant.geomTailPartial 1 half (start + 1) terms +
            1 * half ^ ((start + 1) + terms) := by
          have hexponent : start + terms + 1 = (start + 1) + terms := by
            omega
          rw [Rat.one_mul, hexponent]

/-- The uniform tail radius after `stage` computed terms. -/
def stageRadius (stage : Nat) : Rat :=
  RationalMajorant.geomTailBound 1 half (stage + 1)

theorem tailPartial_normBound_le_stageRadius {w : QComplex}
    (hw : QComplex.normBound w <= half) (start terms : Nat) :
    QComplex.normBound (tailPartial w start terms) <= stageRadius start := by
  exact Rat.le_trans (tailPartial_normBound_le hw start terms)
    (RationalMajorant.geometric_tail_partial_bound
      (by decide +kernel : (0 : Rat) <= 1)
      (by decide +kernel : (0 : Rat) <= half)
      (by exact Rat.le_refl) )

theorem stageRadius_eq_half_pow (stage : Nat) :
    stageRadius stage = half ^ stage := by
  unfold stageRadius RationalMajorant.geomTailBound
  rw [Rat.pow_succ]
  unfold half
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem half_pow_antitone {first later : Nat}
    (h : first <= later) : half ^ later <= half ^ first := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact Rat.le_refl
  | succ extra ih =>
      rw [show first + (extra + 1) = (first + extra) + 1 by omega,
        Rat.pow_succ]
      have hnonneg : 0 <= half ^ (first + extra) :=
        Rat.pow_nonneg (by decide +kernel)
      have hstep : half ^ (first + extra) * half <=
          half ^ (first + extra) := by
        calc
          half ^ (first + extra) * half <=
              half ^ (first + extra) * 1 :=
            Rat.mul_le_mul_of_nonneg_left (by decide +kernel) hnonneg
          _ = half ^ (first + extra) := Rat.mul_one _
      exact Rat.le_trans hstep ih

theorem stageRadius_shrinks : ShrinksToZero stageRadius := by
  intro eps
  let start := RationalMajorant.halfDecayShift 1 eps
  refine ⟨start, ?_⟩
  intro stage hstage
  rw [stageRadius_eq_half_pow]
  calc
    half ^ stage <= half ^ start := half_pow_antitone hstage
    _ = 1 * ((1 : Rat) / 2) ^ start := by
      unfold half
      rw [Rat.one_mul]
    _ <= eps.val :=
      RationalMajorant.halfDecayShift_spec (by decide +kernel) eps

/-! ## Formal derivative data -/

/-- Coefficients of the local logarithm, including its zero constant term. -/
def logOnePlusCoefficients : FormalPowerSeries.Coeffs
  | 0 => 0
  | n + 1 =>
      FormalPowerSeries.altSign n / (((n + 1 : Nat) : Rat))

/-- Coefficients of the geometric series for `1/(1+w)`. -/
def reciprocalOnePlusCoefficients : FormalPowerSeries.Coeffs :=
  FormalPowerSeries.altSign

/-- The finite coefficient calculation behind
`D log(1+w) = 1/(1+w)`.  Analytic differentiation of the represented
evaluator will refine this algebraic statement with a secant remainder. -/
theorem coefficientShift_logOnePlusCoefficients :
    FormalPowerSeries.coefficientShift logOnePlusCoefficients =
      reciprocalOnePlusCoefficients := by
  funext n
  unfold FormalPowerSeries.coefficientShift reciprocalOnePlusCoefficients
  simp only [logOnePlusCoefficients]
  rw [Rat.div_def]
  have hne : (((n + 1 : Nat) : Rat)) ≠ 0 :=
    Rat.ne_of_gt (denominator_pos n)
  calc
    (((n + 1 : Nat) : Rat)) *
        (FormalPowerSeries.altSign n * (((n + 1 : Nat) : Rat))⁻¹) =
      FormalPowerSeries.altSign n *
        ((((n + 1 : Nat) : Rat)) * (((n + 1 : Nat) : Rat))⁻¹) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = FormalPowerSeries.altSign n := by
      rw [Rat.mul_inv_cancel _ hne, Rat.mul_one]

/-- Direct exact Taylor-prefix candidates. -/
def directCandidate (w : QComplex) : ComplexCompute where
  compute := fun stage => QBox.point (logPrefix w stage)

/-- The executable local logarithm value, stabilized into nested boxes. -/
def logOnePlusRawAt (w : QComplex) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (directCandidate w) stageRadius

private theorem logOnePlusRawAt_contained_current_expand
    (w : QComplex) (stage : Nat) :
    ((logOnePlusRawAt w).compute stage).NestedIn
      (QBox.expand ((directCandidate w).compute stage)
        (stageRadius stage)) := by
  cases stage with
  | zero =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ stage =>
      change (QBox.intersection
        (ComplexCompute.cauchyStabilizeCompute
          (directCandidate w).compute stageRadius stage)
        (QBox.expand ((directCandidate w).compute (stage + 1))
          (stageRadius (stage + 1)))).NestedIn
        (QBox.expand ((directCandidate w).compute (stage + 1))
          (stageRadius (stage + 1)))
      exact QBox.intersection_contained_right _ _

/-- Both coordinate widths have the explicit half-geometric bound used by
the local logarithm runtime. -/
theorem logOnePlusRawAt_width_height_geometric
    (w : QComplex) (stage : Nat) :
    ((logOnePlusRawAt w).compute stage).width <=
        2 * half ^ stage /\
      ((logOnePlusRawAt w).compute stage).height <=
        2 * half ^ stage := by
  have hnested := logOnePlusRawAt_contained_current_expand w stage
  have hwidthHeight := QBox.width_height_le_of_nested hnested
  rw [QBox.expand_width, QBox.expand_height,
    stageRadius_eq_half_pow] at hwidthHeight
  simpa [directCandidate, QBox.point, QBox.width, QBox.height,
    Rat.sub_self, Rat.zero_add] using hwidthHeight

/-- Machine-readable convergence-rate metadata for the local logarithm. -/
def logOnePlusRate (w : QComplex) :
    ComplexCompute.Rate (logOnePlusRawAt w).compute :=
  .geometric 0 2 half
    (by decide +kernel)
    (by decide +kernel)
    (fun stage _ => logOnePlusRawAt_width_height_geometric w stage)

private theorem directCandidate_ordered (w : QComplex) :
    forall stage, ((directCandidate w).compute stage).Ordered := by
  intro stage
  exact QComplex.le_refl _

private theorem directCandidate_shrinks (w : QComplex) :
    ComplexCompute.WidthsShrinkToZero (directCandidate w).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  constructor <;>
    simpa [directCandidate, QBox.point, QBox.width, QBox.height,
      Rat.sub_self] using Rat.le_of_lt eps.property

private theorem directCandidate_future {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    forall first later, first <= later ->
      ((directCandidate w).compute later).NestedIn
        (QBox.expand ((directCandidate w).compute first)
          (stageRadius first)) := by
  intro first later hfl
  let extra := later - first
  have hlater : later = first + extra := by
    dsimp [extra]
    omega
  have hprefix := logPrefix_add w first extra
  rw [← hlater] at hprefix
  change (QBox.point (logPrefix w later)).NestedIn
    (QBox.expand (QBox.point (logPrefix w first)) (stageRadius first))
  rw [hprefix]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _
    (tailPartial_normBound_le_stageRadius hw first extra)

/-- The stabilized computation contains its current exact Taylor prefix. -/
theorem logOnePlusRawAt_contains_prefix {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    (QBox.point (logPrefix w stage)).NestedIn
      ((logOnePlusRawAt w).compute stage) := by
  exact ComplexCompute.cauchyStabilize_contains_current
    (directCandidate_future hw) stage

/-- The local logarithm evaluator is a valid represented complex number on
the closed half-ball. -/
theorem logOnePlusRawAt_valid {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (logOnePlusRawAt w).Valid := by
  apply ComplexCompute.cauchyStabilize_valid
  · exact directCandidate_ordered w
  · exact directCandidate_shrinks w
  · exact directCandidate_future hw
  · exact stageRadius_shrinks

/-- A concrete partial evaluator for the local branch `w ↦ log(1+w)`. -/
def logOnePlus : FunctionRaw where
  domain := fun w => QComplex.normBound w <= half
  compute := fun w _ => (logOnePlusRawAt w).compute

theorem logOnePlus_valid (w : QComplex) (hw : logOnePlus.domain w) :
    ComplexCompute.ValidCompute (logOnePlus.compute w hw) :=
  logOnePlusRawAt_valid hw

/-- The corresponding branch around the rational-complex point `1`. -/
def localLog : FunctionRaw where
  domain := fun z =>
    QComplex.normBound (QComplex.sub z QComplex.one) <= half
  compute := fun z _ =>
    (logOnePlusRawAt (QComplex.sub z QComplex.one)).compute

theorem localLog_valid (z : QComplex) (hz : localLog.domain z) :
    ComplexCompute.ValidCompute (localLog.compute z hz) :=
  logOnePlusRawAt_valid hz

end ComplexLogarithmApproximation
end ComputableAnalysis


