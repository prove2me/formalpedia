-- Prove2me | Definitions.Def_NSBlowupCertificate
-- name    : NSBlowupCertificate
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T18:49:04.818271+00:00
-- url     : https://prove2.me/theorems/67541052-acb5-478f-abe5-4f40541621af
-- title:
--   Navier–Stokes blow-up: certificate data and conditions (Certificate layer)
-- statement:
--   The certificate layer of Alpöge–Buckmaster Section 7 / Appendix B: symmetry pairs, matrix and period norms, perturbations and right-hand sides, profile fields, the frozen and stationary quadratic forms, the defect field, and the structure `CertificateData` with the predicate `IsCertificate` (coercive estimate, frozen-form lower bound, defect bounds, smallness, slope/inclusion and nontriviality conditions). `CertificateHypothesis` asserts that some certificate exists. Transcribed verbatim from `lean/CertificateChallenge.lean` (definitions only).
-- source:
--   Alpöge–Buckmaster, Finite-time blow-up for the Navier–Stokes equations (20 Nov 2026), https://github.com/tristanbuckmaster/navier-stokes, lean/CertificateChallenge.lean (definitions).

import Mathlib
import Definitions.Def_NSBlowupChallenge

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

abbrev Symmetry := (Space ≃ₗᵢ[ℝ] Space) × ℝ

def matSq (G : Space →L[ℝ] Space) : ℝ := ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2

def matInner (G K : Space →L[ℝ] Space) : ℝ :=
  ∑ i : Fin 3, inner ℝ (G (unitVector i)) (K (unitVector i))

def secondDerivTrace (H : Space →L[ℝ] Space →L[ℝ] Space) : Space :=
  ∑ j : Fin 3, H (unitVector j) (unitVector j)

def periodLIntegral (f : ℝ → Space → ℝ) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y)

def periodBallLIntegral (r : ℝ) (f : ℝ → Space → ℝ) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (f σ y)

def periodNorm (F : ℝ → Space → Space) : ℝ :=
  Real.sqrt (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal

def periodBallNorm (r : ℝ) (F : ℝ → Space → Space) : ℝ :=
  Real.sqrt (periodBallLIntegral r (fun σ y => ‖F σ y‖ ^ 2)).toReal

def vecNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

def IsTimePeriodic {β : Type*} (f : ℝ → Space → β) : Prop := ∀ σ y, f (σ + 1) y = f σ y

def IsSpaceTimeTestVector (φ : ℝ → Space → Space) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2) ∧
    HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)

structure IsPerturbation (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) : Prop where
  measurable_velocity : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume
  measurable_gradient : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume
  measurable_secondDeriv : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume
  measurable_derivative : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume
  periodic_velocity : IsTimePeriodic v
  periodic_gradient : IsTimePeriodic G
  periodic_secondDeriv : IsTimePeriodic H
  periodic_derivative : IsTimePeriodic g
  weak_gradient : ∀ᵐ σ, IsWeakGradient (v σ) (G σ)
  weak_secondDeriv : ∀ᵐ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => G σ y (unitVector j)) (fun y => (H σ y).flip (unitVector j))
  divergence_free : ∀ᵐ σ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0
  sixth_power : ∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤
  gradient_finite : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤
  sumSecondPartials_finite : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) < ⊤
  derivative_finite : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) < ⊤
  transport : ∀ φ, IsSpaceTimeTestVector φ →
    ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2) = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2)
  invariant : ∀ γ ∈ Γ, ∀ᵐ z : ℝ × Space, v (z.1 + γ.2) (γ.1 z.2) = γ.1 (v z.1 z.2)

def IsRightSide {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (g F : ℝ → Space → Space) :
    Prop :=
  ∀ φ, IsSpaceTimeTestField φ →
    ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2))

def weightedEnergy (w : Space → ℝ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y))).toReal

def pinValue (χ G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (χ σ y)

structure IsProfileField (Γ : Set Symmetry) (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  weak_gradient : IsWeakGradient w G
  weak_secondDeriv : ∀ j : Fin 3,
    IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j))
  divergence_free : ∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0
  sixth_power : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤
  gradient_finite : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤
  sumSecondPartials_finite : ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2) < ⊤
  invariant : ∀ γ ∈ Γ, γ.2 = 0 → ∀ᵐ y, w (γ.1 y) = γ.1 (w y)

def frozenForm (W : Space → Space) (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) + (1 / 4 : ℝ) * (∫ y, matSq (G y))
    + ∫ y, inner ℝ (G y (W y) + fderiv ℝ W y (w y)) (-secondDerivTrace (H y))

def stationaryEnergy (w : Space → ℝ) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) + ∫ y, w y * matSq (G y)

def defectField {k : ℕ} (P : ℝ) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (b : Fin k → ℝ → Space → Space) (lam : Fin k → ℝ) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => W s y) σ + (1 / 2 : ℝ) • W σ y + (1 / 2 : ℝ) • fderiv ℝ (W σ) y y
    - sumSecondPartialsAt (W σ) y + advectionAt (W σ) y + ∑ i, lam i • b i σ y + gradientAt (q σ) y

def supBoundFactor (w₀ : ℝ) : ℝ := 1 / Real.sqrt (2 * Real.pi * (2 * Real.sqrt w₀))

structure CertificateData (k : ℕ) where
  symmetries : Set Symmetry
  center : Fin k → ℝ
  radius : Fin k → ℝ
  period : (Fin k → ℝ) → ℝ
  profile : (Fin k → ℝ) → ℝ → Space → Space
  pressure : (Fin k → ℝ) → ℝ → Space → ℝ
  multiplier : (Fin k → ℝ) → Fin k → ℝ
  target : (Fin k → ℝ) → Fin k → ℝ
  actuator : Fin k → ℝ → Space → Space
  pin : Fin k → ℝ → Space → (Space →L[ℝ] Space)
  slope : Matrix (Fin k) (Fin k) ℝ
  slopeInverse : Matrix (Fin k) (Fin k) ℝ
  slopeOffset : Fin k → ℝ
  defectBound : (Fin k → ℝ) → ℝ
  defectBallBound : (Fin k → ℝ) → ℝ
  weight : ℝ
  weightFn : Space → ℝ
  weightMax : ℝ
  coerciveL2 : ℝ
  coerciveBall : ℝ
  coercivePin : ℝ
  coerciveTotal : ℝ
  ballRadius : ℝ
  decay : ℝ
  periodMax : ℝ
  twist : ℕ
  actuatorBound : ℝ
  formBound : ℝ
  defectMax : ℝ
  sizeBound : ℝ
  supBound : ℝ

def CertificateData.box {k : ℕ} (d : CertificateData k) : Set (Fin k → ℝ) :=
  Set.Icc (d.center - d.radius) (d.center + d.radius)

structure IsCertificate {k : ℕ} (d : CertificateData k) : Prop where
  radius_nonneg : ∀ i, 0 ≤ d.radius i
  weight_pos : 0 < d.weight
  weightFn_measurable : Measurable d.weightFn
  weightFn_lower : ∀ y, d.weight ≤ d.weightFn y
  weightFn_upper : ∀ y, d.weightFn y ≤ d.weightMax
  weightFn_invariant : ∀ γ ∈ d.symmetries, ∀ y, d.weightFn (γ.1 y) = d.weightFn y
  coerciveL2_nonneg : 0 ≤ d.coerciveL2
  coerciveBall_nonneg : 0 ≤ d.coerciveBall
  coercivePin_nonneg : 0 ≤ d.coercivePin
  coerciveTotal_ge : d.coerciveL2 + d.coerciveBall ≤ d.coerciveTotal
  coerciveTotal_pos : 0 < d.coerciveTotal
  actuatorBound_nonneg : 0 ≤ d.actuatorBound
  formBound_nonneg : 0 ≤ d.formBound
  sizeBound_nonneg : 0 ≤ d.sizeBound
  supBound_pos : 0 < d.supBound
  period_continuous : ContinuousOn d.period d.box
  period_pos : ∀ p ∈ d.box, 0 < d.period p
  period_le : ∀ p ∈ d.box, d.period p ≤ d.periodMax
  twist_pos : 0 < d.twist
  twist_mem : d.twist = 1 ∨ (d.twist = 2 ∧ ∃ Q, (Q, (1 / 2 : ℝ)) ∈ d.symmetries)
  multiplier_continuous : ContinuousOn d.multiplier d.box
  target_continuous : ContinuousOn d.target d.box
  profile_smooth : ContDiff ℝ 2 (fun q : (Fin k → ℝ) × ℝ × Space => d.profile q.1 q.2.1 q.2.2)
  profile_periodic : ∀ p, IsTimePeriodic (d.profile p)
  profile_divergence : ∀ p ∈ d.box, ∀ σ y, divergenceAt (d.profile p σ) y = 0
  profile_decay : ∀ p ∈ d.box, ∀ σ y, ∀ j ≤ 2,
    ‖iteratedFDeriv ℝ j (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ (j + 1)
  profile_invariant : ∀ p ∈ d.box, ∀ γ ∈ d.symmetries, ∀ σ y,
    d.profile p (σ + γ.2) (γ.1 y) = γ.1 (d.profile p σ y)
  pressure_smooth : ∀ p ∈ d.box, ContDiff ℝ 1 (fun z : ℝ × Space => d.pressure p z.1 z.2)
  pressure_periodic : ∀ p ∈ d.box, IsTimePeriodic (d.pressure p)
  actuator_measurable : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume
  actuator_periodic : ∀ i, IsTimePeriodic (d.actuator i)
  actuator_invariant : ∀ i, ∀ γ ∈ d.symmetries, ∀ᵐ z : ℝ × Space,
    d.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (d.actuator i z.1 z.2)
  actuator_norm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
    ENNReal.ofReal (d.actuatorBound ^ 2)
  pin_measurable : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.pin i z.1 z.2) volume
  pin_finite : ∀ i, periodLIntegral (fun σ y => matSq (d.pin i σ y)) < ⊤
  coercive : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.profile p) d.actuator κ v G g F →
      Real.sqrt (weightedEnergy d.weightFn G H + ∑ i, κ i ^ 2) ≤
        d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F
          + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)
  frozen_form : ∀ p ∈ d.box, ∀ σ w G H, IsProfileField d.symmetries w G H →
    -d.formBound * stationaryEnergy d.weightFn G H ≤ frozenForm (d.profile p σ) w G H
  defect_nonneg : ∀ p ∈ d.box, 0 ≤ d.defectBound p ∧ 0 ≤ d.defectBallBound p
  defect_l2 : ∀ p ∈ d.box,
    periodLIntegral (fun σ y => ‖defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
      (d.multiplier p) σ y‖ ^ 2) ≤ ENNReal.ofReal (d.defectBound p ^ 2)
  defect_ball : ∀ p ∈ d.box,
    periodBallLIntegral d.ballRadius (fun σ y => ‖defectField (d.period p) (d.profile p)
      (d.pressure p) d.actuator (d.multiplier p) σ y‖ ^ 2) ≤ ENNReal.ofReal (d.defectBallBound p ^ 2)
  defect_le : ∀ p ∈ d.box, d.defectBound p ≤ d.defectMax
  size : ∀ p ∈ d.box, d.coerciveL2 * d.defectBound p + d.coerciveBall * d.defectBallBound p
    + d.coercivePin * vecNorm (fun i => d.target p i
      - pinValue (d.pin i) (fun σ y => fderiv ℝ (d.profile p σ) y)) ≤ d.sizeBound
  small_first : 2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound < 1
  small_second : 4 * d.sizeBound ^ 2 * ((1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
      + 2 * (d.periodMax / d.twist) * d.actuatorBound + 2 * (d.periodMax / d.twist) / d.coerciveTotal) ≤
    d.supBound ^ 2
  small_third : 4 * (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound) * d.sizeBound ^ 2
    + 4 * (d.periodMax / d.twist) * d.sizeBound * (d.defectMax + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound
      + 2 * d.actuatorBound * d.sizeBound) ≤ d.supBound ^ 2
  slope_inverse : d.slopeInverse * d.slope = 1
  slope_offset : ∀ p ∈ d.box, ∀ j,
    |d.multiplier p j - (d.slope.mulVec (p - d.center)) j| ≤ d.slopeOffset j
  inclusion : ∀ i, ∑ j, |d.slopeInverse i j| * (2 * d.sizeBound + d.slopeOffset j) ≤ d.radius i
  nontrivial : ∀ p ∈ d.box, 4 * d.sizeBound ^ 2 / d.weight <
    (periodLIntegral (fun σ y => matSq (fderiv ℝ (d.profile p σ) y))).toReal

def CertificateHypothesis : Prop := ∃ (k : ℕ) (d : CertificateData k), IsCertificate d

end Breakdown


