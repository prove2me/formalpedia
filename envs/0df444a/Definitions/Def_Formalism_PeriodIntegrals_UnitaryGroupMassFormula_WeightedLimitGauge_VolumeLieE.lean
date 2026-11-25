-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:33.501821+00:00
-- url     : https://prove2.me/theorems/1cc57331-5098-4d63-a687-a3e05509b395
-- title:
--   Volume Lie E
-- statement:
--   Definitions and structural lemmas for Volume Lie E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/VolumeLieE.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def tBall (k r : ℕ) (m : Mat k r) (ρ : ℝ) : Set (Mt k r) :=
  {x | (fun i j => (m⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}
def MBaseMem : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → mBase k r z z' μsec ∈ UWb k r
def TBallMeas : Prop :=
  ∀ (k r : ℕ) (m : Mat k r) (ρ : ℝ), MeasurableSet (tBall k r m ρ)
def GaugeExists : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νg : Measure (Mt k r), IsHaarOn (UWb k r) νg ∧
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → 0 < νg (bBall k r ρ) ∧ νg (bBall k r ρ) < ⊤) ∧
    ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)
def RhsHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∃ ν : Measure (Mt k r), IsHaarOn (UWb k r) ν ∧
      (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (bBall k r ρ) < ⊤) ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → rhsW k r z z' μW μW' μsec φ = ∫⁻ x, φ x ∂ν
def HaarUniq : Prop :=
  ∀ (k r : ℕ) (ν₁ ν₂ : Measure (Mt k r)), 1 ≤ k → IsHaarOn (UWb k r) ν₁ → IsHaarOn (UWb k r) ν₂ →
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
      ν₁ (bBall k r ρ) < ⊤ ∧ 0 < ν₂ (bBall k r ρ) ∧ ν₂ (bBall k r ρ) < ⊤) →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ν₁ = c • ν₂
def ConstVal : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ (νg : Measure (Mt k r)) (c : ℝ≥0∞),
      IsHaarOn (UWb k r) νg →
      (∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) →
      (∀ φ : Mt k r → ℝ≥0∞, Measurable φ → rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg) →
      c.toReal = (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹
def sVol (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE S) ρ)).toReal
def IsGaugeOn (k r : ℕ) (S : Set (Mat k r)) (ν : Measure (Mt k r)) : Prop :=
  IsHaarOn S ν ∧ Tendsto (fun ρ : ℝ => (ν (expBall (k := k) (r := r) S ρ)).toReal / sVol k r S ρ) (𝓝[>] 0) (𝓝 1)
def wLast (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))
def ConstValStd : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r ((Real.sqrt T : ℂ) • wLast k r) ((Real.sqrt T' : ℂ) • wLast k r) μW μW' a a' μsec →
    ∀ (νg : Measure (Mt k r)) (c : ℝ≥0∞), IsHaarOn (UWb k r) νg →
      (∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) →
      (∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
        rhsW k r ((Real.sqrt T : ℂ) • wLast k r) ((Real.sqrt T' : ℂ) • wLast k r) μW μW' μsec φ =
          c * ∫⁻ x, φ x ∂νg) →
      c.toReal = (wbConst k T T' a a')⁻¹
def GaugeVolUk : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), IsGaugeOn k r (UWset k r (wLast k r)) ν →
    ν Set.univ = ENNReal.ofReal (volU k)
def hypMeas (k : ℕ) (T' : ℝ) (f : (Fin k → ℂ) × ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∫⁻ y : EuclideanSpace ℂ (Fin k), ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
    f (fun i => y i, (Real.sqrt (‖y‖ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I))
def OrbitPush : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / T' ^ k) * hypMeas k T' f
def PolarHyp : Prop :=
  ∀ (k : ℕ) (T T' : ℝ), 1 ≤ k → 0 < T → 0 < T' → ∀ g : ℝ → ℂ → ℝ≥0∞, Measurable (Function.uncurry g) →
    hypMeas k T' (fun v => g ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * T ^ k)) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) *
          g (Real.sqrt ((Complex.normSq ζ - T * T') / T)) (-(ζ / (Real.sqrt T : ℂ)))
def VolURatio : Prop :=
  ∀ k : ℕ, 1 ≤ k → volU k = volU (k - 1) * (2 * Real.pi) ^ k / ((k - 1).factorial : ℝ)
def ChartLim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (X : Type) [MeasurableSpace X] (Φ : E → X) (ν : Measure X) (δ : E → ℝ≥0∞),
    ContinuousAt δ 0 → δ 0 ≠ ⊤ →
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x) →
    Tendsto (fun ρ : ℝ => (ν (Φ '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (δ 0).toReal)
def ChartJac : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (Φ : E → E) (ν : Measure E) (δ : E → ℝ≥0∞),
    ContDiffAt ℝ 1 Φ 0 → (fderiv ℝ Φ 0).det ≠ 0 → ContinuousAt δ (Φ 0) → δ (Φ 0) ≠ ⊤ →
    (∃ U ∈ 𝓝 (Φ 0), ∀ A ⊆ U, MeasurableSet A → ν A = ∫⁻ x in A, δ x) →
    Tendsto (fun ρ : ℝ => (ν (Φ '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 ((δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det|))
end PI.RhsWLim.W


