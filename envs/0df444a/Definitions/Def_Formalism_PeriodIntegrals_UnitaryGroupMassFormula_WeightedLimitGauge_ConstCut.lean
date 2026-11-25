-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:42.5598+00:00
-- url     : https://prove2.me/theorems/d11376eb-7957-4051-8518-4c2b1db3a5f8
-- title:
--   Const Cut
-- statement:
--   Definitions and structural lemmas for Const Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/ConstCut.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
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
def pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ :=
  herm (Hpk k r) (Matrix.of x *ᵥ z') z
def pairConst (k : ℕ) (T T' : ℝ) : ℝ := 2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1))
def RhsTest : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ g : ℂ → ℝ≥0∞, Measurable g →
      rhsW k r z z' μW μW' μsec (fun x => g (pairF k r z z' x)) =
        ENNReal.ofReal (a * a') * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ
def PairPush : Prop :=
  ∀ (k r : ℕ) (νg : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) νg →
    ∀ z z' : Fin (2 * r + k + 1) → ℂ, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (pairF k r z z' x) ∂νg = ENNReal.ofReal (pairConst k (Tz k r z) (Tz k r z')) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ
def rmulM {k r : ℕ} (p : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * p
def TransW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ p ∈ UWb k r, p *ᵥ ((Real.sqrt (Tz k r z) : ℂ) • wLast k r) = z
def UnimodW : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ p ∈ UWb k r, ν.map (rmulM p) = ν
def OrbitPushG : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / Tz k r z' ^ k) * hypMeas k (Tz k r z') f
def annU (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < 4 * (T * T')}
end PI.RhsWLim.W


