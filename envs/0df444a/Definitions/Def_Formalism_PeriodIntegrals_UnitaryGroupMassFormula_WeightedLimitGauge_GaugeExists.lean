-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:50.159249+00:00
-- url     : https://prove2.me/theorems/2c22a392-d90a-481a-9a21-0043d932bea1
-- title:
--   Gauge Exists
-- statement:
--   Definitions and structural lemmas for Gauge Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/GaugeExists.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
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
open scoped ENNReal NNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def expC (k r : ℕ) : lieE (UWb k r) → Mt k r :=
  fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j
def HaarDens : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh ∧
    ∃ δ : lieE (UWb k r) → ℝ≥0∞, ContinuousAt δ 0 ∧ δ 0 ≠ 0 ∧ δ 0 ≠ ⊤ ∧
      ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x
namespace GE
variable {k r : ℕ}
def p0 (k r : ℕ) : Fin (2 * r + k + 1) := wI k r 0
def dg (k r : ℕ) (u : ℂ) : Mat k r := diagonal fun i => if i = p0 k r then u else 1
def dV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if i = p0 k r then Complex.I else 0
end GE
end PI.RhsWLim.W


