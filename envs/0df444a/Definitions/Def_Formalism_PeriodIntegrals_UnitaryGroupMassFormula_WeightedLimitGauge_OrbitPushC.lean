-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:23.067428+00:00
-- url     : https://prove2.me/theorems/f613d2ad-c9a3-54b5-866f-717052408b07
-- title:
--   Orbit Push C
-- statement:
--   Definitions and structural lemmas for Orbit Push C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushC.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def hq (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : (Fin k → ℂ) × ℂ :=
  (y, (Real.sqrt (∑ i, Complex.normSq (y i) + T') : ℂ) * Complex.exp (θ * Complex.I))
def hqI (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ y, E.indicator 1 (hq k T' y θ)
def HypTh : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = c * hqI k T' E
def ConeVol : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → volume (coneSh k T' E) = c * hqI k T' E
end PI.RhsWLim.W


