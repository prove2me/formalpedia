-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:18.346831+00:00
-- url     : https://prove2.me/theorems/a8fbe02a-3834-4c0c-b80a-c6f30dec187b
-- title:
--   Orbit Push I
-- statement:
--   Definitions and structural lemmas for Orbit Push I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushI.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
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
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
def toW (k : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (k + 1) → ℂ := fun j =>
  if h : j.val < k then p.1 ⟨j.val, h⟩ else p.2
def ofW (k : ℕ) (v : Fin (k + 1) → ℂ) : (Fin k → ℂ) × ℂ := (fun i => v (Fin.castSucc i), v (Fin.last k))
def blkAct (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ :=
  ofW k (μ *ᵥ toW k p)
def qf (k : ℕ) (p : (Fin k → ℂ) × ℂ) : ℝ := ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2
def LebInvB : Prop :=
  ∀ (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), μᴴ * Hb k * μ = Hb k →
    (volume : Measure ((Fin k → ℂ) × ℂ)).map (blkAct k μ) = volume
def coneSh (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : ((Fin k → ℂ) × ℂ) × ℝ => q.2 • q.1) '' ((E ∩ hypS k T') ×ˢ Set.Ioo (1 : ℝ) 2)
def ConeForm : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = κ * volume (coneSh k T' E)
end PI.RhsWLim.W


