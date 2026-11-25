-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:32.546841+00:00
-- url     : https://prove2.me/theorems/46f8b1d1-d674-47fa-a982-dcbf733b2696
-- title:
--   Rhs WInv O
-- statement:
--   Definitions and structural lemmas for Rhs WInv O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvO.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
namespace PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
def UnimodK : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), IsHaarOn (UWset k r z) μ → μ Set.univ ≠ ⊤ →
    ∀ b ∈ UWset k r z, μ.map (rmulM b) = μ
def FibTrans : Prop :=
  ∀ (k r : ℕ) (z v v' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r v → inWb k r v' → 0 < Tz k r z →
    herm (Hpk k r) v v = herm (Hpk k r) v' v' → herm (Hpk k r) v z = herm (Hpk k r) v' z →
      ∃ u ∈ UWset k r z, u *ᵥ v = v'
def HypQ : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∃ Q : Measure (Fin (2 * r + k + 1) → ℂ), SigmaFinite Q ∧ (∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q) ∧
      Q {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ v, g (herm (Hpk k r) v z) ∂Q = c * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
def Gf (μW : Measure (Mt k r)) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (v : Fin (2 * r + k + 1) → ℂ) : ℝ≥0∞ :=
  ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW
end PI.RhsWLim.W.RI


