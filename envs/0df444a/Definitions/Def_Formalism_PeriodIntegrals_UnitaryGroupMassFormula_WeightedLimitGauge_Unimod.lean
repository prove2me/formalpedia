-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:00.956739+00:00
-- url     : https://prove2.me/theorems/1ca2935c-0b87-4b3f-ad2f-6bf2a33e4bb1
-- title:
--   Unimod
-- statement:
--   Definitions and structural lemmas for Unimod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/Unimod.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
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
def UnitInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ q ∈ UWb k r, qᴴ * q = 1 → ν.map (rmulM q) = ν
def HermInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, B₀ᴴ * Hb k * B₀ = Hb k → B₀ᴴ = B₀ →
      ν.map (rmulM (embWb k r B₀)) = ν
def PolarDecW : Prop :=
  ∀ (k r : ℕ) (p : Mat k r), p ∈ UWb k r → ∃ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
    B₀ᴴ * Hb k * B₀ = Hb k ∧ B₀ᴴ = B₀ ∧ ∃ q ∈ UWb k r, qᴴ * q = 1 ∧ p = embWb k r B₀ * q
end PI.RhsWLim.W


