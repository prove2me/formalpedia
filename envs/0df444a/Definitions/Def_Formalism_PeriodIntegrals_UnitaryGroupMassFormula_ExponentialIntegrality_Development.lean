-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:59.890476+00:00
-- url     : https://prove2.me/theorems/03f71ce5-a783-4471-aad7-e63054cd502f
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.ExpIntWProof
open PI
def StepI : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf (expMv f)
def KeyW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ℂ_[p]), x ∈ Wp p → ‖x‖ < 1 → x / (p : ℂ_[p]) ∈ Wp p
def StepIII : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ℂ_[p]), InWf x → ‖x‖ ≤ 1 → x ∈ Wp p
end PI.ExpIntWProof
end


