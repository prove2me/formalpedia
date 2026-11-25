-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:24.177721+00:00
-- url     : https://prove2.me/theorems/213e08a2-fa7c-5079-9243-5d6158d12963
-- title:
--   Analytic At Hf Left
-- statement:
--   Definitions and structural lemmas for Analytic At Hf Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/VacuumEntire/AnalyticAtHfLeft.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VacEntire.UnitaryGroupMassFormula
open PI.VacEntire
def coordL (ι : Type) [Fintype ι] (N N' : ℕ) (τ : ι) (i : Fin N') (j : Fin N) :
    (ι → Fin N' → Fin N → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => Fin N' → Fin N → ℂ) τ))
def blockL (n : Type) [Fintype n] (N N' : ℕ) (i : Fin N') (j : Fin N) :
    (n → Fin N' → Fin N → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun τ => coordL n N N' τ i j
end PI.VacEntire.UnitaryGroupMassFormula


