-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:33.138515+00:00
-- url     : https://prove2.me/theorems/0392a60e-d29f-42ca-b023-96d0f13d3ca5
-- title:
--   Map Subtype Injective
-- statement:
--   Definitions and structural lemmas for Map Subtype Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
namespace Formalism.LT.Asm
open Formalism.G
section Integral
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Integral
theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero
section FG
open Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries τ (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d F, hF d⟩
end FG
end Formalism.LT.Asm
namespace Formalism.LT
end Formalism.LT


