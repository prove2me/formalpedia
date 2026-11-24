-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobB
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobB
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:04.204047+00:00
-- url     : https://prove2.me/theorems/4085a53e-9b48-4e1b-ac93-5ec578c956ba
-- title:
--   Grow Sob B
-- statement:
--   Definitions and structural lemmas for Grow Sob B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobB.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory
variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
def Om : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i v, y i v ∈ v.adicCompletionIntegers F}
end PositivityTheory.ThKF0.Grow


