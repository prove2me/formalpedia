-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:15.007097+00:00
-- url     : https://prove2.me/theorems/87133e6a-11b1-4c00-a348-9d867e0a57ca
-- title:
--   Row Tie Axes
-- statement:
--   Definitions and structural lemmas for Row Tie Axes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
section VanS
variable {τ : Type}
def Van (T : Set τ) (f : MvPowerSeries τ C) : Prop :=
  ∀ ν : τ →₀ ℕ, (∀ w ∈ ν.support, w ∉ T) → coeff ν f = 0
end VanS
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
section FBpart
variable {dd : ℕ}
end FBpart
end Formalism.L2.FormalSeriesBounds


