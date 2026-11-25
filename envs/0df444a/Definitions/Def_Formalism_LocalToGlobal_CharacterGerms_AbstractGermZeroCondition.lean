-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
-- name    : Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:41.543074+00:00
-- url     : https://prove2.me/theorems/bab40269-c266-4b68-a094-b6a41d2780d0
-- title:
--   Abstract Germ Zero Condition
-- statement:
--   Definitions and structural lemmas for Abstract Germ Zero Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AbstractGermZeroCondition.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
def eG' {I : Fin 2 → Type} (g : Fin 2) : I g ↪ WV I := ⟨fun x => ⟨g, x⟩, sigma_mk_injective⟩
def AbstractGermZeroCondition : Prop :=
  ∀ (I : Fin 2 → Type) [∀ g, Fintype (I g)] (t t₂ φ φ₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) → (∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ g k) = 0) → (∀ g k, IntS V (φ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ g k)).det = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ₂ g k) = 0) → (∀ g k, IntS V (φ₂ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ₂ g k)).det = 0) →
    (∀ g k, MvPowerSeries.subst (t g) (φ g k) = MvPowerSeries.subst (t₂ g) (φ₂ g k)) →
    IntGerm V t = IntGerm V t₂
end AbstractGermZero
end Formalism.L2.FormalSeriesBounds


