-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
-- name    : Formalism_LocalToGlobal_UnitaryNorms_UnrAe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:28.75781+00:00
-- url     : https://prove2.me/theorems/26017bfa-40a8-4b7d-b5dd-bcaedb15f6f9
-- title:
--   Unr Ae
-- statement:
--   Definitions and structural lemmas for Unr Ae, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAe.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace Formalism.L2.Host
def UnrAE (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ χ : Ideles L →* ℂˣ, Continuous χ →
    ∀ᶠ v in Filter.cofinite, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) = 1
def SMOne (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ χ χ' : HChar L, (∀ᶠ v in Filter.cofinite, χ.UnrAt v ∧ χ'.UnrAt v ∧ χ.val v = χ'.val v) → χ = χ'
variable {L : Type} [Field L] [NumberField L]
end Formalism.L2.Host


