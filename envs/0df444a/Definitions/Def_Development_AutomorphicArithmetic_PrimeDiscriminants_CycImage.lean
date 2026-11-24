-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:02.4148+00:00
-- url     : https://prove2.me/theorems/3f688212-5df0-4949-a713-5544c5c3c371
-- title:
--   Cyc Image
-- statement:
--   Definitions and structural lemmas for Cyc Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
def congrGal (m : ℕ) : Subgroup (H.E ≃ₐ[ℚ] H.E) :=
  Subgroup.closure {σ | ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] ∧ H.gal σ = H.art u}
theorem exists_thM (m : ℕ) : ∃ θ : H.E, ℚ⟮θ⟯ = fixedField (H.congrGal m) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ (fixedField (H.congrGal m))
  refine ⟨a, ?_⟩
  have h1 := IntermediateField.lift_adjoin_simple ℚ (fixedField (H.congrGal m)) a
  have h2 := congrArg IntermediateField.lift ha
  exact h1.symm.trans (h2.trans (IntermediateField.lift_top ℚ (fixedField (H.congrGal m))))
def thM (m : ℕ) : H.E := (H.exists_thM m).choose
end Formalism.HC.HostRaw
end


