-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:16:25.809059+00:00
-- url     : https://prove2.me/theorems/1598e369-9143-5983-b057-d10a39a775c5
-- title:
--   Mod Fix J
-- statement:
--   Definitions and structural lemmas for Mod Fix J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFixJ.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
def fixJRoots {Ω : Type*} [Field Ω] (P : Polynomial ℤ) : Finset Ω := (P.map (Int.castRingHom Ω)).roots.toFinset
def fixJStab (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω] (P : Polynomial ℤ) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {g | ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb r hr
    rw [AlgEquiv.mul_apply, hb r hr, ha r hr]
  inv_mem' := by
    intro a ha r hr
    have := ha r hr
    calc a⁻¹ r = a⁻¹ (a r) := by rw [this]
      _ = r := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
end ReciprocityTheory.ChartRestriction.L1


