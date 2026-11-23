-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:36.647893+00:00
-- url     : https://prove2.me/theorems/5816330f-7b4c-4c0b-bc80-7fe4cb5b88f6
-- title:
--   Blk Bijective
-- statement:
--   Definitions and structural lemmas for Blk Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/BlkBijective.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply


set_option autoImplicit false
open Finset Equiv
noncomputable section
namespace GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ w : NC ε → V, v = ∑ i : NC ε, E i.1.1 i.1.2 (w i)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', by simp [Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl⟩
    exact ⟨c • w, by simp [Finset.smul_sum]⟩
end GlobalTheory.CompanionTheory.CapelliBlocks


