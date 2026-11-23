-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:48.146205+00:00
-- url     : https://prove2.me/theorems/4d85c3ba-06a4-4f84-9198-62648c23993a
-- title:
--   Mem Filt Of Words
-- statement:
--   Definitions and structural lemmas for Mem Filt Of Words, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MemFiltOfWords.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
section Ring
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Ring
section Filt
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}
def filt (d : ι → Module.End ℂ Z) (m : ℕ) : Submodule ℂ Z :=
  Nat.rec (motive := fun _ => Submodule ℂ Z) ⊥ (fun _ S => ⨅ i, S.comap (d i)) m
end Filt
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
end GlobalTheory.CompanionTheory.DSICKoszul


