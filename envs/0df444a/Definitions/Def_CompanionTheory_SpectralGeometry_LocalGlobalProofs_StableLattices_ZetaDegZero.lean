-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:09.032562+00:00
-- url     : https://prove2.me/theorems/67c037ac-ff73-45dd-a11e-cf3cd4b47093
-- title:
--   Zeta Deg Zero
-- statement:
--   Definitions and structural lemmas for Zeta Deg Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean

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
open Finset
noncomputable section
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
section Rel
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def Pres (R : Submodule ℂ (V × W)) (S : Module.End ℂ V) (T : Module.End ℂ W) : Prop :=
  ∀ x y, (x, y) ∈ R → (S x, T y) ∈ R
end Rel
section Chains
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def degSub (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (j : ℕ) : Submodule ℂ (Ch ε V) where
  carrier := {x | Deg j x}
  add_mem' := fun {x y} hx hy A hA => by simp [hx A hA, hy A hA]
  zero_mem' := fun A _ => rfl
  smul_mem' := fun c x hx A hA => by simp [hx A hA]
end Chains
end GlobalTheory.CompanionTheory.CasselmanOsborne


