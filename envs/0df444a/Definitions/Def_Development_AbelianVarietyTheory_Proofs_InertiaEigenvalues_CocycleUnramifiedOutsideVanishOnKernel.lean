-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:21.989796+00:00
-- url     : https://prove2.me/theorems/f8cbfd91-82b2-45e5-b8ee-4b23189bf2ff
-- title:
--   Cocycle Unramified Outside Vanish On Kernel
-- statement:
--   Definitions and structural lemmas for Cocycle Unramified Outside Vanish On Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
namespace GlobalTheory.UnramCocycle
def kerSub {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : Subgroup Γ where
  carrier := {n | x.1 n = 0 ∧ ∀ m, ρ n m = m}
  one_mem' := ⟨by simpa using x.2.2 1 1, fun m => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [x.2.2, ha, hb]; simp, fun m => ?_⟩
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    · have h := x.2.2 a a⁻¹
      rw [mul_inv_cancel, h1, ha, ha', zero_add] at h
      exact h.symm
    · conv_lhs => rw [← ha' m]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end GlobalTheory.UnramCocycle


