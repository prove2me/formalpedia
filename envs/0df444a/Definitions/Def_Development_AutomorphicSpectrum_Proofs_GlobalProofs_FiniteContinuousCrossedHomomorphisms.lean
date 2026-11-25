-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:21:12.989306+00:00
-- url     : https://prove2.me/theorems/7500aa52-b406-4f4a-996f-69904f5d5b12
-- title:
--   Finite Continuous Crossed Homomorphisms
-- statement:
--   Definitions and structural lemmas for Finite Continuous Crossed Homomorphisms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace GlobalTheory.CompanionTheory.Cocycles
section Algebra
variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}
theorem cocycle_map_one (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : f 1 = 0 := by
  simpa using hf 1 1
theorem cocycle_map_inv (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (a : G) :
    f a⁻¹ = -ρ a⁻¹ (f a) := by
  have h := hf a⁻¹ a
  rw [inv_mul_cancel, cocycle_map_one hf] at h
  exact eq_neg_of_add_eq_zero_left h.symm
def cocycleKer (ρ : Representation k G V) (f : G → V)
    (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : Subgroup G where
  carrier := {g | ρ g = 1 ∧ f g = 0}
  one_mem' := ⟨map_one ρ, cocycle_map_one hf⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    rw [hf, ha', hb', map_zero, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have h2 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [ha, mul_one] at h2
    refine ⟨h1, ?_⟩
    rw [cocycle_map_inv hf, ha', map_zero, neg_zero]
end Algebra
end GlobalTheory.CompanionTheory.Cocycles


