-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:19:34.783195+00:00
-- url     : https://prove2.me/theorems/42ba3f62-531e-544e-ba1f-d91f0bd8bc7c
-- title:
--   Galois Unramified Outside Cohomology
-- statement:
--   Definitions and structural lemmas for Galois Unramified Outside Cohomology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomology.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map
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
open scoped Pointwise IntermediateField
namespace GlobalTheory.CompanionTheory.Glob.InertiaLift
section
variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
noncomputable def actInt (g : Ω ≃ₐ[F] Ω) : IntCl K Ω ≃+* IntCl K Ω where
  toFun b := ⟨g b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    (g.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨(g⁻¹ : Ω ≃ₐ[F] Ω) b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (by
    show (g⁻¹ * g) (b : Ω) = b
    simp)
  right_inv b := Subtype.ext (mul_inv_apply (σ := g) (b : Ω))
  map_mul' a b := Subtype.ext (map_mul g (a : Ω) b)
  map_add' a b := Subtype.ext (map_add g (a : Ω) b)
end
end GlobalTheory.CompanionTheory.Glob.InertiaLift


