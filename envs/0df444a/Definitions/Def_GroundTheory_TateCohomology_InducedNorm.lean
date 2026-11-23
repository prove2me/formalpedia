-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_InducedNorm
-- name    : GroundTheory_TateCohomology_InducedNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:05.086371+00:00
-- url     : https://prove2.me/theorems/74a59c11-32ba-4837-9da8-d2dd821c515a
-- title:
--   Induced Norm
-- statement:
--   Definitions and structural lemmas for Induced Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
section Criterion
variable (M : Rep.{u} k G)
noncomputable def toCoindRes :
    M ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) :=
  ofHom ⟨LinearMap.codRestrict _ (LinearMap.pi fun x : G => M.ρ x) fun m => by
      rw [Representation.mem_coindV]
      intro s x
      simp [map_mul],
    fun g => LinearMap.ext fun m => by
      apply Subtype.ext
      funext x
      change M.ρ x (M.ρ g m) = M.ρ (x * g) m
      rw [map_mul, Module.End.mul_apply]⟩
noncomputable def fromCoindRes (φ : M.V →ₗ[k] M.V) :
    coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) ⟶ M :=
  ofHom ⟨∑ x : G, M.ρ x⁻¹ ∘ₗ φ ∘ₗ LinearMap.proj x ∘ₗ
      (Representation.coindV (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M).ρ).subtype,
    fun g => LinearMap.ext fun f => by
      simp only [LinearMap.coe_comp, LinearMap.coe_sum, Function.comp_apply, Finset.sum_apply,
        map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
      change M.ρ x⁻¹ (φ (f.1 (x * g))) = M.ρ g (M.ρ (x * g)⁻¹ (φ (f.1 (x * g))))
      rw [← Module.End.mul_apply (M.ρ g) (M.ρ (x * g)⁻¹), ← map_mul, mul_inv_rev,
        mul_inv_cancel_left]⟩
end Criterion
section Tensor
omit [Fintype G] in

noncomputable def coeffOneProj : MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G :=
  MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
variable (B : Rep.{u} k G)
end Tensor
section Free
variable (M : Rep.{u} k G)
end Free
end GroundTheory.GroupCoh


