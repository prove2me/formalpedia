-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousRho
-- name    : ReciprocityTheory_GroupCohomology_ContinuousRho
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:49.439818+00:00
-- url     : https://prove2.me/theorems/2846e4c9-b26b-4815-bd2d-1528a2718060
-- title:
--   Continuous Rho
-- statement:
--   Definitions and structural lemmas for Continuous Rho, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ContinuousRho.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero


set_option autoImplicit false
namespace ReciprocityTheory.Coh
namespace QuadraticConjugation
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def conjHom (U : Subgroup G) [U.Normal] (s : G) : U →* U where
  toFun g := ⟨s⁻¹ * g * s, by simpa using ‹U.Normal›.conj_mem g g.2 s⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
@[simp] theorem conjHom_coe (U : Subgroup G) [U.Normal] (s : G) (g : U) :
    ((conjHom U s g : U) : G) = s⁻¹ * g * s := rfl
theorem continuous_rho' (N : TRep R G) (s : G) : Continuous (N.rho s) :=
  N.cont.comp (f := fun m : N.V => (s, m)) (continuous_const.prodMk continuous_id)
theorem rho_conj (N : TRep R G) (s g : G) (m : N.V) :
    N.rho s (N.rho (s⁻¹ * g * s) m) = N.rho g (N.rho s m) := by
  have : s * (s⁻¹ * g * s) = g * s := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]
def conjPair (N : TRep R G) (U : Subgroup G) [U.Normal] (s : G) : Pair (N.resSub U) (N.resSub U) where
  φ := conjHom U s
  u := N.rho s
  φ_cont := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m
def conjG (s : G) : G →* G where
  toFun g := s⁻¹ * g * s
  map_one' := by simp
  map_mul' a b := by group
def innerPair (N : TRep R G) (s : G) : Pair N N where
  φ := conjG s
  u := N.rho s
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m
end
section Lemmas
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Lemmas
section Main
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' : TRep R G} {U : Subgroup G} [U.Normal] (P : Pair M' (M.resSub U))
theorem phi_apply (hφ : P.φ = U.subtype) (g : U) : P.φ g = (g : G) := by rw [hφ]; rfl
noncomputable def PU (hφ : P.φ = U.subtype) : Pair (M'.resSub U) (M.resSub U) where
  φ := MonoidHom.id U
  u := P.u
  φ_cont := continuous_id
  u_cont := P.u_cont
  equiv g m := by
    have := P.equiv g m
    rw [phi_apply P hφ] at this
    exact this
noncomputable def eqv (hP : IsHomeomorph P.u) : M'.V ≃ₗ[R] (M.resSub U).V := LinearEquiv.ofBijective P.u hP.bijective
theorem eqv_symm (hP : IsHomeomorph P.u) (m : (M.resSub U).V) : P.u ((eqv P hP).symm m) = m :=
  (eqv P hP).apply_symm_apply m
noncomputable def PInv (hφ : P.φ = U.subtype) (hP : IsHomeomorph P.u) : Pair (M.resSub U) (M'.resSub U) where
  φ := MonoidHom.id U
  u := (eqv P hP).symm.toLinearMap
  φ_cont := continuous_id
  u_cont := by
    have h1 : ∀ m, P.u ((hP.homeomorph P.u).symm m) = m := fun m =>
      (hP.homeomorph P.u).apply_symm_apply m
    refine (hP.homeomorph P.u).symm.continuous.congr fun m => hP.bijective.1 ?_
    show P.u _ = P.u ((eqv P hP).symm m)
    rw [h1, eqv_symm]
  equiv g m := by
    apply hP.bijective.1
    show P.u ((eqv P hP).symm ((M.resSub U).rho g m)) = P.u (M'.rho g ((eqv P hP).symm m))
    have := P.equiv g ((eqv P hP).symm m)
    rw [phi_apply P hφ] at this
    rw [this, eqv_symm, eqv_symm]
end Main
end QuadraticConjugation
end ReciprocityTheory.Coh


