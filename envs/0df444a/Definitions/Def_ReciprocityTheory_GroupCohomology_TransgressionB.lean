-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
-- name    : ReciprocityTheory_GroupCohomology_TransgressionB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:19.118686+00:00
-- url     : https://prove2.me/theorems/05e32194-281e-4286-a967-ef6badf858a5
-- title:
--   Transgression B
-- statement:
--   Definitions and structural lemmas for Transgression B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionB.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
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
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
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
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe


set_option autoImplicit false
namespace ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def ev1 (M : TRep R G) (N : Subgroup G) (f0 : (M.resSub N).coch.X 1) (n : N) : M.V := f0.1 (e1 n)
def conjN (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) : Pair (M.resSub N) (M.resSub N) where
  φ := { toFun := cj N s
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (by simp only [cj_coe, Subgroup.coe_mul]; group) }
  u := M.rho s
  φ_cont := Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := by
    have h := M.cont.comp (Continuous.prodMk (continuous_const (y := s)) (continuous_id (X := M.V)))
    exact h
  equiv g m := by
    have key : ∀ (g : G) (m : M.V), M.rho s (M.rho (s⁻¹ * g * s) m) = M.rho g (M.rho s m) := by
      intro g m
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
    exact key g m
section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP
end
end
end ReciprocityTheory.Coh.InflationTransgression


