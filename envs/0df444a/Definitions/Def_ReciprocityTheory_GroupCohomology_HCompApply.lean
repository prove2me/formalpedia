-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_HCompApply
-- name    : ReciprocityTheory_GroupCohomology_HCompApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:45.752799+00:00
-- url     : https://prove2.me/theorems/ed65cfde-03c4-47c4-9c9a-8e60ddc78681
-- title:
--   HComp Apply
-- statement:
--   Definitions and structural lemmas for HComp Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HCompApply.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
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
namespace ReciprocityTheory.Coh.SelH
open ReciprocityTheory.Coh Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
def piHom {ι : Type u} {A B : ι → Cx R} (f : ∀ v, Hom (A v) (B v)) : Hom (pi A) (pi B) where
  f n := LinearMap.pi fun v => ((f v).f n).comp (LinearMap.proj v)
  comm n x := funext fun v => (f v).comm n (x v)
def negHom {A B : Cx R} (φ : Hom A B) : Hom A B where
  f n := -(φ.f n)
  comm n x := by simp [φ.comm]
def inr (A B : Cx R) : Hom B (prod A B) where
  f _ := LinearMap.inr R _ _
  comm n _ := Prod.ext (map_zero (A.d n)).symm rfl
end
end ReciprocityTheory.Coh.SelH


