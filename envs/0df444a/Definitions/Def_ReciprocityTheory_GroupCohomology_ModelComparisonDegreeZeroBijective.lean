-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
-- name    : ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:06.078932+00:00
-- url     : https://prove2.me/theorems/21b299e3-385d-4dc9-8e7b-c09fa47cca6c
-- title:
--   Model Comparison Degree Zero Bijective
-- statement:
--   Definitions and structural lemmas for Model Comparison Degree Zero Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ModelComparisonDegreeZeroBijective.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
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
namespace ProcyclicCohomology
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def stab (M : TRep R G) (m : M.V) : Subgroup G where
  carrier := {a | M.rho a m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end ProcyclicCohomology
end ReciprocityTheory.Coh
namespace ReciprocityTheory.Coh
namespace ProcyclicCohomology
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def psum (M : TRep R G) (s : G) (m : M.V) (j : ℕ) : M.V :=
  ∑ i ∈ Finset.range j, M.rho (s ^ i) m
end ProcyclicCohomology
end ReciprocityTheory.Coh
namespace ReciprocityTheory.Coh
namespace ProcyclicCohomology
open ReciprocityTheory.Gal Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end ProcyclicCohomology
end ReciprocityTheory.Coh


