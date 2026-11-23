-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
-- name    : ReciprocityTheory_GroupCohomology_PrismOpZeroEval
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:42.633852+00:00
-- url     : https://prove2.me/theorems/b495f031-58c2-466f-832e-b8330fdb057c
-- title:
--   Prism Op Zero Eval
-- statement:
--   Definitions and structural lemmas for Prism Op Zero Eval, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
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
open Function
universe u
section Comb
variable {V X Y : Type u} [AddCommGroup V]
noncomputable def prismOp (a b : X → Y) : (n : ℕ) → ((Fin (n + 2) → Y) → V) → (Fin (n + 1) → X) → V
  | 0, F, x => F (Fin.cons (a (x 0)) fun j => b (x j))
  | n + 1, F, x => F (Fin.cons (a (x 0)) fun j => b (x j)) -
      prismOp a b n (fun y => F (Fin.cons (a (x 0)) y)) (Fin.tail x)
end Comb
section Key
variable {V X Y : Type u} [AddCommGroup V]
end Key
section Top
variable {V X Y : Type u} [AddCommGroup V]
end Top
section Main
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
noncomputable def pullH (M : TRep R G) {X Y : Type u} [TopologicalSpace X] [MulAction G X]
    [TopologicalSpace Y] [MulAction G Y] (a : X → Y) (ha : Continuous a)
    (hga : ∀ (g : G) x, a (g • x) = g • a x) (n : ℕ) : hcoch M Y n →ₗ[R] hcoch M X n where
  toFun F := ⟨fun x => F.1 fun i => a (x i), F.2.1.comp (continuous_pi fun i => ha.comp (continuous_apply i)),
    fun g x => by simp only [hga]; exact F.2.2 g _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Main
end ReciprocityTheory.Coh


