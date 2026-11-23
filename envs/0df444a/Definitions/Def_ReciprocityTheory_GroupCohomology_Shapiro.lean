-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
-- name    : ReciprocityTheory_GroupCohomology_Shapiro
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:24.129308+00:00
-- url     : https://prove2.me/theorems/faa055c4-9e02-43c8-a7b4-cc8f7f8bcc04
-- title:
--   Shapiro
-- statement:
--   Definitions and structural lemmas for Shapiro, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Shapiro.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
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
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
section QI
variable {R : Type u} [CommRing R] {A B : Cx R}
end QI
section Push
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)
include hφ in
theorem shp_phi (y : U) : ev.φ y = (y : G) := by
  rw [hφ]
  rfl
def shpPush (n : ℕ) : hcoch C G n →ₗ[R] hcoch M G n where
  toFun F := ⟨fun x => ev.u (F.1 x), ev.u_cont.comp F.2.1, fun g x => by
    have h := F.2.2 (g : G) x
    show ev.u (F.1 fun i => (g : G) * x i) = M.rho g (ev.u (F.1 x))
    rw [← ev.equiv, shp_phi ev hφ]
    exact congrArg ev.u h⟩
  map_add' F F' := Subtype.ext (funext fun x => map_add ev.u _ _)
  map_smul' c F := Subtype.ext (funext fun x => map_smul ev.u _ _)
variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)
end Push
section Coind
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : TRep R U)
def coindSub : Submodule R C(G, M.V) where
  carrier := {f | ∀ (x : U) g, f (x * g) = M.rho x (f g)}
  zero_mem' := fun x g => by simp
  add_mem' := fun {a b} ha hb x g => by simp [ha x g, hb x g]
  smul_mem' c a ha x g := by simp [ha x g]
variable {U M}
def coindTr (g : G) : coindSub U M →ₗ[R] coindSub U M where
  toFun f := ⟨f.1.comp ⟨(· * g), continuous_mul_const g⟩, fun x h => by
    show f.1 (x * h * g) = M.rho x (f.1 (h * g))
    rw [mul_assoc]; exact f.2 x (h * g)⟩
  map_add' f f' := rfl
  map_smul' c f := rfl
@[simp] theorem coindTr_apply (g : G) (f : coindSub U M) (h : G) : (coindTr g f).1 h = f.1 (h * g) := rfl
variable (U M)
def coindRho : Representation R G (coindSub U M) where
  toFun := coindTr
  map_one' := LinearMap.ext fun f => Subtype.ext (ContinuousMap.ext fun h => by simp)
  map_mul' g g' := LinearMap.ext fun f => Subtype.ext (ContinuousMap.ext fun h => by
    show f.1 (h * (g * g')) = f.1 (h * g * g')
    rw [mul_assoc])
instance : ContinuousConstSMul R (coindSub U M) :=
  ⟨fun c => ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩
variable [LocallyCompactSpace G]
theorem coindRho_cont : ContAction (coindRho U M) := by
  let m : C(G × G, G) := ⟨fun q => q.2 * q.1, continuous_snd.mul continuous_fst⟩
  have h1 : Continuous fun p : G × coindSub U M => (ContinuousMap.curry m p.1, (p.2 : C(G, M.V))) :=
    ((ContinuousMap.curry m).continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h2 := ContinuousMap.continuous_comp'.comp h1
  show Continuous fun p : G × coindSub U M => coindRho U M p.1 p.2
  refine continuous_induced_rng.2 ?_
  exact h2
def coindRep : TRep R G where
  V := coindSub U M
  rho := coindRho U M
  cont := coindRho_cont U M
def coindEv : Pair (coindRep U M) M where
  φ := U.subtype
  u := { toFun := fun f => f.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  φ_cont := continuous_subtype_val
  u_cont := (continuous_eval_const 1).comp continuous_subtype_val
  equiv g f := by
    show f.1 (1 * (g : G)) = M.rho g (f.1 1)
    have h := f.2 g 1
    rw [mul_one] at h
    rw [one_mul]; exact h
end Coind
end
end ReciprocityTheory.Coh


