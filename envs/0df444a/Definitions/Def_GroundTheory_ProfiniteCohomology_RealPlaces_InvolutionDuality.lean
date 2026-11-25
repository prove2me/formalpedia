-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
-- name    : GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:34:47.613797+00:00
-- url     : https://prove2.me/theorems/7544ea5d-47c5-4cd4-ae41-5c6b61603d29
-- title:
--   Involution Duality
-- statement:
--   Definitions and structural lemmas for Involution Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_evalHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.QZ.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZ.evalHom_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.eval_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
namespace Involution
variable {M : Type*} [AddCommGroup M]
def fixedSub (σ : M →+ M) : AddSubgroup M := (σ - AddMonoidHom.id M).ker
theorem mem_fixedSub {σ : M →+ M} {x : M} : x ∈ fixedSub σ ↔ σ x = x := by
  rw [fixedSub, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
def traceSub (σ : M →+ M) : AddSubgroup M := (AddMonoidHom.id M + σ).range
theorem mem_traceSub {σ : M →+ M} {x : M} : x ∈ traceSub σ ↔ ∃ y, y + σ y = x := by
  rw [traceSub, AddMonoidHom.mem_range]
  rfl
abbrev tateQuot (σ : M →+ M) : Type _ :=
  fixedSub σ ⧸ (traceSub σ).addSubgroupOf (fixedSub σ)
def dualInv (σ : M →+ M) : (M →+ QZ) →+ (M →+ QZ) where
  toFun f := -(f.comp σ)
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [add_comm]
@[simp]
theorem dualInv_apply (σ : M →+ M) (f : M →+ QZ) (x : M) : dualInv σ f x = -f (σ x) :=
  rfl
theorem mem_fixedSub_dualInv_iff {σ : M →+ M} (f : M →+ QZ) :
    f ∈ fixedSub (dualInv σ) ↔ ∀ y, f (y + σ y) = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro h y
    have e := DFunLike.congr_fun h y
    rw [dualInv_apply] at e
    rw [map_add, ← e, neg_add_cancel]
  · intro h
    ext y
    rw [dualInv_apply, neg_eq_iff_add_eq_zero, add_comm, ← map_add]
    exact h y
def fixedPair (σ : M →+ M) : fixedSub σ →+ fixedSub (dualInv σ) →+ QZ where
  toFun x :=
    { toFun := fun f => (f : M →+ QZ) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
@[simp]
theorem fixedPair_apply (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    fixedPair σ x f = (f : M →+ QZ) x :=
  rfl
theorem fixedPair_eq_zero_of_mem_left (σ : M →+ M) (x : fixedSub σ) (hx : (x : M) ∈ traceSub σ)
    (f : fixedSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨y, hy⟩ := mem_traceSub.1 hx
  rw [fixedPair_apply, ← hy]
  exact (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 y
theorem fixedPair_eq_zero_of_mem_right (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ))
    (hf : (f : M →+ QZ) ∈ traceSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨g, hg⟩ := mem_traceSub.1 hf
  have hx : σ x = x := mem_fixedSub.1 x.2
  rw [fixedPair_apply, ← hg, AddMonoidHom.add_apply, dualInv_apply, hx, add_neg_cancel]
def tatePair (σ : M →+ M) : tateQuot σ →+ tateQuot (dualInv σ) →+ QZ :=
  QuotientAddGroup.lift _
    { toFun := fun x => QuotientAddGroup.lift _ (fixedPair σ x) fun f hf =>
        fixedPair_eq_zero_of_mem_right σ x f hf
      map_zero' := by
        ext f
        simp
      map_add' := fun x y => by
        ext f
        simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.add_apply,
          QuotientAddGroup.lift_mk, map_add]
        rfl }
    fun x hx => by
      ext f
      exact fixedPair_eq_zero_of_mem_left σ x hx f
@[simp]
theorem tatePair_mk (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    tatePair σ (x : tateQuot σ) (f : tateQuot (dualInv σ)) = (f : M →+ QZ) x :=
  rfl
variable {σ : M →+ M}
instance finite_tateQuot [Finite M] (τ : M →+ M) : Finite (tateQuot τ) :=
  inferInstance
section Transport
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
def fixedSubCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    fixedSub σ ≃+ fixedSub τ where
  toFun x := ⟨e (x : M), mem_fixedSub.2 (by rw [← he, mem_fixedSub.1 x.2])⟩
  invFun y := ⟨e.symm (y : N), mem_fixedSub.2 (by
    apply e.injective
    rw [he, e.apply_symm_apply, mem_fixedSub.1 y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : M))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : N))
  map_add' x y := Subtype.ext (map_add e (x : M) (y : M))
@[simp]
theorem coe_fixedSubCongr_apply (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N}
    (he : ∀ x, e (σ x) = τ (e x)) (x : fixedSub σ) : (fixedSubCongr e he x : N) = e (x : M) :=
  rfl
def tateQuotCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    tateQuot σ ≃+ tateQuot τ :=
  QuotientAddGroup.congr _ _ (fixedSubCongr e he) (by
    ext y
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hx
      refine mem_traceSub.2 ⟨e z, ?_⟩
      show e z + τ (e z) = e (x : M)
      rw [← he, ← map_add, hz]
    · intro hy
      refine ⟨(fixedSubCongr e he).symm y, ?_, AddEquiv.apply_symm_apply _ _⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hy
      refine mem_traceSub.2 ⟨e.symm z, ?_⟩
      apply e.injective
      rw [map_add, he, e.apply_symm_apply, hz]
      change (y : N) = e (e.symm (y : N))
      rw [e.apply_symm_apply])
end Transport
section Pairings
variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
end Pairings
end Involution
end GroundTheory.ProfCoh


