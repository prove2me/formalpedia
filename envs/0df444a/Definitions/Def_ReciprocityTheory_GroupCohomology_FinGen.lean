-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
-- name    : ReciprocityTheory_GroupCohomology_FinGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:00.878289+00:00
-- url     : https://prove2.me/theorems/7664aa6e-0d34-472b-b6b1-f856b6498ef4
-- title:
--   Fin Gen
-- statement:
--   Definitions and structural lemmas for Fin Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
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
open Cx Function
universe u
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R]
end SlopeTestRemainingChoices
section Aux2
theorem tower_family {X : ℕ → Type*} (f : ∀ k, X (k + 1) → X k) (hf : ∀ k, Surjective (f k)) :
    ∀ (m : ℕ) (y : X m), ∃ z : ∀ k, X k, (∀ k, f k (z (k + 1)) = z k) ∧ z m = y := by
  intro m
  induction m generalizing X with
  | zero =>
    intro y
    let z : ∀ k, X k := fun k => Nat.rec (motive := fun k => X k) y
      (fun k zk => Classical.choose (hf k zk)) k
    exact ⟨z, fun k => Classical.choose_spec (hf k (z k)), rfl⟩
  | succ m ih =>
    intro y
    obtain ⟨z', hz', hm⟩ := ih (X := fun k => X (k + 1)) (fun k => f (k + 1)) (fun k => hf (k + 1)) y
    refine ⟨fun k => match k with | 0 => f 0 (z' 0) | k + 1 => z' k, fun k => ?_, hm⟩
    cases k with
    | zero => rfl
    | succ k => exact hz' k
variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
noncomputable def descend (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) : P →ₗ[R] Q :=
  (LinearMap.ker p).liftQ g h ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap
theorem descend_apply (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) (x : M) : descend p hp g h (p x) = g x := by
  have : (p.quotKerEquivOfSurjective hp).symm (p x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [descend, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, this,
    Submodule.liftQ_apply]
end Aux2
section Tower
variable {R : Type u} [CommRing R] (t : R) {A : ℕ → Cx R} {τ : ∀ m, Hom (A (m + 1)) (A m)}
  {L : Cx R} {π : ∀ m, Hom L (A m)}
theorem tower_pi_surj (hT : IsTowerLim A τ L π) (m n : ℕ) : Surjective ((π m).f n) := by
  intro y
  obtain ⟨z, hz, hm⟩ := tower_family (X := fun k => (A k).X n) (fun k => (τ k).f n)
    (fun k => hT.surj k n) m y
  obtain ⟨x, hx⟩ := hT.lift n z hz
  exact ⟨x, (hx m).trans hm⟩
def smulHom (L : Cx R) (t : R) : Hom L L := ⟨fun _ => t • LinearMap.id, fun n x => by simp⟩
variable (hT : IsTowerLim A τ L π) (htf : ∀ n (x : L.X n), t • x = 0 → x = 0)
  (hk : ∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y)
include hT htf hk
theorem ker_le_ker_smul (m n : ℕ) : LinearMap.ker ((π 0).f n) ≤
    LinearMap.ker ((π (m + 1)).f n ∘ₗ (t ^ (m + 1) • LinearMap.id)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (hk 0 n x).1 hx
  show (π (m + 1)).f n (t ^ (m + 1) • t ^ (0 + 1) • y) = 0
  rw [hk, smul_smul, ← pow_add]
  exact ⟨y, by ring_nf⟩
noncomputable def jf (m n : ℕ) : (A 0).X n →ₗ[R] (A (m + 1)).X n :=
  descend ((π 0).f n) (tower_pi_surj hT 0 n) _ (ker_le_ker_smul t hT htf hk m n)
theorem jf_apply (m n : ℕ) (x : L.X n) :
    jf t hT htf hk m n ((π 0).f n x) = (π (m + 1)).f n (t ^ (m + 1) • x) :=
  descend_apply _ _ _ _ x
noncomputable def jHom (m : ℕ) : Hom (A 0) (A (m + 1)) where
  f n := jf t hT htf hk m n
  comm n a := by
    obtain ⟨x, rfl⟩ := tower_pi_surj hT 0 n a
    rw [← (π 0).comm, jf_apply, jf_apply, ← (π (m + 1)).comm]
    simp only [map_smul]
end Tower
end ReciprocityTheory.Coh


