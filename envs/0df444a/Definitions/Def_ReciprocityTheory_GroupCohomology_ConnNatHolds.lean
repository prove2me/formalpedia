-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
-- name    : ReciprocityTheory_GroupCohomology_ConnNatHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:54.694809+00:00
-- url     : https://prove2.me/theorems/3be4454a-416a-4c86-98ce-fe60fcd1fa99
-- title:
--   Conn Nat Holds
-- statement:
--   Definitions and structural lemmas for Conn Nat Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ConnNatHolds.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
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
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_zero
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
namespace LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R}
theorem cls_surj (A : Cx R) (n : ℕ) (h : A.H n) : ∃ x hx, h = A.cls n x hx := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨x, hx, rfl⟩
theorem cls_eq_zero (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl
theorem mem_B_succ (A : Cx R) (n : ℕ) (x : A.X (n + 1)) : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  show x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range
theorem mem_B_zero (A : Cx R) (x : A.X 0) : x ∈ A.B 0 ↔ x = 0 := by
  show x ∈ (⊥ : Submodule R (A.X 0)) ↔ _
  exact Submodule.mem_bot R
end LongExactSequenceMaps
namespace LongExactSequenceMaps
noncomputable section
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
theorem p_i (hs : SES i p) (n : ℕ) (a : A.X n) : p.f n (i.f n a) = 0 := by
  exact (hs.exact n (i.f n a)).2 ⟨a, rfl⟩
def S (i : Hom A B) (n : ℕ) : Submodule R (B.X n) := (LinearMap.range (i.f (n + 1))).comap (B.d n)
def toRange (n : ℕ) : S i n →ₗ[R] LinearMap.range (i.f (n + 1)) :=
  ((B.d n).comp (S i n).subtype).codRestrict _ (fun b => b.2)
def pre (hs : SES i p) (n : ℕ) : S i n →ₗ[R] A.X (n + 1) :=
  (LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).symm.toLinearMap.comp (toRange i n)
theorem i_pre (hs : SES i p) (n : ℕ) (b : S i n) : i.f (n + 1) (pre i p hs n b) = B.d n b := by
  have key : ∀ y : LinearMap.range (i.f (n + 1)),
      i.f (n + 1) ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).symm y) = y := fun y => by
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).apply_symm_apply y)
    simpa using h
  simp only [pre, LinearMap.comp_apply, LinearEquiv.coe_coe, key]
  rfl
theorem pre_d (hs : SES i p) (n : ℕ) (b : S i n) : A.d (n + 1) (pre i p hs n b) = 0 := by
  apply hs.inj (n + 1 + 1)
  rw [map_zero, i.comm, i_pre, B.dd]
theorem pre_eq (hs : SES i p) (n : ℕ) (b : S i n) (a : A.X (n + 1)) (h : B.d n b = i.f (n + 1) a) :
    pre i p hs n b = a := by
  exact hs.inj (n + 1) (by rw [i_pre, h])
def θ (hs : SES i p) (n : ℕ) : S i n →ₗ[R] A.H (n + 1) :=
  (Submodule.mkQ _).comp ((pre i p hs n).codRestrict (A.Z (n + 1)) (fun b => pre_d i p hs n b))
theorem pS_mem (hs : SES i p) (n : ℕ) (b : S i n) : C.d n (p.f n b) = 0 := by
  have hb : B.d n b ∈ LinearMap.range (i.f (n + 1)) := b.2
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hb
  rw [← p.comm, ← ha, p_i i p hs]
def pS (hs : SES i p) (n : ℕ) : S i n →ₗ[R] C.H n :=
  (Submodule.mkQ _).comp (((p.f n).comp (S i n).subtype).codRestrict (C.Z n)
    (fun b => pS_mem i p hs n b))
theorem θ_apply (hs : SES i p) (n : ℕ) (b : S i n) (a : A.X (n + 1)) (ha : A.d (n + 1) a = 0)
    (h : B.d n b = i.f (n + 1) a) : θ i p hs n b = A.cls (n + 1) a ha := by
  have e : pre i p hs n b = a := pre_eq i p hs n b a h
  unfold θ Cx.cls
  rw [LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact Subtype.ext e
theorem pS_apply (hs : SES i p) (n : ℕ) (b : S i n) : pS i p hs n b = C.cls n (p.f n b) (pS_mem i p hs n b) := rfl
theorem rep (hs : SES i p) (n : ℕ) (h : C.H n) : ∃ (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0)
    (_ : A.d (n + 1) a = 0), B.d n b = i.f (n + 1) a ∧ h = C.cls n (p.f n b) hc := by
  obtain ⟨c, hc, rfl⟩ := cls_surj C n h
  obtain ⟨b, rfl⟩ := hs.surj n c
  have hdb : p.f (n + 1) (B.d n b) = 0 := by rw [p.comm, hc]
  obtain ⟨a, ha⟩ := (hs.exact (n + 1) (B.d n b)).1 hdb
  have had : A.d (n + 1) a = 0 := by
    apply hs.inj (n + 1 + 1)
    rw [map_zero, i.comm, ha, B.dd]
  exact ⟨b, a, hc, had, ha.symm, rfl⟩
theorem pS_surj (hs : SES i p) (n : ℕ) : Surjective (pS i p hs n) := by
  intro h
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := rep i p hs n h
  exact ⟨⟨b, LinearMap.mem_range.2 ⟨a, hba.symm⟩⟩, rfl⟩
end
end LongExactSequenceMaps
namespace LongExactSequenceMaps
noncomputable section
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
theorem ker_le (hs : SES i p) (n : ℕ) : LinearMap.ker (pS i p hs n) ≤ LinearMap.ker (θ i p hs n) := by
  intro b hb
  rw [LinearMap.mem_ker] at hb ⊢
  rw [pS_apply, cls_eq_zero] at hb
  obtain ⟨a0, ha0⟩ : ∃ a0, B.d n b = i.f (n + 1) (A.d n a0) := by
    cases n with
    | zero =>
      rw [mem_B_zero] at hb
      obtain ⟨a0, ha0⟩ := (hs.exact 0 _).1 hb
      exact ⟨a0, by rw [i.comm, ha0]⟩
    | succ k =>
      rw [mem_B_succ] at hb
      obtain ⟨c', hc'⟩ := hb
      obtain ⟨b', rfl⟩ := hs.surj k c'
      have hp : p.f (k + 1) ((b : B.X (k + 1)) - B.d k b') = 0 := by
        rw [map_sub, p.comm, hc', sub_self]
      obtain ⟨a0, ha0⟩ := (hs.exact (k + 1) _).1 hp
      refine ⟨a0, ?_⟩
      rw [i.comm, ha0, map_sub, B.dd, sub_zero]
  rw [θ_apply i p hs n b (A.d n a0) (A.dd n a0) ha0, cls_eq_zero, mem_B_succ]
  exact ⟨a0, rfl⟩
def conn (hs : SES i p) (n : ℕ) : C.H n →ₗ[R] A.H (n + 1) :=
  ((LinearMap.ker (pS i p hs n)).liftQ (θ i p hs n) (ker_le i p hs n)).comp
    (LinearMap.quotKerEquivOfSurjective (pS i p hs n) (pS_surj i p hs n)).symm.toLinearMap
end
end LongExactSequenceMaps
namespace LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
end LongExactSequenceMaps
end ReciprocityTheory.Coh


