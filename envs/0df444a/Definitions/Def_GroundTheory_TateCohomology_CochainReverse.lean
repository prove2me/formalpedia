-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CochainReverse
-- name    : GroundTheory_TateCohomology_CochainReverse
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:32.127952+00:00
-- url     : https://prove2.me/theorems/77d0967d-4dba-4b1a-b934-0ce5090975d2
-- title:
--   Cochain Reverse
-- statement:
--   Definitions and structural lemmas for Cochain Reverse, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
namespace GroundTheory.GroupCoh
section Signs
def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + (n + 1)
theorem triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := rfl
theorem neg_one_pow_eq_of_mod_two {R : Type*} [Monoid R] [HasDistribNeg R] {a b : ℕ}
    (h : a % 2 = b % 2) : (-1 : R) ^ a = (-1 : R) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    neg_one_sq, one_pow, one_pow, h]
end Signs
section Tuples
variable {G : Type*} [Group G] {n : ℕ}
def revInv (x : Fin n → G) : Fin n → G := fun i => (x i.rev)⁻¹
theorem revInv_apply (x : Fin n → G) (i : Fin n) : revInv x i = (x i.rev)⁻¹ := rfl
theorem tail_revInv (x : Fin (n + 1) → G) : Fin.tail (revInv x) = revInv (Fin.init x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega
theorem init_revInv (x : Fin (n + 1) → G) : Fin.init (revInv x) = revInv (Fin.tail x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega
theorem contractNth_revInv (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.contractNth (Fin.castSucc j) (· * ·) (revInv x) =
      revInv (Fin.contractNth (Fin.castSucc j.rev) (· * ·) x) := by
  funext i
  simp only [Fin.contractNth, revInv_apply, Fin.val_castSucc, Fin.val_rev]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | omega
    | (exact congrArg (fun t => (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))
    | (rw [mul_inv_rev]
       exact congrArg₂ (fun s t => (x s)⁻¹ * (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega))
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))
theorem partialProd_last_contractNth (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.partialProd (Fin.contractNth (Fin.castSucc j) (· * ·) x) (Fin.last n) =
      Fin.partialProd x (Fin.last (n + 1)) := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp [Fin.le_def]
theorem contractNth_last (x : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) x = Fin.init x := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl
theorem tail_revInv' (x : Fin (n + 1) → G) :
    (fun i : Fin n => revInv x i.succ) = revInv (Fin.init x) :=
  tail_revInv x
theorem init_revInv' (x : Fin (n + 1) → G) :
    Fin.init (revInv x) = revInv (fun i : Fin n => x i.succ) :=
  init_revInv x
end Tuples
theorem add_add_eq_add_add {M : Type*} [AddCommMonoid M] {a s c b t d : M} (h₁ : a = d)
    (h₂ : c = b) (h₃ : s = t) : a + (s + c) = b + (t + d) := by
  subst h₁ h₂ h₃
  abel
section Cochains
variable {k G : Type u} [CommRing k] [Group G]
def revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) : (Fin n → G) → A :=
  fun x => (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x))
theorem revCochain_apply {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) (x : Fin n → G) :
    revCochain n f x =
      (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x)) :=
  rfl
theorem d_revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) :
    (inhomogeneousCochains.d A n).hom (revCochain n f) =
      revCochain (n + 1) ((inhomogeneousCochains.d A n).hom f) := by
  funext x
  have hP : Fin.partialProd x (Fin.last (n + 1)) =
      x 0 * Fin.partialProd (fun i : Fin n => x i.succ) (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ']
    rfl
  have hP' : Fin.partialProd x (Fin.last (n + 1)) =
      Fin.partialProd (Fin.init x) (Fin.last n) * x (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ, Fin.partialProd_init]
  simp only [inhomogeneousCochains.d_hom_apply, revCochain_apply, Fin.sum_univ_castSucc,
    Fin.val_last, Fin.val_castSucc, contractNth_last, contractNth_revInv,
    partialProd_last_contractNth, tail_revInv', init_revInv', map_add, map_sum, map_smul,
    smul_add, Finset.smul_sum]
  refine add_add_eq_add_add ?_ ?_ ?_
  · rw [← Module.End.mul_apply, ← map_mul, ← hP, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · rw [revInv_apply, Fin.rev_zero, ← Module.End.mul_apply, ← map_mul, hP', mul_inv_cancel_right,
      smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ, Fin.val_rev]
    have := j.isLt
    omega
variable (A : Rep k G)
def revₗ (n : ℕ) : ((Fin n → G) → A) →ₗ[k] ((Fin n → G) → A) where
  toFun := revCochain n
  map_add' f g := by
    funext x
    simp only [revCochain_apply, Pi.add_apply, map_add, smul_add]
  map_smul' c f := by
    funext x
    simp only [revCochain_apply, Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _
def revHom : inhomogeneousCochains A ⟶ inhomogeneousCochains A where
  f n := ModuleCat.ofHom (revₗ A n)
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [inhomogeneousCochains.d_def]
    exact ModuleCat.hom_ext (LinearMap.ext fun f => d_revCochain i f)
variable {A}
end Cochains
section Cohomology
variable {k G : Type u} [CommRing k] [Group G]
variable {A : Rep k G} {n : ℕ}
end Cohomology
end GroundTheory.GroupCoh


