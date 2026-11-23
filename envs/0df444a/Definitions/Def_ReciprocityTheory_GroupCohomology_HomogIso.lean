-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
-- name    : ReciprocityTheory_GroupCohomology_HomogIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:42.993479+00:00
-- url     : https://prove2.me/theorems/a1cd2636-6cfd-47af-9047-fa41088b58d6
-- title:
--   Homog Iso
-- statement:
--   Definitions and structural lemmas for Homog Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean

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
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace HomogeneousCochainIso
theorem hgi_val {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1) ∨
      ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j) := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega
theorem hgi_sign {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (i.succAbove j : ℕ) * (-1) ^ (j.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  rw [← pow_add, ← pow_add]
  rcases hgi_val i j with h | h
  · rw [h, pow_succ]; ring
  · rw [← h, pow_succ]; ring
theorem hd_hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) :
    hd (n + 1) (hd n F) = 0 := by
  funext x
  simp only [hd, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun (i : Fin (n + 3)) (j : Fin (n + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • F fun k => x (i.succAbove (j.succAbove k)))]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_succAbove_predAbove, hgi_sign, neg_smul]
    exact add_neg_cancel _
  · rintro ⟨i, j⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    exact Fin.succAbove_ne i j h.1
  · intros; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def hdL (R : Type u) [CommRing R] {V X : Type u} [AddCommGroup V] [Module R V] (n : ℕ) :
    ((Fin (n + 1) → X) → V) →ₗ[R] ((Fin (n + 2) → X) → V) where
  toFun := hd n
  map_add' F F' := by funext x; simp [hd, Finset.sum_add_distrib]
  map_smul' r F := by
    funext x
    simp only [hd, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
theorem hd_mem (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ)
    (F : (Fin (n + 1) → X) → M.V) (hF : F ∈ hcoch M X n) : hd n F ∈ hcoch M X (n + 1) := by
  refine ⟨?_, fun g x => ?_⟩
  · exact continuous_finsetSum _ fun i _ => (continuous_const_smul ((-1 : ℤ) ^ (i : ℕ))).comp
      (hF.1.comp (continuous_pi fun j => continuous_apply (i.succAbove j)))
  · simp only [hd, hF.2, map_sum, map_zsmul]
def hcx (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] : Cx R where
  X n := hcoch M X n
  d n := (hdL R n).restrict fun F hF => hd_mem M X n F hF
  dd n F := Subtype.ext (hd_hd n F.1)
theorem continuous_partialProd' {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun g : Fin m → G => Fin.partialProd g i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ i ih => simp only [Fin.partialProd_succ]; exact ih.mul (continuous_apply i)
def eFun (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  M.rho (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)
theorem eFun_mem (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) :
    eFun M n f ∈ hcoch M G n := by
  refine ⟨?_, fun g x => ?_⟩
  · exact M.cont.comp (f := fun x : Fin (n + 1) → G => (x 0, f fun i => (x i.castSucc)⁻¹ * x i.succ))
      ((continuous_apply 0).prodMk (hf.comp (continuous_pi fun i =>
        ((continuous_apply _).inv).mul (continuous_apply _))))
  · simp only [eFun, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul,
      Module.End.mul_apply]
def eIso (M : TRep R G) (n : ℕ) : M.coch.X n ≃ₗ[R] hcoch M G n where
  toFun f := ⟨eFun M n f.1, eFun_mem M n f.1 f.2⟩
  map_add' f f' := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((f.1 + f'.1) fun i => _) = _
    rw [Pi.add_apply, map_add]; rfl)
  map_smul' r f := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((r • f.1) fun i => _) = _
    rw [Pi.smul_apply, map_smul]; rfl)
  invFun F := ⟨fun g => F.1 (Fin.partialProd g),
    F.2.1.comp (continuous_pi fun i => continuous_partialProd' i)⟩
  left_inv f := Subtype.ext (funext fun g => by
    simp [eFun, Fin.partialProd_zero, Fin.partialProd_right_inv])
  right_inv F := Subtype.ext (funext fun x => by
    show M.rho (x 0) (F.1 (Fin.partialProd fun i => (x i.castSucc)⁻¹ * x i.succ)) = F.1 x
    rw [← F.2.2]
    conv_rhs => rw [← Fin.partialProd_left_inv x]
    rfl)
end HomogeneousCochainIso
open HomogeneousCochainIso
end
end ReciprocityTheory.Coh


