-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
-- name    : LeanPool_QECCertificates_GF2_HGPKunneth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:46:43.765293+00:00
-- url     : https://prove2.me/theorems/bf4b9ad9-0dc5-41e8-a5a7-e9782e33b2ee
-- title:
--   HGPKunneth
-- statement:
--   Definitions and structural lemmas for HGPKunneth, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.vee_apply
attribute [local simp] QECCertificates.wedge_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}
noncomputable def mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) : VMat q s →ₗ[ZMod 2] VMat p s where
  toFun M := fun ij => ∑ a, A ij.1 a * M (a, ij.2)
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro x _
    ring
noncomputable def mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) : VMat p r →ₗ[ZMod 2] VMat p s
    where
  toFun N := fun ij => ∑ t, N (ij.1, t) * B t ij.2
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
def blkL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat n₁ n₂ :=
  fun ab => v (Sum.inl ab)
def blkR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat r₁ r₂ :=
  fun st => v (Sum.inr st)
end QECCertificates


