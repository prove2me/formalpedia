-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
-- name    : LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:59.981381+00:00
-- url     : https://prove2.me/theorems/0815eb3b-3a68-41e9-b471-a233a7d74734
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Examples/CofK/Basic.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
noncomputable instance instVectorLatticeCofK : VectorLattice C(K, ℝ) where
  smul_le_smul_of_nonneg_left {a} ha {b₁ b₂} hb := by
    rw [ContinuousMap.le_def] at hb ⊢
    intro x; simp only [ContinuousMap.smul_apply]
    exact smul_le_smul_of_nonneg_left (hb x) ha
instance instHasSolidNormCofK : HasSolidNorm C(K, ℝ) where
  solid {f g} h := by
    simp only [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_mono ⟨‖g‖, Set.forall_mem_range.mpr
      (fun x => ContinuousMap.norm_coe_le_norm g x)⟩
    intro x
    have := ContinuousMap.le_def.mp h x
    rw [ContinuousMap.abs_apply, ContinuousMap.abs_apply] at this
    exact HasSolidNorm.solid this
noncomputable instance instNormedVectorLatticeCofK :
    NormedVectorLattice C(K, ℝ) where
noncomputable instance instBanachLatticeCofK : BanachLattice C(K, ℝ) where


