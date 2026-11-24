-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:53.051142+00:00
-- url     : https://prove2.me/theorems/0cf7107f-277f-478a-94aa-baddf0c76489
-- title:
--   Cert Family
-- statement:
--   Definitions and structural lemmas for Cert Family, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
structure CertFamily (V ι : Type*) [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] where
  /-- The partial assignment cutting out the `i`-th certificate subcube. -/
  P : ι → PartialAssign V
  /-- The common codimension of the certificates. -/
  c : ℕ
  /-- The radius-one certificate-list bound (`A = 3` for the construction). -/
  A : ℕ
  /-- The radius-two certificate-list bound (`B = 7` for the construction). -/
  B : ℕ
  /-- Every certificate has codimension `c`. -/
  codim_eq : ∀ i, (P i).codim = c
  /-- Distinct certificates have exactly one conflicting fixed literal. -/
  uniqueConflict : ∀ i j, i ≠ j → ∃! v, (P i).Conflict (P j) v
  /-- Property (L1) of Section 6. -/
  listOne : ∀ i x, (P i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (P j).dist x = 1).card ≤ A
  /-- Property (L2) of Section 6. -/
  listTwo : ∀ i x, (P i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (P j).dist x ≤ 2).card ≤ B
namespace CertFamily
variable (F : CertFamily V ι)
noncomputable def conflictCoord {i j : ι} (h : i ≠ j) : V := (F.uniqueConflict i j h).choose
def ind : Input V → Bool := PartialAssign.indUnion F.P
@[simp] lemma ind_eq_true_iff {x : Input V} : F.ind x = true ↔ ∃ i, (F.P i).Sat x :=
  PartialAssign.indUnion_eq_true_iff
noncomputable def owner (x : Ones F.ind) : ι := (F.ind_eq_true_iff.1 x.2).choose
end CertFamily
end BSLambda


