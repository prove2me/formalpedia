-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
-- name    : LeanPool_BlockSpectralSensitivity_Defs_Spectral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:57:20.95462+00:00
-- url     : https://prove2.me/theorems/7ab86218-9759-4329-95c8-a617cc9aa51e
-- title:
--   Spectral
-- statement:
--   Definitions and structural lemmas for Spectral, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.zeroInput_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
noncomputable def adj (f : Input V → Bool) : Matrix (Input V) (Input V) ℝ :=
  Matrix.of fun x y => if hammingDist x y = 1 ∧ f x ≠ f y then (1 : ℝ) else 0
lemma adj_apply (f : Input V → Bool) (x y : Input V) :
    adj f x y = if hammingDist x y = 1 ∧ f x ≠ f y then (1 : ℝ) else 0 := rfl
lemma adj_comm (f : Input V → Bool) (x y : Input V) : adj f x y = adj f y x := by
  simp [adj_apply, hammingDist_comm y x, ne_comm]
lemma transpose_adj (f : Input V → Bool) : (adj f)ᵀ = adj f :=
  Matrix.ext fun x y ↦ adj_comm f y x
lemma isHermitian_adj (f : Input V → Bool) : (adj f).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial (adj f)).trans (transpose_adj f)
section DecEq
variable [DecidableEq V]
def nbrs (f : Input V → Bool) (x : Input V) : Finset (Input V) :=
  Finset.univ.filter fun y => hammingDist x y = 1 ∧ f x ≠ f y
noncomputable def lam (f : Input V → Bool) : ℝ := ⨆ i, (isHermitian_adj f).eigenvalues i
end DecEq
end BSLambda


