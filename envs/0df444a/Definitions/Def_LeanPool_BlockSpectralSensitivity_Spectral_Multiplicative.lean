-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
-- name    : LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:46.672132+00:00
-- url     : https://prove2.me/theorems/f10860ab-5573-43da-9c1a-f18f5ad4d876
-- title:
--   Multiplicative
-- statement:
--   Definitions and structural lemmas for Multiplicative, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.iterBlock_zero
attribute [local simp] BSLambda.iterFun_zero
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
open scoped Matrix
section Blocks
variable {W V : Type*}
def blk (x : Input (W × V)) : W → Input V := Function.curry x
def topBits (g : Input V → Bool) (x : Input (W × V)) : Input W := fun w ↦ g (blk x w)
theorem blk_injective : Function.Injective (blk : Input (W × V) → W → Input V) :=
  Function.curry_injective
variable [DecidableEq W]
def setBlk (x : Input (W × V)) (w : W) (z : Input V) : Input (W × V) :=
  Function.uncurry (Function.update (blk x) w z)
@[simp] theorem blk_setBlk (x : Input (W × V)) (w : W) (z : Input V) :
    blk (setBlk x w z) = Function.update (blk x) w z := rfl
@[simp] theorem setBlk_blk_self (x : Input (W × V)) (w : W) : setBlk x w (blk x w) = x :=
  blk_injective (by simp)
@[simp] theorem setBlk_setBlk (x : Input (W × V)) (w : W) (z z' : Input V) :
    setBlk (setBlk x w z) w z' = setBlk x w z' :=
  blk_injective (by simp)
end Blocks
section Composition
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
noncomputable def fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) : ℝ :=
  Real.sqrt (∑ x : Input (W × V), (if topBits g x = b then ψ x else 0) ^ 2)
def blockEquiv (w : W) :
    Input V × {x : Input (W × V) // blk x w = zeroInput V} ≃ Input (W × V) where
  toFun p := setBlk p.2.1 w p.1
  invFun x := ⟨blk x w, setBlk x w (zeroInput V), Function.update_self w _ (blk x)⟩
  left_inv := by
    rintro ⟨z, x, hx⟩
    simp [← hx]
  right_inv x := by simp
end Composition
end BSLambda


