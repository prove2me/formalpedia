-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:04.902566+00:00
-- url     : https://prove2.me/theorems/988a4cc1-2a22-4789-8b2e-ad247e13df49
-- title:
--   Symmetric Chain Projected Level Of Pattern
-- statement:
--   Definitions and structural lemmas for Symmetric Chain Projected Level Of Pattern, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.SymChain.PrImage
section Plain
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}
variable (k n c) in

def fixX : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {v | ∀ r x, v.val r (.inl x) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro v w hv hw r x
    have : (v.val * w.val) r (.inl x) = (v.val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hw _ x]
    rw [Units.val_mul, this, Matrix.mul_one, hv]
  inv_mem' := by
    intro v hv r x
    have : ((v⁻¹).val * v.val) r (.inl x) = ((v⁻¹).val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hv _ x]
    rw [Matrix.mul_one, Units.inv_mul] at this
    exact this.symm
end Plain
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}
end GlobalTheory.SymChain.PrImage


