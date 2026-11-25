-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToBlocksMulFinZero
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToBlocksMulFinZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:37.140111+00:00
-- url     : https://prove2.me/theorems/c4a4169b-9654-4799-822a-242ce9aa737b
-- title:
--   To Blocks Mul Fin Zero
-- statement:
--   Definitions and structural lemmas for To Blocks Mul Fin Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ToBlocksMulFinZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ValuativeRel
namespace GlobalTheory.PenVol
variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]
theorem toBlocks_mul_fin_zero (g h : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]
theorem toBlocks_one_fin_zero : (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]
def cosStab (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    Subgroup (GL (n ⊕ Fin 0) k) where
  carrier := {g | g ∈ J ∧ ∀ y : n → k,
    (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨J.mul_mem hg hh, fun y => ?_⟩
    rw [show (g * h).val = g.val * h.val from rfl, toBlocks_mul_fin_zero, ← Matrix.mulVec_mulVec, hg', hh']
  one_mem' := ⟨J.one_mem, fun y => by
    rw [show (1 : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨J.inv_mem hg, fun y => ?_⟩
    have e : g.val.toBlocks₁₁ *ᵥ ((g⁻¹ : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, show g.val * (g⁻¹ : GL (n ⊕ Fin 0) k).val = 1 from g.mul_inv,
        toBlocks_one_fin_zero, Matrix.one_mulVec]
    rw [← hg', e]
end GlobalTheory.PenVol
end


