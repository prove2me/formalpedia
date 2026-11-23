-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:50.39002+00:00
-- url     : https://prove2.me/theorems/12379b88-665a-4e17-b20a-d9f6e5c7a7a8
-- title:
--   Lintegral Mul Right
-- statement:
--   Definitions and structural lemmas for Lintegral Mul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
namespace GlobalTheory.MinorInt
noncomputable def cutEquiv (ι κ : Type*) :
    (ι ⊕ κ → ι ⊕ κ → ℂ) ≃ₗ[ℝ] ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) where
  toFun y := ((fun j a => conj (y (Sum.inl a) (Sum.inl j)),
    fun c j => conj (y (Sum.inr c) (Sum.inl j))), fun c r => conj (y r (Sum.inr c)))
  invFun x := fun r s => Sum.elim
    (fun j => Sum.elim (fun a => conj (x.1.1 j a)) (fun c => conj (x.1.2 c j)) r)
    (fun c => conj (x.2 c r)) s
  map_add' y y' := by ext <;> simp
  map_smul' t y := by ext <;> simp
  left_inv y := by ext r s; rcases r with r | r <;> rcases s with s | s <;> simp
  right_inv x := by ext <;> simp
end GlobalTheory.MinorInt


