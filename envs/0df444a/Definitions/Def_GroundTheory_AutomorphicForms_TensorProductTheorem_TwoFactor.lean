-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:54.960115+00:00
-- url     : https://prove2.me/theorems/9408ddcc-9b26-44be-888f-7ce9d754c350
-- title:
--   Two Factor
-- statement:
--   Definitions and structural lemmas for Two Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactor.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V : Type*} [AddCommGroup V] [Module ℂ V]
def prodRep (ρ₁ : Representation ℂ M₁ V) (ρ₂ : Representation ℂ M₂ V)
    (hcomm : ∀ a b, ρ₁ a * ρ₂ b = ρ₂ b * ρ₁ a) : Representation ℂ (M₁ × M₂) V where
  toFun p := ρ₁ p.1 * ρ₂ p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc ρ₁ p.1 * ρ₁ q.1 * (ρ₂ p.2 * ρ₂ q.2) = ρ₁ p.1 * (ρ₁ q.1 * ρ₂ p.2) * ρ₂ q.2 := by
          simp only [mul_assoc]
      _ = ρ₁ p.1 * (ρ₂ p.2 * ρ₁ q.1) * ρ₂ q.2 := by rw [hcomm]
      _ = ρ₁ p.1 * ρ₂ p.2 * (ρ₁ q.1 * ρ₂ q.2) := by simp only [mul_assoc]
section Existence
variable {ρ₁ : Representation ℂ M₁ V} {ρ₂ : Representation ℂ M₂ V}
  {hcomm : ∀ a b, ρ₁ a * ρ₂ b = ρ₂ b * ρ₁ a} {e₁ e₂ : End ℂ V}
def tensorForm {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (φ : Dual ℂ V₁) (ψ : Dual ℂ V₂) : Dual ℂ (V₁ ⊗[ℂ] V₂) :=
  TensorProduct.lid ℂ ℂ ∘ₗ TensorProduct.map φ ψ
end Existence
end RestrictedTensor
end GroundTheory.Automorphic


