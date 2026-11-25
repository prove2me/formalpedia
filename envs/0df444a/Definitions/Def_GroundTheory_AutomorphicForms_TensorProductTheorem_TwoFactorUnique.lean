-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:51.028571+00:00
-- url     : https://prove2.me/theorems/571c7880-1c97-4bb1-ba95-39667e049039
-- title:
--   Two Factor Unique
-- statement:
--   Definitions and structural lemmas for Two Factor Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TwoFactorUnique.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']
def contractRight (l : Dual ℂ V₂) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₁ :=
  TensorProduct.rid ℂ V₁ ∘ₗ TensorProduct.map LinearMap.id l
def contractLeft (l : Dual ℂ V₁) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₂ :=
  TensorProduct.lid ℂ V₂ ∘ₗ TensorProduct.map l LinearMap.id
variable {π₁ : Representation ℂ M₁ V₁} {π₂ : Representation ℂ M₂ V₂}
  {π₁' : Representation ℂ M₁ V₁'} {π₂' : Representation ℂ M₂ V₂'}
end RestrictedTensor
end GroundTheory.Automorphic


