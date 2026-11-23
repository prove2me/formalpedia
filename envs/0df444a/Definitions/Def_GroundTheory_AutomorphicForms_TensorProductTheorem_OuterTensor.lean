-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:54.873806+00:00
-- url     : https://prove2.me/theorems/2f2c16a8-d24c-48a5-b4ae-5a4f8b4f8ce2
-- title:
--   Outer Tensor
-- statement:
--   Definitions and structural lemmas for Outer Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
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
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
def outerTensor (ρ₁ : Representation ℂ M₁ V₁) (ρ₂ : Representation ℂ M₂ V₂) :
    Representation ℂ (M₁ × M₂) (V₁ ⊗[ℂ] V₂) where
  toFun p := TensorProduct.map (ρ₁ p.1) (ρ₂ p.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    exact TensorProduct.map_one
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact TensorProduct.map_mul _ _ _ _
end RestrictedTensor
end GroundTheory.Automorphic


