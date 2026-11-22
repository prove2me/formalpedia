-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:49.42148+00:00
-- url     : https://prove2.me/theorems/ce19a87d-0e06-4d80-bd7c-bb927384bd0b
-- title:
--   Condition Iff Dual Eq Functional
-- statement:
--   Definitions and structural lemmas for Condition Iff Dual Eq Functional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ConditionIffDualEqFunctional.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
section Count
variable {F : Type} [Field F]
noncomputable def dotProductDual (m : ℕ) : (Fin m → F) →ₗ[F] Module.Dual F (Fin m → F) :=
  LinearMap.mk₂ F (fun a b => a ⬝ᵥ b) (fun a b c => add_dotProduct a b c)
    (fun c a b => smul_dotProduct c a b) (fun a b c => dotProduct_add a b c)
    (fun c a b => dotProduct_smul c a b)
noncomputable def functionalWithScalar {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (c : F) :
    ((Fin n → F) × F) →ₗ[F] F :=
  fL.coprod (c • LinearMap.id)
variable [Fintype F]
end Count
section FJ
variable {F : Type} [Field F] [Fintype F]
end FJ
section Onto
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
section FFOnto
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
def unitSmulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]
end FFOnto
end Onto
end Formalism.HermitianLattices.LocalLatticeBases


