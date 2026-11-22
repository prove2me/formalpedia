-- Prove2me | Definitions.Def_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian
-- name    : Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:58.55658+00:00
-- url     : https://prove2.me/theorems/b555526f-97e3-4ccc-b416-3347db5699d2
-- title:
--   Hermitian Tensor Mul Hermitian
-- statement:
--   Definitions and structural lemmas for Hermitian Tensor Mul Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/HermitianTensorMulHermitian.lean

import Definitions.Def_Formalism_FockGram_StatementTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix LinearMap Module TensorProduct
noncomputable section
namespace Formalism.E
example {R M₁ M₂ : Type} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (a : R) (z w : M₁ ⊗[R] M₂) :
    htmul B₁ B₂ (a • z) w = star a * htmul B₁ B₂ z w ∧ htmul B₁ B₂ z (a • w) = a * htmul B₁ B₂ z w := by
  simp [starRingEnd_apply]
example {R M : Type} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) : B.IsSymm ↔ ∀ x y, star (B x y) = B y x := by
  simp [LinearMap.isSymm_def, starRingEnd_apply]
example (n : ℤ) : star n = n := rfl
end Formalism.E


