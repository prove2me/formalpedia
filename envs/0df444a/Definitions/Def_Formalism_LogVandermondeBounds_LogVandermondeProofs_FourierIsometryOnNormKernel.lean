-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_FourierIsometryOnNormKernel
-- name    : Formalism_LogVandermondeBounds_LogVandermondeProofs_FourierIsometryOnNormKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:43:01.243684+00:00
-- url     : https://prove2.me/theorems/a7c71899-d81a-4838-bd05-d534173f44d5
-- title:
--   Fourier Isometry On Norm Kernel
-- statement:
--   Definitions and structural lemmas for Fourier Isometry On Norm Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/FourierIsometryOnNormKernel.lean

import Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section Helpers
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
def smulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]
end Helpers
end Formalism.LogVandermondeBounds.product_first_zeroth_parts


