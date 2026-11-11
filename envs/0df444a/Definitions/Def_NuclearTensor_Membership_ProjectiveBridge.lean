-- Prove2me | Definitions.Def_NuclearTensor_Membership_ProjectiveBridge
-- name    : NuclearTensor_Membership_ProjectiveBridge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:14:29.65294+00:00
-- url     : https://prove2.me/theorems/6db077b8-4713-45d5-ab4d-e1bec7e6074d
-- title:
--   Coordinate realization in Mathlib’s real tensor product
-- statement:
--   A complete real tensor array $M$ determines its algebraic tensor-product element by expansion in the standard orthonormal tensor basis:
--   $$\mathcal T(M)=\sum_I M_I\,e_{I_1}\otimes\cdots\otimes e_{I_k}.$$
--   This explicit coordinate map permits a theorem comparing the source's signed finite-decomposition infimum with Mathlib's projective seminorm. The Euclidean norm used elsewhere remains the Frobenius norm. This map introduces no alternate norm or restricted class of input tensors.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.21, Section 5.1.1 nuclear-norm definition; Mathlib Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean

import Definitions.Def_NuclearTensor_Membership_Geometry

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct

namespace NuclearTensor.Membership

/-- The ordinary tensor-product element represented by the explicit real coefficient array.
This is separate from the Euclidean coordinate norm: Mathlib's tensor norm is projective. -/
def coordinateTensor (d k : ℕ) (M : Tensor (List.replicate k d)) :
    ⨂[ℝ] (_j : Fin k), Vec d :=
  ∑ I : Fin (List.replicate k d).prod, M I •
    PiTensorProduct.tprod ℝ (fun j : Fin k =>
      WithLp.toLp 2 (fun i : Fin d =>
        if i.val = (I.val / d ^ (k - 1 - j.val)) % d then (1 : ℝ) else 0))

end NuclearTensor.Membership


