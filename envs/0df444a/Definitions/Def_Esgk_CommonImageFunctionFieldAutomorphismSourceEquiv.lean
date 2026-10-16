-- Prove2me | Definitions.Def_Esgk_CommonImageFunctionFieldAutomorphismSourceEquiv
-- name    : Esgk_CommonImageFunctionFieldAutomorphismSourceEquiv
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:52.527727+00:00
-- url     : https://prove2.me/theorems/3bca8c73-843b-40d6-9d1b-a8ce3d1420fe
-- title:
--   Common-image automorphism after changing the source field
-- statement:
--   Given an algebra isomorphism between two source fields and surjective maps from them into a common target field, this constructs the target automorphism after transporting one source through that isomorphism.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CommonImageFunctionFieldAutomorphism
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

variable {F L₁ L₂ K : Type*}
variable [Field F] [Field L₁] [Field L₂] [Field K]
variable [Algebra F L₁] [Algebra F L₂] [Algebra F K]


noncomputable def commonImageFunctionFieldAutomorphismOfSourceEquiv
    (φ₁ : L₁ →ₐ[F] K)
    (φ₂ : L₂ →ₐ[F] K)
    (e : L₁ ≃ₐ[F] L₂)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂) :
    K ≃ₐ[F] K :=
  commonImageFunctionFieldAutomorphism φ₁ (φ₂.comp e.toAlgHom) hφ₁
    (hφ₂.comp e.surjective)


end Esgk


