-- Prove2me | Definitions.Def_Esgk_CommonImageFunctionFieldAutomorphism
-- name    : Esgk_CommonImageFunctionFieldAutomorphism
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:48.777986+00:00
-- url     : https://prove2.me/theorems/cf0cd2cf-3eab-41db-b2ca-dfb026c76c69
-- title:
--   Automorphism induced by two common field presentations
-- statement:
--   Given two surjective algebra maps from one field into another field, this constructs the induced algebra automorphism of the common target by transporting through the two presentations.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.SimpleRing.Basic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

variable {F L K : Type*}
variable [Field F] [Field L] [Field K]
variable [Algebra F L] [Algebra F K]


noncomputable def commonImageFunctionFieldAutomorphism
    (φ₁ φ₂ : L →ₐ[F] K)
    (hφ₁ : Function.Surjective φ₁)
    (hφ₂ : Function.Surjective φ₂) :
    K ≃ₐ[F] K :=
  (AlgEquiv.ofBijective φ₂ ⟨RingHom.injective φ₂.toRingHom, hφ₂⟩).symm.trans
    (AlgEquiv.ofBijective φ₁ ⟨RingHom.injective φ₁.toRingHom, hφ₁⟩)


end Esgk


