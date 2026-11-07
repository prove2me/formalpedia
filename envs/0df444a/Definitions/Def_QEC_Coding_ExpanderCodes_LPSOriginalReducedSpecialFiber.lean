-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:31:22.743193+00:00
-- url     : https://prove2.me/theorems/3e1c5efd-6cfe-46d1-8011-7ba2e51c5c4f
-- title:
--   LPSOriginal Reduced Special Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reduced Special Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
open scoped TensorProduct
def quotientPrimeTensorEquiv (C : Type) [CommRing C] (p : ℕ) :
    (C ⧸ Ideal.span {(p : C)}) ≃+* (C ⊗[ℤ] ZMod p) := by
  have hI : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ C) = Ideal.span {(p : C)} := by
    rw [Ideal.map_span,Set.image_singleton,map_natCast]
  exact (Ideal.quotEquivOfEq hI.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (Ideal.span {(p : ℤ)})).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℤ) (A₁ := C))
        (Int.quotientSpanNatEquivZMod p).toIntAlgEquiv).toRingEquiv)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
end
end QEC.Coding.TannerLiftedProduct


