-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:03:40.438691+00:00
-- url     : https://prove2.me/theorems/e6db4ccf-14e3-4448-8f5d-74680a280e59
-- title:
--   Prime Reduced Base Change
-- statement:
--   Definitions and structural lemmas for Prime Reduced Base Change, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_constant

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
open scoped TensorProduct
noncomputable section
variable (p : ℕ) [Fact p.Prime]
def primeFrobeniusAlgHom (C : Type*) [CommRing C] [Algebra (ZMod p) C] :
    C →ₐ[ZMod p] C where
  __ := primeAlgebraFrobenius p C
  commutes' := primeAlgebraFrobenius_constant p C
end
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
end
end QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange


