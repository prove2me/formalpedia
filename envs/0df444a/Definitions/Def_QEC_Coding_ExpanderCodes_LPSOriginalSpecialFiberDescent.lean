-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:22:37.407372+00:00
-- url     : https://prove2.me/theorems/a4b18d31-4fe9-407d-88bf-af71c8e6730c
-- title:
--   LPSOriginal Special Fiber Descent
-- statement:
--   Definitions and structural lemmas for LPSOriginal Special Fiber Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
end
end QEC.Coding.TannerLiftedProduct


