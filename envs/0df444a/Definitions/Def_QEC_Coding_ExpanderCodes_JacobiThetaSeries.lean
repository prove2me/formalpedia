-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
-- name    : QEC_Coding_ExpanderCodes_JacobiThetaSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:51:22.063048+00:00
-- url     : https://prove2.me/theorems/039e57b3-ad07-4861-9957-1d4b29b66f8c
-- title:
--   Jacobi Theta Series
-- statement:
--   Definitions and structural lemmas for Jacobi Theta Series, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
noncomputable def integerTriangularRoots (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-((n : ℤ)) - 1) (n : ℤ)).filter fun z =>
    z ^ 2 + z = n
noncomputable def rationalBilateralTriangularSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (integerTriangularRoots n).card
noncomputable def rationalTriangularThetaSeries : ℚ⟦X⟧ :=
  PowerSeries.C (1 / 2 : ℚ) * rationalBilateralTriangularSeries
noncomputable def jacobiWeightedTriangularSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z ∈ integerTriangularRoots n, (2 * (z : ℚ) + 1) ^ 2
noncomputable def jacobiWeightedSquareSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z ∈ integerSquareRoots n, (2 * (z : ℚ)) ^ 2
end QEC.Coding.TannerLiftedProduct


