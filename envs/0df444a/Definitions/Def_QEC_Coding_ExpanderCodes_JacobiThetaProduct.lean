-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
-- name    : QEC_Coding_ExpanderCodes_JacobiThetaProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:49:57.04541+00:00
-- url     : https://prove2.me/theorems/7facd5c0-9a8f-4149-addf-a9240003655b
-- title:
--   Jacobi Theta Product
-- statement:
--   Definitions and structural lemmas for Jacobi Theta Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
noncomputable def jacobiThetaProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2
noncomputable def rationalIntegerThetaSeries : ℚ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℚ) integerThetaSeries
noncomputable def jacobiEulerSixProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6
noncomputable def jacobiEulerSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2
noncomputable def jacobiEvenMinusProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))
noncomputable def jacobiOddMinusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) ^ 2
noncomputable def jacobiAlternatingThetaProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 - PowerSeries.X ^ (2 * n + 1)) ^ 2
noncomputable def jacobiEvenMinusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2
noncomputable def jacobiAllPlusSquareProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2
noncomputable def jacobiTriangularProduct : ℚ⟦X⟧ :=
  ∏' n : ℕ,
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
      (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2
end QEC.Coding.TannerLiftedProduct


