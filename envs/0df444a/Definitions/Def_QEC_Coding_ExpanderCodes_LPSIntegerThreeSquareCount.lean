-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
-- name    : QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:47:12.287222+00:00
-- url     : https://prove2.me/theorems/7214e1f9-4880-4fe3-985d-6b99f77009e7
-- title:
--   LPSInteger Three Square Count
-- statement:
--   Definitions and structural lemmas for LPSInteger Three Square Count, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
def lpsIntegerCircleSquaredDistance (a b : ℤ × ℤ) : ℤ :=
  (b.1-a.1)^2 + (b.2-a.2)^2
def lpsIntegerCircleChordDet (a b c : ℤ × ℤ) : ℤ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)
def lpsNatCircleBoxRank (M L : ℕ) (a : ℕ × ℕ) : ℕ := a.1/L + (M-a.2/L)
def lpsIntegerThreeSquareAbs (a : (ℤ × ℤ) × ℤ) : (ℕ × ℕ) × ℕ :=
  ((a.1.1.natAbs,a.1.2.natAbs),a.2.natAbs)
def lpsIntegerThreeSquareSignedBox (a : (ℕ × ℕ) × ℕ) : Finset ((ℤ × ℤ) × ℤ) :=
  (({(a.1.1 : ℤ), -(a.1.1 : ℤ)} : Finset ℤ).product
    {(a.1.2 : ℤ), -(a.1.2 : ℤ)}).product {(a.2 : ℤ), -(a.2 : ℤ)}
end
end QEC.Coding.TannerLiftedProduct


