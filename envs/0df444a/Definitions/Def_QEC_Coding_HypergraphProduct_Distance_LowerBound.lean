-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
-- name    : QEC_Coding_HypergraphProduct_Distance_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:33:00.912766+00:00
-- url     : https://prove2.me/theorems/cb4e574e-04e4-46e4-b9c5-90eedf74bfa2
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u
def inputDistanceMinimum
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) : WithTop Nat :=
  min
    (min (extendedMinimumDistance (firstCode D))
      (extendedMinimumDistance (secondCode D)))
    (min (extendedMinimumDistance (firstTransposeCode D))
      (extendedMinimumDistance (secondTransposeCode D)))
end QEC.Coding.HypergraphProduct


