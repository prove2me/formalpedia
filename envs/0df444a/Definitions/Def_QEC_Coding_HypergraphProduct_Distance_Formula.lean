-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
-- name    : QEC_Coding_HypergraphProduct_Distance_Formula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:14:14.532318+00:00
-- url     : https://prove2.me/theorems/c6017e76-2670-43b2-bf31-1473a9bb65c4
-- title:
--   Formula
-- statement:
--   Definitions and structural lemmas for Formula, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Formula.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u
def DistanceEqualityCondition
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) : Prop :=
  (extendedMinimumDistance (firstCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (secondCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (secondCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (firstCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (firstTransposeCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (secondTransposeCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (secondTransposeCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (firstTransposeCode D) ≠ ⊤)
end QEC.Coding.HypergraphProduct


