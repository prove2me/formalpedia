-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
-- name    : QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:07:54.403567+00:00
-- url     : https://prove2.me/theorems/bcf71b90-c290-4dfa-96ff-ee742a33efb0
-- title:
--   QLocal Weight
-- statement:
--   Definitions and structural lemmas for QLocal Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
set_option autoImplicit false
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators
def qBitWeight (a : Field) : Nat := if a = 0 then 0 else 1
def qBitGap (a b : Field) : Nat := if a = b then 0 else 1
def qArmValue (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S)) (copy : Two)
    (z : QStarEdge P q) (i : Nat) : Field :=
  if hi : i < S.half then
    f (copy, qSubdivisionEdgeStart P q S (z, ⟨i, hi⟩))
  else f (copy, Sum.inl (Sum.inr z))
noncomputable def qArmWeight (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (copy : Two) (z : QStarEdge P q) : Nat :=
  ∑ i : Fin S.half, qBitWeight
    (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f (Sum.inl (copy, z, i)))
noncomputable def qLeafWeight (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (f : Word Field (QDoubleCylinderVertex P q S))
    (z : QStarEdge P q) : Nat :=
  qArmWeight P q S f 0 z + qArmWeight P q S f 1 z +
    qBitWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f (Sum.inr z))
end QEC.Coding.BDL26RXLocalReplacement


