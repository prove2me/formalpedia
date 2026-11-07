-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
-- name    : QEC_Coding_QuantumTanner_CayleyLink
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:54:41.654189+00:00
-- url     : https://prove2.me/theorems/1fa2e8a7-2402-413b-9cf4-3e621e09648d
-- title:
--   Cayley Link
-- statement:
--   Definitions and structural lemmas for Cayley Link, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleyLink.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def HasCayleyLinkIdentities (X : LeftRightCayleySquareComplex G A B Square) : Prop :=
  (∀ g side a b, X.link (g, side) (a, b) =
    X.link (X.leftGenerator a * g, !side) (X.leftInverse a, b)) ∧
  (∀ g side a b, X.link (g, side) (a, b) =
    X.link (g * X.rightGenerator b, !side) (a, X.rightInverse b))
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


