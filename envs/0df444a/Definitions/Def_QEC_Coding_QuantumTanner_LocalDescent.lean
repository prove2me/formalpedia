-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
-- name    : QEC_Coding_QuantumTanner_LocalDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:34:52.993894+00:00
-- url     : https://prove2.me/theorems/40a92ee0-4635-4645-a054-e4e95f210048
-- title:
--   Local Descent
-- statement:
--   Definitions and structural lemmas for Local Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalDescent.lean

import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


