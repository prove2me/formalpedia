-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
-- name    : QEC_Coding_QuantumTanner_ExpandingDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:43:44.687999+00:00
-- url     : https://prove2.me/theorems/1c875ffe-87ab-4faa-9482-3e3e90a852d1
-- title:
--   Expanding Distance
-- statement:
--   Definitions and structural lemmas for Expanding Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
namespace QEC.Coding.QuantumTanner.Data
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
end QEC.Coding.QuantumTanner.Data


