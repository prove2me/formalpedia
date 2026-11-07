-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
-- name    : QEC_Coding_QuantumTanner_ExceptionalVertices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:12:48.408767+00:00
-- url     : https://prove2.me/theorems/e0773bde-b66b-467f-95a2-4968edaeb902
-- title:
--   Exceptional Vertices
-- statement:
--   Definitions and structural lemmas for Exceptional Vertices, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExceptionalVertices.lean

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


