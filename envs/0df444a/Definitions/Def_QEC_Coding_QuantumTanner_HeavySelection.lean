-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
-- name    : QEC_Coding_QuantumTanner_HeavySelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:30:32.077543+00:00
-- url     : https://prove2.me/theorems/42bd183c-a043-4985-8274-ca445ad91e55
-- title:
--   Heavy Selection
-- statement:
--   Definitions and structural lemmas for Heavy Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


