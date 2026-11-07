-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_Parameters
-- name    : QEC_Coding_QuantumTanner_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:47:23.220229+00:00
-- url     : https://prove2.me/theorems/fc46e2f7-0051-41fe-b356-33d256516e8d
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.Data
open Classical
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
end QEC.Coding.QuantumTanner.Data


