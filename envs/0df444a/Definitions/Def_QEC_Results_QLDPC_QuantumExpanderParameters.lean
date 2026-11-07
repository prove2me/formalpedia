-- Prove2me | Definitions.Def_QEC_Results_QLDPC_QuantumExpanderParameters
-- name    : QEC_Results_QLDPC_QuantumExpanderParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:02:23.746843+00:00
-- url     : https://prove2.me/theorems/0bc63eaa-5ec0-449c-9baa-a8fe3c242a71
-- title:
--   Quantum Expander Parameters
-- statement:
--   Definitions and structural lemmas for Quantum Expander Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/QuantumExpanderParameters.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
namespace BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
end BiregularBipartiteGraph
end QEC.Coding.QuantumExpander


