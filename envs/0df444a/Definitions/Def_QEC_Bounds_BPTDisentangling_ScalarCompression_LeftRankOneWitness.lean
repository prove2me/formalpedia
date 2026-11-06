-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:46:16.68729+00:00
-- url     : https://prove2.me/theorems/1a00a098-0a2b-45ee-adc7-75286e09940f
-- title:
--   Left Rank One Witness
-- statement:
--   Definitions and structural lemmas for Left Rank One Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneWitness.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


