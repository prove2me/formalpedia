-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:55:41.303367+00:00
-- url     : https://prove2.me/theorems/26654862-5687-456e-b134-22dfdedc552a
-- title:
--   Left Rank One Product Witness Norm
-- statement:
--   Definitions and structural lemmas for Left Rank One Product Witness Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneProductWitnessNorm.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
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


