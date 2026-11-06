-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutActive
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutActive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:00:08.71345+00:00
-- url     : https://prove2.me/theorems/868c5a5a-fbe4-44cb-9ba2-b7e907ccdc07
-- title:
--   Second Cut Active
-- statement:
--   Definitions and structural lemmas for Second Cut Active, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutActive.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
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


