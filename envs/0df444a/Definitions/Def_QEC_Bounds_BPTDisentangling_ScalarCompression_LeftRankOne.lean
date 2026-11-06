-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:44:57.600499+00:00
-- url     : https://prove2.me/theorems/369ab862-09c1-4fc5-80ab-7548d4fd3320
-- title:
--   Left Rank One
-- statement:
--   Definitions and structural lemmas for Left Rank One, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOne.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOne
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


