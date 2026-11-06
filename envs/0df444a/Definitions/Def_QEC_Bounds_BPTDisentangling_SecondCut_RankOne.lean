-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_RankOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:23:33.87883+00:00
-- url     : https://prove2.me/theorems/f1821779-12ce-492b-8909-9ec28efbcdb1
-- title:
--   Rank One
-- statement:
--   Definitions and structural lemmas for Rank One, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RankOne.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
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


