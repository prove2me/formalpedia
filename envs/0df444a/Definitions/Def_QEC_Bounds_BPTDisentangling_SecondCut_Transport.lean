-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:24:49.145399+00:00
-- url     : https://prove2.me/theorems/8b9dc8e9-53d3-40bd-9ec7-e7682074666a
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Transport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
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


