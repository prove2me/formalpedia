-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
-- name    : QEC_Bounds_BPTDisentangling_Joint_BlockTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:19:57.786381+00:00
-- url     : https://prove2.me/theorems/3f363616-7b42-4656-bf36-c60848beb970
-- title:
--   Block Transport
-- statement:
--   Definitions and structural lemmas for Block Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
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


