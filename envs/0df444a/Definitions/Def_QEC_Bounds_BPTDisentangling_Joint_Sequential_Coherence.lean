-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:20:22.6274+00:00
-- url     : https://prove2.me/theorems/28818244-198c-4787-bd13-65a5355ff7c4
-- title:
--   Coherence
-- statement:
--   Definitions and structural lemmas for Coherence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean

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


