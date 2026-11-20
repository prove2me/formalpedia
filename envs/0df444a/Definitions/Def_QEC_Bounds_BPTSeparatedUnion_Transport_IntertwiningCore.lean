-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningCore
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:27:20.740715+00:00
-- url     : https://prove2.me/theorems/75a23420-87de-4835-bac4-ed39e96b908d
-- title:
--   Intertwining Core
-- statement:
--   Definitions and structural lemmas for Intertwining Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningCore.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTransportCore
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


