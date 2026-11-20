-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompression
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:57:32.468322+00:00
-- url     : https://prove2.me/theorems/5a25bb3a-02b2-444d-a846-bb8345fed446
-- title:
--   Region Compression
-- statement:
--   Definitions and structural lemmas for Region Compression, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RegionCompression.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
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


