-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_TransportFactorizationCore
-- name    : QEC_Bounds_BPTDisentangling_Joint_TransportFactorizationCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:00:37.169199+00:00
-- url     : https://prove2.me/theorems/b2daf03b-1999-4252-bffb-3053fcd5316a
-- title:
--   Transport Factorization Core
-- statement:
--   Definitions and structural lemmas for Transport Factorization Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/TransportFactorizationCore.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Compression
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
namespace BPTCommutingProjectorModel
end BPTCommutingProjectorModel
end Bounds
end QEC


