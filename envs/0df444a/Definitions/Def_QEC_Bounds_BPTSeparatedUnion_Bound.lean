-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Bound
-- name    : QEC_Bounds_BPTSeparatedUnion_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:08:38.674216+00:00
-- url     : https://prove2.me/theorems/ac3a1e8b-3354-41b9-ba1e-04a36a542fed
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Bound.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_Factorization
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
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


