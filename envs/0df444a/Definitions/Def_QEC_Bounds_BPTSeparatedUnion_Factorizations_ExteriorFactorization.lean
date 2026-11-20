-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ExteriorFactorization
-- name    : QEC_Bounds_BPTSeparatedUnion_Factorizations_ExteriorFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:40:32.529653+00:00
-- url     : https://prove2.me/theorems/be1082f6-80d9-45df-9cdc-4ecfbfc7a6be
-- title:
--   Exterior Factorization
-- statement:
--   Definitions and structural lemmas for Exterior Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ExteriorFactorization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Core
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


