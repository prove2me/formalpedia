-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ActualDataFactorization
-- name    : QEC_Bounds_BPTSeparatedUnion_Factorizations_ActualDataFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:58:57.010584+00:00
-- url     : https://prove2.me/theorems/bdd63f14-ac5f-4078-b803-dc2eae1c1fac
-- title:
--   Actual Data Factorization
-- statement:
--   Definitions and structural lemmas for Actual Data Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ActualDataFactorization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_FixedDataFactorization
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


