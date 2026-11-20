-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_FixedDataFactorization
-- name    : QEC_Bounds_BPTSeparatedUnion_Factorizations_FixedDataFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:54:58.604195+00:00
-- url     : https://prove2.me/theorems/296cf3d2-8495-4ed0-8e7c-7c6f386394bb
-- title:
--   Fixed Data Factorization
-- statement:
--   Definitions and structural lemmas for Fixed Data Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/FixedDataFactorization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_TransportWitnessFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
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


