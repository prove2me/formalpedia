-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_TransportWitnessFactorization
-- name    : QEC_Bounds_BPTSeparatedUnion_Factorizations_TransportWitnessFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:48:17.649023+00:00
-- url     : https://prove2.me/theorems/31c034a7-4a46-4daa-8f08-bb683ee4154b
-- title:
--   Transport Witness Factorization
-- statement:
--   Definitions and structural lemmas for Transport Witness Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/TransportWitnessFactorization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ExteriorFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportCore
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


