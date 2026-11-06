-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:42:10.449194+00:00
-- url     : https://prove2.me/theorems/80a9b2db-c305-46aa-823b-8e395d07ea48
-- title:
--   Left Probe
-- statement:
--   Definitions and structural lemmas for Left Probe, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftProbe.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
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


