-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
-- name    : QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:12:24.734676+00:00
-- url     : https://prove2.me/theorems/1344afd1-491b-4b50-a345-55351dbff74c
-- title:
--   Active Transport
-- statement:
--   Definitions and structural lemmas for Active Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def activeSectorJointBCUnitary
    {B C WB NB WC NC : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC) :=
  conjugateUnitaryTransport (activeSectorCoordinateTransport pB pC UB UC)
    (unitaryLTensor WB (unitaryRTensor U NC))
end BPTCommutingProjectorModel
end Bounds
end QEC


