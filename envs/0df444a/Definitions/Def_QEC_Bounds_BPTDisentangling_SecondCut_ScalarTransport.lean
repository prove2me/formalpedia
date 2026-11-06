-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:34:28.29024+00:00
-- url     : https://prove2.me/theorems/829ae381-d8d6-4839-9233-14ec98320856
-- title:
--   Scalar Transport
-- statement:
--   Definitions and structural lemmas for Scalar Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def overlapLeftSubtypeLift
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (p : Submodule Complex B)
    (E : Semantics.Operator (Semantics.CompositeSystem A p)) :
    Semantics.Operator (Semantics.CompositeSystem A B) :=
  let K := TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Kadj := TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  K.comp (E.comp Kadj)
end BPTCommutingProjectorModel
end Bounds
end QEC


