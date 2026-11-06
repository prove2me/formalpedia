-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
-- name    : QEC_Bounds_BPTDisentangling_Joint_Regrouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:25:15.777341+00:00
-- url     : https://prove2.me/theorems/c28602df-cb95-409b-809a-e38717bb96a3
-- title:
--   Regrouping
-- statement:
--   Definitions and structural lemmas for Regrouping, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def productBlockRegrouping
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
          (Semantics.CompositeSystem N X)) D)
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) := by
  let e1 := (TensorProduct.assocIsometry Complex (Semantics.CompositeSystem A W) N X).symm.rTensor D
  let e2 := TensorProduct.assocIsometry Complex (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N) X D
  let e := e1.trans e2
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        exact e.inner_map_map x y }
end BPTCommutingProjectorModel
end Bounds
end QEC


