-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:11:07.26616+00:00
-- url     : https://prove2.me/theorems/85122377-50f9-42a4-b3e5-b5432703bb41
-- title:
--   Sector
-- statement:
--   Definitions and structural lemmas for Sector, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def jointBCSectorEmbeddingLeft
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB) pC) D) →ₗ[Complex]
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) D) :=
  TensorProduct.map
    (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) pB.subtype) pC.subtype)
    (1 : Semantics.Operator D)
noncomputable def jointBCSectorEmbeddingRight
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem
      (Semantics.CompositeSystem A pB) (Semantics.CompositeSystem pC D)) →ₗ[Complex]
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem A B) (Semantics.CompositeSystem C D)) :=
  TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) pB.subtype)
    (TensorProduct.map pC.subtype (1 : Semantics.Operator D))
noncomputable def fourFactorJointBCSectorEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
      (Semantics.CompositeSystem pC D)) →ₗ[Complex]
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
  (tensorAssociatorUnitary A B (Semantics.CompositeSystem C D)).toLinearEquiv.toLinearMap.comp
    (jointBCSectorEmbeddingRight pB pC)
noncomputable def fourFactorBCUnitaryTransport
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
  conjugateUnitaryTransport
    (unitaryLTensor A (tensorAssociatorUnitary B C D).symm)
    (unitaryLTensor A (unitaryRTensor E D))
noncomputable def jointBCSectorMiddleEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    (Semantics.CompositeSystem A
      (Semantics.CompositeSystem (Semantics.CompositeSystem pB pC) D)) →ₗ[Complex]
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)) :=
  TensorProduct.map (1 : Semantics.Operator A)
    (TensorProduct.map (submoduleTensorEmbedding pB pC).toLinearMap
      (1 : Semantics.Operator D))
noncomputable def jointBCSectorMiddleTransport
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D))
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem pB pC) D)) :=
  composeUnitaryTransport
    (tensorAssociatorUnitary A pB (Semantics.CompositeSystem pC D))
    (unitaryLTensor A (tensorAssociatorUnitary pB pC D).symm)
noncomputable def jointBCSectorActiveUnitary
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D))
      (Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
        (Semantics.CompositeSystem pC D)) :=
  conjugateUnitaryTransport (jointBCSectorMiddleTransport pB pC)
    (unitaryLTensor A (unitaryRTensor V D))
end BPTCommutingProjectorModel
end Bounds
end QEC


