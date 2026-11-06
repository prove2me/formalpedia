-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
-- name    : QEC_Bounds_BPTDisentangling_Sectors_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:19:00.675116+00:00
-- url     : https://prove2.me/theorems/85ce00ba-1d0e-4089-b8e4-66654b688593
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Transport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def isotypicSectorBlockTransportLeft
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) C)
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport
        (unitaryRTensor (unitaryLTensor A U) C)
        (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm
noncomputable def isotypicSectorBlockTransportRight
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) C)
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport
        (tensorAssociatorUnitary A H C)
        (unitaryLTensor A (unitaryRTensor U C)))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm
end BPTCommutingProjectorModel
end Bounds
end QEC


