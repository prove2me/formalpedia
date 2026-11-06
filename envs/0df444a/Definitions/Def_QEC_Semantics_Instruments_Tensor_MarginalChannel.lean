-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
-- name    : QEC_Semantics_Instruments_Tensor_MarginalChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:39:46.511579+00:00
-- url     : https://prove2.me/theorems/4c5b7a6d-c972-46d3-816d-0568bbd7ab99
-- title:
--   Marginal Channel
-- statement:
--   Definitions and structural lemmas for Marginal Channel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
end FiniteInstrument
end
end Semantics
end QEC


