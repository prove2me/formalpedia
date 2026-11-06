-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
-- name    : QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:40:17.343045+00:00
-- url     : https://prove2.me/theorems/6d812117-1d30-4c8c-9a04-0c17de4fd73b
-- title:
--   Filtered Branch Operator
-- statement:
--   Definitions and structural lemmas for Filtered Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/FilteredBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end FiniteInstrument
end
end Semantics
end QEC


