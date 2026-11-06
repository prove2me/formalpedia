-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
-- name    : QEC_Semantics_Instruments_Sequential_BornMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:52:01.552897+00:00
-- url     : https://prove2.me/theorems/7fb9c705-e6b8-4142-88a3-9fc696d1e710
-- title:
--   Born Mass
-- statement:
--   Definitions and structural lemmas for Born Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/BornMass.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Omega -> Type x} [forall outcome, Fintype (kappaTwo outcome)]
variable {Xi : Omega -> Type y} [forall outcome, Fintype (Xi outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
section FixedRawIndex
variable {kappaPrime : Type x} [Fintype kappaPrime]
end FixedRawIndex
end FiniteInstrument
end
end Semantics
end QEC


