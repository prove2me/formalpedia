-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
-- name    : QEC_Semantics_Instruments_Registers_ProductDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:54:39.463076+00:00
-- url     : https://prove2.me/theorems/8a970227-fb04-4692-ac15-db734beb685a
-- title:
--   Product Density
-- statement:
--   Definitions and structural lemmas for Product Density, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
namespace FiniteInstrument
noncomputable def tensorPowerRegisterProductDensity
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat) :
    DensityOperator (Qubit.QubitRegister (Fin attempts × ι)) :=
  (tensorPowerQubitRegisterTransport ι attempts).conjDensity
    (tensorPowerProductInput rho rhoUnit attempts)
end FiniteInstrument
end
end Semantics
end QEC


