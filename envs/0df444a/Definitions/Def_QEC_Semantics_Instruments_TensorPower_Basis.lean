-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
-- name    : QEC_Semantics_Instruments_TensorPower_Basis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:44:28.869206+00:00
-- url     : https://prove2.me/theorems/30bb0047-6788-414c-9f12-c68f33522d24
-- title:
--   Basis
-- statement:
--   Definitions and structural lemmas for Basis, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]
noncomputable def tensorPowerBasis (b : OrthonormalBasis β Complex H) : (attempts : Nat) →
    OrthonormalBasis (tensorPowerHistory β attempts) Complex (tensorPowerCarrier H attempts)
  | 0 =>
      (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex).reindex
        (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  | attempts + 1 => b.tensorProduct (tensorPowerBasis b attempts)
def tensorPowerQubitBitstringEquiv (ι : Type u) [Fintype ι] (attempts : Nat) :
    tensorPowerHistory (Qubit.Bitstring ι) attempts ≃
      Qubit.Bitstring (Fin attempts × ι) :=
  (tensorPowerHistoryEquiv (Qubit.Bitstring ι) attempts).trans
    (Equiv.curry (Fin attempts) ι (Fin 2)).symm
noncomputable def tensorPowerQubitRegisterTransport (ι : Type u) [Fintype ι] [DecidableEq ι]
    (attempts : Nat) :
    UnitaryTransport (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin attempts × ι)) := by
  let sourceBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  let targetBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
  let U := sourceBasis.equiv targetBasis (tensorPowerQubitBitstringEquiv ι attempts)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
end FiniteInstrument
end
end Semantics
end QEC


