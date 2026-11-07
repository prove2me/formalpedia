-- Prove2me | Definitions.Def_QEC_Locality_CorrectableRegions_OperationalErasureDistance
-- name    : QEC_Locality_CorrectableRegions_OperationalErasureDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:48:58.475619+00:00
-- url     : https://prove2.me/theorems/bb134d02-87b6-4cfd-8e43-ec5a8e68b1a5
-- title:
--   Operational Erasure Distance
-- statement:
--   Definitions and structural lemmas for Operational Erasure Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/OperationalErasureDistance.lean

import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def FiniteOperationalErasureFailureAt
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι)) (n : Nat) : Prop :=
  ∃ S : Semantics.FiniteSubsystem ι,
    S.selected.card = n ∧ ¬ S.ErasureRecoverableFromRegister C
noncomputable def finiteOperationalErasureDistance
    (C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι)) : Nat := by
  classical
  exact if h : ∃ n, FiniteOperationalErasureFailureAt C n then Nat.find h
    else Fintype.card ι + 1
end Locality
end QEC


