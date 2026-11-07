-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
-- name    : QEC_Coding_Stabilizer_HermitianPauli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:11:28.506213+00:00
-- url     : https://prove2.me/theorems/ad3cf5de-4e89-4aaf-8474-5050162001d6
-- title:
--   Hermitian Pauli
-- statement:
--   Definitions and structural lemmas for Hermitian Pauli, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def binaryOverlapSupport (P : Binary ι) : Finset ι :=
  zSupport P ∩ xSupport P
def binaryOverlapCount (P : Binary ι) : Nat :=
  (binaryOverlapSupport P).card
def hermitianPhaseScalar (P : Binary ι) : Complex :=
  Complex.I ^ binaryOverlapCount P
def toHermitianQubitOperator (P : Binary ι) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  hermitianPhaseScalar P • toQubitOperator P
end PauliSymplectic
end Coding
end QEC


