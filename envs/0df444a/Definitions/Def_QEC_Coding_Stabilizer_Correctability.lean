-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Correctability
-- name    : QEC_Coding_Stabilizer_Correctability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:43:58.577348+00:00
-- url     : https://prove2.me/theorems/d3f7b1b8-6b2b-4443-a80b-da170f79c8b8
-- title:
--   Correctability
-- statement:
--   Definitions and structural lemmas for Correctability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open scoped ComplexConjugate
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def binaryPauliKrausFamily {α : Type v} [Fintype α]
    (E : α → Binary ι) (amp : α → Complex) :
    Semantics.FiniteKrausFamily α
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) := by
  classical
  exact { operator := fun a => amp a • toQubitOperator (E a) }
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end StabilizerCode
end Coding
end QEC


