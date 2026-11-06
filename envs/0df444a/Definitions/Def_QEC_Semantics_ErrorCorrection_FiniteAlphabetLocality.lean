-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
-- name    : QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:10:39.877227+00:00
-- url     : https://prove2.me/theorems/3b9887db-9df4-4616-ad56-acde029f6077
-- title:
--   Finite Alphabet Locality
-- statement:
--   Definitions and structural lemmas for Finite Alphabet Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
set_option autoImplicit false
noncomputable section
namespace QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
local instance _p2m_local_instance_ac378d2a8a_23 : Fintype (I → A) := Fintype.ofFinite _
def labelEquiv : (I → A) ≃ Qudit.Label (fun _ : I => Fintype.card A) :=
  Equiv.piCongrRight fun _ => Fintype.equivFin A
def registerUnitary :
    UnitaryTransport (EuclideanSpace Complex (I → A))
      (Qudit.QuditRegister (fun _ : I => Fintype.card A)) where
  toLinearEquiv := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (labelEquiv A I)).toLinearEquiv
  map_inner := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (labelEquiv A I)).inner_map_map
variable {A I}
def localOperator (S : QuditSubsystem (fun _ : I => Fintype.card A))
    (E : Operator S.selectedSystem) : Operator (EuclideanSpace Complex (I → A)) :=
  (registerUnitary A I).symm.conjOperator (S.extendLocalToRegister E)
end QEC.Semantics.FiniteAlphabet


