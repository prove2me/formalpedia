-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:34:39.292475+00:00
-- url     : https://prove2.me/theorems/f0d237fb-019c-4e26-90c9-75b73f2c2f13
-- title:
--   LPSQuaternion Exact Division
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Exact Division, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
def LPSQuaternion.CoordinatesDvd (s : ℤ) (t : LPSQuaternion) : Prop :=
  s ∣ t.a ∧ s ∣ t.b ∧ s ∣ t.c ∧ s ∣ t.d
def lpsQuaternionDiv (s : ℤ) (t : LPSQuaternion) : LPSQuaternion where
  a := t.a / s
  b := t.b / s
  c := t.c / s
  d := t.d / s
end QEC.Coding.TannerLiftedProduct


