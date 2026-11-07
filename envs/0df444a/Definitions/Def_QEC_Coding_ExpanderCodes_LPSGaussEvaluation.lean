-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
-- name    : QEC_Coding_ExpanderCodes_LPSGaussEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:46:58.874703+00:00
-- url     : https://prove2.me/theorems/f49dec75-1d38-4e8c-bc4a-f493c1fe5c06
-- title:
--   LPSGauss Evaluation
-- statement:
--   Definitions and structural lemmas for LPSGauss Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussEvaluation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
def lpsGaussFourthFactor (N : ℕ) : ℤ :=
  if N%2=1 then 1 else if N%4=0 then -4 else 0
end QEC.Coding.TannerLiftedProduct


