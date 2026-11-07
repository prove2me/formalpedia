-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:04:22.933245+00:00
-- url     : https://prove2.me/theorems/48a7f2fb-3a7c-4060-8082-ac476f4562fc
-- title:
--   LPSOriginal Integer QExpansion
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer QExpansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section
def lpsOriginalSigmaZSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n=>(ArithmeticFunction.sigma k n:ℤ)
def lpsOriginalSigmaCombinationZSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n=>((5*ArithmeticFunction.sigma 3 n+7*ArithmeticFunction.sigma 5 n)/12:ℕ)
def lpsOriginalDeltaZSeries : PowerSeries ℤ :=
  lpsOriginalSigmaCombinationZSeries+
    PowerSeries.C 100*(lpsOriginalSigmaZSeries 3)^2-
    PowerSeries.C 147*(lpsOriginalSigmaZSeries 5)^2+
    PowerSeries.C 8000*(lpsOriginalSigmaZSeries 3)^3
def lpsOriginalDeltaSlopeZSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n=>lpsOriginalDeltaZSeries.coeff (n+1)
def lpsOriginalE4ZSeries : PowerSeries ℤ :=
  1+PowerSeries.C 240*lpsOriginalSigmaZSeries 3
def lpsOriginalJZSeries : PowerSeries ℤ :=
  lpsOriginalE4ZSeries^3*PowerSeries.invOfUnit lpsOriginalDeltaSlopeZSeries 1
end
end QEC.Coding.TannerLiftedProduct


