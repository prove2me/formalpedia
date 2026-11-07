-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:03:16.551193+00:00
-- url     : https://prove2.me/theorems/5938b162-ef62-49a1-80b5-33e71b785a57
-- title:
--   LPSOriginal QExpansion Arithmetic
-- statement:
--   Definitions and structural lemmas for LPSOriginal QExpansion Arithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
def lpsOriginalTaylorSeries (f : ℂ→ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial:ℂ)⁻¹*iteratedDeriv n f 0
def lpsOriginalEisensteinQSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n=0 then 1 else
    -(2*k/bernoulli k:ℚ)*(ArithmeticFunction.sigma (k-1) n)
def lpsOriginalE4CubeSubE6SquareForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (ModularForm.E₄.pow 3)-
    ModularForm.mcast (by decide) (ModularForm.E₆.pow 2)
def lpsOriginalDeltaQSeries : PowerSeries ℚ :=
  PowerSeries.C (1728:ℚ)⁻¹*
    ((lpsOriginalEisensteinQSeries 4)^3-(lpsOriginalEisensteinQSeries 6)^2)
def lpsOriginalDeltaSlopeQSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => lpsOriginalDeltaQSeries.coeff (n+1)
def lpsOriginalJQSeries : PowerSeries ℚ :=
  (lpsOriginalEisensteinQSeries 4)^3*
    PowerSeries.invOfUnit lpsOriginalDeltaSlopeQSeries 1
end
end QEC.Coding.TannerLiftedProduct


