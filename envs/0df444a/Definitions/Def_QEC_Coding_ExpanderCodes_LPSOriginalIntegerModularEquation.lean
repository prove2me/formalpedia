-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:05:52.09073+00:00
-- url     : https://prove2.me/theorems/0059f409-9621-4cc7-8433-1e2ef00cf6d9
-- title:
--   LPSOriginal Integer Modular Equation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Modular Equation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalClearedAffineCusp (B m : ℕ) (r : ℚ) (q : ℂ) : ℂ :=
  q^(B-m)/Function.Periodic.qParam 1 (r:ℂ)*
    lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (r:ℂ)*q^m)
def lpsOriginalClearedUnivariateSeries
    (N D : ℕ) (K : PowerSeries ℂ) (p : Polynomial ℂ) : PowerSeries ℂ :=
  ∑ i ∈ Finset.range (D+1),
    PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i
def lpsOriginalCuspAnalyticSubring : Subring (ℂ→ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := hf.mul hg
def lpsOriginalCuspTaylorRingHom :
    lpsOriginalCuspAnalyticSubring →+* PowerSeries ℂ where
  toFun f := lpsOriginalTaylorSeries f.val
  map_zero' := lpsOriginalTaylorSeries_zero
  map_one' := lpsOriginalTaylorSeries_one
  map_add' f g := lpsOriginalTaylorSeries_add f.property g.property
  map_mul' f g := lpsOriginalTaylorSeries_mul f.property g.property
def lpsOriginalCuspEvaluateRingHom (q : ℂ) :
    lpsOriginalCuspAnalyticSubring →+* ℂ where
  toFun f := f.val q
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
def lpsOriginalClearedUnivariateCusp
    (N D : ℕ) (p : Polynomial ℂ) : ℂ→ℂ :=
  ∑ i∈Finset.range (D+1), fun q : ℂ =>
    p.coeff i*q^(N*(D-i))*lpsOriginalJQCoefficient (q^N)^i
end
end QEC.Coding.TannerLiftedProduct


