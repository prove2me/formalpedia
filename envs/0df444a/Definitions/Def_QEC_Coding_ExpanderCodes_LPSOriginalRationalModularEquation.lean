-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:54:17.558575+00:00
-- url     : https://prove2.me/theorems/5a4bee1b-3efc-4388-b17d-643ee1fb0366
-- title:
--   LPSOriginal Rational Modular Equation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Rational Modular Equation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
lemma lpsOriginalRationalRetraction_exists :
    ∃ L : ℂ →ₗ[ℚ] ℚ, L 1=1 := by
  obtain ⟨L, _, hL⟩ := LinearMap.exists_extend_of_notMem
    (0 : (⊥ : Submodule ℚ ℂ) →ₗ[ℚ] ℚ) (v := (1:ℂ))
    (by simp) (1:ℚ)
  exact ⟨L,hL⟩
def lpsOriginalRationalRetraction : ℂ →ₗ[ℚ] ℚ :=
  Classical.choose lpsOriginalRationalRetraction_exists
def lpsOriginalRationalSeriesRetraction (S : PowerSeries ℂ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => lpsOriginalRationalRetraction (S.coeff n)
def lpsOriginalRationalPolynomialRetraction (P : Polynomial ℂ) : Polynomial ℚ :=
  P.sum fun n c=>Polynomial.monomial n (lpsOriginalRationalRetraction c)
def lpsOriginalRationalBivariateRetraction (P : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial ℚ) :=
  P.sum fun n c=>Polynomial.monomial n (lpsOriginalRationalPolynomialRetraction c)
def lpsOriginalClearingBound (N : ℕ) (P : Polynomial (Polynomial ℂ)) : ℕ :=
  P.support.sup fun k=>(P.coeff k).support.sup fun i=>i+N*k
def lpsOriginalClearedMonomial (N B i k : ℕ) (q : ℂ) : ℂ :=
  q^(B-(i+N*k))*lpsOriginalJQCoefficient q^i*lpsOriginalJQCoefficient (q^N)^k
def lpsOriginalClearedFormalMonomial (N : ℕ) (hN : N≠0)
    (B i k : ℕ) : PowerSeries ℚ :=
  PowerSeries.X^(B-(i+N*k))*lpsOriginalJQSeries^i*
    (PowerSeries.expand N hN lpsOriginalJQSeries)^k
def lpsOriginalClearedCusp (N B : ℕ) (P : Polynomial (Polynomial ℂ)) : ℂ→ℂ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun q=> (P.coeff k).coeff i*lpsOriginalClearedMonomial N B i k q
def lpsOriginalClearedRationalCusp (N B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : ℂ→ℂ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun q=> (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*
      lpsOriginalClearedMonomial N B i k q
def lpsOriginalClearedFormal (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : PowerSeries ℚ :=
  ∑ k∈P.support,∑ i∈(P.coeff k).support,
    PowerSeries.C (lpsOriginalRationalRetraction ((P.coeff k).coeff i))*
      lpsOriginalClearedFormalMonomial N hN B i k
end
end QEC.Coding.TannerLiftedProduct


