-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part4_QECert
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part4_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:32:47.990967+00:00
-- url     : https://prove2.me/theorems/35c5dcca-96e7-4b52-addc-6c6867b59091
-- title:
--   Fricke integral construction: literal segment 4
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part3_QECert
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToNormal_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalOverlap_localization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
def lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalRationalFrickePullback N hN x.val,
        lpsOriginalIntegerFricke_maps_normalInfinity_to_localized N hN x⟩
      map_one' := Subtype.ext (map_one (lpsOriginalRationalFrickePullback N hN))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalRationalFrickePullback N hN) x.val y.val)
      map_zero' := Subtype.ext (map_zero (lpsOriginalRationalFrickePullback N hN))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalRationalFrickePullback N hN) x.val y.val) }
def lpsOriginalIntegerFrickeLocalizedChartToInfinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Spec (.of (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)) ⟶
      lpsOriginalIntegerNormalSchemeChart N hN true :=
  Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN))
lemma lpsOriginalIntegerFrickeLocalizedChartToInfinity_openImmersion
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    IsOpenImmersion (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedNormalChart_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)))
lemma lpsOriginalIntegerFrickeLocalizedChartToInfinity_range
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Set.range (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN) =
      (PrimeSpectrum.basicOpen
        (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
          (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) :
        Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedNormalChart_localization N hN
  exact PrimeSpectrum.localization_away_comap_range _ _
lemma lpsOriginalIntegerNormalInfinityToLaurent_range
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Set.range (lpsOriginalIntegerNormalSchemeOverlapMap N hN true) =
      (PrimeSpectrum.basicOpen
        (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) :
        Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToLaurent N hN).toAlgebra
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerReciprocalNormalOverlap_localization N hN
  exact PrimeSpectrum.localization_away_comap_range _ _
lemma lpsOriginalIntegerFrickeInfinity_basicOpen_cover
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN)) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    x ∈ PrimeSpectrum.basicOpen
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) ∨
    x ∈ PrimeSpectrum.basicOpen
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let g := algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
  have hc := (lpsOriginalIntegerFrickeReciprocalDenominator_coprime_X _
    (lpsOriginalIntegerPolynomial_monic N hN)).map g
  rcases hc with ⟨a,b,hab⟩
  simp only [PrimeSpectrum.mem_basicOpen]
  by_contra! h
  have h1 := x.asIdeal.add_mem
    (x.asIdeal.mul_mem_left a h.1) (x.asIdeal.mul_mem_left b h.2)
  rw [hab] at h1
  exact x.2.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
def lpsOriginalIntegerFrickeRefinedSchemeChart
    (N : ℕ) [NeZero N] (hN : 0 < N) : Bool → Scheme
  | false => lpsOriginalIntegerNormalSchemeChart N hN false
  | true => Spec (.of (lpsOriginalIntegerFrickeLocalizedNormalChart N hN))
def lpsOriginalIntegerFrickeRefinedChartToGlued
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  cases b with
  | false => exact lpsOriginalIntegerNormalGluedChartMap N hN false
  | true => exact lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true
end
end QEC.Coding.TannerLiftedProduct


