-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:46:08.021852+00:00
-- url     : https://prove2.me/theorems/74758759-a21d-46aa-aa67-52416dbe4dcc
-- title:
--   LPSOriginal Integral Fricke
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part5_QECert
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
set_option backward.isDefEq.respectTransparency false in
/-- The genuine refined charts cover the whole original integer model. -/
lemma lpsOriginalIntegerFrickeRefinedChartToGlued_cover
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalIntegerFrickeRefinedSchemeChart N hN b),
      lpsOriginalIntegerFrickeRefinedChartToGlued N hN b y = x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  cases b with
  | false => exact ⟨false,y,rfl⟩
  | true =>
      rcases lpsOriginalIntegerFrickeInfinity_basicOpen_cover N hN y with hx | hq
      · change y ∈ (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) :
          Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) at hx
        rw [← lpsOriginalIntegerNormalInfinityToLaurent_range N hN] at hx
        obtain ⟨z,hz⟩ := hx
        refine ⟨false,lpsOriginalIntegerNormalSchemeOverlapMap N hN false z, ?_⟩
        have he := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f z)
          (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
        change lpsOriginalIntegerNormalGluedChartMap N hN false
          (lpsOriginalIntegerNormalSchemeOverlapMap N hN false z) =
          lpsOriginalIntegerNormalGluedChartMap N hN true y
        have he' : lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false z) =
          lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true z) := he
        exact he'.trans (congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hz)
      · change y ∈ (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
            (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) :
          Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) at hq
        rw [← lpsOriginalIntegerFrickeLocalizedChartToInfinity_range N hN] at hq
        obtain ⟨z,hz⟩ := hq
        refine ⟨true,z,?_⟩
        change lpsOriginalIntegerNormalGluedChartMap N hN true
          (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN z) =
            lpsOriginalIntegerNormalGluedChartMap N hN true y
        exact congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hz
def lpsOriginalIntegerFrickeRefinedChartMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN false
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN)) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true
set_option backward.isDefEq.respectTransparency false in
/-- The infinity field-valued point is the same literal generic point of the glued model. -/
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_infinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true =
        lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let u := Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalLaurentChart N hN)
    (lpsOriginalGeneratedFunctionFieldQ N hN)))
  have h0 : u ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN false =
      Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) := by
    rw [lpsOriginalIntegerNormalSchemeOverlapMap, ← Spec.map_comp]
    rfl
  have h1 : u ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN true =
      Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) := by
    rw [lpsOriginalIntegerNormalSchemeOverlapMap, ← Spec.map_comp]
    rfl
  have he := congrArg (fun f => u ≫ f) (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
  rw [← Category.assoc, ← Category.assoc, h0, h1] at he
  exact he.symm
def lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN)) ⟶
      lpsOriginalIntegerFrickeRefinedSchemeChart N hN b := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      exact Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN)))
  | true =>
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      exact Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN)))
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN b ≫
      lpsOriginalIntegerFrickeRefinedChartToGlued N hN b =
        lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false => rfl
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN true) = _
      rw [← Category.assoc, ← Spec.map_comp]
      exact lpsOriginalIntegerNormalGeneratedFieldPoint_infinity N hN
set_option backward.isDefEq.respectTransparency false in
/-- Both local maps induce exactly the already proved Fricke action on the original field. -/
lemma lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN b ≫
      lpsOriginalIntegerFrickeRefinedChartMap N hN b =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroFrickePullback N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false) =
        Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap
            (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
              lpsOriginalIntegerNormalGluedChartMap N hN false)
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      rw [← lpsOriginalIntegerNormalGeneratedFieldPoint_infinity N hN]
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN true) =
        Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap
            (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
              lpsOriginalIntegerNormalGluedChartMap N hN true)
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
def lpsOriginalIntegerFrickeRefinedOpenCover
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalGluedScheme N hN).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (lpsOriginalIntegerFrickeRefinedSchemeChart N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued_cover N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN)
lemma lpsOriginalIntegerNormalGluedScheme_separated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalGluedScheme N hN).IsSeparated := by
  let := lpsOriginalIntegerNormalGluedToSpecZ_proper N hN
  constructor
  rw [← terminal.comp_from (lpsOriginalIntegerNormalGluedToSpecZ N hN)]
  infer_instance
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_dominant
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsDominant (lpsOriginalIntegerNormalGeneratedFieldPoint N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN))
  let f := lpsOriginalIntegerNormalGeneratedFieldPoint N hN
  have hη : f (genericPoint Y) = genericPoint X := by
    change lpsOriginalIntegerNormalGluedChartMap N hN false
      (Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) (genericPoint Y)) = _
    rw [lpsOriginalInjectiveSpecMap_generic _ _ _ Subtype.val_injective]
    exact genericPoint_eq_of_isOpenImmersion _
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  rw [← isGenericPoint_def.mp (genericPoint_spec X)]
  apply closure_mono
  intro z hz
  have hz' : z = genericPoint X := Set.mem_singleton_iff.mp hz
  subst z
  exact ⟨genericPoint Y,hη⟩
set_option backward.isDefEq.respectTransparency false in
/-- The two actual local Fricke maps agree on their genuine scheme-theoretic intersection. -/
lemma lpsOriginalIntegerFrickeRefinedChartMap_overlap
    (N : ℕ) [NeZero N] (hN : 0 < N) (i j : Bool) :
    pullback.fst (lpsOriginalIntegerFrickeRefinedChartToGlued N hN i)
      (lpsOriginalIntegerFrickeRefinedChartToGlued N hN j) ≫
        lpsOriginalIntegerFrickeRefinedChartMap N hN i =
    pullback.snd (lpsOriginalIntegerFrickeRefinedChartToGlued N hN i)
      (lpsOriginalIntegerFrickeRefinedChartToGlued N hN j) ≫
        lpsOriginalIntegerFrickeRefinedChartMap N hN j := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_separated N hN
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant N hN
  let := lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN i
  let := lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN j
  let fi := lpsOriginalIntegerFrickeRefinedChartToGlued N hN i
  let fj := lpsOriginalIntegerFrickeRefinedChartToGlued N hN j
  let u := lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN i
  let v := lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN j
  have he : u ≫ fi = v ≫ fj :=
    (lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN i).trans
      (lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN j).symm
  let t := pullback.lift u v he
  let g := pullback.fst fi fj ≫ fi
  let : IsOpenImmersion g := inferInstance
  let : IsReduced (pullback fi fj) := isReduced_of_isOpenImmersion g
  have ht : t ≫ g = lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
    simp only [t,g,pullback.lift_fst_assoc]
    exact lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN i
  let : IsDominant (t ≫ g) := by rw [ht]; infer_instance
  let : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t g
  apply ext_of_isDominant t
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target,
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target]
def lpsOriginalIntegerNormalGluedFricke
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerFrickeRefinedOpenCover N hN).glueMorphisms
    (lpsOriginalIntegerFrickeRefinedChartMap N hN)
    (lpsOriginalIntegerFrickeRefinedChartMap_overlap N hN)
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGluedFricke_chart
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedChartToGlued N hN b ≫
      lpsOriginalIntegerNormalGluedFricke N hN =
        lpsOriginalIntegerFrickeRefinedChartMap N hN b :=
  (lpsOriginalIntegerFrickeRefinedOpenCover N hN).ι_glueMorphisms
    (lpsOriginalIntegerFrickeRefinedChartMap N hN)
    (lpsOriginalIntegerFrickeRefinedChartMap_overlap N hN) b
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_fricke
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint N hN ≫
      lpsOriginalIntegerNormalGluedFricke N hN =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN false,
    Category.assoc, lpsOriginalIntegerNormalGluedFricke_chart]
  exact lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target N hN false
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGluedFricke_involutive
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedFricke N hN ≫ lpsOriginalIntegerNormalGluedFricke N hN =
      𝟙 (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_separated N hN
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant N hN
  apply ext_of_isDominant (lpsOriginalIntegerNormalGeneratedFieldPoint N hN)
  rw [← Category.assoc, lpsOriginalIntegerNormalGeneratedFieldPoint_fricke,
    Category.assoc, lpsOriginalIntegerNormalGeneratedFieldPoint_fricke,
    ← Category.assoc, ← Spec.map_comp, Category.comp_id]
  have he : CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN) ≫
      CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact lpsOriginalRationalFrickePullback_involutive N hN
  rw [he, Spec.map_id, Category.id_comp]
def lpsOriginalIntegerNormalGluedFrickeIso
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedScheme N hN ≅
      lpsOriginalIntegerNormalGluedScheme N hN where
  hom := lpsOriginalIntegerNormalGluedFricke N hN
  inv := lpsOriginalIntegerNormalGluedFricke N hN
  hom_inv_id := lpsOriginalIntegerNormalGluedFricke_involutive N hN
  inv_hom_id := lpsOriginalIntegerNormalGluedFricke_involutive N hN
end
end QEC.Coding.TannerLiftedProduct


