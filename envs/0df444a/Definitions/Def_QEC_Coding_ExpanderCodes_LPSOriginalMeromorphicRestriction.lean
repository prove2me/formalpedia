-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:25:34.118494+00:00
-- url     : https://prove2.me/theorems/586f7235-a768-4f77-a865-ceffd448a185
-- title:
--   LPSOriginal Meromorphic Restriction
-- statement:
--   Definitions and structural lemmas for LPSOriginal Meromorphic Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicRestriction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_chart_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_chart_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicToMeromorphicGerm_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
lemma lpsOriginalFilledInteriorChart_projection_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (τ : ℍ) (hs : letI := lpsOriginalFilledTopology N
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        (lpsOriginalFilledInteriorChart N hN x).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)))) τ := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change Sum.inl (proj τ) ∈ Sum.inl '' (chartAt ℂ x).source at hs
  obtain ⟨a,ha,he⟩ := hs
  have hm : proj τ ∈ (chartAt ℂ x).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ ∈ ((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).source at hm
  have hanalytic := lpsGamma0_localInverse_analytic N hN (r x) τ hm.1
  have heq : (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (proj (UpperHalfPlane.ofComplex z)))) =
      (fun z : ℂ => ((hf.localInverseAt (r x))
        (proj (UpperHalfPlane.ofComplex z)) : ℂ)) := by
    funext z
    change ((chartAt ℂ x).lift_openEmbedding
      (lpsOriginalFilledTopology_interior_openEmbedding N))
      (Sum.inl (proj (UpperHalfPlane.ofComplex z))) = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  rw [heq]
  exact hanalytic
def lpsOriginalFilledChartMeromorphic (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) : Prop :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  ∀ x : LPSOriginalFilledCurve N, ∀ z ∈ (chartAt ℂ x).target,
    MeromorphicAt (F ∘ (chartAt ℂ x).symm) z
def lpsOriginalFilledMeromorphicPullback (N : ℕ)
    (F : LPSOriginalFilledCurve N → ℂ) : ℂ → ℂ :=
  fun z => F (Sum.inl (Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (UpperHalfPlane.ofComplex z)))
lemma lpsOriginalFilledMeromorphicPullback_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    MeromorphicOn (lpsOriginalFilledMeromorphicPullback N F)
      UpperHalfPlane.upperHalfPlaneSet := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro z hz
  let τ : ℍ := ⟨z,hz⟩
  let proj : ℂ → LPSOriginalFilledCurve N := fun w => Sum.inl (Quotient.mk
    (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
      (UpperHalfPlane.ofComplex w))
  let x := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ
  let e := lpsOriginalFilledInteriorChart N hN x
  have he : proj z = Sum.inl x := by
    dsimp [proj,x,τ]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hs : proj z ∈ e.source := by
    rw [he]
    exact lpsOriginalFilledInteriorChart_mem N hN x
  have ha : AnalyticAt ℂ (e ∘ proj) z :=
    lpsOriginalFilledInteriorChart_projection_analytic N hN x τ
      (lpsOriginalFilledInteriorChart_mem N hN x)
  have hm : MeromorphicAt (F ∘ e.symm) (e (proj z)) :=
    hF (Sum.inl x) (e (proj z)) (e.map_source hs)
  have hh := hm.comp_analyticAt (g := e ∘ proj) (x := z) ha
  apply hh.congr
  have hp : ContinuousAt proj z :=
    (lpsOriginalFilledTopology_interior_continuous N).continuousAt.comp
      (continuous_quot_mk.continuousAt.comp
        (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz).continuousAt)
  have hn : ∀ᶠ w in 𝓝 z, proj w ∈ e.source := hp (e.open_source.mem_nhds hs)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with w hw
  change F (e.symm (e (proj w))) = F (proj w)
  rw [e.left_inv hw]
lemma lpsOriginalFilledChartMeromorphic_const
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (c : ℂ) :
    lpsOriginalFilledChartMeromorphic N hN (fun _ => c) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact MeromorphicAt.const c z
lemma lpsOriginalFilledChartMeromorphic_add
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F G : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hG : lpsOriginalFilledChartMeromorphic N hN G) :
    lpsOriginalFilledChartMeromorphic N hN (F+G) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).add (hG x z hz)
lemma lpsOriginalFilledChartMeromorphic_neg
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic N hN (-F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).neg
lemma lpsOriginalFilledChartMeromorphic_mul
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F G : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hG : lpsOriginalFilledChartMeromorphic N hN G) :
    lpsOriginalFilledChartMeromorphic N hN (F*G) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).mul (hG x z hz)
lemma lpsOriginalFilledChartMeromorphic_inv
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic N hN F⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).inv
lemma lpsOriginalUpperHalfMeromorphicGerm_val_inv
    (A : LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) :
    (A⁻¹).val = A.val⁻¹ := by
  by_cases hA : A = 0
  · simp only [hA,inv_zero,ZeroMemClass.coe_zero]
    change ((0 : ℂ → ℂ) : Filter.Germ
      (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) =
      ((0 : ℂ → ℂ)⁻¹ : Filter.Germ
        (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ)
    apply congrArg (fun f : ℂ → ℂ => (f : Filter.Germ
      (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ))
    funext z
    exact inv_zero.symm
  · have hm : A.val * (A⁻¹).val = 1 :=
      congrArg Subtype.val (mul_inv_cancel₀ hA)
    exact (inv_eq_of_mul_eq_one_right hm).symm
def lpsOriginalFilledMeromorphicRestrictionSubfield
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Subfield (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) where
  carrier := {A | ∃ F : LPSOriginalFilledCurve N → ℂ,
    lpsOriginalFilledChartMeromorphic N hN F ∧
      A.val = (lpsOriginalFilledMeromorphicPullback N F :
        Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ)}
  zero_mem' := ⟨0,lpsOriginalFilledChartMeromorphic_const N hN 0,rfl⟩
  one_mem' := ⟨1,lpsOriginalFilledChartMeromorphic_const N hN 1,rfl⟩
  add_mem' := by
    rintro A B ⟨F,hF,hA⟩ ⟨G,hG,hB⟩
    refine ⟨F+G,lpsOriginalFilledChartMeromorphic_add N hN hF hG,?_⟩
    change A.val + B.val = _
    rw [hA,hB]
    rfl
  neg_mem' := by
    rintro A ⟨F,hF,hA⟩
    refine ⟨-F,lpsOriginalFilledChartMeromorphic_neg N hN hF,?_⟩
    change -A.val = _
    rw [hA]
    rfl
  mul_mem' := by
    rintro A B ⟨F,hF,hA⟩ ⟨G,hG,hB⟩
    refine ⟨F*G,lpsOriginalFilledChartMeromorphic_mul N hN hF hG,?_⟩
    change A.val * B.val = _
    rw [hA,hB]
    rfl
  inv_mem' := by
    rintro A ⟨F,hF,hA⟩
    refine ⟨F⁻¹,lpsOriginalFilledChartMeromorphic_inv N hN hF,?_⟩
    rw [lpsOriginalUpperHalfMeromorphicGerm_val_inv,hA]
    rfl
def lpsOriginalFilledMeromorphicRestriction
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
  ⟨⟨(lpsOriginalFilledMeromorphicPullback N F :
      Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ),
    lpsOriginalFilledMeromorphicPullback N F,
    lpsOriginalFilledMeromorphicPullback_meromorphic N hN F hF,rfl⟩,
    F,hF,rfl⟩
lemma lpsOriginalFilledChartMeromorphic_j
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    lpsOriginalFilledChartMeromorphic N hN (lpsOriginalFilledJ N) :=
  lpsOriginalFilledJ_chart_meromorphic N hN
lemma lpsOriginalFilledMeromorphicRestriction_j
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    (lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN) :
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) =
      lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [Filter.self_mem_codiscreteWithin UpperHalfPlane.upperHalfPlaneSet] with z hz
  rw [lpsOriginalFilledMeromorphicPullback,lpsOriginalFilledJ_projection]
  rfl
lemma lpsOriginalFilledChartMeromorphic_jN
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    lpsOriginalFilledChartMeromorphic N hN (lpsOriginalFilledJDilated N hpos) :=
  lpsOriginalFilledJDilated_chart_meromorphic N hpos hN
lemma lpsOriginalFilledMeromorphicRestriction_jN
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    (lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalFilledJDilated N hpos)
      (lpsOriginalFilledChartMeromorphic_jN N hpos hN) :
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) =
      lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalJNHolomorphic N hpos) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [Filter.self_mem_codiscreteWithin UpperHalfPlane.upperHalfPlaneSet] with z hz
  rw [lpsOriginalFilledMeromorphicPullback,lpsOriginalFilledJDilated_projection]
  rfl
lemma lpsOriginalFilledMeromorphicRestriction_constant_mem
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (c : ℂ) :
    algebraMap ℂ (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) c ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
  ⟨fun _ => c,lpsOriginalFilledChartMeromorphic_const N hN c,rfl⟩
lemma lpsOriginalFilledMeromorphicRestriction_j_mem
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  rw [← lpsOriginalFilledMeromorphicRestriction_j N hN]
  exact (lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalFilledJ N)
    (lpsOriginalFilledChartMeromorphic_j N hN)).property
lemma lpsOriginalFilledMeromorphicRestriction_j_polynomial_mem
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (P : Polynomial ℂ) :
    lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalJHolomorphicEval P) ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add,map_add]
    exact (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).add_mem hP hQ
  | monomial n c =>
    simp only [lpsOriginalJHolomorphicEval,Polynomial.aeval_monomial,
      map_mul,map_pow,
      lpsOriginalHolomorphicToMeromorphicGerm_constant]
    exact (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).mul_mem
      (lpsOriginalFilledMeromorphicRestriction_constant_mem N hN c)
      ((lpsOriginalFilledMeromorphicRestrictionSubfield N hN).pow_mem
        (lpsOriginalFilledMeromorphicRestriction_j_mem N hN) n)
lemma lpsOriginalFilledMeromorphicRestriction_j_fraction_mem
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (r : FractionRing (Polynomial ℂ)) :
    lpsOriginalHolomorphicFractionToMeromorphicGerm (lpsOriginalJFractionEmbedding r) ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  obtain ⟨P,Q,hQ,he⟩ := IsFractionRing.div_surjective (Polynomial ℂ) r
  rw [← he,map_div₀,map_div₀,lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
  exact (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).div_mem
    (lpsOriginalFilledMeromorphicRestriction_j_polynomial_mem N hN P)
    (lpsOriginalFilledMeromorphicRestriction_j_polynomial_mem N hN Q)
lemma lpsOriginalGeneratedFunctionField_mem_full_meromorphic
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ x : lpsOriginalGeneratedFunctionField N hpos,
      lpsOriginalHolomorphicFractionToMeromorphicGerm x.val ∈
        lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  have hf : Set.range (algebraMap (FractionRing (Polynomial ℂ))
      LPSOriginalHolomorphicFractionField) ⊆
      (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).comap
        lpsOriginalHolomorphicFractionToMeromorphicGerm := by
    rintro a ⟨r,rfl⟩
    exact lpsOriginalFilledMeromorphicRestriction_j_fraction_mem N hN r
  have hs : ({lpsOriginalJNInFractionField N hpos} :
      Set LPSOriginalHolomorphicFractionField) ⊆
      (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).comap
        lpsOriginalHolomorphicFractionToMeromorphicGerm := by
    rintro a rfl
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJNHolomorphic N hpos)) ∈
        lpsOriginalFilledMeromorphicRestrictionSubfield N hN
    rw [lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
      ← lpsOriginalFilledMeromorphicRestriction_jN N hpos hN]
    exact (lpsOriginalFilledMeromorphicRestriction N hN
      (lpsOriginalFilledJDilated N hpos)
      (lpsOriginalFilledChartMeromorphic_jN N hpos hN)).property
  have ht := IntermediateField.adjoin_le_subfield
    (F := FractionRing (Polynomial ℂ))
    (S := {lpsOriginalJNInFractionField N hpos}) hf hs
  intro x
  exact ht x.property
def lpsOriginalGeneratedToFullMeromorphic
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hpos →+*
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact {
    toFun := fun x => ⟨lpsOriginalHolomorphicFractionToMeromorphicGerm x.val,
      lpsOriginalGeneratedFunctionField_mem_full_meromorphic N hpos hN x⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext (map_mul _ x.val y.val)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
end
end QEC.Coding.TannerLiftedProduct


