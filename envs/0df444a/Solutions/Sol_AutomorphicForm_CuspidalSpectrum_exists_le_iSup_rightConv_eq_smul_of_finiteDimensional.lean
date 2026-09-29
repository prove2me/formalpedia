-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/012e8e85-6cf2-5cbf-aa3c-272798564397

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace BenchS10

theorem exists_eigen_family {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (K : Submodule ℂ E) [FiniteDimensional ℂ K]
    (hK : ∀ v ∈ K, T v ∈ K) :
    ∃ (d : ℕ) (lam : Fin d → ℝ) (w : Fin d → E),
      (∀ i, w i ∈ K) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, T (w i) = ((lam i : ℝ) : ℂ) • w i) ∧
      ∀ v ∈ K, ∃ coef : Fin d → ℂ, v = ∑ i, coef i • w i := by
  classical
  have hTK := hT.restrict_invariant hK
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Module.finrank ℂ ↥K = d := ⟨_, rfl⟩
  let b := hTK.eigenvectorBasis hd
  refine ⟨d, fun i => hTK.eigenvalues hd i, fun i => (b i : E), fun i => (b i).2, fun i => ?_, fun i => ?_, fun v hv => ?_⟩
  · intro h0
    exact b.orthonormal.ne_zero i (Subtype.ext h0)
  · show T (b i : E) = ((hTK.eigenvalues hd i : ℝ) : ℂ) • (b i : E)
    have h := congrArg Subtype.val (hTK.apply_eigenvectorBasis hd i)
    simp only [LinearMap.coe_restrict_apply, Submodule.coe_smul] at h
    exact h
  · refine ⟨fun i => b.repr ⟨v, hv⟩ i, ?_⟩
    have := congrArg (fun z : ↥K => (z : E)) (b.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm

end BenchS10

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (hXc : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hfin : FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hflat : flat F σ f = f)
    (hpres : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys, rightConv F φ f ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)
    (hinj : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys, rightConv F φ f = 0 → φ = 0) :
    ∃ (n : ℕ) (lam : Fin n → ℂ) (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, E i ≤ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ∧ ∀ φ ∈ E i, rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by
  classical
  haveI := hfin
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  obtain ⟨Tc, -, hsymm, hcomm⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hf hflat

  let ι : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) →ₗ[ℂ] ↥(cuspMemberSubmodule F Φ₀ ξ) := Submodule.inclusion hXc
  let L : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := (toCuspSubcarrier F hΦ₀ σ ξ).comp ι
  have hL_coe : ∀ x : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys), ((L x : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨(x : AdelicGL2 (𝓞 F) F → ℂ), (hXc x.2).1.1.1⟩ :=
    fun x => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    have hmem : (a : AdelicGL2 (𝓞 F) F → ℂ) - b ∈ cuspMemberSubmodule F Φ₀ ξ := (cuspMemberSubmodule F Φ₀ ξ).sub_mem (hXc a.2) (hXc b.2)
    have h1 : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : toCarrier F hΦ₀ σ ξ ⟨(a : AdelicGL2 (𝓞 F) F → ℂ) - b, hmem.1.1.1⟩ = 0 := by
      have := congrArg (fun z : ↥(cuspSubcarrier F hΦ₀ σ ξ) => (z : Carrier F Φ₀ σ)) h1
      simp [hL_coe] at this
      exact this
    exact sub_eq_zero.mp (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _ ⟨hmem.1.1.1, hmem.2⟩ h2)

  let Rf : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) → ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) := fun x => ⟨rightConv F x f, hpres x x.2⟩
  have hLT : ∀ x : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys), Tc (L x) = L (Rf x) := fun x => hcomm (ι x) (hXc (hpres x x.2))
  have hRf_smul : ∀ (r : ℂ) (x : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)), Rf (r • x) = r • Rf x := by
    intro r x
    apply hLinj
    rw [← hLT, L.map_smul, L.map_smul, Tc.map_smul, hLT]

  obtain ⟨K, hKdef⟩ : ∃ K : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), LinearMap.range L = K := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ ↥K := by rw [← hKdef]; infer_instance
  have hKstab : ∀ v ∈ K, (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) v ∈ K := by
    intro v hv
    rw [← hKdef] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    exact ⟨Rf x, (hLT x).symm⟩
  obtain ⟨d, lamR, w, hwK, hw0, hweig, hwspan⟩ :=
    BenchS10.exists_eigen_family (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) hsymm K hKstab
  let lam : Fin d → ℂ := fun i => ((lamR i : ℝ) : ℂ)

  have hwL : ∀ i, ∃ x : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys), L x = w i := by
    intro i
    have h := hwK i
    rw [← hKdef] at h
    exact h
  choose xv hxv using hwL
  have heig : ∀ i, Rf (xv i) = lam i • xv i := by
    intro i
    apply hLinj
    rw [← hLT, L.map_smul, hxv]
    exact hweig i
  have hlam : ∀ i, lam i ≠ 0 := by
    intro i h0
    have h1 : Rf (xv i) = 0 := by rw [heig i, h0, zero_smul]
    have h2 : ((xv i : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)) : AdelicGL2 (𝓞 F) F → ℂ) = 0 :=
      hinj _ (xv i).2 (congrArg (fun z : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) => (z : AdelicGL2 (𝓞 F) F → ℂ)) h1)
    have h3 : xv i = 0 := Subtype.ext h2
    apply hw0 i
    rw [← hxv i, h3, map_zero]
  refine ⟨d, lam, hlam, fun i => ℂ ∙ ((xv i : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)) : AdelicGL2 (𝓞 F) F → ℂ), fun i => ⟨?_, ?_⟩, ?_⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (xv i).2
  · intro φ hφ
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hφ
    have h1 := congrArg (fun z : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) => (z : AdelicGL2 (𝓞 F) F → ℂ)) (hRf_smul r (xv i))
    have h2 := congrArg (fun z : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) => (z : AdelicGL2 (𝓞 F) F → ℂ)) (heig i)
    simp only [Rf, Submodule.coe_smul] at h1 h2
    rw [h1, h2, smul_comm]
  · intro x hx
    have hLx : L ⟨x, hx⟩ ∈ K := by rw [← hKdef]; exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨coef, hcoef⟩ := hwspan _ hLx
    have hsum : (⟨x, hx⟩ : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)) = ∑ i, coef i • xv i := by
      apply hLinj
      rw [hcoef, map_sum]
      simp only [L.map_smul, hxv]
    have hx' : x = ∑ i, coef i • ((xv i : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)) : AdelicGL2 (𝓞 F) F → ℂ) := by
      have := congrArg (fun z : ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys) => (z : AdelicGL2 (𝓞 F) F → ℂ)) hsum
      simpa [Submodule.coe_sum, Submodule.coe_smul] using this
    rw [hx']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

end S_AutomorphicForm_CuspidalSpectrum_exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_le_iSup_rightConv_eq_smul_of_finiteDimensional (solution)
