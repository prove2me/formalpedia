-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/05770f3c-2a34-5e36-89af-1df5b9905eb9

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ArchcBochnerEngine

open MeasureTheory Set

theorem integrable_and_integral_eq_of_forall_lintegral
    {Ω A ι : Type*} {B : ι → Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace A] [∀ i, MeasurableSpace (B i)]
    (μ : Measure Ω) (α : Measure A) [SigmaFinite α] (β : ∀ i, Measure (B i)) [∀ i, SigmaFinite (β i)]
    (qa : Ω → A) (hqa : Measurable qa) (qb : ∀ i, Ω → B i) (hqb : ∀ i, Measurable (qb i))
    (P : Set Ω) (hP : MeasurableSet P)
    (H : ∀ (g : A → ℝ≥0∞) (f : ∀ i, B i → ℝ≥0∞), Measurable g → (∀ i, Measurable (f i)) →
      ∫⁻ ω, g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ =
        (∫⁻ a, g a ∂α) * ∏ i, ∫⁻ b, f i b ∂(β i))
    (g : A → ℂ) (f : ∀ i, B i → ℂ) (hg : Integrable g α) (hf : ∀ i, Integrable (f i) (β i)) :
    Integrable (fun ω => g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω) μ ∧
    ∫ ω, g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω ∂μ =
      (∫ a, g a ∂α) * ∏ i, ∫ b, f i b ∂(β i) := by
  classical

  set π : Ω → A × (∀ i, B i) := fun ω => (qa ω, fun i => qb i ω) with hπdef
  have hπ : Measurable π := hqa.prodMk (measurable_pi_lambda _ fun i => hqb i)
  have key : α.prod (Measure.pi β) = Measure.map π (μ.restrict P) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := univ.pi '' univ.pi fun i => {s : Set (B i) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi MeasurableSpace.isPiSystem_measurableSet
      isPiSystem_pi α.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun i => (β i).toFiniteSpanningSetsIn) ?_
    intro s hs t ht
    obtain ⟨t, ht, rfl⟩ := ht
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (mem_univ i)
    have hst : MeasurableSet (s ×ˢ univ.pi t) := hs.prod (MeasurableSet.univ_pi ht')
    rw [Measure.map_apply hπ hst, Measure.restrict_apply (hπ hst), Measure.pi_pi,
      ← lintegral_indicator_one ((hπ hst).inter hP)]
    have hind : (fun ω => (π ⁻¹' (s ×ˢ univ.pi t) ∩ P).indicator (1 : Ω → ℝ≥0∞) ω) =
        fun ω => s.indicator (fun _ => (1 : ℝ≥0∞)) (qa ω) *
          (∏ i, (t i).indicator (fun _ => (1 : ℝ≥0∞)) (qb i ω)) * P.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      funext ω
      by_cases hω : ω ∈ π ⁻¹' (s ×ˢ univ.pi t) ∩ P
      · rw [indicator_of_mem hω]
        obtain ⟨⟨h1, h2⟩, h3⟩ := hω
        rw [indicator_of_mem h1, indicator_of_mem h3, Finset.prod_eq_one fun i _ => indicator_of_mem (h2 i (mem_univ i)) _]
        simp
      · rw [indicator_of_notMem hω]
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, not_and_or, not_forall] at hω
        rcases hω with (h1 | ⟨i, hi⟩) | h3
        · rw [indicator_of_notMem h1]; simp
        · rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)]; simp
        · rw [indicator_of_notMem h3]; simp
    rw [hind, H _ _ (measurable_const.indicator hs) (fun i => measurable_const.indicator (ht' i))]
    have h1 : ∫⁻ a, s.indicator (fun _ => (1 : ℝ≥0∞)) a ∂α = α s := by
      rw [lintegral_indicator hs, setLIntegral_const, one_mul]
    have h2 : ∀ i, ∫⁻ b, (t i).indicator (fun _ => (1 : ℝ≥0∞)) b ∂(β i) = β i (t i) := fun i => by
      rw [lintegral_indicator (ht' i), setLIntegral_const, one_mul]
    rw [h1]
    congr 1
    exact Finset.prod_congr rfl fun i _ => h2 i

  set F : A × (∀ i, B i) → ℂ := fun p => g p.1 * ∏ i, f i (p.2 i) with hFdef
  have hFint : Integrable F (α.prod (Measure.pi β)) := hg.mul_prod (Integrable.fintype_prod_dep hf)
  have hFval : ∫ p, F p ∂(α.prod (Measure.pi β)) = (∫ a, g a ∂α) * ∏ i, ∫ b, f i b ∂(β i) := by
    rw [hFdef, integral_prod_mul g (fun b : ∀ i, B i => ∏ i, f i (b i)), integral_fintype_prod_eq_prod]

  have hcomp : (fun ω => g (qa ω) * (∏ i, f i (qb i ω)) * P.indicator (fun _ => (1 : ℂ)) ω) =
      P.indicator (F ∘ π) := by
    funext ω
    by_cases hω : ω ∈ P
    · rw [indicator_of_mem hω, indicator_of_mem hω, mul_one]; rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero]
  rw [key] at hFint hFval
  have hFint' : Integrable (F ∘ π) (μ.restrict P) :=
    (integrable_map_measure hFint.aestronglyMeasurable hπ.aemeasurable).mp hFint
  refine ⟨?_, ?_⟩
  · rw [hcomp, integrable_indicator_iff hP]
    exact hFint'
  · rw [hcomp, integral_indicator hP, ← hFval, integral_map hπ.aemeasurable hFint.aestronglyMeasurable]
    rfl

end ArchcBochnerEngine

section SemiLocalCont

open AutomorphicForm

private theorem kb_continuous_generalLinearGroup_map {R S : Type} [CommRing R] [TopologicalSpace R] [CommRing S]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem kb_continuous_semiLocalComponent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : Continuous (semiLocalComponent K L v) :=
  kb_continuous_generalLinearGroup_map (semiLocalEval K L v)
    ((HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).symm.continuous.comp
      (continuous_pi fun w : v.Extension (𝓞 L) => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1))

end SemiLocalCont

set_option synthInstance.maxHeartbeats 400000 in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ κ : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)),
      @IsProbabilityMeasure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) κ ∧
      κ = @Measure.map (adelicMaximalCompact L) (GL (Fin 2) (InfiniteAdeleRing L)) _
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing L))
            (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) (maximalCompactHaar L) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞),
        @Measurable _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) _ g →
        (∀ v ∈ S, @Measurable _ _ (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) →
        ∫⁻ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫⁻ x, g x ∂κ) *
          ∏ v ∈ S, ∫⁻ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v)) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        Integrable g κ →
        (∀ v ∈ S, IntegrableOn (f v) (AutomorphicForm.semiLocalIntegralSet K L v) (AutomorphicForm.semiLocalHaar K L v)) →
        Integrable (fun k : adelicMaximalCompact L => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))))
          (maximalCompactHaar L) ∧
        ∫ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫ x, g x ∂κ) *
          ∏ v ∈ S, ∫ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v) := by
  classical
  obtain ⟨κ, hκp, hκe, hlin⟩ :=
    AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar K L
  refine ⟨κ, hκp, hκe, hlin, fun S g f hg hf => ?_⟩
  letI instA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing L)
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  letI instB : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    fun v => glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI hκp' : IsProbabilityMeasure κ := hκp
  have harch : Measurable fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L) :=
    ((continuous_glArch (𝓞 L) L).comp continuous_subtype_val).measurable
  have hqb : ∀ i : ↥S, Measurable fun k : adelicMaximalCompact L =>
      semiLocalComponent K L i.1 (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) := by
    intro i
    haveI := borelSpace_glBorelOf (L ⊗[K] (i.1).adicCompletion K)
    exact ((kb_continuous_semiLocalComponent K L i.1).comp ((continuous_glFin (𝓞 L) L).comp
      continuous_subtype_val)).measurable

  haveI hfinβ : ∀ i : ↥S,
      IsFiniteMeasure ((semiLocalHaar K L i.1).restrict (semiLocalIntegralSet K L i.1)) := fun i =>
    ⟨by rw [Measure.restrict_apply_univ, semiLocalHaar_semiLocalIntegralSet]; exact ENNReal.one_lt_top⟩

  have H : ∀ (g' : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
      (f' : ∀ i : ↥S, GL (Fin 2) (L ⊗[K] (i.1).adicCompletion K) → ℝ≥0∞),
      Measurable g' → (∀ i, Measurable (f' i)) →
      ∫⁻ k, g' (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
          (∏ i : ↥S, f' i (semiLocalComponent K L i.1 (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))) *
          (Set.univ : Set (adelicMaximalCompact L)).indicator (fun _ => (1 : ℝ≥0∞)) k ∂(maximalCompactHaar L) =
        (∫⁻ a, g' a ∂κ) * ∏ i : ↥S, ∫⁻ b, f' i b ∂((semiLocalHaar K L i.1).restrict
          (semiLocalIntegralSet K L i.1)) := by
    intro g' f' hg' hf'
    let F : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞ :=
      fun v => if h : v ∈ S then f' ⟨v, h⟩ else fun _ => 1
    have hFi : ∀ i : ↥S, F i.1 = f' i := fun i => by
      simp only [F, dif_pos i.2]
    have hF : ∀ v ∈ S, Measurable (F v) := fun v hv => by
      rw [hFi ⟨v, hv⟩]; exact hf' ⟨v, hv⟩
    have h1 := hlin S g' F hg' hF
    simp only [← Finset.prod_coe_sort S] at h1
    simp only [Set.indicator_univ, mul_one, ← hFi]
    convert h1 using 3
  haveI hσβ : ∀ i : ↥S, SigmaFinite ((semiLocalHaar K L i.1).restrict (semiLocalIntegralSet K L i.1)) :=
    fun i => by infer_instance
  have key := ArchcBochnerEngine.integrable_and_integral_eq_of_forall_lintegral (maximalCompactHaar L) κ
    (fun i : ↥S => (semiLocalHaar K L i.1).restrict (semiLocalIntegralSet K L i.1))
    (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) harch
    (fun (i : ↥S) (k : adelicMaximalCompact L) => semiLocalComponent K L i.1 (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
    hqb Set.univ MeasurableSet.univ H g (fun i : ↥S => f i.1) hg (fun i => hf i.1 i.2)
  have hfun : (fun k : adelicMaximalCompact L => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
      ∏ v ∈ S, f v (semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))) =
      fun k : adelicMaximalCompact L => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
        (∏ i : ↥S, f i.1 (semiLocalComponent K L i.1 (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))) *
        (Set.univ : Set (adelicMaximalCompact L)).indicator (fun _ => (1 : ℂ)) k := by
    funext k
    rw [Set.indicator_of_mem (Set.mem_univ k), mul_one, ← Finset.prod_coe_sort S]
  rw [hfun, ← Finset.prod_coe_sort S]
  exact key

end S_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar (solution)
