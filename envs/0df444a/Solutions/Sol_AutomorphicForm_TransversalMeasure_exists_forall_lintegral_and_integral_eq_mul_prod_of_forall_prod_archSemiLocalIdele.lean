-- Prove2me | solution 1 for AutomorphicForm.TransversalMeasure.exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/dae12db4-77d2-59e5-81eb-6e5e92e26667

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt"
p2m_attr_erase "simp" "LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel

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

set_option synthInstance.maxHeartbeats 400000 in
/-!

                               -/
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hbad : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin v = Measure.map (fun x => πs v * x) (Measure.map Subtype.val μN))
    (harch : ∀ v : InfinitePlace K,
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch v = Measure.map Subtype.val μN)
    (hfac : ∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂τ =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin v)) :
    ∃ τA : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ),
      @SigmaFinite (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ) τA ∧
      (∀ g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞, (∀ v, Measurable (g v)) →
        ∫⁻ y, ∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archFibre K L v y) ∂τA =
          ∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch v)) ∧
      (∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
          (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
          @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g → (∀ v ∈ Sf, Measurable (f v)) →
          ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℝ≥0∞)) t ∂τ =
            (∫⁻ y, g y ∂τA) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin v)) ∧
      ∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
        ∀ (g : (InfiniteAdeleRing L)ˣ → ℂ)
          (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℂ),
          Integrable g τA → (∀ v ∈ Sf, Integrable (f v) (τfin v)) →
          Integrable (fun t : (AdeleRing (𝓞 L) L)ˣ =>
              g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
                (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
                Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                    AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                      AutomorphicForm.TransversalMeasure.integralUnits K L v}
                  (fun _ => (1 : ℂ)) t) τ ∧
          ∫ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℂ)) t ∂τ =
            (∫ y, g y ∂τA) * ∏ v ∈ Sf, ∫ x, f v x ∂(τfin v) := by
  classical
  obtain ⟨τA, hσ, h1, h2⟩ :=
    AutomorphicForm.TransversalMeasure.exists_forall_lintegral_eq_lintegral_mul_prod_of_forall_prod_archSemiLocalIdele
      K L Sτ τ τfin τarch πs hgood hbad harch hfac
  refine ⟨τA, hσ, h1, h2, fun Sf hSf g f hg hf => ?_⟩
  letI instA : MeasurableSpace (InfiniteAdeleRing L)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing L)ˣ := ⟨rfl⟩
  letI instI : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ := NumberField.Idele.ideleBorel L
  haveI : BorelSpace (AdeleRing (𝓞 L) L)ˣ := NumberField.Idele.borelSpace_ideleBorel L
  haveI hσA : SigmaFinite τA := hσ
  obtain ⟨-, hfinfacts, -, hopen, -, -, hclosed, -⟩ :=
    NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L

  haveI hσf : ∀ i : ↥Sf, SigmaFinite (τfin i.1) := by
    intro i
    by_cases hv : i.1 ∈ Sτ
    · obtain ⟨μN, hμN, hτ⟩ := hbad i.1 hv
      rw [hτ]
      obtain ⟨htg, hlc, ht2, hsc, -, -⟩ := hfinfacts i.1
      haveI := htg; haveI := hlc; haveI := ht2; haveI := hsc
      haveI : BorelSpace (L ⊗[K] (i.1).adicCompletion K)ˣ := ⟨rfl⟩
      have hcl := hclosed i.1
      haveI : LocallyCompactSpace (AutomorphicForm.TransversalMeasure.normOneUnits K L i.1) := hcl.locallyCompactSpace
      haveI : SecondCountableTopology (AutomorphicForm.TransversalMeasure.normOneUnits K L i.1) :=
        TopologicalSpace.Subtype.secondCountableTopology _
      haveI : SigmaCompactSpace (AutomorphicForm.TransversalMeasure.normOneUnits K L i.1) :=
        sigmaCompactSpace_of_locallyCompact_secondCountable
      haveI := hμN
      haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
      have hemb : MeasurableEmbedding
          (Subtype.val : (AutomorphicForm.TransversalMeasure.normOneUnits K L i.1) → (L ⊗[K] (i.1).adicCompletion K)ˣ) :=
        MeasurableEmbedding.subtype_coe hcl.measurableSet
      haveI : SigmaFinite (Measure.map Subtype.val μN) := hemb.sigmaFinite_map
      have he : (fun x : (L ⊗[K] (i.1).adicCompletion K)ˣ => πs i.1 * x) =
          ((Homeomorph.mulLeft (πs i.1)).toMeasurableEquiv : (L ⊗[K] (i.1).adicCompletion K)ˣ → (L ⊗[K] (i.1).adicCompletion K)ˣ) := by
        rw [Homeomorph.toMeasurableEquiv_coe]; rfl
      rw [he]
      exact MeasurableEquiv.sigmaFinite_map _
    · obtain ⟨μ, hμ, hτ⟩ := hgood i.1 hv
      rw [hτ]
      haveI : IsFiniteMeasure ((μ (AutomorphicForm.TransversalMeasure.integralUnits K L i.1 :
            Set (L ⊗[K] (i.1).adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L i.1 : Set (L ⊗[K] (i.1).adicCompletion K)ˣ)) :=
        ⟨by
          rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
          exact (ENNReal.inv_mul_le_one _).trans_lt ENNReal.one_lt_top⟩
      exact IsFiniteMeasure.toSigmaFinite _
  have harch' : Measurable fun t : (AdeleRing (𝓞 L) L)ˣ =>
      Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t :=
    (Continuous.units_map _ continuous_fst).measurable
  have hqb : ∀ i : ↥Sf, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t := by
    intro i
    letI : MeasurableSpace (L ⊗[K] (i.1).adicCompletion K)ˣ :=
      AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel K L i.1
    haveI : BorelSpace (L ⊗[K] (i.1).adicCompletion K)ˣ := ⟨rfl⟩
    refine Continuous.measurable ?_
    unfold AutomorphicForm.TransversalMeasure.semiLocalIdele
    refine (Continuous.units_map _ ?_).comp (Continuous.units_map _ continuous_snd)
    exact (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) i.1).symm.continuous.comp
      (continuous_pi fun w : (i.1).Extension (𝓞 L) => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1)
  have hP : MeasurableSet {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
              AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                AutomorphicForm.TransversalMeasure.integralUnits K L v} := (hopen Sf).measurableSet

  have H : ∀ (g' : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
      (f' : ∀ i : ↥Sf, (L ⊗[K] (i.1).adicCompletion K)ˣ → ℝ≥0∞),
      Measurable g' → (∀ i, Measurable (f' i)) →
      ∫⁻ t, g' (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
          (∏ i : ↥Sf, f' i (AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)) *
          Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
              AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℝ≥0∞)) t ∂τ =
        (∫⁻ a, g' a ∂τA) * ∏ i : ↥Sf, ∫⁻ b, f' i b ∂(τfin i.1) := by
    intro g' f' hg' hf'
    let F : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞ :=
      fun v => if h : v ∈ Sf then f' ⟨v, h⟩ else fun _ => 1
    have hFi : ∀ i : ↥Sf, F i.1 = f' i := fun i => by
      simp only [F, dif_pos i.2]
    have hF : ∀ v ∈ Sf, Measurable (F v) := fun v hv => by
      rw [hFi ⟨v, hv⟩]; exact hf' ⟨v, hv⟩
    have h1' := h2 Sf hSf g' F hg' hF
    simp only [← Finset.prod_coe_sort Sf] at h1'
    simp only [← hFi]
    convert h1' using 3
  have key := ArchcBochnerEngine.integrable_and_integral_eq_of_forall_lintegral τ τA
    (fun i : ↥Sf => τfin i.1)
    (fun t : (AdeleRing (𝓞 L) L)ˣ => Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t)
    harch' (fun (i : ↥Sf) (t : (AdeleRing (𝓞 L) L)ˣ) => AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)
    hqb _ hP H g (fun i : ↥Sf => f i.1) hg (fun i => hf i.1 i.2)
  obtain ⟨hint, hval⟩ := key
  have hfun : (fun t : (AdeleRing (𝓞 L) L)ˣ =>
      g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
        (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
        Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
              AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℂ)) t) =
      fun t : (AdeleRing (𝓞 L) L)ˣ =>
        g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
        (∏ i : ↥Sf, f i.1 (AutomorphicForm.TransversalMeasure.semiLocalIdele K L i.1 t)) *
        Set.indicator {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
              AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                AutomorphicForm.TransversalMeasure.integralUnits K L v} (fun _ => (1 : ℂ)) t := by
    funext t
    rw [← Finset.prod_coe_sort Sf]
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun, hval, ← Finset.prod_coe_sort Sf]

end S_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele
end P2MW
export P2MW.S_AutomorphicForm_TransversalMeasure_exists_forall_lintegral_and_integral_eq_mul_prod_of_forall_prod_archSemiLocalIdele (solution)
