-- Prove2me | solution 1 for AutomorphicForm.integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/311a43c9-fd93-5fb7-bdb6-10dac33bdb49

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LT_TwistedNorm_exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
import Theorems.Thm_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open scoped Pointwise ENNReal

namespace P2mUnfoldRegroup

theorem existsUnique_prod_reps {Γ : Type*} [Group Γ] (Λ Λ₀ : Subgroup Γ) (hle : Λ₀ ≤ Λ)
    {ι : Type*} (r : ι → Γ) (hr : ∀ γ, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    {m : ℕ} (s : Fin m → Γ) (hsΛ : ∀ j, s j ∈ Λ) (hs : ∀ l ∈ Λ, ∃! j, (s j)⁻¹ * l ∈ Λ₀) :
    ∀ γ, ∃! p : ι × Fin m, (r p.1 * s p.2)⁻¹ * γ ∈ Λ₀ := by
  intro γ
  obtain ⟨i, hi, hiu⟩ := hr γ
  obtain ⟨j, hj, hju⟩ := hs _ hi
  refine ⟨(i, j), ?_, ?_⟩
  · show (r i * s j)⁻¹ * γ ∈ Λ₀
    rwa [mul_inv_rev, mul_assoc]
  · rintro ⟨i', j'⟩ hp
    have hp' : (s j')⁻¹ * ((r i')⁻¹ * γ) ∈ Λ₀ := by
      have : (r i' * s j')⁻¹ * γ ∈ Λ₀ := hp
      rwa [mul_inv_rev, mul_assoc] at this
    have hi' : (r i')⁻¹ * γ ∈ Λ := by
      have h1 : s j' * ((s j')⁻¹ * ((r i')⁻¹ * γ)) ∈ Λ := Λ.mul_mem (hsΛ j') (hle hp')
      rwa [mul_inv_cancel_left] at h1
    have hii : i' = i := hiu i' hi'
    subst hii
    have hjj : j' = j := hju j' hp'
    subst hjj
    rfl

section Fibre

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem fibre_unfold_lintegral
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓH : Γ ≤ H) [Countable Γ]
    (S : Set G) (hSm : MeasurableSet S) (hS : ∀ γ ∈ Γ, ∀ x : G, γ * x ∈ S ↔ x ∈ S)
    (F₂ : Set G) (hF₂m : MeasurableSet F₂) (hF₂S : F₂ ⊆ S)
    (hcov : ∀ᵐ x ∂(μ.restrict S), ∃ γ : Γ, (γ : G) * x ∈ F₂)
    (hdisj : ∀ γ γ' : Γ, γ ≠ γ' →
      μ ((fun x => (γ : G)⁻¹ * x) ⁻¹' F₂ ∩ (fun x => (γ' : G)⁻¹ * x) ⁻¹' F₂) = 0)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (Ω : Set H) (hΩ : IsFundamentalDomain (Γ.subgroupOf H) Ω μH) :
    ∫⁻ x in F₂, f x ∂μ =
      ∫⁻ q, (∫⁻ h in Ω, S.indicator f ((h : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  set ν := HaarQuotient.measure μ H μH with hν
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  set f₀ : G → ℝ≥0∞ := F₂.indicator f with hf₀
  have hf₀m : Measurable f₀ := hf.indicator hF₂m

  have hA : ∫⁻ x in F₂, f x ∂μ = ∫⁻ q, (∫⁻ x, f₀ ((x : G) * q.out) ∂μH) ∂ν := by
    rw [← lintegral_indicator hF₂m]
    exact HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH f₀ hf₀m

  set Bad : Set G :=
    (S ∩ ⋂ γ : Γ, ((fun x => (γ : G) * x) ⁻¹' F₂)ᶜ) ∪
      ⋃ γ : Γ, ⋃ γ' : Γ, ⋃ (_ : γ ≠ γ'),
        ((fun x => (γ : G)⁻¹ * x) ⁻¹' F₂ ∩ (fun x => (γ' : G)⁻¹ * x) ⁻¹' F₂) with hBad
  have hBadm : MeasurableSet Bad := by
    refine (hSm.inter (MeasurableSet.iInter fun γ => ?_)).union
      (MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun γ' => MeasurableSet.iUnion fun _ => ?_)
    · exact (hF₂m.preimage (measurable_const_mul _)).compl
    · exact (hF₂m.preimage (measurable_const_mul _)).inter (hF₂m.preimage (measurable_const_mul _))
  have hBad0 : μ Bad = 0 := by
    refine measure_union_null ?_ ?_
    · rw [Set.inter_comm, ← Measure.restrict_apply' hSm, measure_eq_zero_iff_ae_notMem]
      filter_upwards [hcov] with x hx
      obtain ⟨γ, hγ⟩ := hx
      simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, not_forall, not_not]
      exact ⟨γ, hγ⟩
    · exact measure_iUnion_null fun γ => measure_iUnion_null fun γ' =>
        measure_iUnion_null fun hne => hdisj γ γ' hne
  have hone : Measurable (Bad.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hBadm
  have hfib : ∀ᵐ q ∂ν, ∀ᵐ (x : H) ∂μH, (x : G) * q.out ∉ Bad := by
    have h1 := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH _ hone
    rw [lintegral_indicator_one hBadm, hBad0] at h1
    have hm := HaarQuotient.measurable_lintegral_mul_out H hH μH _ hone
    filter_upwards [(lintegral_eq_zero_iff hm).1 h1.symm] with q hq
    have hq' : ∫⁻ x, Bad.indicator (1 : G → ℝ≥0∞) ((x : G) * q.out) ∂μH = 0 := hq
    have hm2 : Measurable fun x : H => Bad.indicator (1 : G → ℝ≥0∞) ((x : G) * q.out) :=
      hone.comp (measurable_subtype_coe.mul_const _)
    filter_upwards [(lintegral_eq_zero_iff hm2).1 hq'] with x hx
    have hx' : Bad.indicator (1 : G → ℝ≥0∞) ((x : G) * q.out) = 0 := hx
    intro hmem
    rw [Set.indicator_of_mem hmem, Pi.one_apply] at hx'
    exact one_ne_zero hx'

  have hSΓ : ∀ (γ : Γ.subgroupOf H) (x : H), ((γ • x : H) : G) = ((γ : H) : G) * (x : G) :=
    fun _ _ => rfl
  have hmemΓ : ∀ γ : Γ.subgroupOf H, ((γ : H) : G) ∈ Γ := fun γ => Subgroup.mem_subgroupOf.1 γ.2
  haveI : Countable (Γ.subgroupOf H) :=
    (Subgroup.subgroupOfEquivOfLe hΓH).toEquiv.countable_iff.2 inferInstance
  have key : ∀ᵐ q ∂ν,
      ∫⁻ x, f₀ ((x : G) * q.out) ∂μH = ∫⁻ h in Ω, S.indicator f ((h : G) * q.out) ∂μH := by
    filter_upwards [hfib] with q hq
    set o : G := q.out with ho
    set φ' : H → ℝ≥0∞ := fun x => f ((x : G) * o) with hφ'
    set A : Set H := (fun x : H => (x : G) * o) ⁻¹' F₂ with hA
    set So : Set H := (fun x : H => (x : G) * o) ⁻¹' S with hSo
    have hmo : Measurable fun x : H => (x : G) * o := measurable_subtype_coe.mul_const _
    have hAm : MeasurableSet A := hF₂m.preimage hmo
    have hSom : MeasurableSet So := hSm.preimage hmo
    have hASo : A ⊆ So := fun x hx => hF₂S hx
    have hf₀o : (fun x : H => f₀ ((x : G) * o)) = A.indicator φ' := by
      funext x
      by_cases hx : (x : G) * o ∈ F₂
      · rw [hf₀, Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ A from hx)]
      · rw [hf₀, Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ A from hx)]
    have hSgo : (fun x : H => S.indicator f ((x : G) * o)) = So.indicator φ' := by
      funext x
      by_cases hx : (x : G) * o ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ So from hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ So from hx)]

    have hSo_inv : ∀ (γ : Γ.subgroupOf H) (x : H), γ • x ∈ So ↔ x ∈ So := by
      intro γ x
      show ((γ • x : H) : G) * o ∈ S ↔ (x : G) * o ∈ S
      rw [hSΓ, mul_assoc]
      exact hS _ (hmemΓ γ) _
    have hφ_inv : ∀ (γ : Γ.subgroupOf H) (x : H), So.indicator φ' (γ • x) = So.indicator φ' x := by
      intro γ x
      by_cases hx : x ∈ So
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hSo_inv γ x).2 hx), hφ']
        show f (((γ • x : H) : G) * o) = f ((x : G) * o)
        rw [hSΓ, mul_assoc]
        exact hfΓ _ (hmemΓ γ) _
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (fun h => hx ((hSo_inv γ x).1 h))]

    haveI : SMulInvariantMeasure (Γ.subgroupOf H) H (μH.restrict So) := by
      refine ⟨fun c s hs => ?_⟩
      have hpre : MeasurableSet ((fun x : H => c • x) ⁻¹' s) := hs.preimage (measurable_const_smul c)
      rw [Measure.restrict_apply hpre, Measure.restrict_apply hs]
      have hset : (fun x : H => c • x) ⁻¹' s ∩ So = (fun x : H => c • x) ⁻¹' (s ∩ So) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, hSo_inv]
      rw [hset]
      exact SMulInvariantMeasure.measure_preimage_smul c (hs.inter hSom)
    have hΩ' : IsFundamentalDomain (Γ.subgroupOf H) Ω (μH.restrict So) :=
      hΩ.mono Measure.restrict_le_self.absolutelyContinuous
    have hnull : μH ((fun x : H => (x : G) * o) ⁻¹' Bad) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      exact hq
    have hAfd : IsFundamentalDomain (Γ.subgroupOf H) A (μH.restrict So) := by
      refine ⟨hAm.nullMeasurableSet, ?_, ?_⟩
      · rw [ae_restrict_iff' hSom]
        filter_upwards [hq] with x hx hxS
        have hxS' : (x : G) * o ∈ S := hxS
        have : ¬ ((x : G) * o ∈ S ∩ ⋂ γ : Γ, ((fun y => (γ : G) * y) ⁻¹' F₂)ᶜ) :=
          fun h => hx (Or.inl h)
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage,
          not_and, not_forall, not_not] at this
        obtain ⟨γ, hγ⟩ := this hxS'
        set γH : Γ.subgroupOf H := ⟨⟨(γ : G), hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩ with hγH
        refine ⟨γH, ?_⟩
        show ((γH • x : H) : G) * o ∈ F₂
        rw [hSΓ, mul_assoc]
        exact hγ
      · intro γ γ' hne
        have hne' : (⟨((γ : H) : G), hmemΓ γ⟩ : Γ) ≠ ⟨((γ' : H) : G), hmemΓ γ'⟩ := by
          intro h
          apply hne
          have h' : ((γ : H) : G) = ((γ' : H) : G) := congrArg (fun z : Γ => (z : G)) h
          exact Subtype.ext (Subtype.ext h')
        have hsub : γ • A ∩ γ' • A ⊆ (fun x : H => (x : G) * o) ⁻¹' Bad := by
          rintro x ⟨hx1, hx2⟩
          rw [Set.mem_smul_set_iff_inv_smul_mem] at hx1 hx2
          refine Or.inr (Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨hne', ?_⟩⟩⟩)
          refine ⟨?_, ?_⟩
          · show ((γ : H) : G)⁻¹ * ((x : G) * o) ∈ F₂
            have : ((γ⁻¹ • x : H) : G) * o ∈ F₂ := hx1
            rwa [hSΓ, mul_assoc] at this
          · show ((γ' : H) : G)⁻¹ * ((x : G) * o) ∈ F₂
            have : ((γ'⁻¹ • x : H) : G) * o ∈ F₂ := hx2
            rwa [hSΓ, mul_assoc] at this
        exact Measure.restrict_le_self.absolutelyContinuous (measure_mono_null hsub hnull)

    have hμA : (μH.restrict So).restrict A = μH.restrict A := by
      rw [Measure.restrict_restrict hAm, Set.inter_eq_left.2 hASo]
    have hμΩ : (μH.restrict So).restrict Ω = μH.restrict (Ω ∩ So) := by
      rw [Measure.restrict_restrict' hSom]
    have hEA : ∫⁻ x, f₀ ((x : G) * o) ∂μH = ∫⁻ x in A, So.indicator φ' x ∂(μH.restrict So) := by
      rw [hf₀o, lintegral_indicator hAm, hμA, setLIntegral_indicator hSom, Set.inter_eq_right.2 hASo]
    have hEΩ : ∫⁻ x in Ω, So.indicator φ' x ∂(μH.restrict So) = ∫⁻ x in Ω, So.indicator φ' x ∂μH := by
      rw [hμΩ, setLIntegral_indicator hSom, setLIntegral_indicator hSom,
        show So ∩ (Ω ∩ So) = So ∩ Ω from by rw [Set.inter_comm Ω So, ← Set.inter_assoc, Set.inter_self]]
    rw [hEA, hAfd.setLIntegral_eq hΩ' _ hφ_inv, hEΩ, hSgo]
  rw [hA]
  exact lintegral_congr_ae key

end Fibre

section Adelic

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 (L : Type) [Field L] [NumberField L] :
    BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem countable_GL2 (L : Type) [Field L] [NumberField L] : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

theorem globalPoints_injective (L : Type) [Field L] [NumberField L] :
    Function.Injective (AutomorphicForm.globalPoints (𝓞 L) L) := by
  intro a b h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hij := congrArg
    (fun M : AutomorphicForm.AdelicGL2 (𝓞 L) L => (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) h
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 L) L hij

theorem secondCountableTopology_mulOpposite {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := secondCountableTopology_mulOpposite
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles (L : Type) [Field L] [NumberField L] :
    SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  exact secondCountableTopology_units

theorem lunfold
    (L : Type) [Field L] [NumberField L]
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      AutomorphicForm.globalPoints (𝓞 L) L γ * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S))
    (Λ : Subgroup (GL (Fin 2) L)) {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L)
    (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hH : IsClosed (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (hΛH : Λ.map (AutomorphicForm.globalPoints (𝓞 L) L) ≤ H)
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (f : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hf : Measurable f)
    (hfΛ : ∀ γ ∈ Λ, ∀ x, f (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = f x) :
    ∫⁻ x in Φ₀, ∑' i, f ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫⁻ q, (∫⁻ h in Ω, S.indicator f ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by

  set μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set gp : GL (Fin 2) L →* AutomorphicForm.AdelicGL2 (𝓞 L) L := AutomorphicForm.globalPoints (𝓞 L) L
    with hgp
  set μS : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := μ.restrict S with hμS
  haveI : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaFinite μ := inferInstance
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L
  have inj : Function.Injective gp := globalPoints_injective L
  have injR : Function.Injective gp.rangeRestrict := MonoidHom.rangeRestrict_injective_iff.2 inj
  set Γ₀ : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) := gp.range with hΓ₀
  haveI : Countable Γ₀ := (MonoidHom.rangeRestrict_surjective gp).countable
  set Λ' : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L) := Λ.map gp with hΛ'
  haveI : Countable Λ' := by
    refine (Function.Surjective.countable (f := fun l : Λ => (⟨gp l, Subgroup.mem_map_of_mem gp l.2⟩ : Λ'))
      ?_)
    rintro ⟨x, hx⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨⟨l, hl⟩, rfl⟩
  set Λ₀ : Subgroup Γ₀ := Λ.map gp.rangeRestrict with hΛ₀

  have hSΓ₀ : ∀ (c : Γ₀) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), (c : _) * x ∈ S ↔ x ∈ S := by
    intro c x
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 c.2
    rw [← hγ]
    exact hS γ x
  have hSΛ' : ∀ γ ∈ Λ', ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L, γ * x ∈ S ↔ x ∈ S := by
    intro γ hγ x
    obtain ⟨l, -, rfl⟩ := Subgroup.mem_map.1 hγ
    exact hS l x
  have hfΛ' : ∀ γ ∈ Λ', ∀ x, f (γ * x) = f x := by
    intro γ hγ x
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hγ
    exact hfΛ l hl x

  haveI : SMulInvariantMeasure Γ₀ (AutomorphicForm.AdelicGL2 (𝓞 L) L) μS := by
    refine ⟨fun c s hs => ?_⟩
    have hpre : MeasurableSet ((fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => c • x) ⁻¹' s) :=
      hs.preimage (measurable_const_smul c)
    rw [hμS, Measure.restrict_apply hpre, Measure.restrict_apply hs]
    have hset : (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => c • x) ⁻¹' s ∩ S =
        (fun x => (c : AutomorphicForm.AdelicGL2 (𝓞 L) L) * x) ⁻¹' (s ∩ S) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, hSΓ₀]
      rfl
    rw [hset]
    exact measure_preimage_mul μ _ _

  set R : ι → (⊤ : Subgroup Γ₀) := fun i => ⟨gp.rangeRestrict (r i), Subgroup.mem_top _⟩ with hR
  have hRuniq : ∀ γ : (⊤ : Subgroup Γ₀), ∃! i, ((R i)⁻¹ * γ : Γ₀) ∈ Λ₀ := by
    rintro ⟨γ, -⟩
    obtain ⟨γ', rfl⟩ := MonoidHom.rangeRestrict_surjective gp γ
    obtain ⟨i, hi, huniq⟩ := hr γ'
    refine ⟨i, ?_, fun j hj => huniq j ?_⟩
    · show (gp.rangeRestrict (r i))⁻¹ * gp.rangeRestrict γ' ∈ Λ₀
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hi
    · have hj' : gp.rangeRestrict ((r j)⁻¹ * γ') ∈ Λ₀ := by
        rw [map_mul, map_inv]; exact hj
      exact (Subgroup.mem_map_iff_mem injR).1 hj'
  have hΦ₀' : IsFundamentalDomain (⊤ : Subgroup Γ₀) Φ₀ μS :=
    hΦ₀.preimage_of_equiv (Measure.QuasiMeasurePreserving.id μS)
      (Subgroup.topEquiv : (⊤ : Subgroup Γ₀) ≃* Γ₀).symm.bijective (fun _ _ => rfl)
  have hRsmul : ∀ (i : ι) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      ((R i : Γ₀) : Γ₀)⁻¹ • x = (gp (r i))⁻¹ * x := fun _ _ => rfl
  set F2 : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := ⋃ i, ((R i : Γ₀)⁻¹) • Φ₀ with hF2
  have hF2fd : IsFundamentalDomain Λ₀ F2 μS :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μS ⊤ Λ₀ le_top Φ₀
      hΦ₀' R hRuniq
  have hμSΦ₀ : μS.restrict Φ₀ = μ.restrict Φ₀ := by
    rw [hμS, Measure.restrict_restrict' hSm, Set.inter_eq_left.2 hΦ₀S]
  obtain ⟨hcosetL, hcosetB⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      μS ⊤ Λ₀ le_top Φ₀ hΦ₀' R hRuniq

  have _hpin := fun (h : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) => hcosetB h
  clear _hpin hcosetB
  have hEq : ∫⁻ x in F2, f x ∂μS = ∫⁻ x in Φ₀, ∑' i, f ((gp (r i))⁻¹ * x) ∂μ := by
    have h1 := hcosetL f hf
    rw [hμSΦ₀] at h1
    simp_rw [hRsmul] at h1
    exact h1

  have hF2S : F2 ⊆ S := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hi
    rw [hRsmul, ← map_inv]
    exact (hS _ y).2 (hΦ₀S hy)
  obtain ⟨F₂, hF₂sub, hF₂m, hF₂ae⟩ := hF2fd.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hF₂S : F₂ ⊆ S := hF₂sub.trans hF2S
  have hμSF₂ : μS.restrict F₂ = μ.restrict F₂ := by
    rw [hμS, Measure.restrict_restrict' hSm, Set.inter_eq_left.2 hF₂S]

  have hcovΛ₀ : ∀ᵐ x ∂μS, ∃ γ : Λ₀, γ • x ∈ F₂ := by
    have hD : μS (F2 \ F₂) = 0 := (ae_eq_set.1 hF₂ae).2
    have hall : ∀ᵐ x ∂μS, ∀ γ : Λ₀, γ • x ∉ F2 \ F₂ := by
      rw [ae_all_iff]
      intro γ
      have h0 : μS ((fun x => γ • x) ⁻¹' (F2 \ F₂)) = 0 :=
        (measurePreserving_smul γ μS).quasiMeasurePreserving.preimage_null hD
      rw [measure_eq_zero_iff_ae_notMem] at h0
      exact h0
    filter_upwards [hF2fd.ae_covers, hall] with x hx hx'
    obtain ⟨γ, hγ⟩ := hx
    exact ⟨γ, by_contra fun h => hx' γ ⟨hγ, h⟩⟩
  have hΛ₀mem : ∀ γ : Λ₀, ((γ : Γ₀) : AutomorphicForm.AdelicGL2 (𝓞 L) L) ∈ Λ' := by
    intro γ
    obtain ⟨l, hl, hlγ⟩ := Subgroup.mem_map.1 γ.2
    rw [← hlγ]
    exact Subgroup.mem_map_of_mem gp hl
  have hcov : ∀ᵐ x ∂(μ.restrict S), ∃ γ : Λ', (γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) * x ∈ F₂ := by
    filter_upwards [hcovΛ₀] with x hx
    obtain ⟨γ, hγ⟩ := hx
    exact ⟨⟨_, hΛ₀mem γ⟩, hγ⟩

  have hlift : ∀ a : Λ', ∃ â : Λ₀, ((â : Γ₀) : AutomorphicForm.AdelicGL2 (𝓞 L) L) = a := by
    rintro ⟨a, ha⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨gp.rangeRestrict l, Subgroup.mem_map_of_mem _ hl⟩, rfl⟩
  have hdisj : ∀ γ γ' : Λ', γ ≠ γ' →
      μ ((fun x => (γ : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x) ⁻¹' F₂ ∩
        (fun x => (γ' : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x) ⁻¹' F₂) = 0 := by
    intro γ γ' hne
    obtain ⟨a, ha⟩ := hlift γ
    obtain ⟨b, hb⟩ := hlift γ'
    have hab : a ≠ b := by
      intro h; apply hne; apply Subtype.ext; rw [← ha, ← hb, h]
    have h0 : μS (a • F2 ∩ b • F2) = 0 := hF2fd.aedisjoint hab
    set T := (fun x => (γ : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x) ⁻¹' F₂ ∩
        (fun x => (γ' : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x) ⁻¹' F₂ with hT
    have hTS : T ⊆ S := by
      rintro x ⟨hx, -⟩
      have hx' : (γ : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x ∈ S := hF₂S hx
      exact (hSΛ' _ (inv_mem γ.2) x).1 hx'
    have hTsub : T ⊆ a • F2 ∩ b • F2 := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨Set.mem_smul_set_iff_inv_smul_mem.2 ?_, Set.mem_smul_set_iff_inv_smul_mem.2 ?_⟩
      · show ((a : Γ₀) : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x ∈ F2
        rw [ha]; exact hF₂sub hx1
      · show ((b : Γ₀) : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ * x ∈ F2
        rw [hb]; exact hF₂sub hx2
    have hμT : μ T = μS T := by
      rw [hμS, Measure.restrict_apply' hSm, Set.inter_eq_left.2 hTS]
    rw [hμT]
    exact measure_mono_null hTsub h0

  have h5 := fibre_unfold_lintegral μ H hH μH Λ' hΛH S hSm hSΛ' F₂ hF₂m hF₂S hcov hdisj f hf hfΛ' Ω hΩ
  calc ∫⁻ x in Φ₀, ∑' i, f ((gp (r i))⁻¹ * x) ∂μ
      = ∫⁻ x in F2, f x ∂μS := hEq.symm
    _ = ∫⁻ x in F₂, f x ∂μS := setLIntegral_congr hF₂ae.symm
    _ = ∫⁻ x in F₂, f x ∂μ := by rw [hμSF₂]
    _ = _ := h5

end Adelic

section TwoByTwo

variable {A : Type*} [CommRing A]

theorem val_mul_apply (x y : GL (Fin 2) A) (i j : Fin 2) :
    ((x * y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      (x : Matrix (Fin 2) (Fin 2) A) i 0 * (y : Matrix (Fin 2) (Fin 2) A) 0 j +
        (x : Matrix (Fin 2) (Fin 2) A) i 1 * (y : Matrix (Fin 2) (Fin 2) A) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem val_mul_inv_apply (x : GL (Fin 2) A) (i j : Fin 2) :
    (x : Matrix (Fin 2) (Fin 2) A) i 0 * ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 j +
      (x : Matrix (Fin 2) (Fin 2) A) i 1 * ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 j =
        (1 : Matrix (Fin 2) (Fin 2) A) i j := by
  rw [← val_mul_apply, mul_inv_cancel, Units.val_one]

theorem val_inv_mul_apply (x : GL (Fin 2) A) (i j : Fin 2) :
    ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i 0 * (x : Matrix (Fin 2) (Fin 2) A) 0 j +
      ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i 1 * (x : Matrix (Fin 2) (Fin 2) A) 1 j =
        (1 : Matrix (Fin 2) (Fin 2) A) i j := by
  rw [← val_mul_apply, inv_mul_cancel, Units.val_one]

theorem diag_comm (x y : GL (Fin 2) A)
    (hx10 : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (hx01 : (x : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hy10 : (y : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (hy01 : (y : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) :
    x * y = y * x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [val_mul_apply, val_mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, hx10, hx01, hy10, hy01, mul_zero, zero_mul,
      add_zero, zero_add, mul_comm]

def diagUnit00 (x : GL (Fin 2) A)
    (hx10 : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (hx01 : (x : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) : Aˣ where
  val := (x : Matrix (Fin 2) (Fin 2) A) 0 0
  inv := ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
  val_inv := by
    have h := val_mul_inv_apply x 0 0
    rw [hx01, zero_mul, add_zero, Matrix.one_apply_eq] at h
    exact h
  inv_val := by
    have h := val_inv_mul_apply x 0 0
    rw [hx10, mul_zero, add_zero, Matrix.one_apply_eq] at h
    exact h

theorem weyl_mul_val {K : Type*} [Field K] (x : GL (Fin 2) K) (i j : Fin 2) :
    ((AutomorphicForm.gl2Weyl * x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      (x : Matrix (Fin 2) (Fin 2) K) (if i = 0 then 1 else 0) j := by
  rw [val_mul_apply, AutomorphicForm.gl2Weyl_val]
  fin_cases i <;> simp

theorem mul_weyl_val {K : Type*} [Field K] (x : GL (Fin 2) K) (i j : Fin 2) :
    ((x * AutomorphicForm.gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      (x : Matrix (Fin 2) (Fin 2) K) i (if j = 0 then 1 else 0) := by
  rw [val_mul_apply, AutomorphicForm.gl2Weyl_val]
  fin_cases j <;> simp

theorem weyl_mul_weyl {K : Type*} [Field K] :
    (AutomorphicForm.gl2Weyl * AutomorphicForm.gl2Weyl : GL (Fin 2) K) = 1 := by
  conv_lhs => rw [← AutomorphicForm.gl2Weyl_inv (K := K)]
  exact inv_mul_cancel _

theorem det_val_ne_zero {K : Type*} [Field K] (x : GL (Fin 2) K) :
    (x : Matrix (Fin 2) (Fin 2) K) 0 0 * (x : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) K) 0 1 * (x : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det x).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h

end TwoByTwo

section Stabiliser

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (u : L)
  (Λ Λ₀ : Subgroup (GL (Fin 2) L))
  (hshape : ∀ γ : GL (Fin 2) L, γ ∈ Λ ↔
    (((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 ∧
        σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) * u ^ 2 =
          (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0))
  (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))

include hshape hΛ₀

theorem le_of_shape : Λ₀ ≤ Λ := by
  intro γ hγ
  obtain ⟨h1, h2, h3⟩ := (hΛ₀ γ).1 hγ
  exact (hshape γ).2 (Or.inl ⟨⟨h1, h2⟩, h3⟩)

theorem mem_Λ₀_of_mem_of_apply_one_zero (γ : GL (Fin 2) L) (hγ : γ ∈ Λ)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : γ ∈ Λ₀ := by
  rcases (hshape γ).1 hγ with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2, -⟩
  · exact (hΛ₀ γ).2 ⟨h1, h2, h3⟩
  · exfalso
    apply det_val_ne_zero γ
    rw [h1, h10, zero_mul, mul_zero, sub_zero]

theorem anti_of_mem_of_not_mem (γ : GL (Fin 2) L) (hγ : γ ∈ Λ) (hn : γ ∉ Λ₀) :
    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 ∧
      σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) * u ^ 2 =
        (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0 := by
  rcases (hshape γ).1 hγ with ⟨⟨h1, h2⟩, h3⟩ | h
  · exact absurd ((hΛ₀ γ).2 ⟨h1, h2, h3⟩) hn
  · exact h

theorem existsUnique_fin_two (a : GL (Fin 2) L) (ha : a ∈ Λ)
    (ha00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 = 0) (ha11 : (a : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) :
    ∀ l ∈ Λ, ∃! j : Fin 2, ((![(1 : GL (Fin 2) L), a] : Fin 2 → GL (Fin 2) L) j)⁻¹ * l ∈ Λ₀ := by
  intro l hl
  have hle := le_of_shape σ u Λ Λ₀ hshape hΛ₀

  have hai00 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
    have h1 := val_mul_inv_apply a 1 0
    rw [ha11, zero_mul, add_zero, Matrix.one_apply_ne (by decide)] at h1

    have ha10 : (a : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
      intro h; apply det_val_ne_zero a; rw [ha00, h, zero_mul, mul_zero, sub_zero]
    exact (mul_eq_zero.1 h1).resolve_left ha10
  have hai11 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
    have h1 := val_mul_inv_apply a 0 1
    rw [ha00, zero_mul, zero_add, Matrix.one_apply_ne (by decide)] at h1
    have ha01 : (a : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
      intro h; apply det_val_ne_zero a; rw [ha00, h, zero_mul, zero_mul, sub_zero]
    exact (mul_eq_zero.1 h1).resolve_left ha01
  by_cases hl0 : l ∈ Λ₀
  · refine ⟨0, ?_, ?_⟩
    · show ((![(1 : GL (Fin 2) L), a] : Fin 2 → GL (Fin 2) L) 0)⁻¹ * l ∈ Λ₀
      simpa using hl0
    · intro j hj
      fin_cases j
      · rfl
      · exfalso
        have hj' : a⁻¹ * l ∈ Λ₀ := by simpa using hj
        obtain ⟨hl10, hl01, -⟩ := (hΛ₀ l).1 hl0
        obtain ⟨h10, h01, -⟩ := (hΛ₀ _).1 hj'

        have h00 : ((a⁻¹ * l : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
          rw [val_mul_apply, hai00, hl10, zero_mul, mul_zero, add_zero]
        apply det_val_ne_zero (a⁻¹ * l)
        rw [h00, h10, zero_mul, mul_zero, sub_zero]
  · obtain ⟨hl00, hl11, -⟩ := anti_of_mem_of_not_mem σ u Λ Λ₀ hshape hΛ₀ l hl hl0
    refine ⟨1, ?_, ?_⟩
    · show ((![(1 : GL (Fin 2) L), a] : Fin 2 → GL (Fin 2) L) 1)⁻¹ * l ∈ Λ₀
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      refine mem_Λ₀_of_mem_of_apply_one_zero σ u Λ Λ₀ hshape hΛ₀ _ (Λ.mul_mem (Λ.inv_mem ha) hl) ?_
      rw [val_mul_apply, hai11, hl00, mul_zero, zero_mul, add_zero]
    · intro j hj
      fin_cases j
      · exfalso
        have hj' : l ∈ Λ₀ := by simpa using hj
        exact hl0 hj'
      · rfl

end Stabiliser

section StabiliserNorm

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (u : L)
  (Λ Λ₀ : Subgroup (GL (Fin 2) L))
  (hshape : ∀ γ : GL (Fin 2) L, γ ∈ Λ ↔
    (((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 ∧
        σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) * u ^ 2 =
          (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0))
  (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))

include hshape hΛ₀

include hgen in

theorem exists_anti (hN : Algebra.norm K u = -1) :
    ∃ a ∈ Λ, (a : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
  have h1 : Algebra.norm K (u ^ 2) = 1 := by rw [map_pow, hN]; norm_num
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, fun x => Subgroup.mem_zpowers_iff.mp (hgen x)⟩⟩
  obtain ⟨yy, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (g := σ) hgen h1
  have hyσ : (σ (yy : L)) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff σ σ.injective]; exact yy.ne_zero
  have hdet : Matrix.det !![(0 : L), (yy : L); 1, 0] ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simpa using yy.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, rfl, rfl⟩
  refine (hshape _).2 (Or.inr ⟨rfl, rfl, ?_⟩)
  show σ ((yy : L) / 1) * u ^ 2 = (yy : L) / 1
  rw [div_one, ← hy, mul_div_cancel₀ _ hyσ]

theorem mem_Λ₀_of_norm_ne (hN1 : Algebra.norm K u ≠ 1) (hN2 : Algebra.norm K u ≠ -1) :
    ∀ γ ∈ Λ, γ ∈ Λ₀ := by
  intro γ hγ
  by_contra hn
  obtain ⟨h00, h11, hσ⟩ := anti_of_mem_of_not_mem σ u Λ Λ₀ hshape hΛ₀ γ hγ hn
  set x : L := (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0 with hx
  have h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
    intro h; apply det_val_ne_zero γ; rw [h00, h, zero_mul, zero_mul, sub_zero]
  have h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
    intro h; apply det_val_ne_zero γ; rw [h00, h, zero_mul, mul_zero, sub_zero]
  have hx0 : x ≠ 0 := div_ne_zero h01 h10
  have hN := congrArg (Algebra.norm K) hσ
  rw [map_mul, map_pow, Algebra.norm_eq_of_algEquiv] at hN
  have hNx : Algebra.norm K x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx0
  have hsq : Algebra.norm K u ^ 2 = 1 := by
    have : Algebra.norm K x * (Algebra.norm K u ^ 2 - 1) = 0 := by rw [mul_sub, mul_one, hN, sub_self]
    have h2 := (mul_eq_zero.1 this).resolve_left hNx
    exact sub_eq_zero.1 h2
  rcases sq_eq_one_iff.1 hsq with h | h
  · exact hN1 h
  · exact hN2 h

end StabiliserNorm

section Invariance

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

noncomputable def bracket (R : ℝ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) : ℂ :=
  1 - Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
      (fun _ => (1 : ℂ)) y
    - Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
      (fun _ => (1 : ℂ)) y

noncomputable def orb [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (δ₀ : GL (Fin 2) L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

variable {K L}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  (isClosed_Icc.preimage
    ((NumberField.TateGlobal.continuous_ideleNorm L).comp Matrix.GeneralLinearGroup.continuous_det)).measurableSet

theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : GL (Fin 2) L) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.globalPoints (𝓞 L) L γ * g ∈ slab L α β ↔ g ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem indicator_one_congr {X : Type*} {s t : Set X} {a b : X} (h : a ∈ s ↔ b ∈ t) :
    s.indicator (fun _ => (1 : ℂ)) a = t.indicator (fun _ => (1 : ℂ)) b := by
  by_cases hb : b ∈ t
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h.2 hb)]
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt h.1 hb)]

theorem mem_borelSubgroup {γ : GL (Fin 2) L} (h : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    γ ∈ AutomorphicForm.borelSubgroup L := h

theorem bracket_globalPoints_mul (R : ℝ) (γ : GL (Fin 2) L)
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0))
    (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    bracket L R (AutomorphicForm.globalPoints (𝓞 L) L γ * y) = bracket L R y := by
  set gp := AutomorphicForm.globalPoints (𝓞 L) L with hgp
  set w : GL (Fin 2) L := AutomorphicForm.gl2Weyl with hw
  have hW : AutomorphicForm.adelicWeyl (𝓞 L) L = gp w := rfl
  have Hb := fun (γ' : GL (Fin 2) L) (h : (γ' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
    NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (mem_borelSubgroup h) g
  have hww : w * w = 1 := weyl_mul_weyl
  set S1 : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    {y | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} with hS1
  set S2 : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    {y | Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)} with hS2
  show 1 - S1.indicator (fun _ => (1 : ℂ)) (gp γ * y) - S2.indicator (fun _ => (1 : ℂ)) (gp γ * y) =
    1 - S1.indicator (fun _ => (1 : ℂ)) y - S2.indicator (fun _ => (1 : ℂ)) y
  rcases hγ with ⟨h10, h01⟩ | ⟨h00, h11⟩
  ·
    have e1 : NumberField.AdelicHeight.adelicHeight L (gp γ * y) = NumberField.AdelicHeight.adelicHeight L y :=
      Hb γ h10 y
    have e2 : NumberField.AdelicHeight.adelicHeight L (gp w * (gp γ * y)) =
        NumberField.AdelicHeight.adelicHeight L (gp w * y) := by
      have hm : gp w * (gp γ * y) = gp (w * γ * w) * (gp w * y) := by
        rw [← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, mul_assoc (w * γ), hww, mul_one]
      rw [hm]
      refine Hb _ ?_ _
      rw [mul_weyl_val, weyl_mul_val]; simpa using h01
    have i1 : S1.indicator (fun _ => (1 : ℂ)) (gp γ * y) = S1.indicator (fun _ => (1 : ℂ)) y :=
      indicator_one_congr (by rw [hS1, Set.mem_setOf_eq, Set.mem_setOf_eq, e1])
    have i2 : S2.indicator (fun _ => (1 : ℂ)) (gp γ * y) = S2.indicator (fun _ => (1 : ℂ)) y :=
      indicator_one_congr (by rw [hS2, Set.mem_setOf_eq, Set.mem_setOf_eq, hW, e2])
    rw [i1, i2]
  ·
    have e1 : NumberField.AdelicHeight.adelicHeight L (gp γ * y) =
        NumberField.AdelicHeight.adelicHeight L (gp w * y) := by
      have hm : gp γ * y = gp (γ * w) * (gp w * y) := by
        rw [← mul_assoc, ← map_mul, mul_assoc γ, hww, mul_one]
      rw [hm]
      refine Hb _ ?_ _
      rw [mul_weyl_val]; simpa using h11
    have e2 : NumberField.AdelicHeight.adelicHeight L (gp w * (gp γ * y)) =
        NumberField.AdelicHeight.adelicHeight L y := by
      rw [← mul_assoc, ← map_mul]
      refine Hb _ ?_ _
      rw [weyl_mul_val]; simpa using h00
    have i1 : S1.indicator (fun _ => (1 : ℂ)) (gp γ * y) = S2.indicator (fun _ => (1 : ℂ)) y :=
      indicator_one_congr (by rw [hS1, hS2, Set.mem_setOf_eq, Set.mem_setOf_eq, hW, e1])
    have i2 : S2.indicator (fun _ => (1 : ℂ)) (gp γ * y) = S1.indicator (fun _ => (1 : ℂ)) y :=
      indicator_one_congr (by rw [hS1, hS2, Set.mem_setOf_eq, Set.mem_setOf_eq, hW, e2])
    rw [i1, i2, sub_right_comm]

theorem globalPoints_scalar (z : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) z) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j <;>
    simp [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.map_apply,
      Matrix.diagonal_apply, hij]

theorem sigmaAdelicAct_globalPoints' (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (γ : GL (Fin 2) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L γ) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ

noncomputable def xiTop (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun z := ξL ⟨z, Subgroup.mem_top z⟩
  map_one' := by exact map_one ξL
  map_mul' a b := by rw [← map_mul]; rfl

theorem xiTop_apply (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    xiTop ξL z = ξL ⟨z, Subgroup.mem_top z⟩ := rfl

theorem unitsAct_map_algebraMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) (u : Lˣ) :
    D.unitsAct g (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (g : L →* L) u) := by
  apply Units.ext
  exact D.compat g (u : L)

theorem unitsAct_unitsAct_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct g (D.unitsAct g⁻¹ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
    z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
      ξL ⟨z, Subgroup.mem_top z⟩ = 1)
  (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
  (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
  (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)

theorem orb_mul_eq (g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (m : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ g =
      AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.centralScalar (𝓞 L) L m) :
    orb K L νZL D σ ξL δ₀ φ (g * y) =
      (((xiTop ξL (D.unitsAct σ⁻¹ m))⁻¹ : ℂˣ) : ℂ) * orb K L νZL D σ ξL δ₀ φ y :=
  AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    K L D σ νZL (xiTop ξL) φ _ g y m hg

include hξt in

theorem orb_globalPoints_mul (γ : GL (Fin 2) L)
    (hγ : δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    orb K L νZL D σ ξL δ₀ φ (AutomorphicForm.globalPoints (𝓞 L) L γ * y) = orb K L νZL D σ ξL δ₀ φ y := by
  set gp := AutomorphicForm.globalPoints (𝓞 L) L with hgp
  set sγ := Matrix.GeneralLinearGroup.map (σ : L →+* L) γ with hsγ
  have hcen := hγ
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨z₀, hz₀⟩ := hcen
  set c : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) z₀ with hc
  have hcz : c⁻¹ ∈ Subgroup.center (GL (Fin 2) L) := by
    rw [hz₀]; exact Subgroup.inv_mem _ hγ
  have h1 : δ₀ * c = γ * δ₀ * sγ⁻¹ := by rw [hz₀, mul_inv_cancel_left]
  have hcomm : sγ * c⁻¹ = c⁻¹ * sγ := Subgroup.mem_center_iff.1 hcz sγ
  have key : γ⁻¹ * δ₀ * sγ = δ₀ * c⁻¹ := by
    calc γ⁻¹ * δ₀ * sγ = γ⁻¹ * (δ₀ * c) * (c⁻¹ * sγ) := by group
      _ = γ⁻¹ * (γ * δ₀ * sγ⁻¹) * (sγ * c⁻¹) := by rw [h1, hcomm]
      _ = δ₀ * c⁻¹ := by group
  set m : (AdeleRing (𝓞 L) L)ˣ :=
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) z₀)⁻¹ with hm
  have keyA : (gp γ)⁻¹ * gp δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (gp γ) =
      gp δ₀ * AutomorphicForm.centralScalar (𝓞 L) L m := by
    rw [sigmaAdelicAct_globalPoints', ← hsγ, ← map_inv, ← map_mul, ← map_mul, key, map_mul, map_inv, hc,
      globalPoints_scalar, ← map_inv]
  rw [orb_mul_eq νZL D σ ξL δ₀ φ (gp γ) y m keyA]
  have htriv : xiTop ξL (D.unitsAct σ⁻¹ m) = 1 := by
    rw [hm, map_inv, unitsAct_map_algebraMap, map_inv, xiTop_apply, hξt _ ⟨_, rfl⟩, inv_one]
  rw [htriv, inv_one, Units.val_one, one_mul]

include hξσ hδ₀u hδ₀l in

theorem orb_mul_of_diag_of_mem_center (h : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    orb K L νZL D σ ξL δ₀ φ (h * y) = orb K L νZL D σ ξL δ₀ φ y := by
  set gp := AutomorphicForm.globalPoints (𝓞 L) L with hgp
  set sh := AutomorphicForm.sigmaAdelicAct K L D σ h with hsh
  have hcen' := hcen
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen'
  obtain ⟨mm, hmm⟩ := hcen'
  have hmm' : AutomorphicForm.centralScalar (𝓞 L) L mm = sh * h⁻¹ := hmm
  have hcs : AutomorphicForm.centralScalar (𝓞 L) L mm ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
    rw [hmm']; exact hcen
  have e1 : sh = AutomorphicForm.centralScalar (𝓞 L) L mm * h := by rw [hmm', inv_mul_cancel_right]
  have e2 : gp δ₀ * h = h * gp δ₀ := by
    refine diag_comm _ _ ?_ ?_ h10 h01
    · rw [hgp, AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply, hδ₀u, map_zero]
    · rw [hgp, AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply, hδ₀l, map_zero]
  have e3 : AutomorphicForm.centralScalar (𝓞 L) L mm * h = h * AutomorphicForm.centralScalar (𝓞 L) L mm :=
    (Subgroup.mem_center_iff.1 hcs h).symm
  have key : h⁻¹ * gp δ₀ * sh = gp δ₀ * AutomorphicForm.centralScalar (𝓞 L) L mm := by
    calc h⁻¹ * gp δ₀ * sh = h⁻¹ * gp δ₀ * (AutomorphicForm.centralScalar (𝓞 L) L mm * h) := by rw [e1]
      _ = h⁻¹ * (gp δ₀ * h) * AutomorphicForm.centralScalar (𝓞 L) L mm := by rw [e3]; group
      _ = gp δ₀ * AutomorphicForm.centralScalar (𝓞 L) L mm := by rw [e2]; group
  rw [orb_mul_eq νZL D σ ξL δ₀ φ h y mm key]

  set hu : (AdeleRing (𝓞 L) L)ˣ := diagUnit00 h h10 h01 with hhu
  have hmm_eq : mm = D.unitsAct σ hu * hu⁻¹ := by
    apply Units.ext
    have hval := congrArg (fun M : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0) hmm'
    beta_reduce at hval
    rw [val_mul_apply] at hval
    have hsh01 : (sh : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 := by
      rw [hsh, AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply, h01, map_zero]
    have hsh00 : (sh : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 =
        (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0) := by
      rw [hsh, AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.map_apply]; rfl
    rw [hsh01, zero_mul, add_zero, hsh00] at hval
    have hlhs : ((AutomorphicForm.centralScalar (𝓞 L) L mm : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = (mm : AdeleRing (𝓞 L) L) := by
      simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar]
    rw [hlhs] at hval
    rw [hval, Units.val_mul]
    rfl
  have htriv : xiTop ξL (D.unitsAct σ⁻¹ mm) = 1 := by
    have hσ' : ∀ z, xiTop ξL (D.unitsAct σ z) = xiTop ξL z := fun z => hξσ z
    calc xiTop ξL (D.unitsAct σ⁻¹ mm) = xiTop ξL (D.unitsAct σ (D.unitsAct σ⁻¹ mm)) := (hσ' _).symm
      _ = xiTop ξL mm := by rw [unitsAct_unitsAct_inv]
      _ = 1 := by rw [hmm_eq, map_mul, map_inv, hσ', mul_inv_cancel]
  rw [htriv, inv_one, Units.val_one, one_mul]

end Invariance

section Core

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

theorem continuous_centralScalar (L : Type) [Field L] [NumberField L] :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem core
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AutomorphicForm.AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (hda : ∀ γ ∈ Λ, ((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (hle : Λ₀ ≤ Λ)
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (R : ℝ)
    (m : ℕ) (hm : 0 < m) (s : Fin m → GL (Fin 2) L) (hs1 : ∀ j, s j ∈ Λ)
    (hs2 : ∀ l ∈ Λ, ∃! j, (s j)⁻¹ * l ∈ Λ₀)
    (hfin : ∫⁻ q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L),
      (∫⁻ h in Ω, ‖(slab L α β).indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) *
          bracket L R ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out)‖ₑ ∂μH) *
        ‖orb K L νZL D σ ξL δ₀ φ q.out‖ₑ ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) < ⊤) :
    IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L => ∑' i,
        bracket L R ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) *
          orb K L νZL D σ ξL δ₀ φ ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        (∫ h in Ω, (slab L α β).indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) *
            bracket L R ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH) *
          orb K L νZL D σ ξL δ₀ φ q.out)
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i,
        bracket L R ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) *
          orb K L νZL D σ ξL δ₀ φ ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (1 / (m : ℂ)) *
        ∫ q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L),
          (∫ h in Ω, (slab L α β).indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) *
              bracket L R ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH) *
            orb K L νZL D σ ξL δ₀ φ q.out ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by

  set μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set gp : GL (Fin 2) L →* AutomorphicForm.AdelicGL2 (𝓞 L) L := AutomorphicForm.globalPoints (𝓞 L) L with hgp
  set S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) := slab L α β with hSdef
  set bR : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ := bracket L R with hbR
  set F : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ := orb K L νZL D σ ξL δ₀ φ with hF
  set ν := HaarQuotient.measure μ H μH with hν
  haveI hSCG : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI hSCZ : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite νZL := inferInstance

  have hSm : MeasurableSet S := measurableSet_slab α β
  have hS : ∀ (γ : GL (Fin 2) L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L), gp γ * x ∈ S ↔ x ∈ S :=
    globalPoints_mul_mem_slab_iff α β

  set g : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ := fun y => bR y * F y with hg
  have hFH : ∀ (h : H) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L), F ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * y) = F y := by
    intro h y
    obtain ⟨h10, h01, hcen⟩ := (hH _).1 h.2
    exact orb_mul_of_diag_of_mem_center νZL D σ ξL hξσ δ₀ hδ₀u hδ₀l φ _ h10 h01 hcen y
  have hgΛ : ∀ γ ∈ Λ, ∀ y, g (gp γ * y) = g y := by
    intro γ hγ y
    show bR (gp γ * y) * F (gp γ * y) = bR y * F y
    rw [hbR, bracket_globalPoints_mul R γ (hda γ hγ) y, hF,
      orb_globalPoints_mul νZL D σ ξL hξt δ₀ φ γ ((hΛ γ).1 hγ) y]
  have hgΛ₀ : ∀ γ ∈ Λ₀, ∀ y, g (gp γ * y) = g y := fun γ hγ => hgΛ γ (hle hγ)

  have hs1m : MeasurableSet {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} :=
    (isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight L)).measurableSet
  have hs2m : MeasurableSet {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)} :=
    (isOpen_lt continuous_const
      ((NumberField.AdelicHeight.continuous_adelicHeight L).comp (continuous_const_mul _))).measurableSet
  have hbRm : Measurable bR :=
    (measurable_const.sub (measurable_const.indicator hs1m)).sub (measurable_const.indicator hs2m)
  have c1 : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1⁻¹ * gp δ₀ :=
    continuous_fst.inv.mul continuous_const
  have c2 : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1 :=
    ((continuous_centralScalar L).comp continuous_snd).mul continuous_fst
  have c3 : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      p.1⁻¹ * gp δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1) :=
    c1.mul ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp c2)
  have c4 : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) := hξc.comp continuous_snd
  have hI : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        φ (p.1⁻¹ * gp δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) :=
    c4.mul (hφc.comp c3)
  have hFm : Measurable F := (hI.stronglyMeasurable.integral_prod_right' (ν := νZL)).measurable
  have hgm : Measurable g := hbRm.mul hFm

  have hΛ₀H : Λ₀.map gp ≤ H := by
    rw [Subgroup.map_le_iff_le_comap]
    intro γ hγ
    obtain ⟨h10, h01, ⟨k, hk⟩⟩ := (hΛ₀ γ).1 hγ
    rw [Subgroup.mem_comap]
    have hdet := det_val_ne_zero γ
    rw [h10, mul_zero, sub_zero] at hdet
    have h00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have h11 : (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hσ00 : σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := by rwa [ne_eq, map_eq_zero_iff σ σ.injective]
    have hσr : σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) =
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
      rw [← hk, AlgEquiv.commutes]
    rw [map_div₀, div_eq_div_iff ((map_ne_zero_iff σ σ.injective).2 h11) h11] at hσr
    set z₁ : Lˣ := Units.mk0 (σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 0) / (γ : Matrix (Fin 2) (Fin 2) L) 0 0)
      (div_ne_zero hσ00 h00) with hz₁
    have hz : Matrix.GeneralLinearGroup.map (σ : L →+* L) γ = Matrix.GeneralLinearGroup.scalar (Fin 2) z₁ * γ := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [Matrix.GeneralLinearGroup.map_apply, val_mul_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      fin_cases i <;> fin_cases j
      · simp [hz₁, div_mul_cancel₀ _ h00]
      · simp [h01]
      · simp [h10]
      · simp only [Fin.mk_one, Fin.isValue, RingHom.coe_coe, Matrix.diagonal_apply_ne, ne_eq,
          one_ne_zero, not_false_eq_true, zero_mul, Matrix.diagonal_apply_eq, zero_add, hz₁, Units.val_mk0]
        rw [div_mul_eq_mul_div, eq_div_iff h00]
        linear_combination hσr.symm
    refine (hH _).2 ⟨?_, ?_, ?_⟩
    · rw [hgp, AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply, h10, map_zero]
    · rw [hgp, AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply, h01, map_zero]
    · have e : AutomorphicForm.sigmaAdelicAct K L D σ (gp γ) * (gp γ)⁻¹ =
          gp (Matrix.GeneralLinearGroup.scalar (Fin 2) z₁) := by
        rw [sigmaAdelicAct_globalPoints', hz, map_mul, mul_inv_cancel_right]
      rw [e, hgp, globalPoints_scalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩

  set r' : ι × Fin m → GL (Fin 2) L := fun p => r p.1 * s p.2 with hr'
  have hr'u : ∀ γ : GL (Fin 2) L, ∃! p, (r' p)⁻¹ * γ ∈ Λ₀ := existsUnique_prod_reps Λ Λ₀ hle r hr s hs1 hs2
  have hsummand : ∀ (p : ι × Fin m) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      g ((gp (r' p))⁻¹ * x) = g ((gp (r p.1))⁻¹ * x) := by
    intro p x
    show g ((gp (r p.1 * s p.2))⁻¹ * x) = g ((gp (r p.1))⁻¹ * x)
    rw [map_mul, mul_inv_rev, ← map_inv, mul_assoc]
    exact hgΛ _ (Λ.inv_mem (hs1 _)) _

  have hinnerpt : ∀ (h : H) (o : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * o) =
        S.indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * o) *
          bR ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * o) * F o := by
    intro h o
    by_cases hmem : (h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * o ∈ S
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul]
      show bR _ * F _ = _
      rw [hFH h o]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul, zero_mul]

  have hLU := lunfold L S hSm hS Φ₀ hΦ₀s hΦ₀ Λ₀ r' hr'u H hHc hΛ₀H μH Ω hΩ (fun y => ‖g y‖ₑ) hgm.enorm
    (fun γ hγ x => by show ‖g _‖ₑ = ‖g _‖ₑ; rw [hgΛ₀ γ hγ x])
  have hfin' : ∫⁻ x in Φ₀, ∑' p, ‖g ((gp (r' p))⁻¹ * x)‖ₑ ∂μ < ∞ := by
    rw [hLU]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun q => ?_)) hfin
    rw [← lintegral_mul_const' _ _ enorm_ne_top]
    refine lintegral_congr fun h => ?_
    by_cases hmem : (h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out ∈ S
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul, ← enorm_mul]
      show ‖bR _ * F _‖ₑ = _
      rw [hFH h]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul, enorm_zero, zero_mul]

  obtain ⟨h1, h2, -, h4, h5⟩ :=
    AutomorphicForm.integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
      L S hSm hS Φ₀ hΦ₀s hΦ₀ Λ₀ r' hr'u H hHc hΛ₀H μH Ω hΩ g hgm hgΛ₀ hfin'

  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hregroup : ∀ᵐ x ∂(μ.restrict Φ₀),
      ∑' p, g ((gp (r' p))⁻¹ * x) = (m : ℂ) * ∑' i, g ((gp (r i))⁻¹ * x) := by
    filter_upwards [h2] with x hx
    have hx' : Summable fun p : ι × Fin m => g ((gp (r p.1))⁻¹ * x) :=
      (hx.of_norm).congr (fun p => hsummand p x)
    calc ∑' p, g ((gp (r' p))⁻¹ * x) = ∑' p : ι × Fin m, g ((gp (r p.1))⁻¹ * x) :=
          tsum_congr (fun p => hsummand p x)
      _ = ∑' i, ∑' j : Fin m, g ((gp (r i))⁻¹ * x) := hx'.tsum_prod' (fun i => (hasSum_fintype _).summable)
      _ = ∑' i, (m : ℂ) * g ((gp (r i))⁻¹ * x) := by
          refine tsum_congr fun i => ?_
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (m : ℂ) * ∑' i, g ((gp (r i))⁻¹ * x) := tsum_mul_left
  have hae : (fun x => ∑' i, g ((gp (r i))⁻¹ * x)) =ᵐ[μ.restrict Φ₀]
      fun x => (1 / (m : ℂ)) * ∑' p, g ((gp (r' p))⁻¹ * x) := by
    filter_upwards [hregroup] with x hx
    rw [hx, ← mul_assoc, one_div, inv_mul_cancel₀ hm0, one_mul]
  have hinner : ∀ q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L),
      ∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH =
        (∫ h in Ω, S.indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) *
            bR ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH) * F q.out := by
    intro q
    simp_rw [hinnerpt]
    exact integral_mul_const _ _
  refine ⟨?_, ?_, ?_⟩
  ·
    have hi : IntegrableOn (fun x => (1 / (m : ℂ)) * ∑' p, g ((gp (r' p))⁻¹ * x)) Φ₀ μ := h1.const_mul _
    exact hi.congr hae.symm
  ·
    have hfun : (fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        (∫ h in Ω, S.indicator (fun _ => (1 : ℂ)) ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) *
            bR ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH) * F q.out) =
        fun q => ∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH :=
      funext fun q => (hinner q).symm
    rw [hfun]
    exact h4
  ·
    calc ∫ x in Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) ∂μ
        = ∫ x in Φ₀, (1 / (m : ℂ)) * ∑' p, g ((gp (r' p))⁻¹ * x) ∂μ := integral_congr_ae hae
      _ = (1 / (m : ℂ)) * ∫ x in Φ₀, ∑' p, g ((gp (r' p))⁻¹ * x) ∂μ := integral_const_mul _ _
      _ = (1 / (m : ℂ)) * ∫ q, (∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH) ∂ν := by
          rw [h5]
      _ = _ := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall hinner)

end Core

end P2mUnfoldRegroup

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hfin : ∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)))‖ₑ ∂μH) * ‖(∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)‖ₑ ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) < ⊤) :
    IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
      (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
      (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
      - Set.indicator {y : AdelicGL2 (𝓞 L) L |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
      (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
      ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))) ∂μH) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)) (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) *
        ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))) ∂μH) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL) ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  set uu : L := (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 with huu
  obtain ⟨-, hrow⟩ :=
    LT.TwistedNorm.exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
      hgen δ₀ hδ₀u hδ₀l hreg
  have hshape : ∀ γ : GL (Fin 2) L, γ ∈ Λ ↔
      (((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
          (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)) ∨
        ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 ∧
          σ ((γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) * uu ^ 2 =
            (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 0) :=
    fun γ => (hΛ γ).trans (hrow γ)
  have hle : Λ₀ ≤ Λ := P2mUnfoldRegroup.le_of_shape σ uu Λ Λ₀ hshape hΛ₀
  have hda : ∀ γ ∈ Λ, ((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) := by
    intro γ hγ
    rcases (hshape γ).1 hγ with ⟨h, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  by_cases hN : Algebra.norm K uu = -1
  · obtain ⟨a, haΛ, ha00, ha11⟩ := P2mUnfoldRegroup.exists_anti σ hgen uu Λ Λ₀ hshape hΛ₀ hN
    have hs1 : ∀ j : Fin 2, ((![(1 : GL (Fin 2) L), a] : Fin 2 → GL (Fin 2) L) j) ∈ Λ := by
      intro j
      fin_cases j
      · exact one_mem _
      · exact haΛ
    have hs2 := P2mUnfoldRegroup.existsUnique_fin_two σ uu Λ Λ₀ hshape hΛ₀ a haΛ ha00 ha11
    obtain ⟨h1, h2, h3⟩ := P2mUnfoldRegroup.core K L α β νZL D σ ξL hξc hξt Φ₀ hΦ₀s hΦ₀ H hHc hH μH hξσ δ₀ hδ₀u
      hδ₀l Λ hΛ hda r hr Λ₀ hΛ₀ hle Ω hΩ φ hφc R 2 two_pos _ hs1 hs2 hfin
    refine ⟨h1, h2, h3.trans ?_⟩
    rw [if_pos hN]
    exact congrArg₂ (· * ·) (by norm_num) rfl
  · have hall := P2mUnfoldRegroup.mem_Λ₀_of_norm_ne σ uu Λ Λ₀ hshape hΛ₀ hreg hN
    have hs1 : ∀ j : Fin 1, ((![(1 : GL (Fin 2) L)] : Fin 1 → GL (Fin 2) L) j) ∈ Λ := by
      intro j
      fin_cases j
      exact one_mem _
    have hs2 : ∀ l ∈ Λ, ∃! j : Fin 1, ((![(1 : GL (Fin 2) L)] : Fin 1 → GL (Fin 2) L) j)⁻¹ * l ∈ Λ₀ :=
      fun l hl => ⟨0, by simpa using hall l hl, fun j _ => Subsingleton.elim _ _⟩
    obtain ⟨h1, h2, h3⟩ := P2mUnfoldRegroup.core K L α β νZL D σ ξL hξc hξt Φ₀ hΦ₀s hΦ₀ H hHc hH μH hξσ δ₀ hδ₀u
      hδ₀l Λ hΛ hda r hr Λ₀ hΛ₀ hle Ω hΩ φ hφc R 1 one_pos _ hs1 hs2 hfin
    refine ⟨h1, h2, h3.trans ?_⟩
    rw [if_neg hN]
    exact congrArg₂ (· * ·) (by norm_num) rfl

end S_AutomorphicForm_integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul (solution)
