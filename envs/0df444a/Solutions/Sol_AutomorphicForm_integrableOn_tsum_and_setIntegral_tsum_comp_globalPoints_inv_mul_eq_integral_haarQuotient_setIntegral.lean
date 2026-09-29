-- Prove2me | solution 1 for AutomorphicForm.integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/20d524ba-e6f8-51ba-8983-c09eae4d3d8e

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open scoped Pointwise ENNReal

namespace P2mUnfoldClassGL2

section Fibre

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem isFundamentalDomain_univ_of_subsingleton {K α : Type*} [Group K] [Subsingleton K]
    [MulAction K α] [MeasurableSpace α] (μ : Measure α) :
    IsFundamentalDomain K (Set.univ : Set α) μ where
  nullMeasurableSet := MeasurableSet.univ.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun _ => ⟨1, Set.mem_univ _⟩
  aedisjoint := Subsingleton.pairwise

theorem fibre_unfold
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓH : Γ ≤ H) [Countable Γ]
    (S : Set G) (hSm : MeasurableSet S) (hS : ∀ γ ∈ Γ, ∀ x : G, γ * x ∈ S ↔ x ∈ S)
    (F₂ : Set G) (hF₂m : MeasurableSet F₂) (hF₂S : F₂ ⊆ S)
    (hcov : ∀ᵐ x ∂(μ.restrict S), ∃ γ : Γ, (γ : G) * x ∈ F₂)
    (hdisj : ∀ γ γ' : Γ, γ ≠ γ' →
      μ ((fun x => (γ : G)⁻¹ * x) ⁻¹' F₂ ∩ (fun x => (γ' : G)⁻¹ * x) ⁻¹' F₂) = 0)
    (g : G → ℂ) (hg : Measurable g) (hgΓ : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x)
    (Ω : Set H) (hΩ : IsFundamentalDomain (Γ.subgroupOf H) Ω μH)
    (hint : ∫⁻ x in F₂, ‖g x‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH),
      IntegrableOn (fun h : H => S.indicator g ((h : G) * q.out)) Ω μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G =>
        ∫ h in Ω, S.indicator g ((h : G) * q.out) ∂μH) (HaarQuotient.measure μ H μH) ∧
    ∫ x in F₂, g x ∂μ =
      ∫ q, (∫ h in Ω, S.indicator g ((h : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  set ν := HaarQuotient.measure μ H μH with hν
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace

  set f₀ : G → ℂ := F₂.indicator g with hf₀
  have hf₀m : Measurable f₀ := hg.indicator hF₂m

  have hbotG : IsFundamentalDomain (⊥ : Subgroup G) (Set.univ : Set G) μ :=
    isFundamentalDomain_univ_of_subsingleton μ
  haveI hsub : Subsingleton ((⊥ : Subgroup G).subgroupOf H) := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  have hbotH : IsFundamentalDomain ((⊥ : Subgroup G).subgroupOf H) (Set.univ : Set H) μH :=
    isFundamentalDomain_univ_of_subsingleton μH
  have hfin₀ : ∫⁻ x in Set.univ, ‖f₀ x‖ₑ ∂μ < ∞ := by
    rw [Measure.restrict_univ]
    simp_rw [hf₀, enorm_indicator_eq_indicator_enorm, lintegral_indicator hF₂m]
    exact hint
  obtain ⟨h3i, h3ii, h3iii⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ H hH μH
      ⊥ bot_le f₀ hf₀m (by intro γ hγ x; rw [Subgroup.mem_bot] at hγ; rw [hγ, one_mul])
      Set.univ hbotG Set.univ hbotH hfin₀
  simp only [Measure.restrict_univ, integrableOn_univ] at h3i h3ii h3iii

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
      IntegrableOn (fun h : H => S.indicator g ((h : G) * q.out)) Ω μH ∧
      ∫ x, f₀ ((x : G) * q.out) ∂μH = ∫ h in Ω, S.indicator g ((h : G) * q.out) ∂μH := by
    filter_upwards [hfib, h3i] with q hq hIq
    set o : G := q.out with ho
    set φ' : H → ℂ := fun x => g ((x : G) * o) with hφ'
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
    have hSgo : (fun x : H => S.indicator g ((x : G) * o)) = So.indicator φ' := by
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
        show g (((γ • x : H) : G) * o) = g ((x : G) * o)
        rw [hSΓ, mul_assoc]
        exact hgΓ _ (hmemΓ γ) _
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

    have hIA : IntegrableOn φ' A μH := by
      rw [hf₀o, integrable_indicator_iff hAm] at hIq
      exact hIq
    have hμA : (μH.restrict So).restrict A = μH.restrict A := by
      rw [Measure.restrict_restrict hAm, Set.inter_eq_left.2 hASo]
    have hμΩ : (μH.restrict So).restrict Ω = μH.restrict (Ω ∩ So) := by
      rw [Measure.restrict_restrict' hSom]
    have hIA' : IntegrableOn (So.indicator φ') A (μH.restrict So) := by
      rw [IntegrableOn, hμA, integrable_indicator_iff hSom, IntegrableOn, Measure.restrict_restrict hSom,
        Set.inter_eq_right.2 hASo]
      exact hIA
    have hIΩ' : IntegrableOn (So.indicator φ') Ω (μH.restrict So) :=
      (hAfd.integrableOn_iff hΩ' hφ_inv).1 hIA'
    have hIΩ : IntegrableOn (So.indicator φ') Ω μH := by
      rw [IntegrableOn, hμΩ, integrable_indicator_iff hSom, IntegrableOn, Measure.restrict_restrict hSom,
        Set.inter_left_comm, Set.inter_self] at hIΩ'
      rw [IntegrableOn, integrable_indicator_iff hSom, IntegrableOn, Measure.restrict_restrict hSom,
        Set.inter_comm]
      exact hIΩ'

    have hEA : ∫ x, f₀ ((x : G) * o) ∂μH = ∫ x in A, So.indicator φ' x ∂(μH.restrict So) := by
      rw [hf₀o, integral_indicator hAm, hμA, setIntegral_indicator hSom, Set.inter_eq_left.2 hASo]
    have hEΩ : ∫ x in Ω, So.indicator φ' x ∂(μH.restrict So) = ∫ x in Ω, So.indicator φ' x ∂μH := by
      rw [hμΩ, setIntegral_indicator hSom, setIntegral_indicator hSom, Set.inter_assoc, Set.inter_self]
    refine ⟨?_, ?_⟩
    · rw [hSgo]; exact hIΩ
    · rw [hEA, hAfd.setIntegral_eq hΩ' hφ_inv, hEΩ, hSgo]

  refine ⟨key.mono fun q hq => hq.1, h3ii.congr (key.mono fun q hq => hq.2), ?_⟩
  calc ∫ x in F₂, g x ∂μ = ∫ x, f₀ x ∂μ := (integral_indicator hF₂m).symm
    _ = ∫ q, (∫ x, f₀ ((x : G) * q.out) ∂μH) ∂ν := h3iii
    _ = ∫ q, (∫ h in Ω, S.indicator g ((h : G) * q.out) ∂μH) ∂ν :=
        integral_congr_ae (key.mono fun q hq => hq.2)

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

theorem main
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
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hg : Measurable g)
    (hgΛ : ∀ γ ∈ Λ, ∀ x, g (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = g x)
    (hfin : ∫⁻ x in Φ₀, ∑' i, ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ∞) :
    IntegrableOn (fun x => ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    (∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀),
      Summable fun i => ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖) ∧
    (∀ᵐ q ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH),
      IntegrableOn (fun h : H => S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out)) Ω μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        ∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫ q, (∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
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
  have hgΛ' : ∀ γ ∈ Λ', ∀ x, g (γ * x) = g x := by
    intro γ hγ x
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hγ
    exact hgΛ l hl x

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
  have hfin' : ∫⁻ x in Φ₀, ∑' i, ‖g (((R i : Γ₀) : Γ₀)⁻¹ • x)‖ₑ ∂μS < ∞ := by
    rw [hμSΦ₀]; simp_rw [hRsmul]; exact hfin
  obtain ⟨-, hcoset⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      μS ⊤ Λ₀ le_top Φ₀ hΦ₀' R hRuniq
  obtain ⟨hInt2, hSumm, hEq⟩ := hcoset g hg.aestronglyMeasurable hfin'
  rw [hμSΦ₀] at hSumm hEq
  simp_rw [hRsmul] at hSumm hEq

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
  have hIntF₂ : IntegrableOn g F₂ μ := by
    have := hInt2.mono_set hF₂sub
    rwa [IntegrableOn, hμSF₂] at this
  have hint : ∫⁻ x in F₂, ‖g x‖ₑ ∂μ < ∞ := hIntF₂.hasFiniteIntegral

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
      have := (hSΛ' _ (inv_mem γ.2) x).1 hx'
      exact this
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

  obtain ⟨h3, h4, h5⟩ := fibre_unfold μ H hH μH Λ' hΛH S hSm hSΛ' F₂ hF₂m hF₂S hcov hdisj g hg hgΛ' Ω hΩ
    hint

  have hTint : IntegrableOn (fun x => ∑' i, g ((gp (r i))⁻¹ * x)) Φ₀ μ := by
    refine ⟨?_, ?_⟩
    · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
        (f := fun s x => ∑ i ∈ s, g ((gp (r i))⁻¹ * x)) (fun s => ?_) ?_
      · exact (Finset.measurable_sum s fun i _ => hg.comp (measurable_const_mul _)).aestronglyMeasurable
      · filter_upwards [hSumm] with x hx
        exact hx.of_norm.hasSum
    · show ∫⁻ x in Φ₀, ‖∑' i, g ((gp (r i))⁻¹ * x)‖ₑ ∂μ < ∞
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
      exact enorm_tsum_le_tsum_enorm
  refine ⟨hTint, hSumm, h3, h4, ?_⟩
  calc ∫ x in Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) ∂μ
      = ∫ x in F2, g x ∂μS := hEq.symm
    _ = ∫ x in F₂, g x ∂μS := setIntegral_congr_set hF₂ae.symm
    _ = ∫ x in F₂, g x ∂μ := by rw [hμSF₂]
    _ = _ := h5

end Adelic

end P2mUnfoldClassGL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
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

    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hg : Measurable g)
    (hgΛ : ∀ γ ∈ Λ, ∀ x, g (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = g x)
    (hfin : ∫⁻ x in Φ₀, ∑' i, ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ∞) :
    IntegrableOn (fun x => ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    (∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀),
      Summable fun i => ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖) ∧
    (∀ᵐ q ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH),
      IntegrableOn (fun h : H => S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out)) Ω μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        ∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫ q, (∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) :=
  P2mUnfoldClassGL2.main L S hSm hS Φ₀ hΦ₀S hΦ₀ Λ r hr H hH hΛH μH Ω hΩ g hg hgΛ hfin

end S_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral (solution)
