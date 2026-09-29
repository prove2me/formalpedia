-- Prove2me | solution 1 for AutomorphicForm.exists_isSemiLocalFactorization_integral_mul_comp_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3f35bba8-6765-5a54-8b4e-802122857fcd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Theorems.Thm_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_integral_mul_comp_inv_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct

namespace ConvFactors

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm Topology
open scoped RestrictedProduct TensorProduct TensorProduct.RightActions

noncomputable section

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

omit [TopologicalSpace G] in

private noncomputable def gconv (μ : Measure G) (ψ φ : G → ℂ) : G → ℂ :=
  fun z => ∫ y, ψ y * φ (y⁻¹ * z) ∂μ

omit [TopologicalSpace G] in
private theorem gconv_apply (μ : Measure G) (ψ φ : G → ℂ) (z : G) :
    gconv μ ψ φ z = ∫ y, ψ y * φ (y⁻¹ * z) ∂μ :=
  rfl

private theorem integrable_gconv_integrand [IsTopologicalGroup G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {ψ φ : G → ℂ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hφ : Continuous φ) (z : G) :
    Integrable (fun y => ψ y * φ (y⁻¹ * z)) μ := by
  have hc : Continuous fun y : G => ψ y * φ (y⁻¹ * z) :=
    hψ.mul (hφ.comp (continuous_id.inv.mul continuous_const))
  have hs : HasCompactSupport fun y : G => ψ y * φ (y⁻¹ * z) := hψc.mul_right
  exact hc.integrable_of_hasCompactSupport hs

private theorem hasCompactSupport_gconv
    [IsTopologicalGroup G] (μ : Measure G) {ψ φ : G → ℂ} (hψc : HasCompactSupport ψ)
    (hφc : HasCompactSupport φ) : HasCompactSupport (gconv μ ψ φ) := by
  have hK : IsCompact ((fun p : G × G => p.1 * p.2) '' (tsupport ψ ×ˢ tsupport φ)) :=
    (hψc.prod hφc).image continuous_mul
  refine HasCompactSupport.intro hK fun z hz => ?_
  have hzero : ∀ y : G, ψ y * φ (y⁻¹ * z) = 0 := by
    intro y
    by_contra hne
    apply hz
    have hψy : ψ y ≠ 0 := left_ne_zero_of_mul hne
    have hφyz : φ (y⁻¹ * z) ≠ 0 := right_ne_zero_of_mul hne
    exact ⟨(y, y⁻¹ * z), Set.mk_mem_prod (subset_tsupport ψ hψy) (subset_tsupport φ hφyz), by simp⟩
  simp only [gconv_apply, hzero, integral_zero]

private theorem continuous_gconv [IsTopologicalGroup G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [FirstCountableTopology G]
    {ψ φ : G → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Continuous (gconv μ ψ φ) := by
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  show Continuous fun z : G => ∫ y, ψ y * φ (y⁻¹ * z) ∂μ
  refine continuous_of_dominated (F := fun z y => ψ y * φ (y⁻¹ * z)) (bound := fun y => ‖ψ y‖ * M)
    (fun z => ?_) (fun z => Filter.Eventually.of_forall fun y => ?_) ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact (integrable_gconv_integrand μ hψ hψc hφ z).aestronglyMeasurable
  · show ‖ψ y * φ (y⁻¹ * z)‖ ≤ ‖ψ y‖ * M
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact (hψ.integrable_of_hasCompactSupport hψc).norm.mul_const M
  · show Continuous fun z : G => ψ y * φ (y⁻¹ * z)
    exact continuous_const.mul (hφ.comp (continuous_const.mul continuous_id))

private theorem integral_integral_eq_integral_gconv [IsTopologicalGroup G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [SigmaFinite μ] [SecondCountableTopology G] {φ ψ : G → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {w : G → ℂ} (hw : Continuous w) (g : G) :
    ∫ y, (∫ x, w (g * y * x) * φ x ∂μ) * ψ y ∂μ = ∫ z, w (g * z) * gconv μ ψ φ z ∂μ := by
  have hinner : ∀ y : G, ∫ x, w (g * y * x) * φ x ∂μ = ∫ z, w (g * z) * φ (y⁻¹ * z) ∂μ := by
    intro y
    have h := integral_mul_left_eq_self (μ := μ) (fun z => w (g * z) * φ (y⁻¹ * z)) y
    simp only [inv_mul_cancel_left] at h
    simp only [mul_assoc]
    exact h
  simp_rw [hinner]
  have hF : Integrable (Function.uncurry fun y z : G => w (g * z) * φ (y⁻¹ * z) * ψ y) (μ.prod μ) := by
    have hc : Continuous (Function.uncurry fun y z : G => w (g * z) * φ (y⁻¹ * z) * ψ y) := by
      have h1 : Continuous fun p : G × G => w (g * p.2) := hw.comp (continuous_const.mul continuous_snd)
      have h2 : Continuous fun p : G × G => φ (p.1⁻¹ * p.2) := hφ.comp (continuous_fst.inv.mul continuous_snd)
      have h3 : Continuous fun p : G × G => ψ p.1 := hψ.comp continuous_fst
      exact (h1.mul h2).mul h3
    have hs : HasCompactSupport (Function.uncurry fun y z : G => w (g * z) * φ (y⁻¹ * z) * ψ y) := by
      have hK : IsCompact (tsupport ψ ×ˢ ((fun p : G × G => p.1 * p.2) '' (tsupport ψ ×ˢ tsupport φ))) :=
        hψc.prod ((hψc.prod hφc).image continuous_mul)
      refine HasCompactSupport.intro hK ?_
      rintro ⟨y, z⟩ hp
      by_contra hne
      apply hp
      have hne' : w (g * z) * φ (y⁻¹ * z) * ψ y ≠ 0 := hne
      have hψy : ψ y ≠ 0 := right_ne_zero_of_mul hne'
      have hφyz : φ (y⁻¹ * z) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne')
      refine Set.mk_mem_prod (subset_tsupport ψ hψy) ?_
      exact ⟨(y, y⁻¹ * z), Set.mk_mem_prod (subset_tsupport ψ hψy) (subset_tsupport φ hφyz), by simp⟩
    exact hc.integrable_of_hasCompactSupport hs
  calc
    ∫ y, (∫ z, w (g * z) * φ (y⁻¹ * z) ∂μ) * ψ y ∂μ
        = ∫ y, ∫ z, w (g * z) * φ (y⁻¹ * z) * ψ y ∂μ ∂μ := by simp only [integral_mul_const]
    _ = ∫ z, ∫ y, w (g * z) * φ (y⁻¹ * z) * ψ y ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ z, w (g * z) * gconv μ ψ φ z ∂μ := by
        congr 1
        funext z
        rw [gconv_apply, ← integral_const_mul]
        congr 1
        funext y
        ring

omit [TopologicalSpace G] in

private theorem gconv_mul_left_eq
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {ψ : G → ℂ} (φ : G → ℂ) {u : G}
    (hψ : ∀ x, ψ (u * x) = ψ x) (z : G) : gconv μ ψ φ (u * z) = gconv μ ψ φ z := by
  rw [gconv_apply, gconv_apply, ← integral_mul_left_eq_self (fun y => ψ y * φ (y⁻¹ * (u * z))) u]
  congr 1
  funext y
  rw [hψ, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

omit [TopologicalSpace G] in

private theorem gconv_mul_right_eq (μ : Measure G) (ψ : G → ℂ) {φ : G → ℂ} {u : G} (hφ : ∀ x, φ (x * u) = φ x)
    (z : G) : gconv μ ψ φ (z * u) = gconv μ ψ φ z := by
  rw [gconv_apply, gconv_apply]
  congr 1
  funext y
  rw [← mul_assoc, hφ]

omit [MeasurableSpace G] in

private theorem exists_isOpen_one_mem_forall_mul_eq_of_isLocallyConstant [IsTopologicalGroup G] {φ : G → ℂ}
    (hφ : IsLocallyConstant φ)
    (hφc : HasCompactSupport φ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ x : G, ∀ k ∈ V, φ (x * k) = φ x := by

  have hloc : ∀ x : G, ∃ W : Set G, IsOpen W ∧ x ∈ W ∧ ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ x' ∈ W, ∀ k ∈ V, φ (x' * k) = φ x := by
    intro x
    have hfib : IsOpen {x' : G | φ x' = φ x} := hφ.isOpen_fiber (φ x)
    have hmem : (fun p : G × G => p.1 * p.2) ⁻¹' {x' : G | φ x' = φ x} ∈ 𝓝 ((x, 1) : G × G) :=
      continuous_mul.continuousAt.preimage_mem_nhds (hfib.mem_nhds (by simp))
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
    obtain ⟨W₀, hW₀, V₀, hV₀, hWV⟩ := hmem
    obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hW₀
    obtain ⟨V, hVsub, hVopen, h1V⟩ := mem_nhds_iff.mp hV₀
    exact ⟨W, hWopen, hxW, V, hVopen, h1V, fun x' hx' k hk => hWV (Set.mk_mem_prod (hWsub hx') (hVsub hk))⟩
  choose W hWopen hxW V hVopen h1V hWV using hloc

  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hφc W hWopen (fun x hx => Set.mem_iUnion.2 ⟨x, hxW x⟩)

  let V₁ : Set G := ⋂ x ∈ t, V x
  have hV₁open : IsOpen V₁ := isOpen_biInter_finset fun x _ => hVopen x
  have h1V₁ : (1 : G) ∈ V₁ := Set.mem_iInter₂.2 fun x _ => h1V x
  have hK : ∀ x ∈ tsupport φ, ∀ k ∈ V₁, φ (x * k) = φ x := by
    intro x hx k hk
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    rw [hWV i x hxi k (Set.mem_iInter₂.1 hk i hi), ← hWV i x hxi 1 (h1V i), mul_one]
  refine ⟨V₁ ∩ V₁⁻¹, hV₁open.inter hV₁open.inv, ⟨h1V₁, by simpa using h1V₁⟩, fun x k hk => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · exact hK x hx k hk.1
  · have hx0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    by_cases hxk : x * k ∈ tsupport φ
    · have := hK (x * k) hxk k⁻¹ (Set.mem_inv.1 hk.2)
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [hx0, image_eq_zero_of_notMem_tsupport hxk]

private theorem isLocallyConstant_gconv [IsTopologicalGroup G] (μ : Measure G) (ψ : G → ℂ) {φ : G → ℂ}
    (hφ : IsLocallyConstant φ)
    (hφc : HasCompactSupport φ) : IsLocallyConstant (gconv μ ψ φ) := by
  obtain ⟨V, hVopen, h1V, hV⟩ := exists_isOpen_one_mem_forall_mul_eq_of_isLocallyConstant hφ hφc
  refine (IsLocallyConstant.iff_exists_open _).2 fun z => ⟨(fun k => z * k) '' V, isOpenMap_mul_left z V hVopen,
    ⟨1, h1V, mul_one z⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact gconv_mul_right_eq μ ψ (fun x => hV x k hk) z

private theorem gconv_add_right [IsTopologicalGroup G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {ψ : G → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {u u' : G → ℂ} (hu : Continuous u)
    (hu' : Continuous u') : gconv μ ψ (u + u') = gconv μ ψ u + gconv μ ψ u' := by
  funext z
  simp only [gconv_apply, Pi.add_apply, mul_add]
  exact integral_add (integrable_gconv_integrand μ hψ hψc hu z) (integrable_gconv_integrand μ hψ hψc hu' z)

omit [TopologicalSpace G] in

private theorem gconv_smul_right (μ : Measure G) (ψ : G → ℂ) (c : ℂ) (u : G → ℂ) :
    gconv μ ψ (c • u) = c • gconv μ ψ u := by
  funext z
  simp only [gconv_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

omit [TopologicalSpace G] in

private theorem gconv_comp_mul_right (μ : Measure G) (ψ u : G → ℂ) (g : G) :
    gconv μ ψ (fun x => u (x * g)) = fun x => gconv μ ψ u (x * g) := by
  funext z
  simp only [gconv_apply, mul_assoc]

private theorem gconv_add_left [IsTopologicalGroup G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {ψ ψ' φ : G → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ' : Continuous ψ')
    (hψc' : HasCompactSupport ψ') (hφ : Continuous φ) : gconv μ (ψ + ψ') φ = gconv μ ψ φ + gconv μ ψ' φ := by
  funext z
  simp only [gconv_apply, Pi.add_apply, add_mul]
  exact integral_add (integrable_gconv_integrand μ hψ hψc hφ z) (integrable_gconv_integrand μ hψ' hψc' hφ z)

omit [TopologicalSpace G] in

private theorem gconv_smul_left (μ : Measure G) (c : ℂ) (ψ φ : G → ℂ) : gconv μ (c • ψ) φ = c • gconv μ ψ φ := by
  funext z
  simp only [gconv_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

omit [TopologicalSpace G] in

private theorem gconv_inv_comp_mul_right [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (u φ : G → ℂ)
    (g x : G) :
    gconv μ (fun y => u (y⁻¹ * g)) φ x⁻¹ = gconv μ (fun y => u y⁻¹) φ (x * g)⁻¹ := by
  rw [gconv_apply, gconv_apply, ← integral_mul_left_eq_self (fun y => u (y⁻¹ * g) * φ (y⁻¹ * x⁻¹)) g]
  congr 1
  funext y
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
end Generic

private theorem secondCountableTopology_restrictedProduct {ι : Type*} [Countable ι] (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)] (C : (i : ι) → Set (X i)) (hC : ∀ i, IsOpen (C i))
    [∀ i, SecondCountableTopology (X i)] : SecondCountableTopology (Πʳ i, [X i, C i]) := by
  have hle : ∀ T : Finset ι, (Filter.cofinite : Filter ι) ≤ Filter.principal ((↑T : Set ι)ᶜ) := by
    intro T
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact T.finite_toSet
  haveI hSC : ∀ T : Finset ι,
      SecondCountableTopology (Set.range (RestrictedProduct.inclusion X C (hle T))) := by
    intro T
    haveI : SecondCountableTopology (Πʳ i, [X i, C i]_[Filter.principal ((↑T : Set ι)ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hC
      (hle T)).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun T : Finset ι => Set.range (RestrictedProduct.inclusion X C (hle T)))
    (fun T => (RestrictedProduct.isOpenEmbedding_inclusion_principal hC (hle T)).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hfin : {i : ι | ¬ x.1 i ∈ C i}.Finite := Filter.eventually_cofinite.1 x.2
  refine ⟨hfin.toFinset, ⟨⟨x.1, ?_⟩, ?_⟩⟩
  · rw [Filter.eventually_principal]
    intro i hi
    by_contra h
    exact hi ((Set.Finite.mem_toFinset hfin).2 h)
  · rfl

section AdelicInstances

variable (L : Type) [Field L] [NumberField L]

private theorem countable_numberField : Countable L :=
  (Module.finBasis ℚ L).equivFun.injective.countable

private theorem countable_ringOfIntegers : Countable (𝓞 L) :=
  haveI := countable_numberField L
  (IsFractionRing.injective (𝓞 L) L).countable

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 L)) := by
  haveI := countable_ringOfIntegers L
  have hsurj : Function.Surjective fun s : Finset (𝓞 L) => Ideal.span (↑s : Set (𝓞 L)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 L)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

omit [NumberField L] in
private theorem secondCountableTopology_completion (v : InfinitePlace L) : SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.secondCountableTopology

private theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 L) L) := by
  haveI := countable_heightOneSpectrum L
  haveI := secondCountableTopology_restrictedProduct (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    (fun v => (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out v)
  exact inferInstanceAs (SecondCountableTopology
    (Πʳ v : HeightOneSpectrum (𝓞 L), [v.adicCompletion L, v.adicCompletionIntegers L]))

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI := secondCountableTopology_completion L
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace L) → v.Completion))

private theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 L) L) := by
  haveI := secondCountableTopology_infiniteAdeleRing L
  haveI := secondCountableTopology_finiteAdeleRing L
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))

private theorem secondCountableTopology_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 L) L) := by
  haveI := secondCountableTopology_adeleRing L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 L) L))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) ≃ₜ
      (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))ᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem sigmaCompactSpace_adelicGL2 : SigmaCompactSpace (AdelicGL2 (𝓞 L) L) := by
  haveI := secondCountableTopology_adelicGL2 L
  infer_instance

end AdelicInstances

section GLInstances

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
private theorem t2Space_gl [T2Space R] : T2Space (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  exact Units.isEmbedding_embedProduct.t2Space

private theorem locallyCompactSpace_gl [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

omit [IsTopologicalRing R] in
private theorem secondCountableTopology_gl [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) R ≃ₜ (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end GLInstances

section SmoothParametric

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : Type} [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem hasCompactSupport_clm_apply_fun
    {F W : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {T : G → F →L[ℝ] W} (hTc : HasCompactSupport T) (v : G → F) :
    HasCompactSupport fun a => T a (v a) :=
  hTc.mono' fun a (ha : T a (v a) ≠ 0) => subset_tsupport T fun (h : T a = 0) => ha (by rw [h]; rfl)

private theorem contDiff_integral_clm_comp (n : ℕ) :
    ∀ (F W : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]
      (Ψ : E → F) (T : G → F →L[ℝ] W) (A : G → E →L[ℝ] E),
      ContDiff ℝ n Ψ → Continuous T → HasCompactSupport T → Continuous A →
      ContDiff ℝ n fun x : E => ∫ a, T a (Ψ (A a x)) ∂μ := by
  induction n with
  | zero =>
    intro F W _ _ _ _ Ψ T A hΨ hT hTc hA
    rw [Nat.cast_zero, contDiff_zero]
    have hf : Continuous (Function.uncurry fun (x : E) (a : G) => T a (Ψ (A a x))) := by
      show Continuous fun p : E × G => T p.2 (Ψ (A p.2 p.1))
      exact (hT.comp continuous_snd).clm_apply (hΨ.continuous.comp ((hA.comp continuous_snd).clm_apply continuous_fst))
    refine (continuous_parametric_integral_of_continuous (μ := μ) hf hTc).congr fun x => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport ha]; rfl
  | succ n ih =>
    intro F W _ _ _ _ Ψ T A hΨ hT hTc hA
    set Ψ' : E → (E →L[ℝ] F) := fderiv ℝ Ψ with hΨ'_def
    set T' : G → (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] W) := fun a =>
      (ContinuousLinearMap.compL ℝ E F W (T a)).comp ((ContinuousLinearMap.compL ℝ E E F).flip (A a)) with hT'_def
    have hT'_apply : ∀ (a : G) (ℓ : E →L[ℝ] F), T' a ℓ = (T a).comp (ℓ.comp (A a)) := fun a ℓ => rfl
    have hΨ' : ContDiff ℝ n Ψ' := hΨ.fderiv_right (m := n) (by norm_cast)
    have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    have hT' : Continuous T' :=
      ((ContinuousLinearMap.compL ℝ E F W).continuous.comp hT).clm_comp
        ((ContinuousLinearMap.compL ℝ E E F).flip.continuous.comp hA)
    have hT'c : HasCompactSupport T' := hTc.mono' fun a (ha : T' a ≠ 0) => subset_tsupport T fun (h : T a = 0) =>
      ha (ContinuousLinearMap.ext fun ℓ => by rw [hT'_apply, h, ContinuousLinearMap.zero_comp]; rfl)
    have hderiv : ∀ x₀ : E,
        HasFDerivAt (fun x : E => ∫ a, T a (Ψ (A a x)) ∂μ) (∫ a, T' a (Ψ' (A a x₀)) ∂μ) x₀ := by
      intro x₀
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ a ∈ tsupport T, ∀ x ∈ Metric.closedBall x₀ 1, ‖Ψ' (A a x)‖ * ‖A a‖ ≤ C := by
        have hK : IsCompact (tsupport T ×ˢ Metric.closedBall x₀ 1) := hTc.prod (isCompact_closedBall x₀ 1)
        have hcont : Continuous fun p : G × E => ‖Ψ' (A p.1 p.2)‖ * ‖A p.1‖ :=
          (hΨ'.continuous.comp ((hA.comp continuous_fst).clm_apply continuous_snd)).norm.mul
            (hA.comp continuous_fst).norm
        obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
        refine ⟨C, fun a ha x hx => ?_⟩
        have h := hC (a, x) ⟨ha, hx⟩
        rwa [Real.norm_of_nonneg (by positivity)] at h
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F' := fun x a => T' a (Ψ' (A a x)))
        (bound := fun a => ‖T a‖ * C) (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun x =>
          (hT.clm_apply (hΨ.continuous.comp (hA.clm_apply continuous_const))).aestronglyMeasurable
      · exact (hT.clm_apply (hΨ.continuous.comp (hA.clm_apply continuous_const))).integrable_of_hasCompactSupport
          (hasCompactSupport_clm_apply_fun hTc _)
      · exact (hT'.clm_apply (hΨ'.continuous.comp (hA.clm_apply continuous_const))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun a x hx => ?_
        rw [hT'_apply]
        by_cases ha : a ∈ tsupport T
        · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.opNorm_comp_le _ _).trans (hC a ha x hx)) (norm_nonneg _))
        · rw [image_eq_zero_of_notMem_tsupport ha, ContinuousLinearMap.zero_comp, norm_zero, norm_zero, zero_mul]
      · exact (hT.norm.integrable_of_hasCompactSupport hTc.norm).mul_const C
      · refine Filter.Eventually.of_forall fun a x _ => ?_
        rw [hT'_apply]
        exact (T a).hasFDerivAt.comp x ((hΨd (A a x)).hasFDerivAt.comp x (A a).hasFDerivAt)
    have hfd : (fderiv ℝ fun x : E => ∫ a, T a (Ψ (A a x)) ∂μ) = fun x => ∫ a, T' a (Ψ' (A a x)) ∂μ :=
      funext fun x => (hderiv x).fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hderiv x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
    rw [hfd]
    exact ih (E →L[ℝ] F) (E →L[ℝ] W) Ψ' T' A hΨ' hT' hT'c hA

private theorem contDiff_top_integral_clm_comp
    {F W : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {Ψ : E → F} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {T : G → F →L[ℝ] W} (hT : Continuous T)
    (hTc : HasCompactSupport T) {A : G → E →L[ℝ] E} (hA : Continuous A) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : E => ∫ a, T a (Ψ (A a x)) ∂μ :=
  contDiff_infty.2 fun n => contDiff_integral_clm_comp μ n F W Ψ T A (contDiff_infty.1 hΨ n) hT hTc hA

end SmoothParametric

section IntegralClosure

variable {A : Type} [CommRing A]

private theorem integralMatrixSet_mul_mem {U : Set A} (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) {m n : Matrix (Fin 2) (Fin 2) A} (hm : m ∈ integralMatrixSet U)
    (hn : n ∈ integralMatrixSet U) : m * n ∈ integralMatrixSet U := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact hadd _ (hmul _ (hm i 0) _ (hn 0 j)) _ (hmul _ (hm i 1) _ (hn 1 j))

private theorem mul_mem_integralUnitsSet {U : Set A} (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) {g h : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U)
    (hh : h ∈ integralUnitsSet U) : g * h ∈ integralUnitsSet U := by
  refine ⟨?_, ?_⟩
  · exact integralMatrixSet_mul_mem hadd hmul hg.1 hh.1
  · rw [mul_inv_rev]
    exact integralMatrixSet_mul_mem hadd hmul hh.2 hg.2

private theorem inv_mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U) :
    g⁻¹ ∈ integralUnitsSet U := by
  refine ⟨hg.2, ?_⟩
  rw [inv_inv]
  exact hg.1

end IntegralClosure

section SemiLocalClosure

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

omit [NumberField L] in
private theorem semiLocalIntegers_add_mem {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a + b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add _ _ _⟩

omit [NumberField L] in
private theorem semiLocalIntegers_mul_mem {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, map_mul _ _ _⟩

omit [NumberField L] in
private theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v :=
  mul_mem_integralUnitsSet (fun _ ha _ hb => semiLocalIntegers_add_mem K L v ha hb)
    (fun _ ha _ hb => semiLocalIntegers_mul_mem K L v ha hb) hg hh

omit [NumberField L] in
private theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet hg

private def IsIntegralOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Prop :=
  ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v

variable {K L}

private theorem IsIntegralOutside.mul
    {S : Finset (HeightOneSpectrum (𝓞 K))} {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hg : IsIntegralOutside K L S g) (hh : IsIntegralOutside K L S h) : IsIntegralOutside K L S (g * h) :=
  fun v hv => by
    rw [map_mul]
    exact mul_mem_semiLocalIntegralSet K L v (hg v hv) (hh v hv)

private theorem IsIntegralOutside.inv {S : Finset (HeightOneSpectrum (𝓞 K))} {g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hg : IsIntegralOutside K L S g) : IsIntegralOutside K L S g⁻¹ := fun v hv => by
  rw [map_inv]
  exact inv_mem_semiLocalIntegralSet K L v (hg v hv)

private theorem IsIntegralOutside.inv_mul_iff {S : Finset (HeightOneSpectrum (𝓞 K))}
    {y h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hy : IsIntegralOutside K L S y) :
    IsIntegralOutside K L S (y⁻¹ * h) ↔ IsIntegralOutside K L S h := by
  constructor
  · intro hyh
    have := hy.mul hyh
    rwa [mul_inv_cancel_left] at this
  · intro hh
    exact hy.inv.mul hh

end SemiLocalClosure

section ArchFactor

open scoped Classical

attribute [local instance] glBorelOf

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  show Continuous fun x : InfiniteAdeleRing F =>
    ((fun v : {w : InfinitePlace F // w.IsReal} => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :
        mixedEmbedding.mixedSpace F)
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

private def archMat (g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) :=
  (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).map (InfiniteAdeleRing.ringEquiv_mixedSpace F)

omit [NumberField F] in
private theorem archEntries_eq_archMat (g : GL (Fin 2) (InfiniteAdeleRing F)) : archEntries F g = archMat F g := rfl

omit [NumberField F] in
private theorem archMat_mul
    (g h : GL (Fin 2) (InfiniteAdeleRing F)) : archMat F (g * h) = archMat F g * archMat F h := by
  simp only [archMat, Units.val_mul, Matrix.map_mul]

omit [NumberField F] in
private theorem continuous_archMat : Continuous (archMat F) :=
  Units.continuous_val.matrix_map (continuous_ringEquiv_mixedSpace F)

omit [NumberField F] in
private theorem continuous_archMat_inv : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) => archMat F g⁻¹ :=
  (continuous_archMat F).comp continuous_inv

private theorem isArchTestFactor_continuous {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have : fa = fun g => Φ (archMat F g) := funext fun g => hfa g
  rw [this]
  exact hΦ.continuous.comp (continuous_archMat F)

private theorem isArchTestFactor_smul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hc⟩ := h
  exact ⟨⟨c • Φ, contDiff_const.smul hΦ, fun g => by simp only [Pi.smul_apply, hfa g]⟩,
    hc.comp_left (g := fun z : ℂ => c • z) (smul_zero c)⟩

private def archMulLeft (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ (archMat F y⁻¹) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) →ₗ[ℝ]
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))

private theorem archMulLeft_apply (y : GL (Fin 2) (InfiniteAdeleRing F))
    (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) : archMulLeft F y m = archMat F y⁻¹ * m :=
  rfl

private theorem continuous_archMulLeft : Continuous (archMulLeft F) := by
  refine continuous_clm_apply.2 fun e => ?_
  rw [show (fun y : GL (Fin 2) (InfiniteAdeleRing F) => archMulLeft F y e) = fun y => archMat F y⁻¹ * Matrix.of e from
    funext fun y => archMulLeft_apply F y (Matrix.of e)]
  exact (continuous_archMat_inv F).matrix_mul continuous_const

private theorem isArchTestFactor_gconv
    (μa : @Measure (GL (Fin 2) (InfiniteAdeleRing F)) (glBorelOf (InfiniteAdeleRing F)))
    (hμa : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing F)) _ _ (glBorelOf (InfiniteAdeleRing F)) μa)
    {ψa φa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hψ : IsArchTestFactor F ψa) (hφ : IsArchTestFactor F φa) :
    IsArchTestFactor F (gconv μa ψa φa) := by
  letI := glBorelOf (InfiniteAdeleRing F)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing F)
  haveI := secondCountableTopology_infiniteAdeleRing F
  haveI := t2Space_gl (InfiniteAdeleRing F)
  haveI := locallyCompactSpace_gl (InfiniteAdeleRing F)
  haveI := secondCountableTopology_gl (InfiniteAdeleRing F)
  haveI : μa.IsHaarMeasure := hμa
  have hψcont : Continuous ψa := isArchTestFactor_continuous F hψ
  obtain ⟨⟨Φφ, hΦφ, hφeq⟩, hφc⟩ := hφ
  obtain ⟨-, hψc⟩ := hψ

  let T : GL (Fin 2) (InfiniteAdeleRing F) → ℂ →L[ℝ] ℂ :=
    ⇑(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) ∘ ψa
  have hT : Continuous T := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).continuous.comp hψcont
  have hTc : HasCompactSupport T := hψc.comp_left (map_zero (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ))
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F =>
      ∫ y, T y (Φφ (archMulLeft F y e)) ∂μa :=
    contDiff_top_integral_clm_comp μa hΦφ hT hTc (continuous_archMulLeft F)
  have hid : ∀ g, gconv μa ψa φa g = ∫ y, T y (Φφ (archMulLeft F y (archEntries F g))) ∂μa := by
    intro g
    rw [gconv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [T, Function.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hφeq (y⁻¹ * g), archEntries_eq_archMat, archEntries_eq_archMat, archMulLeft_apply, archMat_mul]
  exact ⟨⟨_, hsmooth, hid⟩, hasCompactSupport_gconv μa hψc hφc⟩

end ArchFactor

section HaarSplitting

variable (L : Type) [Field L] [NumberField L]

private def haarSplitLaw : Prop :=
  ∃ (μa : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (glBorelOf (InfiniteAdeleRing L)))
    (μf : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (glBorelOf (FiniteAdeleRing (𝓞 L) L))),
    @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing L)) _ _ (glBorelOf (InfiniteAdeleRing L)) μa ∧
    @Measure.IsHaarMeasure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) _ _ (glBorelOf (FiniteAdeleRing (𝓞 L) L)) μf ∧
    ∀ (Fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (Ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      Continuous Fa → Continuous Ff →
      ∫ g, Fa (AdelicLevel.glArch (𝓞 L) L g) * Ff (AdelicLevel.glFin (𝓞 L) L g)
          ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) =
        (∫ a, Fa a ∂μa) * ∫ b, Ff b ∂μf

end HaarSplitting

section GLMap

variable {R S : Type} [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]

private theorem continuous_generalLinearGroup_map (f : R →+* S) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

end GLMap

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private theorem continuous_semiLocalEval : Continuous (semiLocalEval K L v) :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).symm.continuous.comp
    (continuous_pi fun w : v.Extension (𝓞 L) => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1)

private theorem continuous_semiLocalComponent : Continuous (semiLocalComponent K L v) :=
  continuous_generalLinearGroup_map (semiLocalEval K L v) (continuous_semiLocalEval K L v)

private theorem isClosed_semiLocalIntegralSet : IsClosed (semiLocalIntegralSet K L v) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  exact (isCompact_semiLocalIntegralSet K L v).isClosed

private theorem isClosed_setOf_integralOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClosed {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
      ∀ w ∉ S, semiLocalComponent K L w h ∈ semiLocalIntegralSet K L w} := by
  have : {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
        ∀ w ∉ S, semiLocalComponent K L w h ∈ semiLocalIntegralSet K L w} =
      ⋂ w : HeightOneSpectrum (𝓞 K), ⋂ (_ : w ∉ S), semiLocalComponent K L w ⁻¹' semiLocalIntegralSet K L w := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (isClosed_semiLocalIntegralSet K L w).preimage (continuous_semiLocalComponent K L w)

end SemiLocal

section Componentwise

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem exists_of_not_integralOutside {S : Finset (HeightOneSpectrum (𝓞 K))}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hn : ¬ IsIntegralOutside K L S h) :
    ∃ v ∉ S, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v := by
  by_contra hc
  exact hn fun v hv => by_contra fun hnot => hc ⟨v, hv, hnot⟩

private def semiSplitLaw : Prop :=
  ∀ (μf : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (glBorelOf (FiniteAdeleRing (𝓞 L) L))),
    @Measure.IsHaarMeasure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) _ _ (glBorelOf (FiniteAdeleRing (𝓞 L) L)) μf →
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
    ∃ c : ℝ, 0 < c ∧
      ∀ F : (v : HeightOneSpectrum (𝓞 K)) → (GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ v ∈ S, Continuous (F v) ∧ HasCompactSupport (F v)) →
        ∫ h in {h | ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v},
            ∏ v ∈ S, F v (semiLocalComponent K L v h) ∂μf =
          (c : ℂ) * ∏ v ∈ S, ∫ t, F v t ∂(semiLocalHaar K L v)

attribute [local instance] glBorelOf

private theorem exists_isSemiLocalFactorization_gconv (hE2a : haarSplitLaw L) (hE2b : semiSplitLaw K L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ φ : AdelicGL2 (𝓞 L) L → ℂ)
    (ψa φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (ψf φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (ψS φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hψ : IsSemiLocalFactorization K L S ψ ψa ψf ψS) (hφ : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ (χa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (χf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L S (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) χa χf
        (fun v t => ∫ s, ψS v s * φS v (s⁻¹ * t) ∂(semiLocalHaar K L v)) := by
  obtain ⟨μa, μf, hμa, hμf, hsplit⟩ := hE2a
  obtain ⟨c, hc, hE⟩ := hE2b μf hμf S
  obtain ⟨hψa, hψf, hψS, hψprod, hψzero, hψeq⟩ := hψ
  obtain ⟨hφa, hφf, hφS, hφprod, hφzero, hφeq⟩ := hφ
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  haveI := borelSpace_glBorelOf (FiniteAdeleRing (𝓞 L) L)

  have hfin : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L), IsIntegralOutside K L S h →
      gconv μf ψf φf h =
        (c : ℂ) * ∏ v ∈ S, ∫ s, ψS v s * φS v (s⁻¹ * semiLocalComponent K L v h) ∂(semiLocalHaar K L v) := by
    intro h hh
    let F : (v : HeightOneSpectrum (𝓞 K)) → (GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :=
      fun v t => ψS v t * φS v (t⁻¹ * semiLocalComponent K L v h)
    have hF : ∀ v ∈ S, Continuous (F v) ∧ HasCompactSupport (F v) := by
      intro v hv
      obtain ⟨hψlc, hψcs⟩ := hψS v hv
      obtain ⟨hφlc, -⟩ := hφS v hv
      haveI hG := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
      haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hG.toContinuousMul
      haveI : ContinuousInv (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hG.toContinuousInv
      exact ⟨hψlc.continuous.mul (hφlc.continuous.comp (continuous_inv.mul continuous_const)), hψcs.mul_right⟩
    have h0 : ∀ y, y ∉ {y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
        ∀ v ∉ S, semiLocalComponent K L v y ∈ semiLocalIntegralSet K L v} → ψf y * φf (y⁻¹ * h) = 0 := by
      intro y hy
      rw [hψzero y (exists_of_not_integralOutside K L hy), zero_mul]
    calc gconv μf ψf φf h = ∫ y, ψf y * φf (y⁻¹ * h) ∂μf := gconv_apply μf ψf φf h
      _ = ∫ y in {y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
            ∀ v ∉ S, semiLocalComponent K L v y ∈ semiLocalIntegralSet K L v}, ψf y * φf (y⁻¹ * h) ∂μf :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = ∫ y in {y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
            ∀ v ∉ S, semiLocalComponent K L v y ∈ semiLocalIntegralSet K L v},
            ∏ v ∈ S, F v (semiLocalComponent K L v y) ∂μf := by
          refine setIntegral_congr_fun (isClosed_setOf_integralOutside K L S).measurableSet fun y hy => ?_
          have hy' : IsIntegralOutside K L S y := hy
          have hyh : IsIntegralOutside K L S (y⁻¹ * h) := hy'.inv.mul hh
          rw [hψprod y hy', hφprod _ hyh, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun v _ => ?_
          show ψS v (semiLocalComponent K L v y) * φS v (semiLocalComponent K L v (y⁻¹ * h)) =
            ψS v (semiLocalComponent K L v y) *
              φS v ((semiLocalComponent K L v y)⁻¹ * semiLocalComponent K L v h)
          rw [map_mul, map_inv]
      _ = (c : ℂ) * ∏ v ∈ S, ∫ t, F v t ∂(semiLocalHaar K L v) := hE F hF
      _ = _ := rfl

  have hvan : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L), ¬ IsIntegralOutside K L S h → gconv μf ψf φf h = 0 := by
    intro h hh
    rw [gconv_apply]
    have : ∀ y, ψf y * φf (y⁻¹ * h) = 0 := by
      intro y
      by_cases hy : IsIntegralOutside K L S y
      · have hyh : ¬ IsIntegralOutside K L S (y⁻¹ * h) := fun hyh => hh (hy.inv_mul_iff.1 hyh)
        rw [hφzero _ (exists_of_not_integralOutside K L hyh), mul_zero]
      · rw [hψzero y (exists_of_not_integralOutside K L hy), zero_mul]
    simp only [this, integral_zero]
  refine ⟨(c : ℂ) • gconv μa ψa φa, (c : ℂ)⁻¹ • gconv μf ψf φf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isArchTestFactor_smul L (isArchTestFactor_gconv L μa hμa hψa hφa) (c : ℂ)
  · haveI : μf.IsHaarMeasure := hμf
    exact ⟨(isLocallyConstant_gconv μf ψf hφf.1 hφf.2).comp fun z : ℂ => (c : ℂ)⁻¹ • z,
      (hasCompactSupport_gconv μf hψf.2 hφf.2).comp_left (g := fun z : ℂ => (c : ℂ)⁻¹ • z) (smul_zero _)⟩
  · intro v hv
    obtain ⟨hψlc, hψcs⟩ := hψS v hv
    obtain ⟨hφlc, hφcs⟩ := hφS v hv
    haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
    exact ⟨isLocallyConstant_gconv (semiLocalHaar K L v) (ψS v) hφlc hφcs,
      hasCompactSupport_gconv (semiLocalHaar K L v) hψcs hφcs⟩
  · intro h hh
    show (c : ℂ)⁻¹ * gconv μf ψf φf h = _
    rw [hfin h hh, inv_mul_cancel_left₀ hc']
  · intro h hh
    show (c : ℂ)⁻¹ * gconv μf ψf φf h = 0
    rw [hvan h (fun hint => by obtain ⟨v, hv, hnot⟩ := hh; exact hnot (hint v hv)), mul_zero]
  · intro g
    show (∫ y, ψ y * φ (y⁻¹ * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ((c : ℂ) * gconv μa ψa φa (AdelicLevel.glArch (𝓞 L) L g)) *
        ((c : ℂ)⁻¹ * gconv μf ψf φf (AdelicLevel.glFin (𝓞 L) L g))
    have hint : (fun y => ψ y * φ (y⁻¹ * g)) = fun y =>
        (fun a => ψa a * φa (a⁻¹ * AdelicLevel.glArch (𝓞 L) L g)) (AdelicLevel.glArch (𝓞 L) L y) *
          (fun b => ψf b * φf (b⁻¹ * AdelicLevel.glFin (𝓞 L) L g)) (AdelicLevel.glFin (𝓞 L) L y) := by
      funext y
      simp only [hψeq y, hφeq (y⁻¹ * g), map_mul, map_inv]
      ring
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hc', one_mul, hint]
    exact hsplit (fun a => ψa a * φa (a⁻¹ * AdelicLevel.glArch (𝓞 L) L g))
      (fun b => ψf b * φf (b⁻¹ * AdelicLevel.glFin (𝓞 L) L g))
      ((isArchTestFactor_continuous L hψa).mul ((isArchTestFactor_continuous L hφa).comp
        (continuous_inv.mul continuous_const)))
      (hψf.1.continuous.mul (hφf.1.continuous.comp (continuous_inv.mul continuous_const)))

end Componentwise

end

end ConvFactors

open AutomorphicForm

namespace ConvFactors

private theorem haarSplitLaw_holds (L : Type) [Field L] [NumberField L] : haarSplitLaw L := by
  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing L)
  letI : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := glBorelOf (FiniteAdeleRing (𝓞 L) L)
  haveI := borelSpace_glBorelOf (FiniteAdeleRing (𝓞 L) L)
  haveI := locallyCompactSpace_gl (InfiniteAdeleRing L)
  haveI := locallyCompactSpace_gl (FiniteAdeleRing (𝓞 L) L)
  let μa₀ : Measure (GL (Fin 2) (InfiniteAdeleRing L)) := Measure.haarMeasure (Classical.arbitrary _)
  let μf₀ : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := Measure.haarMeasure (Classical.arbitrary _)
  haveI : μa₀.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : μf₀.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : μa₀.Regular := Measure.regular_haarMeasure
  haveI : μf₀.Regular := Measure.regular_haarMeasure
  obtain ⟨c, hc, hsplit⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral L μa₀ μf₀
  have hμa : ((c : ENNReal) • μa₀).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul μa₀ (by exact_mod_cast hc.ne') ENNReal.coe_ne_top
  refine ⟨(c : ENNReal) • μa₀, μf₀, hμa, inferInstance, fun Fa Ff _ _ => ?_⟩
  refine (hsplit Fa Ff).trans ?_
  rw [integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  ring

end ConvFactors

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ψ φ : AdelicGL2 (𝓞 L) L → ℂ)
    (ψa φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (ψf φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (ψS φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hψ : IsSemiLocalFactorization K L S ψ ψa ψf ψS) (hφ : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ (χa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (χf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L S (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) χa χf
        (fun v t => ∫ s, ψS v s * φS v (s⁻¹ * t) ∂(semiLocalHaar K L v)) :=
  ConvFactors.exists_isSemiLocalFactorization_gconv K L
    (ConvFactors.haarSplitLaw_holds L)
    (AutomorphicForm.exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral K L)
    S ψ φ ψa φa ψf φf ψS φS hψ hφ

#print axioms solution

end S_AutomorphicForm_exists_isSemiLocalFactorization_integral_mul_comp_inv_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_integral_mul_comp_inv_mul (solution)
