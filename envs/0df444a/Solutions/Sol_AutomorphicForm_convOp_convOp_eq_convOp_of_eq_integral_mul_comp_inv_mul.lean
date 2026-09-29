-- Prove2me | solution 1 for AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/07a77962-b980-5dd9-8b76-6e917df922da

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_integral_mul_comp_inv_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ConvolutionTier

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

section Extension

variable {H G : Type*} [Group H] [Group G]

section Cosets

variable (ι : H →* G)

private noncomputable def _root_.ConvolutionTier.rep (x : G) : G := (QuotientGroup.mk x : G ⧸ ι.range).out

p2m_export "ConvolutionTier" "rep"
private theorem rep_spec (x : G) : (rep ι x)⁻¹ * x ∈ ι.range := by
  have h : (QuotientGroup.mk (rep ι x) : G ⧸ ι.range) = QuotientGroup.mk x := by
    unfold rep
    exact QuotientGroup.out_eq' _
  exact QuotientGroup.eq.mp h

private theorem rep_mul (x : G) (h : H) : rep ι (x * ι h) = rep ι x := by
  unfold rep
  congr 1
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [inv_mul_cancel_left]
  exact ⟨h, rfl⟩

private noncomputable def cok (x : G) : H := (rep_spec ι x).choose

private theorem cok_spec (x : G) : ι (cok ι x) = (rep ι x)⁻¹ * x := (rep_spec ι x).choose_spec

private theorem rep_mul_cok (x : G) : rep ι x * ι (cok ι x) = x := by
  rw [cok_spec, mul_inv_cancel_left]

variable {ι}

private theorem cok_mul (hι : Function.Injective ι) (x : G) (h : H) :
    cok ι (x * ι h) = cok ι x * h := by
  apply hι
  rw [map_mul, cok_spec, cok_spec, rep_mul, mul_assoc]

end Cosets

section Extend

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem exists_extend_equivariant {ι : H →* G} (hι : Function.Injective ι)
    (ρ' : Representation ℂ H V) (A : Submodule ℂ V) (hA : ∀ (h : H), ∀ a ∈ A, ρ' h a ∈ A)
    (M₀ : A →ₗ[ℂ] (G → ℂ))
    (hM₀ : ∀ (h : H) (a : A) (x : G), M₀ ⟨ρ' h a, hA h a a.2⟩ x = M₀ a (x * ι h)) :
    ∃ M : V →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ' M ∧ ∀ a : A, M a = M₀ a := by
  obtain ⟨M₁, hM₁⟩ := LinearMap.exists_extend M₀
  have hM₁' : ∀ a : A, M₁ a = M₀ a := fun a => by
    rw [← hM₁]
    rfl
  let M : V →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun v x => M₁ (ρ' (cok ι x) v) (rep ι x)
      map_add' := fun v w => by
        funext x
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c v => by
        funext x
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨M, ?_, ?_⟩
  · intro h v x
    show M₁ (ρ' (cok ι x) (ρ' h v)) (rep ι x) = M₁ (ρ' (cok ι (x * ι h)) v) (rep ι (x * ι h))
    rw [cok_mul hι, rep_mul, map_mul, Module.End.mul_apply]
  · intro a
    funext x
    show M₁ (ρ' (cok ι x) a) (rep ι x) = M₀ a x
    have h1 : M₁ (ρ' (cok ι x) a) = M₀ ⟨ρ' (cok ι x) a, hA (cok ι x) a a.2⟩ :=
      hM₁' ⟨ρ' (cok ι x) a, hA (cok ι x) a a.2⟩
    rw [h1, hM₀, rep_mul_cok]

end Extend

section FunctionSpace

variable (ι : H →* G)

private def regRep : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun u x => u (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun u => funext fun x => by simp
  map_mul' a b := LinearMap.ext fun u => funext fun x => by simp [mul_assoc]

variable {ι}

private theorem exists_linear_equivariant_extension (hι : Function.Injective ι) (N : Submodule ℂ (G → ℂ))
    (hN : ∀ (k : H), ∀ u ∈ N, (fun x => u (x * ι k)) ∈ N) (Φ : (G → ℂ) → (G → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (k : H), ∀ u ∈ N, Φ (fun x => u (x * ι k)) = fun x => Φ u (x * ι k)) :
    ∃ Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k)) ∧ ∀ u ∈ N, Ψ u = Φ u := by
  have hN' : ∀ (k : H), ∀ u ∈ N, regRep ι k u ∈ N := fun k u hu => hN k u hu
  let M₀ : N →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun u => Φ u
      map_add' := fun u v => hadd u u.2 v v.2
      map_smul' := fun c u => hsmul c u u.2 }
  have hM₀ : ∀ (k : H) (u : N) (x : G), M₀ ⟨regRep ι k u, hN' k u u.2⟩ x = M₀ u (x * ι k) := by
    intro k u x
    exact congrFun (hequiv k u u.2) x
  obtain ⟨Ψ, hΨ, hΨN⟩ := exists_extend_equivariant hι (regRep ι) N hN' M₀ hM₀
  exact ⟨Ψ, fun k u => funext fun x => hΨ k u x, fun u hu => hΨN ⟨u, hu⟩⟩

private theorem typeSubmodule_le_comap {Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hΨ : ∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k))
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) :
    typeSubmodule ι ρ ≤ (typeSubmodule ι ρ).comap Ψ := by
  unfold typeSubmodule
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, hmem⟩
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hmem
  have hcomp : IsRightEquivariant ι ρ (Ψ.comp T) := by
    intro k w x
    have h1 : T (ρ k w) = fun y => T w (y * ι k) := funext fun y => hT k w y
    show Ψ (T (ρ k w)) x = Ψ (T w) (x * ι k)
    rw [h1]
    exact congrFun (hΨ k (T w)) x
  exact mem_typeSubmodule_of_isRightEquivariant hcomp v

private theorem iSup_typeSubmodule_le_comap {Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hΨ : ∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k))
    {κ : Type*} {W : κ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) :
    (⨆ i, typeSubmodule ι (ρ i)) ≤ (⨆ i, typeSubmodule ι (ρ i)).comap Ψ :=
  iSup_le fun i =>
    (typeSubmodule_le_comap hΨ (ρ i)).trans (Submodule.comap_mono (le_iSup (fun j => typeSubmodule ι (ρ j)) i))

private theorem map_mem_iSup_typeSubmodule (hι : Function.Injective ι) (N : Submodule ℂ (G → ℂ))
    (hN : ∀ (k : H), ∀ u ∈ N, (fun x => u (x * ι k)) ∈ N) (Φ : (G → ℂ) → (G → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (k : H), ∀ u ∈ N, Φ (fun x => u (x * ι k)) = fun x => Φ u (x * ι k))
    {κ : Type*} {W : κ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) {u : G → ℂ} (hu : u ∈ ⨆ i, typeSubmodule ι (ρ i)) (huN : u ∈ N) :
    Φ u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  obtain ⟨Ψ, hΨ, hΨN⟩ := exists_linear_equivariant_extension hι N hN Φ hadd hsmul hequiv
  rw [← hΨN u huN]
  exact iSup_typeSubmodule_le_comap hΨ ρ hu

end FunctionSpace

section Pins

open NumberField

variable (F : Type) [Field F] [NumberField F]

private theorem map_mem_archCutSubmodule
    (hinj : ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w))
    (N : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hN : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      (fun x => u (x * rowIsometryInclAt₀ F w k)) ∈ N)
    (Φ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      Φ (fun x => u (x * rowIsometryInclAt₀ F w k)) = fun x => Φ u (x * rowIsometryInclAt₀ F w k))
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) (huN : u ∈ N) :
    Φ u ∈ archCutSubmodule F tys := by
  unfold archCutSubmodule at hu ⊢
  rw [Submodule.mem_iInf] at hu ⊢
  intro w
  have hw := hu w
  unfold archTypeSubmoduleAt at hw ⊢
  exact map_mem_iSup_typeSubmodule (hinj w) N (hN w) Φ hadd hsmul (hequiv w) (fun i => (tys.rep w i).ρ) hw huN

end Pins

end Extension

section PinsDual

variable (F : Type) [Field F] [NumberField F]

private theorem map_mem_archDualCutSubmodule
    (hinj : ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w))
    (N : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hN : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      (fun x => u (x * rowIsometryInclAt₀ F w k)) ∈ N)
    (Φ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      Φ (fun x => u (x * rowIsometryInclAt₀ F w k)) = fun x => Φ u (x * rowIsometryInclAt₀ F w k))
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archDualCutSubmodule F tys) (huN : u ∈ N) :
    Φ u ∈ archDualCutSubmodule F tys := by
  unfold archDualCutSubmodule at hu ⊢
  rw [Submodule.mem_iInf] at hu ⊢
  intro w
  have hw := hu w
  unfold archDualTypeSubmoduleAt at hw ⊢
  exact map_mem_iSup_typeSubmodule (hinj w) N (hN w) Φ hadd hsmul (hequiv w) (fun i => (tys.rep w i).ρ.dual) hw huN

private theorem inclAt₀_injective (w : InfinitePlace F) : Function.Injective (rowIsometryInclAt₀ F w) := by
  intro k₁ k₂ h
  have h1 : AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k₁) =
      AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k₂) := congrArg _ h
  rw [glArch_rowIsometryInclAt₀, glArch_rowIsometryInclAt₀] at h1
  have h1' : archGLIncl F w (k₁ : GL (Fin 2) w.Completion) = archGLIncl F w (k₂ : GL (Fin 2) w.Completion) := h1
  have h2 := congrArg (AdelicLevel.archComponent F w) h1'
  rw [archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h2
  exact Subtype.ext h2

end PinsDual

section Adelic

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (L : Type) [Field L] [NumberField L]

private noncomputable abbrev adelicConv (ψ φ : AdelicGL2 (𝓞 L) L → ℂ) : AdelicGL2 (𝓞 L) L → ℂ :=
  gconv (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) ψ φ

private theorem convOp_convOp_eq_convOp_adelicConv
    {φ ψ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {w : AdelicGL2 (𝓞 L) L → ℂ} (hw : Continuous w) :
    AutomorphicForm.convOp L ψ (AutomorphicForm.convOp L φ w) =
      AutomorphicForm.convOp L (adelicConv L ψ φ) w := by
  haveI := secondCountableTopology_adelicGL2 L
  haveI := sigmaCompactSpace_adelicGL2 L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  funext g
  simp only [AutomorphicForm.convOp_apply, AutomorphicForm.rightConv_apply]
  exact integral_integral_eq_integral_gconv (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) hφ hφc hψ hψc hw g

private theorem continuous_adelicConv
    {φ ψ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) : Continuous (adelicConv L ψ φ) := by
  haveI := secondCountableTopology_adelicGL2 L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  exact continuous_gconv _ hψ hψc hφ hφc

private theorem hasCompactSupport_adelicConv {φ ψ : AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ)
    (hψc : HasCompactSupport ψ) : HasCompactSupport (adelicConv L ψ φ) :=
  hasCompactSupport_gconv (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) hψc hφc

private theorem isBiInvariantUnder_adelicConv (U : Subgroup (AdelicGL2 (𝓞 L) L)) {φ ψ : AdelicGL2 (𝓞 L) L → ℂ}
    (hψ : AutomorphicForm.IsBiInvariantUnder L U ψ) (hφ : AutomorphicForm.IsBiInvariantUnder L U φ) :
    AutomorphicForm.IsBiInvariantUnder L U (adelicConv L ψ φ) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  intro u hu z
  exact ⟨gconv_mul_left_eq _ φ (fun x => (hψ u hu x).1) z, gconv_mul_right_eq _ ψ (fun x => (hφ u hu x).2) z⟩

private theorem sum_singleton_one_smul_convOp (χ₀ w : AdelicGL2 (𝓞 L) L → ℂ) :
    ∑ χ ∈ ({χ₀} : Finset (AdelicGL2 (𝓞 L) L → ℂ)), (fun _ => (1 : ℂ)) χ • AutomorphicForm.convOp L χ w =
      AutomorphicForm.convOp L χ₀ w := by
  classical
  simp

private theorem convOp_add_fun {χ₁ χ₂ : AdelicGL2 (𝓞 L) L → ℂ} (h₁ : Continuous χ₁) (h₁c : HasCompactSupport χ₁)
    (h₂ : Continuous χ₂) (h₂c : HasCompactSupport χ₂) {w : AdelicGL2 (𝓞 L) L → ℂ} (hw : Continuous w) :
    AutomorphicForm.convOp L (χ₁ + χ₂) w = AutomorphicForm.convOp L χ₁ w + AutomorphicForm.convOp L χ₂ w := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hint : ∀ {χ : AdelicGL2 (𝓞 L) L → ℂ}, Continuous χ → HasCompactSupport χ → ∀ g : AdelicGL2 (𝓞 L) L,
      Integrable (fun x => w (g * x) * χ x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := by
    intro χ hχ hχc g
    have hc : Continuous fun x : AdelicGL2 (𝓞 L) L => w (g * x) * χ x :=
      (hw.comp (continuous_const.mul continuous_id)).mul hχ
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 L) L => w (g * x) * χ x := hχc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext g
  simp only [AutomorphicForm.convOp_apply, AutomorphicForm.rightConv_apply, Pi.add_apply, mul_add]
  exact integral_add (hint h₁ h₁c g) (hint h₂ h₂c g)

private theorem convOp_smul_fun (a : ℂ) (χ w : AdelicGL2 (𝓞 L) L → ℂ) :
    AutomorphicForm.convOp L (a • χ) w = a • AutomorphicForm.convOp L χ w := by
  funext g
  simp only [AutomorphicForm.convOp_apply, AutomorphicForm.rightConv_apply, Pi.smul_apply, smul_eq_mul,
    mul_left_comm _ a]
  exact integral_const_mul a _

private def ccSubmodule : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) where
  carrier := {u | Continuous u ∧ HasCompactSupport u}
  zero_mem' := ⟨continuous_const, HasCompactSupport.zero⟩
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  smul_mem' := fun c _ ha => ⟨ha.1.const_smul c, ha.2.smul_left⟩

private theorem mem_ccSubmodule {u : AdelicGL2 (𝓞 L) L → ℂ} :
    u ∈ ccSubmodule L ↔ Continuous u ∧ HasCompactSupport u :=
  Iff.rfl

private theorem comp_mul_right_mem_ccSubmodule (g : AdelicGL2 (𝓞 L) L) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ ccSubmodule L) : (fun x => u (x * g)) ∈ ccSubmodule L := by
  obtain ⟨hc, hs⟩ := (mem_ccSubmodule L).1 hu
  exact (mem_ccSubmodule L).2
    ⟨hc.comp (continuous_id.mul continuous_const), hs.comp_homeomorph (Homeomorph.mulRight g)⟩

private theorem comp_inv_mem_ccSubmodule {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ ccSubmodule L) :
    (fun x => u x⁻¹) ∈ ccSubmodule L := by
  obtain ⟨hc, hs⟩ := (mem_ccSubmodule L).1 hu
  exact (mem_ccSubmodule L).2 ⟨hc.comp continuous_inv, hs.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 L) L))⟩

private theorem adelicConv_mem_archDualCutSubmodule {ψ : AdelicGL2 (𝓞 L) L → ℂ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (tys : ArchTypeFamily L) (h : φ ∈ archDualCutSubmodule L tys) :
    adelicConv L ψ φ ∈ archDualCutSubmodule L tys := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  refine map_mem_archDualCutSubmodule L (inclAt₀_injective L) (ccSubmodule L)
    (fun w k u hu => comp_mul_right_mem_ccSubmodule L _ hu) (fun u => adelicConv L ψ u)
    (fun u hu u' hu' => gconv_add_right _ hψ hψc ((mem_ccSubmodule L).1 hu).1 ((mem_ccSubmodule L).1 hu').1)
    (fun c u _ => gconv_smul_right _ ψ c u) (fun w k u _ => gconv_comp_mul_right _ ψ u _) tys h
    ((mem_ccSubmodule L).2 ⟨hφ, hφc⟩)

private theorem adelicConv_inv_mem_archCutSubmodule {ψ : AdelicGL2 (𝓞 L) L → ℂ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ)
    (tys : ArchTypeFamily L) (h : (fun x => ψ x⁻¹) ∈ archCutSubmodule L tys) :
    (fun x => adelicConv L ψ φ x⁻¹) ∈ archCutSubmodule L tys := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hmap := map_mem_archCutSubmodule L (inclAt₀_injective L) (ccSubmodule L)
    (fun w k u hu => comp_mul_right_mem_ccSubmodule L _ hu)
    (fun u => fun x => adelicConv L (fun y => u y⁻¹) φ x⁻¹)
    (fun u hu u' hu' => by
      funext x
      obtain ⟨hc₁, hs₁⟩ := (mem_ccSubmodule L).1 (comp_inv_mem_ccSubmodule L hu)
      obtain ⟨hc₂, hs₂⟩ := (mem_ccSubmodule L).1 (comp_inv_mem_ccSubmodule L hu')
      show gconv (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) ((fun y => u y⁻¹) + fun y => u' y⁻¹) φ x⁻¹ = _
      rw [gconv_add_left _ hc₁ hs₁ hc₂ hs₂ hφ]
      rfl)
    (fun c u _ => by
      funext x
      show gconv (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) (c • fun y => u y⁻¹) φ x⁻¹ = _
      rw [gconv_smul_left]
      rfl)
    (fun w k u _ => by
      funext x
      exact gconv_inv_comp_mul_right _ u φ _ x)
    tys h (comp_inv_mem_ccSubmodule L ((mem_ccSubmodule L).2 ⟨hψ, hψc⟩))
  simpa only [inv_inv] using hmap
end Adelic

section FactorizationLaw

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def factorizeLaw : Prop :=
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (ψ φ : AdelicGL2 (𝓞 L) L → ℂ)
    (ψa φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (ψf φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (ψS φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
    IsSemiLocalFactorization K L S ψ ψa ψf ψS → IsSemiLocalFactorization K L S φ φa φf φS →
    ∃ (χa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (χf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L S (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) χa χf
        (fun v t => ∫ s, ψS v s * φS v (s⁻¹ * t) ∂(semiLocalHaar K L v))

end FactorizationLaw

section ConvolutionFactors

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] glBorelOf

private theorem isFactorizableTestFn_adelicConv (hE2a : haarSplitLaw L) {ψ φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hψ : IsFactorizableTestFn L ψ) (hφ : IsFactorizableTestFn L φ) : IsFactorizableTestFn L (adelicConv L ψ φ) := by
  obtain ⟨μa, μf, hμa, hμf, hsplit⟩ := hE2a
  obtain ⟨ψa, ψf, hψa, hψf, hψeq⟩ := hψ
  obtain ⟨φa, φf, hφa, hφf, hφeq⟩ := hφ
  refine ⟨gconv μa ψa φa, gconv μf ψf φf, isArchTestFactor_gconv L μa hμa hψa hφa,
    ⟨isLocallyConstant_gconv μf ψf hφf.1 hφf.2, hasCompactSupport_gconv μf hψf.2 hφf.2⟩, fun g => ?_⟩
  show (∫ y, ψ y * φ (y⁻¹ * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) = _
  have hint : (fun y => ψ y * φ (y⁻¹ * g)) = fun y =>
      (fun a => ψa a * φa (a⁻¹ * AdelicLevel.glArch (𝓞 L) L g)) (AdelicLevel.glArch (𝓞 L) L y) *
        (fun b => ψf b * φf (b⁻¹ * AdelicLevel.glFin (𝓞 L) L g)) (AdelicLevel.glFin (𝓞 L) L y) := by
    funext y
    simp only [hψeq y, hφeq (y⁻¹ * g), map_mul, map_inv]
    ring
  rw [hint]
  exact hsplit (fun a => ψa a * φa (a⁻¹ * AdelicLevel.glArch (𝓞 L) L g))
    (fun b => ψf b * φf (b⁻¹ * AdelicLevel.glFin (𝓞 L) L g))
    ((isArchTestFactor_continuous L hψa).mul ((isArchTestFactor_continuous L hφa).comp
      (continuous_inv.mul continuous_const)))
    (hψf.1.continuous.mul (hφf.1.continuous.comp (continuous_inv.mul continuous_const)))

end ConvolutionFactors

section ConvolutionAssembly

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem isUnitFactorizableAbove_adelicConv (hE2c : factorizeLaw K L) (U : Subgroup (AdelicGL2 (𝓞 L) L))
    (S : Finset (HeightOneSpectrum (𝓞 K))) {ψ φ : AdelicGL2 (𝓞 L) L → ℂ} (hψ : IsUnitFactorizableAbove K L U S ψ)
    (hφ : IsUnitFactorizableAbove K L U S φ) : IsUnitFactorizableAbove K L U S (adelicConv L ψ φ) := by
  obtain ⟨hψinv, ψa, ψf, ψS, hψfac⟩ := hψ
  obtain ⟨hφinv, φa, φf, φS, hφfac⟩ := hφ
  obtain ⟨χa, χf, hχ⟩ := hE2c S ψ φ ψa φa ψf φf ψS φS hψfac hφfac
  exact ⟨isBiInvariantUnder_adelicConv L U hψinv hφinv, χa, χf, _, hχ⟩

private theorem composition_law (hE2a : haarSplitLaw L) (hE2c : factorizeLaw K L)
    (U : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsFactorizableTestFn L φ ∧ Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsFactorizableTestFn L ψ ∧ Continuous ψ ∧ HasCompactSupport ψ) :
    ∀ χ : AdelicGL2 (𝓞 L) L → ℂ,
      χ = (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) →
      (IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ) ∧
      (∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → convOp L ψ (convOp L φ w) = convOp L χ w) ∧
      ((∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) → ∀ u ∈ U, ∀ x, χ (u * x) = χ x) ∧
      ((∀ u ∈ U, ∀ x, φ (x * u) = φ x) → ∀ u ∈ U, ∀ x, χ (x * u) = χ x) ∧
      (∀ tys : ArchTypeFamily L,
        (fun x => ψ x⁻¹) ∈ archCutSubmodule L tys → (fun x => χ x⁻¹) ∈ archCutSubmodule L tys) ∧
      (∀ tys : ArchTypeFamily L, φ ∈ archDualCutSubmodule L tys → χ ∈ archDualCutSubmodule L tys) ∧
      (IsUnitFactorizableAbove K L U S ψ → IsUnitFactorizableAbove K L U S φ →
        IsUnitFactorizableAbove K L U S χ) := by
  obtain ⟨hφF, hφC, hφS⟩ := hφ
  obtain ⟨hψF, hψC, hψS⟩ := hψ
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  rintro χ rfl
  refine ⟨⟨isFactorizableTestFn_adelicConv hE2a hψF hφF, continuous_adelicConv L hφC hφS hψC hψS,
      hasCompactSupport_adelicConv L hφS hψS⟩,
    fun w hw => convOp_convOp_eq_convOp_adelicConv L hφC hφS hψC hψS hw,
    fun hinv u hu x => gconv_mul_left_eq (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) φ (hinv u hu) x,
    fun hinv u hu x => gconv_mul_right_eq (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) ψ (hinv u hu) x,
    fun tys h => adelicConv_inv_mem_archCutSubmodule L hψC hψS hφC tys h,
    fun tys h => adelicConv_mem_archDualCutSubmodule L hψC hψS hφC hφS tys h,
    fun h₁ h₂ => isUnitFactorizableAbove_adelicConv hE2c U S h₁ h₂⟩

end ConvolutionAssembly

end

end ConvolutionTier

open AutomorphicForm

namespace ConvolutionTier

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

end ConvolutionTier

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (U : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsFactorizableTestFn L φ ∧ Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsFactorizableTestFn L ψ ∧ Continuous ψ ∧ HasCompactSupport ψ) :
    ∀ χ : AdelicGL2 (𝓞 L) L → ℂ,
      χ = (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) →
      (IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ) ∧
      (∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → convOp L ψ (convOp L φ w) = convOp L χ w) ∧
      ((∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) → ∀ u ∈ U, ∀ x, χ (u * x) = χ x) ∧
      ((∀ u ∈ U, ∀ x, φ (x * u) = φ x) → ∀ u ∈ U, ∀ x, χ (x * u) = χ x) ∧
      (∀ tys : ArchTypeFamily L,
        (fun x => ψ x⁻¹) ∈ archCutSubmodule L tys → (fun x => χ x⁻¹) ∈ archCutSubmodule L tys) ∧
      (∀ tys : ArchTypeFamily L, φ ∈ archDualCutSubmodule L tys → χ ∈ archDualCutSubmodule L tys) ∧
      (IsUnitFactorizableAbove K L U S ψ → IsUnitFactorizableAbove K L U S φ →
        IsUnitFactorizableAbove K L U S χ) :=
  ConvolutionTier.composition_law
    (ConvolutionTier.haarSplitLaw_holds L)
    (AutomorphicForm.exists_isSemiLocalFactorization_integral_mul_comp_inv_mul K L)
    U S φ ψ hφ hψ

#print axioms solution

end S_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
end P2MW
export P2MW.S_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul (solution)
