-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b5ad1b06-fdce-5676-bc1a-f116a8dd18ae

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

open AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

noncomputable section

namespace NormDomProof

open scoped Pointwise

section FDAction

variable {H X : Type*} [Group H] [MulAction H X] [MeasurableSpace X] [MeasurableConstSMul H X]
  [Countable H] {ν : Measure X} [SMulInvariantMeasure H X ν]

private theorem setLIntegral_fd_le_of_cover {S E : Set X} (hS : IsFundamentalDomain H S ν)
    (hcov : S ⊆ ⋃ γ : H, (γ • ·) ⁻¹' E) (G : X → ℝ≥0∞) (hG : ∀ (γ : H) (w : X), G (γ • w) = G w) :
    ∫⁻ w in S, G w ∂ν ≤ ∫⁻ w in E, G w ∂ν := by
  calc ∫⁻ w in S, G w ∂ν ≤ ∫⁻ w in ⋃ γ : H, S ∩ (γ • ·) ⁻¹' E, G w ∂ν := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hw)
        exact Set.mem_iUnion.mpr ⟨γ, hw, hγ⟩
    _ ≤ ∑' γ : H, ∫⁻ w in S ∩ (γ • ·) ⁻¹' E, G w ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : H, ∫⁻ w in γ • S ∩ E, G w ∂ν := by
        refine tsum_congr fun γ => ?_
        have hpre : (fun w : X => γ • w) ⁻¹' (γ • S ∩ E) = S ∩ (γ • ·) ⁻¹' E := by
          rw [Set.preimage_inter, Set.preimage_smul, inv_smul_smul]
        rw [← (measurePreserving_smul γ ν).setLIntegral_comp_preimage_emb
          (measurableEmbedding_const_smul γ) G (γ • S ∩ E), hpre]
        simp_rw [hG]
    _ = ∫⁻ w in E, G w ∂ν := by
        rw [hS.setLIntegral_eq_tsum G E]
        exact tsum_congr fun γ => by rw [Set.inter_comm]

end FDAction

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {S : Set G} (hS : MeasurableSet S)
    (hΓS : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' S = S) :
    SMulInvariantMeasure ↥Γ G (μ.restrict S) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓS γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hS)

variable [MeasurableMul G]

private theorem setLIntegral_biUnion_translates_le (μ : Measure G) [μ.IsMulLeftInvariant]
    {D : Set G} (Φ : G → ℝ≥0∞) {ι : Type*} (I : Finset ι) (b : ι → G) (k : ι → ℝ≥0∞)
    (hk : ∀ i, k i ≠ ∞) (hΦb : ∀ (i : ι) (w : G), Φ (b i * w) = k i * Φ w) :
    ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, Φ w ∂μ ≤ ∑ i ∈ I, k i * ∫⁻ w in D, Φ w ∂μ := by
  have hpiece : ∀ i, ∫⁻ w in (fun w => b i * w) '' D, Φ w ∂μ = k i * ∫⁻ w in D, Φ w ∂μ := by
    intro i
    rw [← (measurePreserving_mul_left μ (b i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (b i)) Φ D]
    simp_rw [hΦb]
    exact lintegral_const_mul' (k i) _ (hk i)
  calc ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, Φ w ∂μ
      ≤ ∫⁻ w in ⋃ i : ↥I, (fun w => b i * w) '' D, Φ w ∂μ := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hw⟩
    _ ≤ ∑' i : ↥I, ∫⁻ w in (fun w => b i * w) '' D, Φ w ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ I, ∫⁻ w in (fun w => b i * w) '' D, Φ w ∂μ := by
        rw [tsum_fintype, Finset.sum_coe_sort I fun i => ∫⁻ w in (fun w => b i * w) '' D, Φ w ∂μ]
    _ = ∑ i ∈ I, k i * ∫⁻ w in D, Φ w ∂μ := Finset.sum_congr rfl fun i _ => hpiece i

end Group

section Adelic

open NumberField.TateGlobal

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)

private abbrev slab (F : Type) [Field F] [NumberField F] (a b : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

private abbrev μH (F : Type) [Field F] [NumberField F] : Measure (AdelicGL2 (𝓞 F) F) :=
  adelicGLHaar (Fin 2) (𝓞 F) F

private abbrev Γp (F : Type) [Field F] [NumberField F] : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (globalPoints (𝓞 F) F).range

private scoped instance instCountableF : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

private scoped instance instCountableΓ : Countable ↥(Γp F) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (GL (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable

private theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [_root_.map_mul, ideleNorm_mul]

private theorem dn_globalPoints_mul (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    dn (globalPoints (𝓞 F) F γ * g) = dn g := by
  rw [dn_mul]
  show ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)) * dn g = dn g
  rw [AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

private theorem dn_subtype_mul (γ : ↥(Γp F)) (g : AdelicGL2 (𝓞 F) F) : dn ((γ : AdelicGL2 (𝓞 F) F) * g) = dn g := by
  obtain ⟨_, γ', rfl⟩ := γ
  exact dn_globalPoints_mul γ' g

private theorem subtype_mul_mem_slab (γ : ↥(Γp F)) {a b : ℝ} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ slab F a b) :
    (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b := by
  show dn ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ Set.Icc a b
  rw [dn_subtype_mul]
  exact hg

private theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab F a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b

private theorem preimage_subtype_mul_slab (γ : ↥(Γp F)) (a b : ℝ) :
    (fun w : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * w) ⁻¹' slab F a b = slab F a b := by
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [show ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * w)) = dn w from
    dn_subtype_mul γ w]

private theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp F) (AdelicGL2 (𝓞 F) F) ((μH F).restrict (slab F a b)) :=
  smulInvariantMeasure_restrict (Γp F) (μH F) (measurableSet_slab a b) (fun γ => preimage_subtype_mul_slab γ a b)

private theorem setLIntegral_fd_le_sum_mul {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : ∀ g ∈ slab F a b, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D) :
    ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F)
      ≤ (∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) := by
  haveI := smulInvariantMeasure_slab (F := F) a b
  have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
      ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩,
      Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
    exact subtype_mul_mem_slab ⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ (hSs hg)
  have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F),
      (‖f (γ • w)‖₊ : ℝ≥0∞) ^ 2 = (‖f w‖₊ : ℝ≥0∞) ^ 2 := by
    rintro ⟨_, γ, rfl⟩ w
    show (‖f (globalPoints (𝓞 F) F γ * w)‖₊ : ℝ≥0∞) ^ 2 = _
    rw [hΓ]
  calc ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F)
      = ∫⁻ w in S, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂((μH F).restrict (slab F a b)) := by
        rw [Measure.restrict_restrict_of_subset hSs]
    _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
          (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂((μH F).restrict (slab F a b)) :=
        setLIntegral_fd_le_of_cover hS hcovE _ hF
    _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
    _ ≤ ∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) :=
        setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
          (fun n => (‖χ n‖₊ : ℝ≥0∞) ^ 2) (fun n => ENNReal.pow_ne_top ENNReal.coe_ne_top)
          (fun n w => by rw [hZ, nnnorm_mul, ENNReal.coe_mul, mul_pow])
    _ = (∑ n ∈ N, (‖χ n‖₊ : ℝ≥0∞) ^ 2) * ∫⁻ w in D, (‖f w‖₊ : ℝ≥0∞) ^ 2 ∂(μH F) := by
        rw [Finset.sum_mul]

private theorem cover_of_forall {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂) :
    ∀ g ∈ slab F a b, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈
        ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  intro g hg
  obtain ⟨γ, n, hn, x, hx, y, hy, hyx⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyx]
  show (centralScalar (𝓞 F) F n)⁻¹ * (y * (centralScalar (𝓞 F) F n * x)) ∈ _
  rw [← mul_assoc y, mul_centralScalar_comm n y, mul_assoc, inv_mul_cancel_left]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, y, hy, rfl⟩

end Adelic

end NormDomProof
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre.NormDomProof"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre.NormDomProof"

open NormDomProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsLsXiFunction (𝓞 F) F ⊤ ξ φ → Continuous φ →
      ∫⁻ x in Φ₀, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ENNReal.ofReal C *
          ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  classical
  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hΦ₀.pos
  refine ⟨∑ n ∈ N, ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ ^ 2, fun φ hφ _ => ?_⟩
  have hmain := setLIntegral_fd_le_sum_mul (F := F) (D := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (χ := fun n => ((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)) hφ.left_invariant
    (fun n w => hφ.central_transform ⟨n, Subgroup.mem_top n⟩ w)
    hΦ₀.isFundamentalDomain hΦ₀.subset (cover_of_forall hN)
  refine hmain.trans_eq ?_
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

end S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre (solution)
