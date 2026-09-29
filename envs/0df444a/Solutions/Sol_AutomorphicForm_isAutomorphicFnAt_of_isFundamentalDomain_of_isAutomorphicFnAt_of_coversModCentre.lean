-- Prove2me | solution 1 for AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c64ed18c-d09f-5db3-af78-01dba0c8e820

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace SlabDomainTransfer

open scoped Pointwise ENNReal

section FDAction

variable {H α : Type*} [Group H] [MulAction H α] [MeasurableSpace α] [MeasurableConstSMul H α]
  [Countable H] {ν : Measure α} [SMulInvariantMeasure H α ν]

private theorem setLIntegral_fd_le_of_cover {S E : Set α} (hS : IsFundamentalDomain H S ν)
    (hcov : S ⊆ ⋃ γ : H, (γ • ·) ⁻¹' E) (F : α → ℝ≥0∞) (hF : ∀ (γ : H) (w : α), F (γ • w) = F w) :
    ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in E, F w ∂ν := by
  calc ∫⁻ w in S, F w ∂ν ≤ ∫⁻ w in ⋃ γ : H, S ∩ (γ • ·) ⁻¹' E, F w ∂ν := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hw)
        exact Set.mem_iUnion.mpr ⟨γ, hw, hγ⟩
    _ ≤ ∑' γ : H, ∫⁻ w in S ∩ (γ • ·) ⁻¹' E, F w ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : H, ∫⁻ w in γ • S ∩ E, F w ∂ν := by
        refine tsum_congr fun γ => ?_
        have hpre : (fun w : α => γ • w) ⁻¹' (γ • S ∩ E) = S ∩ (γ • ·) ⁻¹' E := by
          rw [Set.preimage_inter, Set.preimage_smul, inv_smul_smul]
        rw [← (measurePreserving_smul γ ν).setLIntegral_comp_preimage_emb
          (measurableEmbedding_const_smul γ) F (γ • S ∩ E), hpre]
        simp_rw [hF]
    _ = ∫⁻ w in E, F w ∂ν := by
        rw [hS.setLIntegral_eq_tsum F E]
        exact tsum_congr fun γ => by rw [Set.inter_comm]

end FDAction

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem smulInvariantMeasure_restrict (Γ : Subgroup G) [MeasurableConstSMul ↥Γ G]
    (μ : Measure G) [SMulInvariantMeasure ↥Γ G μ] {T : Set G} (hT : MeasurableSet T)
    (hΓT : ∀ γ : ↥Γ, (fun w : G => γ • w) ⁻¹' T = T) :
    SMulInvariantMeasure ↥Γ G (μ.restrict T) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← hΓT γ, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter hT)

variable [MeasurableMul G]

private theorem aestronglyMeasurable_of_cover_translates (μ : Measure G) [μ.IsMulLeftInvariant]
    {D X : Set G} {f : G → ℂ} (hf : AEStronglyMeasurable f (μ.restrict D))
    {ι : Type*} [Countable ι] (a : ι → G) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (hfa : ∀ (i : ι) (w : G), f (a i * w) = c i * f w) (hX : X ⊆ ⋃ i, (fun w => a i * w) ⁻¹' D) :
    AEStronglyMeasurable f (μ.restrict X) := by
  have hpiece : ∀ i, AEStronglyMeasurable f (μ.restrict ((fun w => a i * w) ⁻¹' D)) := by
    intro i
    have hmp : MeasurePreserving (fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D))
        (μ.restrict D) :=
      (measurePreserving_mul_left μ (a i)).restrict_preimage_emb (measurableEmbedding_mulLeft (a i)) D
    have h1 : AEStronglyMeasurable (f ∘ fun w => a i * w) (μ.restrict ((fun w => a i * w) ⁻¹' D)) :=
      hf.comp_measurePreserving hmp
    have h2 : (fun w => (c i)⁻¹ * (f ∘ fun w => a i * w) w) = f := by
      funext w
      simp only [Function.comp_apply, hfa, ← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]
    rw [← h2]
    exact h1.const_mul _
  exact (AEStronglyMeasurable.iUnion hpiece).mono_measure (Measure.restrict_mono hX le_rfl)

private theorem setLIntegral_biUnion_translates_le (μ : Measure G) [μ.IsMulLeftInvariant]
    {D : Set G} (F : G → ℝ≥0∞) {ι : Type*} (I : Finset ι) (b : ι → G) (k : ι → ℝ≥0∞)
    (hk : ∀ i, k i ≠ ∞) (hFb : ∀ (i : ι) (w : G), F (b i * w) = k i * F w) :
    ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ ≤ ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := by
  have hpiece : ∀ i, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ = k i * ∫⁻ w in D, F w ∂μ := by
    intro i
    rw [← (measurePreserving_mul_left μ (b i)).setLIntegral_comp_emb (measurableEmbedding_mulLeft (b i)) F D]
    simp_rw [hFb]
    exact lintegral_const_mul' (k i) _ (hk i)
  calc ∫⁻ w in ⋃ i ∈ I, (fun w => b i * w) '' D, F w ∂μ
      ≤ ∫⁻ w in ⋃ i : ↥I, (fun w => b i * w) '' D, F w ∂μ := by
        refine lintegral_mono_set fun w hw => ?_
        obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hw⟩
    _ ≤ ∑' i : ↥I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ I, ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ := by
        rw [tsum_fintype, Finset.sum_coe_sort I fun i => ∫⁻ w in (fun w => b i * w) '' D, F w ∂μ]
    _ = ∑ i ∈ I, k i * ∫⁻ w in D, F w ∂μ := Finset.sum_congr rfl fun i _ => hpiece i

end Group

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem memLp_two_of_lintegral {f : α → ℂ} (h1 : AEStronglyMeasurable f μ)
    (h2 : ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞) : MemLp f 2 μ := by
  refine ⟨h1, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mpr ?_⟩
  simpa only [ENNReal.toReal_ofNat] using h2

private theorem lintegral_lt_top_of_memLp_two {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mp hf.2
  simpa only [ENNReal.toReal_ofNat] using h

end Pairing

end SlabDomainTransfer

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsAutomorphicFnAt productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup exists_finset_central_slab_covering_of_coversModCentre ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"
namespace DetNormSlab

open NumberField.TateGlobal SlabDomainTransfer
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
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

private theorem dn_pos (g : AdelicGL2 (𝓞 F) F) : 0 < dn g := ideleNorm_pos _

private theorem dn_mul (g h : AdelicGL2 (𝓞 F) F) : dn (g * h) = dn g * dn h := by
  show ideleNorm F _ = _
  rw [map_mul, ideleNorm_mul]

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

private def CoveredBy (D : Set (AdelicGL2 (𝓞 F) F)) (N : Finset (AdeleRing (𝓞 F) F)ˣ)
    (X : Set (AdelicGL2 (𝓞 F) F)) : Prop :=
  ∀ g ∈ X, ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
    (centralScalar (𝓞 F) F n)⁻¹ * (globalPoints (𝓞 F) F γ * g) ∈ D

private theorem CoveredBy.mono {D : Set (AdelicGL2 (𝓞 F) F)} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {X X' : Set (AdelicGL2 (𝓞 F) F)} (h : CoveredBy D N X) (hX : X' ⊆ X) : CoveredBy D N X' :=
  fun g hg => h g (hX hg)

private theorem coveredBy_of_forall {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)} {a b : ℝ}
    {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂) :
    CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F a b) := by
  intro g hg
  obtain ⟨γ, n, hn, x, hx, y, hy, hyx⟩ := h g hg
  refine ⟨γ, n, hn, ?_⟩
  rw [← hyx]
  show (centralScalar (𝓞 F) F n)⁻¹ * (y * (centralScalar (𝓞 F) F n * x)) ∈ _
  rw [← mul_assoc y, mul_centralScalar_comm n y, mul_assoc, inv_mul_cancel_left]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, y, hy, rfl⟩

private theorem memLp_of_coveredBy {D S : Set (AdelicGL2 (𝓞 F) F)} {a b : ℝ} {N : Finset (AdeleRing (𝓞 F) F)ˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hmem : MemLp f 2 ((μH F).restrict D))
    (hΓ : ∀ (γ : GL (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * w) = f w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), f (centralScalar (𝓞 F) F n * w) = χ n * f w)
    (hχ : ∀ n, χ n ≠ 0)
    (hS : IsFundamentalDomain ↥(Γp F) S ((μH F).restrict (slab F a b))) (hSs : S ⊆ slab F a b)
    (hX : CoveredBy D N (slab F a b)) : MemLp f 2 ((μH F).restrict S) := by
  have hcov' : ∀ g ∈ slab F a b, ∃ γ : ↥(Γp F), ∃ n ∈ N,
      (centralScalar (𝓞 F) F n)⁻¹ * ((γ : AdelicGL2 (𝓞 F) F) * g) ∈ D := fun g hg => by
    obtain ⟨γ, n, hn, h⟩ := hX g hg
    exact ⟨⟨globalPoints (𝓞 F) F γ, γ, rfl⟩, n, hn, h⟩
  have hfa : ∀ (i : ↥(Γp F) × ↥N) (w : AdelicGL2 (𝓞 F) F),
      f ((centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F) * w)
        = χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ * f w := by
    rintro ⟨⟨_, γ, rfl⟩, n, hn⟩ w
    show f ((centralScalar (𝓞 F) F n)⁻¹ * globalPoints (𝓞 F) F γ * w) = χ n⁻¹ * f w
    rw [← map_inv, mul_assoc, hZ, hΓ]

  have h1 : AEStronglyMeasurable f ((μH F).restrict S) := by
    refine aestronglyMeasurable_of_cover_translates (μH F) hmem.1
      (fun i : ↥(Γp F) × ↥N =>
        (centralScalar (𝓞 F) F (i.2 : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * (i.1 : AdelicGL2 (𝓞 F) F))
      (fun i => χ (i.2 : (AdeleRing (𝓞 F) F)ˣ)⁻¹) (fun i => hχ _) hfa fun g hg => ?_
    obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
    refine Set.mem_iUnion.mpr ⟨⟨γ, n, hn⟩, ?_⟩
    show (centralScalar (𝓞 F) F n)⁻¹ * (γ : AdelicGL2 (𝓞 F) F) * g ∈ D
    rwa [mul_assoc]

  have h2 : ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := by
    haveI := smulInvariantMeasure_slab (F := F) a b
    have hcovE : S ⊆ ⋃ γ : ↥(Γp F), (γ • ·) ⁻¹'
        ((⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b) := fun g hg => by
      obtain ⟨γ, n, hn, h⟩ := hcov' g (hSs hg)
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, _, h, mul_inv_cancel_left _ _⟩, ?_⟩
      exact subtype_mul_mem_slab γ (hSs hg)
    have hF : ∀ (γ : ↥(Γp F)) (w : AdelicGL2 (𝓞 F) F), ‖f (γ • w)‖ₑ ^ (2 : ℝ) = ‖f w‖ₑ ^ (2 : ℝ) := by
      rintro ⟨_, γ, rfl⟩ w
      show ‖f (globalPoints (𝓞 F) F γ * w)‖ₑ ^ (2 : ℝ) = _
      rw [hΓ]
    have hD : ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) < ∞ := lintegral_lt_top_of_memLp_two hmem
    calc ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F)
        = ∫⁻ w in S, ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) := by
          rw [Measure.restrict_restrict_of_subset hSs]
      _ ≤ ∫⁻ w in (⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D) ∩ slab F a b,
            ‖f w‖ₑ ^ (2 : ℝ) ∂((μH F).restrict (slab F a b)) :=
          setLIntegral_fd_le_of_cover hS hcovE _ hF
      _ ≤ ∫⁻ w in ⋃ n ∈ N, (fun w => centralScalar (𝓞 F) F n * w) '' D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          lintegral_mono' (Measure.restrict_mono Set.inter_subset_left Measure.restrict_le_self) le_rfl
      _ ≤ ∑ n ∈ N, ‖χ n‖ₑ ^ (2 : ℝ) * ∫⁻ w in D, ‖f w‖ₑ ^ (2 : ℝ) ∂(μH F) :=
          setLIntegral_biUnion_translates_le (μH F) _ N (fun n => centralScalar (𝓞 F) F n)
            (fun n => ‖χ n‖ₑ ^ (2 : ℝ)) (fun n => ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
            (fun n w => by rw [hZ, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])
      _ < ∞ := by
          refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ hD
          exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  exact memLp_two_of_lintegral h1 h2

end DetNormSlab
p2m_reactivate "P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.AutomorphicForm.DetNormSlab"
end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.AutomorphicForm.DetNormSlab P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.AutomorphicForm"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.AutomorphicForm AutomorphicForm.DetNormSlab in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ) :
    IsAutomorphicFnAt F
      (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ := by
  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hα
  have hX : CoveredBy (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N (slab F α β) :=
    coveredBy_of_forall hN
  obtain ⟨hfn, hmem⟩ := h
  letI := (productionPinsOf F S (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
  letI : MeasureSpace (AdelicGL2 (𝓞 F) F) :=
    ⟨(productionPinsOf F S (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ⟩
  refine ⟨hfn, ?_⟩
  exact memLp_of_coveredBy (χ := fun n => ((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)) hmem hfn.left_invariant
    (fun n w => hfn.central_transform ⟨n, Subgroup.mem_top n⟩ w) (fun n => Units.ne_zero _) hS hSs hX

#print axioms solution

end
end S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre (solution)
