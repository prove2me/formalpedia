-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/399996c6-6e46-5107-8bc4-280859d2f753

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion
import Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open scoped RestrictedProduct ENNReal NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion"
namespace LocalIntertwining
p2m_export "AutomorphicForm.LocalIntertwining" "integral_unramifiedWeylIntegrand_adicCompletion"
namespace FiniteAdeleAssembly
p2m_open "AutomorphicForm.LocalIntertwining AutomorphicForm"

section Recognition

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Y : Type*} [MeasurableSpace Y]

theorem exists_eq_prod_of_forall_map_add_left [T2Space G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (ρ : Measure (G × Y)) (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ Set.univ) < ∞) :
    ∃ σ : Measure Y, IsFiniteMeasure σ ∧ ρ = μ.prod σ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨K₀, hK₀c, hK₀n⟩ := exists_compact_mem_nhds (0 : G)
  have hK₀m : MeasurableSet K₀ := hK₀c.measurableSet
  have hK₀pos : μ K₀ ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK₀n).ne'
  have hK₀top : μ K₀ ≠ ∞ := hK₀c.measure_lt_top.ne
  have hT : ∀ a : G, Measurable fun p : G × Y => (a + p.1, p.2) := fun a =>
    (measurable_fst.const_add a).prodMk measurable_snd

  have hrect : ∀ (a : G) (A : Set G) (B : Set Y), MeasurableSet A → MeasurableSet B →
      ρ (((fun g => a + g) ⁻¹' A) ×ˢ B) = ρ (A ×ˢ B) := by
    intro a A B hA hB
    have h := congrArg (fun m : Measure (G × Y) => m (A ×ˢ B)) (hinv a)
    rw [Measure.map_apply (hT a) (hA.prod hB)] at h
    have hpre : (fun p : G × Y => (a + p.1, p.2)) ⁻¹' (A ×ˢ B) = ((fun g => a + g) ⁻¹' A) ×ˢ B := by
      ext ⟨g, y⟩
      simp only [Set.mem_preimage, Set.mem_prod]
    rw [hpre] at h
    exact h

  let ρB : Set Y → Measure G := fun B => (ρ.restrict (Set.univ ×ˢ B)).map Prod.fst
  have hρB : ∀ (B : Set Y) (A : Set G), MeasurableSet A → ρB B A = ρ (A ×ˢ B) := by
    intro B A hA
    simp only [ρB]
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    congr 1
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]

  let σ : Measure Y := (μ K₀)⁻¹ • (ρ.restrict (K₀ ×ˢ Set.univ)).map Prod.snd
  have hσ : ∀ B : Set Y, MeasurableSet B → σ B = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    intro B hB
    simp only [σ, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 2
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  have hσfin : IsFiniteMeasure σ := by
    refine ⟨?_⟩
    rw [hσ _ MeasurableSet.univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hK₀pos)) (hfin K₀ hK₀c)
  haveI := hσfin
  refine ⟨σ, hσfin, (Measure.prod_eq fun A B hA hB => ?_).symm⟩

  haveI hBinv : (ρB B).IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun A' hA' => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hA', hρB B _ (measurable_const_add a hA'), hρB B A' hA']
    exact hrect a A' B hA' hB
  haveI hBfin : IsFiniteMeasureOnCompacts (ρB B) := by
    refine ⟨fun K hK => ?_⟩
    rw [hρB B K hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono (Set.prod_mono le_rfl (Set.subset_univ _))) (hfin K hK)
  have huniq : ρB B = (ρB B).addHaarScalarFactor μ • μ := Measure.isAddLeftInvariant_eq_smul (ρB B) μ
  set c : ℝ≥0 := (ρB B).addHaarScalarFactor μ with hc_def
  have hcA : ∀ A' : Set G, MeasurableSet A' → ρ (A' ×ˢ B) = (c : ℝ≥0∞) * μ A' := by
    intro A' hA'
    rw [← hρB B A' hA', huniq]
    exact Measure.coe_nnreal_smul_apply c μ A'
  have hc : (c : ℝ≥0∞) = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    rw [hcA K₀ hK₀m, mul_comm (c : ℝ≥0∞) (μ K₀), ← mul_assoc, ENNReal.inv_mul_cancel hK₀pos hK₀top, one_mul]
  rw [hcA A hA, hc, hσ B hB]
  ring

end Recognition

section Places

variable (F : Type) [Field F] [NumberField F]

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := by
    have e := (Module.finBasis ℚ F).equivFun.toEquiv
    exact (Equiv.countable_iff e).mpr inferInstance
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [scoped instance] countable_heightOneSpectrum

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

abbrev Stratum (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((↑T : Set _)ᶜ)]

omit [NumberField F] in
theorem cofinite_le (T : Finset (HeightOneSpectrum (𝓞 F))) :
    cofinite ≤ 𝓟 ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite

def incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (cofinite_le F T)

variable {F} in
@[scoped simp] theorem incl_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (v : HeightOneSpectrum (𝓞 F)) : incl F T x v = x v := rfl

theorem isOpenEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : IsOpenEmbedding (incl F T) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal (isOpen_adicCompletionIntegers F) (cofinite_le F T)

def stratumSet (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, v ∉ T → x v ∈ v.adicCompletionIntegers F}

abbrev GT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type := ∀ i : ↥T, (i.1).adicCompletion F

abbrev YT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  ∀ i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}, (i.1).adicCompletionIntegers F

variable {F} in
theorem mem_of_not_mem {T : Finset (HeightOneSpectrum (𝓞 F))} (x : Stratum F T)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) : x v ∈ v.adicCompletionIntegers F :=
  (Filter.eventually_principal.mp x.2) v (by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv)

theorem range_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Set.range (incl F T) = stratumSet F T := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ v hv
    exact mem_of_not_mem y hv
  · intro hx
    refine ⟨⟨fun v => x v, Filter.eventually_principal.mpr fun v hv => hx v ?_⟩, RestrictedProduct.ext _ _ fun v => rfl⟩
    simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv

theorem isOpen_stratumSet (T : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (stratumSet F T) := by
  rw [← range_incl]
  exact (isOpenEmbedding_incl F T).isOpen_range

open scoped Classical in

def glue (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F :=
  if h : v ∈ T then p.1 ⟨v, h⟩ else ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F)

variable {F} in
theorem glue_of_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) : glue F T p v = p.1 ⟨v, h⟩ := by
  simp only [glue, dif_pos h]

variable {F} in
theorem glue_of_not_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    glue F T p v = ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  simp only [glue, dif_neg h]

def splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) : GT F T × YT F T :=
  (fun i => x i.1, fun i => ⟨x i.1, mem_of_not_mem x i.2⟩)

def splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) : Stratum F T :=
  ⟨glue F T p, Filter.eventually_principal.mpr fun v hv => by
    have hv' : v ∉ T := by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv
    rw [glue_of_not_mem T p hv']
    exact Subtype.coe_prop _⟩

variable {F} in
@[scoped simp] theorem splitInv_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    (v : HeightOneSpectrum (𝓞 F)) : splitInv F T p v = glue F T p v := rfl

variable {F} in
@[scoped simp] theorem splitFun_fst (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) (i : ↥T) :
    (splitFun F T x).1 i = x i.1 := rfl

variable {F} in
@[scoped simp] theorem coe_splitFun_snd (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    ((splitFun F T x).2 i : (i.1).adicCompletion F) = x i.1 := rfl

variable {F} in
theorem splitInv_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    splitInv F T (splitFun F T x) = x := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  rw [splitInv_apply]
  by_cases h : v ∈ T
  · rw [glue_of_mem T _ h, splitFun_fst]
  · rw [glue_of_not_mem T _ h, coe_splitFun_snd]

variable {F} in
theorem splitFun_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    splitFun F T (splitInv F T p) = p := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · rw [splitFun_fst, splitInv_apply, glue_of_mem T p i.2]
  · rw [coe_splitFun_snd, splitInv_apply, glue_of_not_mem T p i.2]

theorem continuous_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitFun F T) :=
  continuous_prodMk.mpr
    ⟨continuous_pi fun i => RestrictedProduct.continuous_eval i.1,
      continuous_pi fun i => (RestrictedProduct.continuous_eval i.1).subtype_mk _⟩

theorem continuous_glue (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun p : GT F T × YT F T => glue F T p v := by
  by_cases h : v ∈ T
  · simp only [glue, dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [glue, dif_neg h]
    exact continuous_subtype_val.comp
      ((continuous_apply (⟨v, h⟩ : {w : HeightOneSpectrum (𝓞 F) // w ∉ T})).comp continuous_snd)

theorem continuous_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitInv F T) :=
  RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun v => continuous_glue F T v)

def split (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T ≃ₜ GT F T × YT F T where
  toFun := splitFun F T
  invFun := splitInv F T
  left_inv := splitInv_splitFun T
  right_inv := splitFun_splitInv T
  continuous_toFun := continuous_splitFun F T
  continuous_invFun := continuous_splitInv F T

variable {F} in
@[scoped simp] theorem split_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    split F T x = splitFun F T x := rfl

variable {F} in
@[scoped simp] theorem split_symm_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    (split F T).symm p = splitInv F T p := rfl

variable {F} in
theorem incl_add (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x + y) = incl F T x + incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

variable {F} in
theorem incl_sub (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x - y) = incl F T x - incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

theorem split_add_symm (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) (p : GT F T × YT F T) :
    split F T ((split F T).symm (a, 0) + (split F T).symm p) = (a + p.1, p.2) := by
  simp only [split_apply, split_symm_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = a i + p.1 i
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_mem T _ i.2, glue_of_mem T _ i.2]
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = (p.2 i : (i.1).adicCompletion F)
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_not_mem T _ i.2,
      glue_of_not_mem T _ i.2]
    show ((0 : (i.1).adicCompletionIntegers F) : (i.1).adicCompletion F) + (p.2 i : (i.1).adicCompletion F)
      = (p.2 i : (i.1).adicCompletion F)
    rw [ZeroMemClass.coe_zero, zero_add]

scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (Stratum F T) := borel _
scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : BorelSpace (Stratum F T) := ⟨rfl⟩

end Places

section Measures

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem measurableEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableEmbedding (incl F T) :=
  (isOpenEmbedding_incl F T).measurableEmbedding

def rhoT (T : Finset (HeightOneSpectrum (𝓞 F))) : Measure (GT F T × YT F T) :=
  (ν.comap (incl F T)).map (split F T).toMeasurableEquiv

omit [ν.IsAddHaarMeasure] in

theorem setIntegral_stratumSet_eq (T : Finset (HeightOneSpectrum (𝓞 F))) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : FiniteAdeleRing (𝓞 F) F → E) :
    ∫ x in stratumSet F T, f x ∂ν = ∫ p, f (incl F T ((split F T).symm p)) ∂(rhoT F ν T) := by
  rw [← range_incl F T, ← (measurableEmbedding_incl F T).map_comap ν,
    (measurableEmbedding_incl F T).integral_map]
  unfold rhoT
  rw [integral_map_equiv]
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply]

omit [ν.IsAddHaarMeasure] in

theorem integrableOn_stratumSet_iff (T : Finset (HeightOneSpectrum (𝓞 F))) {E : Type*} [NormedAddCommGroup E]
    (f : FiniteAdeleRing (𝓞 F) F → E) :
    IntegrableOn f (stratumSet F T) ν ↔ Integrable (fun p => f (incl F T ((split F T).symm p))) (rhoT F ν T) := by
  rw [IntegrableOn, ← range_incl F T, ← (measurableEmbedding_incl F T).map_comap ν,
    (measurableEmbedding_incl F T).integrable_map_iff]
  unfold rhoT
  rw [integrable_map_equiv]
  have hfg : (fun p : GT F T × YT F T => f (incl F T ((split F T).symm p))) ∘ (split F T).toMeasurableEquiv
      = f ∘ incl F T := by
    funext x
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply]
  rw [hfg]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

theorem comap_incl_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (b : Stratum F T) :
    (ν.comap (incl F T)).map (fun x => b + x) = ν.comap (incl F T) := by
  have hme := measurableEmbedding_incl F T
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_add b) hs, hme.comap_apply, hme.comap_apply]
  have hset : incl F T '' ((fun x => b + x) ⁻¹' s) = (fun y => incl F T b + y) ⁻¹' (incl F T '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b + x, hx, incl_add T b x⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨z - b, ?_, ?_⟩
      · show b + (z - b) ∈ s
        rwa [add_sub_cancel]
      · rw [incl_sub, hzy, add_sub_cancel_left]
  rw [hset, measure_preimage_add]

theorem rhoT_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) :
    (rhoT F ν T).map (fun p : GT F T × YT F T => (a + p.1, p.2)) = rhoT F ν T := by
  have hTa : Measurable fun p : GT F T × YT F T => (a + p.1, p.2) :=
    (measurable_fst.const_add a).prodMk measurable_snd
  have hem : Measurable (split F T).toMeasurableEquiv := (split F T).toMeasurableEquiv.measurable
  have hconj : (fun p : GT F T × YT F T => (a + p.1, p.2)) ∘ (split F T).toMeasurableEquiv
      = (split F T).toMeasurableEquiv ∘ fun x => (split F T).symm (a, 0) + x := by
    funext x
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe]
    have h := split_add_symm F T a (split F T x)
    rw [Homeomorph.symm_apply_apply] at h
    exact h.symm
  unfold rhoT
  rw [Measure.map_map hTa hem, hconj, ← Measure.map_map hem (measurable_const_add _), comap_incl_map_add_left]

theorem rhoT_prod_univ_lt_top (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (GT F T)) (hK : IsCompact K) :
    rhoT F ν T (K ×ˢ Set.univ) < ∞ := by
  unfold rhoT
  rw [MeasurableEquiv.map_apply, (measurableEmbedding_incl F T).comap_apply, Homeomorph.toMeasurableEquiv_coe,
    ← Homeomorph.image_symm]
  exact (((hK.prod isCompact_univ).image (split F T).symm.continuous).image
    (isOpenEmbedding_incl F T).continuous).measure_lt_top

theorem exists_rhoT_eq_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure] :
    ∃ σ : Measure (YT F T), IsFiniteMeasure σ ∧
      rhoT F ν T = (Measure.pi fun i : ↥T => μ i.1).prod σ ∧
      ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)
        = (∏ v ∈ T, μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ Set.univ := by
  obtain ⟨σ, hσfin, hρ⟩ := exists_eq_prod_of_forall_map_add_left (Measure.pi fun i : ↥T => μ i.1) (rhoT F ν T)
    (rhoT_map_add_left F ν T) (rhoT_prod_univ_lt_top F ν T)
  haveI := hσfin
  refine ⟨σ, hσfin, hρ, ?_⟩

  have hbox : AdelicBox.integralFiniteAdeles (𝓞 F) F = incl F T '' ((split F T).toMeasurableEquiv ⁻¹'
      ((Set.univ.pi fun i : ↥T => ((i.1).adicCompletionIntegers F : Set ((i.1).adicCompletion F))) ×ˢ
        (Set.univ : Set (YT F T)))) := by
    rw [Homeomorph.toMeasurableEquiv_coe]
    ext y
    constructor
    · intro hy
      have hy' : y ∈ Set.range (incl F T) := by
        rw [range_incl]
        exact fun v _ => hy v
      obtain ⟨x, rfl⟩ := hy'
      refine ⟨x, ?_, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst]
      exact fun i => hy i.1
    · rintro ⟨x, hx, rfl⟩ v
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst] at hx
      by_cases hv : v ∈ T
      · exact hx ⟨v, hv⟩
      · exact mem_of_not_mem x hv
  rw [hbox, ← (measurableEmbedding_incl F T).comap_apply, ← MeasurableEquiv.map_apply]
  show rhoT F ν T _ = _
  rw [hρ, Measure.prod_prod, Measure.pi_pi]
  congr 1
  exact Finset.prod_coe_sort T fun v => μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))

end Measures

section Integrand

variable (F : Type) [Field F] [NumberField F]

def phi0 (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (χ v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y

variable {F} in
theorem phi0_of_mem {χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ} {s : ℂ}
    {v : HeightOneSpectrum (𝓞 F)} {y : v.adicCompletion F} (hy : y ∈ v.adicCompletionIntegers F) :
    phi0 F χ s v y = 1 := by
  have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
  have hy'' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hy'
  simp only [phi0, Set.indicator_of_mem hy', Set.indicator_of_notMem hy'', add_zero]

def eul (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (z : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ z

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

variable {F} in

theorem norm_eul_lt_one {χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ}
    {ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ} {z : ℂ} (hz : z.re < 0)
    {v : HeightOneSpectrum (𝓞 F)} (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) : ‖eul F χ ϖ z v‖ < 1 := by
  have hq : 1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast one_lt_absNorm F v
  have hqpos : 0 < Ideal.absNorm v.asIdeal := lt_trans Nat.zero_lt_one (one_lt_absNorm F v)
  rw [eul, norm_mul, Complex.norm_natCast_cpow_of_pos hqpos]
  calc ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ z.re
      ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ z.re :=
        mul_le_mul_of_nonneg_right hχ₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq hz

variable {F} in

theorem norm_eul_le {χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ}
    {ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ} (z : ℂ)
    {v : HeightOneSpectrum (𝓞 F)} (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) :
    ‖eul F χ ϖ z v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ z.re := by
  have hqpos : 0 < Ideal.absNorm v.asIdeal := lt_trans Nat.zero_lt_one (one_lt_absNorm F v)
  rw [eul, norm_mul, Complex.norm_natCast_cpow_of_pos hqpos]
  calc ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ z.re
      ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ z.re :=
        mul_le_mul_of_nonneg_right hχ₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := one_mul _

variable {F} in
theorem one_sub_ne_zero_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at ha
  exact lt_irrefl _ ha

def Phi (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : FiniteAdeleRing (𝓞 F) F) : ℂ :=
  (∏ v ∈ S, h v (x v)) * ∏ᶠ w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, phi0 F χ s w.1 (x w.1)

open scoped Classical in

def Fi (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (i : ↥T) :
    (i.1).adicCompletion F → ℂ :=
  if i.1 ∈ S then h i.1 else phi0 F χ s i.1

open scoped Classical in

def Iv (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if v ∈ S then ∫ y, h v y ∂(μ v) else ∫ y, phi0 F χ s v y ∂(μ v)

variable {F} in
open scoped Classical in
theorem integral_Fi (S T : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (i : ↥T) :
    ∫ y, Fi F S T h χ s i y ∂(μ i.1) = Iv F S μ h χ s i.1 := by
  unfold Fi Iv
  by_cases hi : i.1 ∈ S
  · simp only [if_pos hi]
  · simp only [if_neg hi]

variable {F} in
open scoped Classical in

theorem Phi_incl_splitInv {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (p : GT F T × YT F T) :
    Phi F S h χ s (incl F T (splitInv F T p)) = ∏ i : ↥T, Fi F S T h χ s i (p.1 i) := by
  have hcoord : ∀ v, incl F T (splitInv F T p) v = glue F T p v := fun v => rfl

  set E : HeightOneSpectrum (𝓞 F) → ℂ :=
    fun v => if v ∈ S then h v (glue F T p v) else phi0 F χ s v (glue F T p v) with hE
  have hFiE : ∀ i : ↥T, Fi F S T h χ s i (p.1 i) = E i.1 := by
    intro i
    simp only [hE, Fi, glue_of_mem T p i.2]
    by_cases hi : i.1 ∈ S
    · simp only [if_pos hi]
    · simp only [if_neg hi]
  rw [Fintype.prod_congr _ _ hFiE, Finset.prod_coe_sort T E]
  rw [hE, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.sdiff_eq_filter]
  unfold Phi
  simp only [hcoord]
  congr 1

  have hone : ∀ w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, w.1 ∉ T → phi0 F χ s w.1 (glue F T p w.1) = 1 := by
    intro w hw
    rw [glue_of_not_mem T p hw]
    exact phi0_of_mem (Subtype.coe_prop _)
  rw [finprod_eq_prod_of_mulSupport_subset
      (fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => phi0 F χ s w.1 (glue F T p w.1))
      (s := (T \ S).subtype fun v => v ∉ S) ?_]
  · exact Finset.prod_subtype_of_mem (f := fun v => phi0 F χ s v (glue F T p v)) fun v hv => (Finset.mem_sdiff.mp hv).2
  · intro w hw
    rw [Function.mem_mulSupport] at hw
    have hwT : w.1 ∈ T := by
      by_contra hwT
      exact hw (hone w hwT)
    exact Finset.mem_coe.mpr (Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨hwT, w.2⟩))

end Integrand

section StratumIdentity

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem measureReal_integers_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)
  exact ⟨((isOpen_adicCompletionIntegers F v).measure_pos (μ v) ⟨0, zero_mem _⟩).ne', hc.measure_lt_top.ne⟩

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem measureReal_box_ne_zero :
    ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨((AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩).ne',
    (AdelicBox.isCompact_integralFiniteAdeles F).measure_ne_top⟩

open scoped Classical in

theorem stratum_identity {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    (ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹ * ∫ x in stratumSet F T, Phi F S h χ s x ∂ν
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)))
        * ∏ v ∈ T \ S, ((1 - eul F χ ϖ (-(2 * s + 1)) v) * (1 - eul F χ ϖ (-(2 * s)) v)⁻¹) := by
  obtain ⟨σ, hσfin, hρ, hboxm⟩ := exists_rhoT_eq_prod F ν T μ
  haveI := hσfin

  have hI : ∫ x in stratumSet F T, Phi F S h χ s x ∂ν = σ.real Set.univ * ∏ v ∈ T, Iv F S μ h χ s v := by
    rw [setIntegral_stratumSet_eq]
    have hfun : (fun p : GT F T × YT F T => Phi F S h χ s (incl F T ((split F T).symm p)))
        = fun p => (fun g : GT F T => ∏ i : ↥T, Fi F S T h χ s i (g i)) p.1 := by
      funext p
      rw [split_symm_apply]
      exact Phi_incl_splitInv hST h χ s p
    have hfst := integral_fun_fst (μ := Measure.pi fun i : ↥T => μ i.1) (ν := σ)
      (fun g : GT F T => ∏ i : ↥T, Fi F S T h χ s i (g i))
    rw [hfun, hρ, hfst, integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := fun i : ↥T => μ i.1)
      (fun i => Fi F S T h χ s i)]
    rw [Complex.real_smul]
    congr 1
    rw [Fintype.prod_congr _ _ (integral_Fi S T μ h χ s), Finset.prod_coe_sort T (Iv F S μ h χ s)]

  have hone : ∀ v ∈ T \ S, Iv F S μ h χ s v
      = ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * ((1 - eul F χ ϖ (-(2 * s + 1)) v) * (1 - eul F χ ϖ (-(2 * s)) v)⁻¹) := by
    intro v hv
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hsv : ‖((χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
      have hz : (-(2 * s)).re < 0 := by
        simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
        linarith
      exact norm_eul_lt_one (F := F) hz (hχ₁ v hvS)
    unfold Iv
    rw [if_neg hvS, ← mul_assoc]
    unfold phi0
    exact integral_unramifiedWeylIntegrand_adicCompletion F v (μ v) (ϖ v) (hϖ v hvS) (χ v) (hχ v hvS) s hsv
  have hS : ∀ v ∈ S, Iv F S μ h χ s v = ∫ y, h v y ∂(μ v) := fun v hv => by
    unfold Iv
    rw [if_pos hv]

  have hbox : ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ.real Set.univ := by
    simp only [measureReal_def]
    rw [hboxm, ENNReal.toReal_mul, ENNReal.toReal_prod]

  have hm : ∀ v, ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ) ≠ 0 := fun v => by
    exact_mod_cast measureReal_integers_ne_zero F μ v
  have hσ0 : (σ.real Set.univ : ℂ) ≠ 0 := by
    have h0 := measureReal_box_ne_zero F ν
    rw [hbox] at h0
    exact_mod_cast right_ne_zero_of_mul h0

  have hIT : ∏ v ∈ T, Iv F S μ h χ s v = (∏ v ∈ T \ S, Iv F S μ h χ s v) * ∏ v ∈ S, Iv F S μ h χ s v :=
    (Finset.prod_sdiff hST).symm
  have hmT : (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (∏ v ∈ T \ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        * ∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (Finset.prod_sdiff hST).symm
  rw [hI, hbox, hIT, hmT, Finset.prod_congr rfl hS, Finset.prod_congr rfl hone]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hPS : (∏ v ∈ S, ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => hm v
  have hPT : (∏ v ∈ T \ S, ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => hm v
  have hPa : (∏ v ∈ T \ S, (1 - eul F χ ϖ (-(2 * s)) v)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v hv => one_sub_ne_zero_of_norm_lt_one ?_
    have hz : (-(2 * s)).re < 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    exact norm_eul_lt_one (F := F) hz (hχ₁ v (Finset.mem_sdiff.mp hv).2)
  push_cast
  field_simp

end StratumIdentity

section Generic

theorem integrable_of_forall_setIntegral_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] {f : X → E} (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcov : ∀ x, ∃ n, x ∈ A n) (hint : ∀ n, IntegrableOn f (A n) μ) (M : ℝ)
    (hbd : ∀ n, ∫ x in A n, ‖f x‖ ∂μ ≤ M) : Integrable f μ := by
  have hU : (⋃ n, A n) = Set.univ := Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (hcov x)
  refine ⟨?_, ?_⟩
  · have h := (aestronglyMeasurable_iUnion_iff (μ := μ) (f := f) (s := A)).mpr
      fun n => (hint n).aestronglyMeasurable
    rwa [hU, Measure.restrict_univ] at h
  · rw [hasFiniteIntegral_iff_enorm]
    have hg_meas : ∀ n, AEMeasurable ((A n).indicator fun x => ‖f x‖ₑ) μ := fun n =>
      (aemeasurable_indicator_iff (hA n)).mpr (hint n).aestronglyMeasurable.enorm
    have hg_mono : ∀ x, Monotone fun n => (A n).indicator (fun x => ‖f x‖ₑ) x := fun x m n hmn =>
      Set.indicator_le_indicator_of_subset (hmono hmn) (fun _ => zero_le) x
    have hg_sup : ∀ x, (⨆ n, (A n).indicator (fun x => ‖f x‖ₑ) x) = ‖f x‖ₑ := fun x => by
      obtain ⟨n, hn⟩ := hcov x
      apply le_antisymm
      · exact iSup_le fun m => Set.indicator_le_self _ _ x
      · calc ‖f x‖ₑ = (A n).indicator (fun x => ‖f x‖ₑ) x := (Set.indicator_of_mem hn fun x => ‖f x‖ₑ).symm
          _ ≤ ⨆ m, (A m).indicator (fun x => ‖f x‖ₑ) x := le_iSup (fun m => (A m).indicator (fun x => ‖f x‖ₑ) x) n
    have hbound : ∀ n, ∫⁻ x, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ ≤ ENNReal.ofReal M := fun n => by
      rw [lintegral_indicator (hA n), ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
      exact ENNReal.ofReal_le_ofReal (hbd n)
    calc ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, ⨆ n, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ :=
          lintegral_congr fun x => (hg_sup x).symm
      _ = ⨆ n, ∫⁻ x, (A n).indicator (fun x => ‖f x‖ₑ) x ∂μ := lintegral_iSup' hg_meas (ae_of_all _ hg_mono)
      _ ≤ ENNReal.ofReal M := iSup_le hbound
      _ < ∞ := ENNReal.ofReal_lt_top

end Generic

section PlaceSum

variable (F : Type) [Field F] [NumberField F]

theorem summable_absNorm_rpow_neg {t : ℝ} (ht : 1 < t) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t) := by
  have H := NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top F ht
  set f : (HeightOneSpectrum (𝓞 F) →₀ ℕ) → ℝ≥0∞ :=
    fun k => (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) with hf
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 F) => Finsupp.single v (1 : ℕ) :=
    fun v w h => Finsupp.single_left_injective one_ne_zero h
  have hle : ∑' v : HeightOneSpectrum (𝓞 F), f (Finsupp.single v 1) ≤ ∑' k, f k :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj f
  have hfin : ∑' v : HeightOneSpectrum (𝓞 F), f (Finsupp.single v 1) ≠ ∞ := (lt_of_le_of_lt hle H).ne
  have hsum := ENNReal.summable_toReal hfin
  refine hsum.congr fun v => ?_
  have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [hf, Finsupp.prod_single_index, pow_zero, pow_one]
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end PlaceSum

section NormData

variable (F : Type) [Field F] [NumberField F]

def chiAbs (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  (Units.map (Complex.ofRealHom : ℝ →* ℂ)).comp ((Units.map (normHom : ℂ →*₀ ℝ).toMonoidHom).comp (χ v))

variable {F} in
@[scoped simp] theorem coe_chiAbs (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ((chiAbs F χ v u : ℂˣ) : ℂ) = ((‖((χ v u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := rfl

variable {F} in
theorem coe_inv_apply (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    (((ψ v)⁻¹ u : ℂˣ) : ℂ) = (((ψ v u : ℂˣ) : ℂ))⁻¹ := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

variable {F} in

theorem ofReal_norm_phi0 (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ((‖phi0 F χ s v y‖ : ℝ) : ℂ) = phi0 F (chiAbs F χ) ((s.re : ℝ) : ℂ) v y := by
  by_cases hy : y ∈ v.adicCompletionIntegers F
  · rw [phi0_of_mem hy, phi0_of_mem hy, norm_one, Complex.ofReal_one]
  · have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
    have hm : 0 < LanglandsTunnell.TateLocal.modulus y := LanglandsTunnell.TateLocal.modulus_pos hy0
    have hm' : (0 : ℝ) < (LanglandsTunnell.TateLocal.modulus y : ℝ) := by exact_mod_cast hm
    have hy' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    have hy'' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hy'
    simp only [phi0, Set.indicator_of_notMem hy', Set.indicator_of_mem hy'', zero_add,
      LanglandsTunnell.TateLocal.charExt_of_ne_zero _ hy0, coe_inv_apply, coe_chiAbs, norm_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos hm']
    have hexp : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
      simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, Complex.one_re]
    have hexp' : (-(2 * ((s.re : ℝ) : ℂ) + 1)) = (((-(2 * s.re + 1)) : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, hexp', ← Complex.ofReal_cpow hm'.le]
    push_cast
    ring

variable {F} in
theorem chiAbs_units (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ} (h : χ v u = 1) : chiAbs F χ v u = 1 := by
  ext
  rw [coe_chiAbs, h, Units.val_one, norm_one, Complex.ofReal_one]

variable {F} in
theorem norm_chiAbs_le (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ} (h : ‖((χ v u : ℂˣ) : ℂ)‖ ≤ 1) :
    ‖((chiAbs F χ v u : ℂˣ) : ℂ)‖ ≤ 1 := by
  rw [coe_chiAbs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact h

def alpha (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (r : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r

variable {F} in
theorem eul_chiAbs_ofReal (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (r : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    eul F (chiAbs F χ) ϖ (r : ℂ) v = ((alpha F χ ϖ r v : ℝ) : ℂ) := by
  have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eul, alpha, coe_chiAbs, Complex.ofReal_mul, Complex.ofReal_cpow hq]
  push_cast
  ring

variable {F} in
theorem alpha_nonneg (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (r : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ alpha F χ ϖ r v :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

variable {F} in
theorem alpha_lt_one (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) {r : ℝ} (hr : r < 0) {v : HeightOneSpectrum (𝓞 F)}
    (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) : alpha F χ ϖ r v < 1 := by
  have h := norm_eul_lt_one (F := F) (χ := chiAbs F χ) (ϖ := ϖ) (z := (r : ℂ)) (by simpa using hr)
    (norm_chiAbs_le χ hχ₁)
  rwa [eul_chiAbs_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (alpha_nonneg χ ϖ r v)] at h

variable {F} in
theorem alpha_le (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (r : ℝ) {v : HeightOneSpectrum (𝓞 F)}
    (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) : alpha F χ ϖ r v ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r := by
  unfold alpha
  calc ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r
      ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right hχ₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := one_mul _

variable {F} in

theorem alpha_succ_le (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    alpha F χ ϖ (-(2 * σ + 1)) v ≤ alpha F χ ϖ (-(2 * σ)) v := by
  unfold alpha
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (one_lt_absNorm F v).le
  exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)

def beta (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (1 - alpha F χ ϖ (-(2 * σ + 1)) v) * (1 - alpha F χ ϖ (-(2 * σ)) v)⁻¹

variable {F} in
theorem one_le_beta (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) {σ : ℝ} (hσ : 0 < σ) {v : HeightOneSpectrum (𝓞 F)}
    (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) : 1 ≤ beta F χ ϖ σ v := by
  have ha : alpha F χ ϖ (-(2 * σ)) v < 1 := alpha_lt_one χ ϖ (by linarith) hχ₁
  have hle := alpha_succ_le χ ϖ σ v
  unfold beta
  rw [le_mul_inv_iff₀ (sub_pos.mpr ha), one_mul]
  linarith

variable {F} in
theorem beta_sub_one_le (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) {σ : ℝ} (hσ : 0 < σ) {v : HeightOneSpectrum (𝓞 F)}
    (hχ₁ : ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) :
    beta F χ ϖ σ v - 1 ≤ (1 - (2 : ℝ) ^ (-(2 * σ)))⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * σ)) := by
  have ha1 : alpha F χ ϖ (-(2 * σ)) v < 1 := alpha_lt_one χ ϖ (by linarith) hχ₁
  have ha0 : 0 ≤ alpha F χ ϖ (-(2 * σ + 1)) v := alpha_nonneg χ ϖ _ v
  have hle := alpha_succ_le χ ϖ σ v
  have hq2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast one_lt_absNorm F v
  have hqa : alpha F χ ϖ (-(2 * σ)) v ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * σ)) := alpha_le χ ϖ _ hχ₁
  have hq2' : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * σ)) ≤ (2 : ℝ) ^ (-(2 * σ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
  have h2 : (2 : ℝ) ^ (-(2 * σ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - alpha F χ ϖ (-(2 * σ)) v := sub_pos.mpr ha1
  have hden2 : 0 < 1 - (2 : ℝ) ^ (-(2 * σ)) := sub_pos.mpr h2

  have hβ : beta F χ ϖ σ v - 1
      = (alpha F χ ϖ (-(2 * σ)) v - alpha F χ ϖ (-(2 * σ + 1)) v) * (1 - alpha F χ ϖ (-(2 * σ)) v)⁻¹ := by
    unfold beta
    field_simp
    ring
  rw [hβ]
  calc (alpha F χ ϖ (-(2 * σ)) v - alpha F χ ϖ (-(2 * σ + 1)) v) * (1 - alpha F χ ϖ (-(2 * σ)) v)⁻¹
      ≤ alpha F χ ϖ (-(2 * σ)) v * (1 - (2 : ℝ) ^ (-(2 * σ)))⁻¹ := by
        refine mul_le_mul (by linarith) ?_ (inv_nonneg.mpr hden.le) (alpha_nonneg χ ϖ _ v)
        exact (inv_le_inv₀ hden hden2).mpr (by linarith)
    _ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * σ)) * (1 - (2 : ℝ) ^ (-(2 * σ)))⁻¹ :=
        mul_le_mul_of_nonneg_right hqa (inv_nonneg.mpr hden2.le)
    _ = _ := mul_comm _ _

variable {F} in

theorem summable_beta_sub_one (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) {σ : ℝ} (hσ : 1 / 2 < σ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) :
    Summable fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => beta F χ ϖ σ w.1 - 1 := by
  have hσ0 : 0 < σ := by linarith
  refine Summable.of_nonneg_of_le (fun w => sub_nonneg.mpr (one_le_beta χ ϖ hσ0 (hχ₁ w.1 w.2)))
    (fun w => beta_sub_one_le χ ϖ hσ0 (hχ₁ w.1 w.2)) ?_
  exact ((summable_absNorm_rpow_neg F (t := 2 * σ) (by linarith)).mul_left _).subtype _

end NormData

section LocalIntegrals

variable (F : Type) [Field F] [NumberField F]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

theorem integral_phi0_eq {S : Finset (HeightOneSpectrum (𝓞 F))}
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) {v : HeightOneSpectrum (𝓞 F)} (hvS : v ∉ S) :
    ∫ y, phi0 F χ s v y ∂(μ v)
      = ((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * ((1 - eul F χ ϖ (-(2 * s + 1)) v) * (1 - eul F χ ϖ (-(2 * s)) v)⁻¹) := by
  have hsv : ‖((χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
    have hz : (-(2 * s)).re < 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    exact norm_eul_lt_one (F := F) hz (hχ₁ v hvS)
  rw [← mul_assoc]
  unfold phi0
  exact integral_unramifiedWeylIntegrand_adicCompletion F v (μ v) (ϖ v) (hϖ v hvS) (χ v) (hχ v hvS) s hsv

theorem integral_phi0_ne_zero {S : Finset (HeightOneSpectrum (𝓞 F))}
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) {v : HeightOneSpectrum (𝓞 F)} (hvS : v ∉ S) :
    ∫ y, phi0 F χ s v y ∂(μ v) ≠ 0 := by
  rw [integral_phi0_eq F μ ϖ hϖ χ hχ hχ₁ s hs hvS]
  have hz1 : (-(2 * s + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero, Complex.one_re]
    linarith
  have hz : (-(2 * s)).re < 0 := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  refine mul_ne_zero (by exact_mod_cast measureReal_integers_ne_zero F μ v) (mul_ne_zero ?_ (inv_ne_zero ?_))
  · exact one_sub_ne_zero_of_norm_lt_one (norm_eul_lt_one (F := F) hz1 (hχ₁ v hvS))
  · exact one_sub_ne_zero_of_norm_lt_one (norm_eul_lt_one (F := F) hz (hχ₁ v hvS))

theorem integral_norm_phi0_eq {S : Finset (HeightOneSpectrum (𝓞 F))}
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) {v : HeightOneSpectrum (𝓞 F)} (hvS : v ∉ S) :
    ∫ y, ‖phi0 F χ s v y‖ ∂(μ v)
      = (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) * beta F χ ϖ s.re v := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_phi0]
  have hχ' : ∀ w ∉ S, ∀ u : (w.adicCompletion F)ˣ, Valued.v (u : w.adicCompletion F) = 1 → chiAbs F χ w u = 1 :=
    fun w hw u hu => chiAbs_units χ (hχ w hw u hu)
  have hχ₁' : ∀ w ∉ S, ‖((chiAbs F χ w (ϖ w) : ℂˣ) : ℂ)‖ ≤ 1 := fun w hw => norm_chiAbs_le χ (hχ₁ w hw)
  rw [integral_phi0_eq F μ ϖ hϖ (chiAbs F χ) hχ' hχ₁' ((s.re : ℝ) : ℂ) (by simpa using hs) hvS]
  have h1 : (-(2 * ((s.re : ℝ) : ℂ) + 1)) = (((-(2 * s.re + 1)) : ℝ) : ℂ) := by push_cast; ring
  have h2 : (-(2 * ((s.re : ℝ) : ℂ))) = (((-(2 * s.re)) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, eul_chiAbs_ofReal, eul_chiAbs_ofReal, beta]
  push_cast
  ring

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

theorem exists_exhaustion (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : ℕ → Finset (HeightOneSpectrum (𝓞 F)), Monotone T ∧ (∀ n, S ⊆ T n) ∧ ∀ v, ∃ n, v ∈ T n := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (HeightOneSpectrum (𝓞 F))
  refine ⟨fun n => S ∪ (Finset.range n).preimage f hf.injOn, fun m n hmn v hv => ?_,
    fun n => Finset.subset_union_left,
    fun v => ⟨f v + 1, Finset.mem_union_right _ (Finset.mem_preimage.mpr (Finset.self_mem_range_succ (f v)))⟩⟩
  simp only [Finset.mem_union, Finset.mem_preimage, Finset.mem_range] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (lt_of_lt_of_le hv hmn)

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem stratumSet_mono {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hTT' : T ⊆ T') :
    stratumSet F T ⊆ stratumSet F T' :=
  fun _ hx v hv => hx v fun h => hv (hTT' h)

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

theorem exists_mem_stratumSet {T : ℕ → Finset (HeightOneSpectrum (𝓞 F))} (hTmono : Monotone T)
    (hTcov : ∀ v, ∃ n, v ∈ T n) (x : FiniteAdeleRing (𝓞 F) F) : ∃ n, x ∈ stratumSet F (T n) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp x.2
  choose nv hnv using hTcov
  refine ⟨hfin.toFinset.sup nv, fun v hv => ?_⟩
  by_contra hbad
  have hvB : v ∈ hfin.toFinset := hfin.mem_toFinset.mpr hbad
  exact hv (hTmono (Finset.le_sup hvB) (hnv v))

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem iUnion_stratumSet_eq_univ {T : ℕ → Finset (HeightOneSpectrum (𝓞 F))} (hTmono : Monotone T)
    (hTcov : ∀ v, ∃ n, v ∈ T n) : (⋃ n, stratumSet F (T n)) = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (exists_mem_stratumSet F hTmono hTcov x)

end LocalIntegrals

section Integrability

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

open scoped Classical in

theorem integrableOn_Phi_stratumSet {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (hFi : ∀ i : ↥T, Integrable (Fi F S T h χ s i) (μ i.1)) :
    IntegrableOn (Phi F S h χ s) (stratumSet F T) ν := by
  rw [integrableOn_stratumSet_iff]
  obtain ⟨σ, hσfin, hρ, -⟩ := exists_rhoT_eq_prod F ν T μ
  haveI := hσfin
  have hfun : (fun p : GT F T × YT F T => Phi F S h χ s (incl F T ((split F T).symm p)))
      = fun p => (∏ i : ↥T, Fi F S T h χ s i (p.1 i)) * (fun _ : YT F T => (1 : ℂ)) p.2 := by
    funext p
    rw [split_symm_apply, mul_one]
    exact Phi_incl_splitInv hST h χ s p
  rw [hfun, hρ]
  exact (Integrable.fintype_prod_dep hFi).mul_prod (integrable_const (1 : ℂ))

open scoped Classical in

theorem setIntegral_norm_Phi_eq {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x in stratumSet F T, ‖Phi F S h χ s x‖ ∂ν
      = ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F)
        * (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∏ v ∈ S, ∫ y, ‖h v y‖ ∂(μ v)) * ∏ v ∈ T \ S, beta F χ ϖ s.re v := by
  obtain ⟨σ, hσfin, hρ, hboxm⟩ := exists_rhoT_eq_prod F ν T μ
  haveI := hσfin
  set J : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => if v ∈ S then ∫ y, ‖h v y‖ ∂(μ v) else ∫ y, ‖phi0 F χ s v y‖ ∂(μ v) with hJ
  have hJi : ∀ i : ↥T, ∫ y, ‖Fi F S T h χ s i y‖ ∂(μ i.1) = J i.1 := by
    intro i
    simp only [hJ, Fi]
    by_cases hi : i.1 ∈ S
    · simp only [if_pos hi]
    · simp only [if_neg hi]
  have hI : ∫ x in stratumSet F T, ‖Phi F S h χ s x‖ ∂ν = σ.real Set.univ * ∏ v ∈ T, J v := by
    rw [setIntegral_stratumSet_eq]
    have hfun : (fun p : GT F T × YT F T => ‖Phi F S h χ s (incl F T ((split F T).symm p))‖)
        = fun p => (fun g : GT F T => ∏ i : ↥T, ‖Fi F S T h χ s i (g i)‖) p.1 := by
      funext p
      rw [split_symm_apply, Phi_incl_splitInv hST h χ s p, norm_prod]
    have hfst := integral_fun_fst (μ := Measure.pi fun i : ↥T => μ i.1) (ν := σ)
      (fun g : GT F T => ∏ i : ↥T, ‖Fi F S T h χ s i (g i)‖)
    rw [hfun, hρ, hfst, integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun i : ↥T => μ i.1)
      (fun i y => ‖Fi F S T h χ s i y‖), smul_eq_mul]
    congr 1
    rw [Fintype.prod_congr _ _ hJi, Finset.prod_coe_sort T J]
  have hS : ∀ v ∈ S, J v = ∫ y, ‖h v y‖ ∂(μ v) := fun v hv => by simp only [hJ, if_pos hv]
  have hoff : ∀ v ∈ T \ S, J v = (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      * beta F χ ϖ s.re v := by
    intro v hv
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    simp only [hJ, if_neg hvS]
    exact integral_norm_phi0_eq F μ ϖ hϖ χ hχ hχ₁ s hs hvS
  have hbox : ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ.real Set.univ := by
    simp only [measureReal_def]
    rw [hboxm, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hPS : (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => measureReal_integers_ne_zero F μ v
  have hJT : ∏ v ∈ T, J v = (∏ v ∈ T \ S, J v) * ∏ v ∈ S, J v := (Finset.prod_sdiff hST).symm
  have hmT : (∏ v ∈ T, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (∏ v ∈ T \ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        * ∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (Finset.prod_sdiff hST).symm
  rw [hI, hbox, hJT, hmT, Finset.prod_congr rfl hS, Finset.prod_congr rfl hoff]
  simp only [Finset.prod_mul_distrib]
  field_simp

theorem integrable_Phi {S : Finset (HeightOneSpectrum (𝓞 F))}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (hh : ∀ v ∈ S, Integrable (h v) (μ v))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) : Integrable (Phi F S h χ s) ν := by
  classical
  have hs0 : 0 < s.re := by linarith
  obtain ⟨T, hTmono, hST, hTcov⟩ := exists_exhaustion F S
  have hFi : ∀ n (i : ↥(T n)), Integrable (Fi F S (T n) h χ s i) (μ i.1) := by
    intro n i
    unfold Fi
    by_cases hi : i.1 ∈ S
    · rw [if_pos hi]
      exact hh i.1 hi
    · rw [if_neg hi]
      exact Integrable.of_integral_ne_zero (integral_phi0_ne_zero F μ ϖ hϖ χ hχ hχ₁ s hs0 hi)
  set C : ℝ := ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F)
        * (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∏ v ∈ S, ∫ y, ‖h v y‖ ∂(μ v)) with hC
  have hC0 : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg measureReal_nonneg (inv_nonneg.mpr ?_)) ?_
    · exact Finset.prod_nonneg fun v _ => measureReal_nonneg
    · exact Finset.prod_nonneg fun v _ => integral_nonneg fun y => norm_nonneg _
  have hsum := summable_beta_sub_one χ ϖ hs S hχ₁
  refine integrable_of_forall_setIntegral_norm_le (fun n => stratumSet F (T n))
    (fun n => (isOpen_stratumSet F (T n)).measurableSet) (fun m n hmn => stratumSet_mono F (hTmono hmn))
    (exists_mem_stratumSet F hTmono hTcov) (fun n => integrableOn_Phi_stratumSet F ν μ (hST n) h χ s (hFi n))
    (C * Real.exp (∑' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (beta F χ ϖ s.re w.1 - 1))) fun n => ?_
  rw [setIntegral_norm_Phi_eq F ν μ (hST n) h ϖ hϖ χ hχ hχ₁ s hs0, ← hC]
  refine mul_le_mul_of_nonneg_left ?_ hC0

  have h1 : ∀ v ∈ T n \ S, 1 ≤ beta F χ ϖ s.re v := fun v hv => one_le_beta χ ϖ hs0 (hχ₁ v (Finset.mem_sdiff.mp hv).2)
  calc ∏ v ∈ T n \ S, beta F χ ϖ s.re v ≤ ∏ v ∈ T n \ S, Real.exp (beta F χ ϖ s.re v - 1) :=
        Finset.prod_le_prod (fun v hv => zero_le_one.trans (h1 v hv)) fun v _ => by
          linarith [Real.add_one_le_exp (beta F χ ϖ s.re v - 1)]
    _ = Real.exp (∑ v ∈ T n \ S, (beta F χ ϖ s.re v - 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (beta F χ ϖ s.re w.1 - 1)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [← Finset.sum_subtype_of_mem (f := fun v => beta F χ ϖ s.re v - 1) (p := fun v => v ∉ S)
          fun v hv => (Finset.mem_sdiff.mp hv).2]
        exact hsum.sum_le_tsum _ fun w _ => sub_nonneg.mpr (one_le_beta χ ϖ hs0 (hχ₁ w.1 w.2))

end Integrability

section Main

variable (F : Type) [Field F] [NumberField F]

variable {F} in

theorem multipliable_one_sub_eul (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) {z : ℂ} (hz : z.re < -1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1) :
    Multipliable fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => 1 - eul F χ ϖ z w.1 := by
  have hsum : Summable fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => ‖-eul F χ ϖ z w.1‖ := by
    simp only [norm_neg]
    refine Summable.of_nonneg_of_le (fun w => norm_nonneg _) (fun w => norm_eul_le z (hχ₁ w.1 w.2)) ?_
    have h := (summable_absNorm_rpow_neg F (t := -z.re) (by linarith)).subtype fun v => v ∉ S
    refine h.congr fun w => ?_
    simp only [Function.comp_apply, neg_neg]
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hsum

theorem integral_finiteAdeleRing_impl
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    (ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x, Phi F S h χ s x ∂ν)
        * ∏' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - eul F χ ϖ (-(2 * s)) w.1)
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)))
        * ∏' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - eul F χ ϖ (-(2 * s + 1)) w.1) := by
  classical
  have hs0 : 0 < s.re := by linarith
  obtain ⟨T, hTmono, hST, hTcov⟩ := exists_exhaustion F S
  have hAmeas : ∀ n, MeasurableSet (stratumSet F (T n)) := fun n => (isOpen_stratumSet F (T n)).measurableSet
  have hAmono : Monotone fun n => stratumSet F (T n) := fun m n hmn => stratumSet_mono F (hTmono hmn)
  have hU : (⋃ n, stratumSet F (T n)) = Set.univ := iUnion_stratumSet_eq_univ F hTmono hTcov
  have hc : (ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ) ≠ 0 := by
    exact_mod_cast measureReal_box_ne_zero F ν
  set PS : ℂ := ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
      * ∫ y, h v y ∂(μ v)) with hPS_def

  have hstar : ∀ n, (ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
      * ∫ x in stratumSet F (T n), Phi F S h χ s x ∂ν
        = PS * ∏ v ∈ T n \ S, ((1 - eul F χ ϖ (-(2 * s + 1)) v) * (1 - eul F χ ϖ (-(2 * s)) v)⁻¹) :=
    fun n => stratum_identity F ν μ (hST n) h ϖ hϖ χ hχ hχ₁ s hs

  have hlimI : Integrable (Phi F S h χ s) ν →
      Tendsto (fun n => ∫ x in stratumSet F (T n), Phi F S h χ s x ∂ν) atTop (𝓝 (∫ x, Phi F S h χ s x ∂ν)) := by
    intro hI
    have hlim := tendsto_setIntegral_of_monotone (μ := ν) (f := Phi F S h χ s) hAmeas hAmono hI.integrableOn
    rwa [hU, setIntegral_univ] at hlim
  by_cases hzero : ∃ v ∈ S, ∫ y, h v y ∂(μ v) = 0
  ·
    obtain ⟨v₀, hv₀, hv₀z⟩ := hzero
    have hPS : PS = 0 := Finset.prod_eq_zero hv₀ (by rw [hv₀z, mul_zero])
    have hstrat0 : ∀ n, ∫ x in stratumSet F (T n), Phi F S h χ s x ∂ν = 0 := fun n => by
      have h1 := hstar n
      rw [hPS, zero_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hc)
    have hint0 : ∫ x, Phi F S h χ s x ∂ν = 0 := by
      by_cases hI : Integrable (Phi F S h χ s) ν
      · have hlim := hlimI hI
        simp only [hstrat0] at hlim
        exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
      · exact integral_undef hI
    rw [hint0, hPS, mul_zero, zero_mul, zero_mul]
  ·
    push Not at hzero
    have hh : ∀ v ∈ S, Integrable (h v) (μ v) := fun v hv => Integrable.of_integral_ne_zero (hzero v hv)
    have hI : Integrable (Phi F S h χ s) ν := integrable_Phi F ν μ h hh ϖ hϖ χ hχ hχ₁ s hs
    have hzA : (-(2 * s)).re < -1 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    have hzA' : (-(2 * s + 1)).re < -1 := by
      simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, Complex.one_re]
      linarith
    have hmultA := multipliable_one_sub_eul χ ϖ hzA S hχ₁
    have hmultA' := multipliable_one_sub_eul χ ϖ hzA' S hχ₁

    have hlimP : ∀ z : ℂ, Multipliable (fun w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => 1 - eul F χ ϖ z w.1) →
        Tendsto (fun n => ∏ v ∈ T n \ S, (1 - eul F χ ϖ z v)) atTop
          (𝓝 (∏' w : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - eul F χ ϖ z w.1))) := by
      intro z hm
      have h1 : ∀ n, ∏ v ∈ T n \ S, (1 - eul F χ ϖ z v)
          = ∏ w ∈ (T n \ S).subtype (fun v => v ∉ S), (1 - eul F χ ϖ z w.1) := fun n =>
        (Finset.prod_subtype_of_mem (f := fun v => 1 - eul F χ ϖ z v) fun v hv => (Finset.mem_sdiff.mp hv).2).symm
      simp only [h1]
      refine hm.hasProd.comp (tendsto_atTop_finset_of_monotone (fun m n hmn w hw => ?_) fun w => ?_)
      · rw [Finset.mem_subtype, Finset.mem_sdiff] at hw ⊢
        exact ⟨hTmono hmn hw.1, hw.2⟩
      · obtain ⟨n, hn⟩ := hTcov w.1
        exact ⟨n, Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨hn, w.2⟩)⟩

    have hkey : ∀ n, (ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x in stratumSet F (T n), Phi F S h χ s x ∂ν) * ∏ v ∈ T n \ S, (1 - eul F χ ϖ (-(2 * s)) v)
          = PS * ∏ v ∈ T n \ S, (1 - eul F χ ϖ (-(2 * s + 1)) v) := by
      intro n
      rw [hstar n, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      have hne : 1 - eul F χ ϖ (-(2 * s)) v ≠ 0 :=
        one_sub_ne_zero_of_norm_lt_one (norm_eul_lt_one (F := F) (by linarith) (hχ₁ v (Finset.mem_sdiff.mp hv).2))
      rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    have hL := ((hlimI hI).const_mul ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹)).mul
      (hlimP _ hmultA)
    have hR := (hlimP _ hmultA').const_mul PS
    exact tendsto_nhds_unique (hL.congr hkey) hR

end Main

end AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm.LocalIntertwining P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm.LocalIntertwining"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm.LocalIntertwining P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly"

open MeasureTheory NumberField IsDedekindDomain in
open scoped RestrictedProduct in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    (ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x, (∏ v ∈ S, h v (x v))
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                      (fun _ => (1 : ℂ)) (x v.1)
                    + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                        (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x v.1))) ∂ν)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)))
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
  AutomorphicForm.LocalIntertwining.FiniteAdeleAssembly.integral_finiteAdeleRing_impl
    F ν S μ h ϖ hϖ χ hχ hχ₁ s hs

#print axioms solution

end S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod (solution)
