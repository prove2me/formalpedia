-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:31:20.865209+00:00
-- url     : https://prove2.me/theorems/5a0729ff-0e40-43dc-85f7-399e3feac689
-- title:
--   Measure
-- statement:
--   Definitions and structural lemmas for Measure, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Measure.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Theorems.Thm_FiniteRange_null_of_compl
public import Theorems.Thm_MeasureTheory_Measure_prod_of_full_measure_finset
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7


set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology
namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]
section measureEntropy
variable {μ : Measure S}
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})
@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ
class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, ∀ᵐ x ∂μ, x ∈ A
noncomputable
def _root_.MeasureTheory.Measure.finiteSupport
    (μ : Measure S) [hμ : FiniteSupport μ] : Finset S :=
  hμ.finite.choose.filter (μ {·} ≠ 0)
lemma measure_compl_support (μ : Measure S) [hμ : FiniteSupport μ] :
    μ μ.finiteSupportᶜ = 0 := by
  let A := hμ.finite.choose
  have :
      (μ.finiteSupport : Set S)ᶜ
        ⊆ (A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x} := by
    intro z hz
    simp only [Measure.finiteSupport, ne_eq, Finset.coe_filter, mem_compl_iff,
      mem_ofPred_eq, not_and, Decidable.not_not] at hz
    by_cases h'z : z ∈ A
    · simp [hz h'z, h'z]
    · simp [h'z]
  apply le_antisymm ?_ bot_le
  calc μ (μ.finiteSupport : Set S)ᶜ ≤ μ ((A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0),
    {x}) :=
    measure_mono this
  _ ≤ μ (Aᶜ) + ∑ x ∈ A.filter (μ {·} = 0), μ {x} := by
    apply (measure_union_le _ _).trans
    gcongr
    apply measure_biUnion_finset_le
  _ ≤ 0 + ∑ x ∈ A.filter (μ {·} = 0), 0 := by
    gcongr with x hx
    · exact hμ.finite.choose_spec.le
    · simp_all
  _ = 0 := by simp
lemma ae_mem_support (μ : Measure S) [FiniteSupport μ] : ∀ᵐ x ∂μ, x ∈ μ.finiteSupport :=
  measure_compl_support _
@[simp] lemma mem_support {μ : Measure S} [hμ : FiniteSupport μ] {x : S} :
    x ∈ μ.finiteSupport ↔ μ {x} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Measure.finiteSupport, ne_eq, Finset.mem_filter] at h
    exact h.2
  · contrapose! h
    exact measure_mono_null (by simpa using h) (measure_compl_support μ)
instance finiteSupport_zero : FiniteSupport (0 : Measure S) where
  finite := ⟨(∅ : Finset S), by simp⟩
noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0
instance finiteSupport_of_fintype {μ : Measure S} [Finite S] : FiniteSupport μ := by
  cases nonempty_fintype S
  use Finset.univ
  simp
instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := ⟨μ.finiteSupport, Measure.ae_smul_measure (ae_mem_support _) _⟩
section
variable [MeasurableSingletonClass S]
instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := ⟨{x}, by simp⟩
instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := by
  by_cases hX : AEMeasurable X μ
  · exact ⟨hX'.toFinset, FiniteRange.null_of_compl μ X hX⟩
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [Measure.map_zero]
    infer_instance
  · rw [Measure.map_of_not_aemeasurable hX]
    infer_instance
instance finiteSupport_of_prod {μ : Measure S} [FiniteSupport μ] {ν : Measure T} [SigmaFinite ν]
    [FiniteSupport ν] :
    FiniteSupport (μ.prod ν) := by
  use μ.finiteSupport ×ˢ ν.finiteSupport
  exact Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support ν)
end
lemma _root_.ProbabilityTheory.measureEntropy_eq_sum
    {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0) :
   Hm[μ] = ∑ s ∈ A, negMulLog (((μ Set.univ)⁻¹ • μ).real {s}) := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ.real {s} = 0 by simp [this]
  rw [Measure.real, measure_mono_null (by simpa) hA]
  simp
@[simp]
lemma _root_.ProbabilityTheory.measureEntropy_zero
    : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]
@[simp]
lemma _root_.ProbabilityTheory.measureEntropy_dirac
    [MeasurableSingletonClass S] (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy]
  simp only [MeasurableSet.univ, Measure.dirac_apply', mem_univ, indicator_of_mem, Pi.one_apply,
    inv_one, one_smul]
  rw [tsum_eq_single x]
  · simp_all
  · simp +contextual [eq_comm]
lemma _root_.ProbabilityTheory.measureEntropy_of_not_isFiniteMeasure
    (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]
lemma _root_.ProbabilityTheory.measureEntropy_of_isProbabilityMeasure_finite
    {μ : Measure S} {A : Finset S} (hA :
  μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_sum hA]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp
lemma _root_.ProbabilityTheory.measureEntropy_of_isProbabilityMeasure_finite'
    {μ : Measure S} {A : Finset S} (hA :
  μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure_finite hA
lemma _root_.ProbabilityTheory.measureEntropy_univ_smul
    : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => simp [measureEntropy]
variable [MeasurableSingletonClass S]
@[simp]
lemma _root_.ProbabilityTheory.measureEntropy_prod
    {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableSingletonClass T] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  let A := μ.finiteSupport
  have hA := measure_compl_support μ
  let B := ν.finiteSupport
  have hB := measure_compl_support ν
  have hC : (μ.prod ν) (A ×ˢ B : Finset (S × T))ᶜ = 0 := by
    have : ((A ×ˢ B : Finset (S × T)) : Set (S × T))ᶜ
      = ((A : Set S)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set T)ᶜ) := by
        ext ⟨a, b⟩
        simp
        tauto
    rw [this]
    simp [hA, hB, A, B]
  have h1 : Hm[μ] = ∑ p ∈ (A ×ˢ B), (negMulLog (μ.real {p.1})) * (ν.real {p.2}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hA, Finset.sum_product]
    congr with s
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices ν.real B = ν.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hB, B]
  have h2 : Hm[ν] = ∑ p ∈ (A ×ˢ B), (negMulLog (ν.real {p.2})) * (μ.real {p.1}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hB, Finset.sum_product_right]
    congr with t
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices μ.real A = μ.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hA, A]
  rw [measureEntropy_of_isProbabilityMeasure_finite' hC, h1, h2, ← Finset.sum_add_distrib]
  congr with ⟨s, t⟩
  simp_rw [← Set.singleton_prod_singleton, measureReal_prod_prod, negMulLog_mul]
  ring
end measureEntropy
section measureMutualInfo
noncomputable
def _root_.ProbabilityTheory.measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]
notation:100 "Im[" μ "]" => measureMutualInfo μ
lemma _root_.ProbabilityTheory.measureMutualInfo_def (μ : Measure (S × T)) :
    Im[μ] = Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ] := rfl
@[simp]
lemma _root_.ProbabilityTheory.measureMutualInfo_zero_measure : Im[(0 : Measure (S × T))] = 0 := by
  simp [measureMutualInfo]
lemma _root_.ProbabilityTheory.measureMutualInfo_of_not_isFiniteMeasure
    {μ : Measure (S × U)} (h : ¬ IsFiniteMeasure μ) :
    Im[μ] = 0 := by
  rw [measureMutualInfo_def]
  have h1 : ¬ IsFiniteMeasure (μ.map Prod.fst) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    convert Measure.map_apply measurable_fst MeasurableSet.univ
    rw [Set.preimage_univ]
  have h2 : ¬ IsFiniteMeasure (μ.map Prod.snd) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    convert Measure.map_apply measurable_snd MeasurableSet.univ
    rw [Set.preimage_univ]
  rw [measureEntropy_of_not_isFiniteMeasure h, measureEntropy_of_not_isFiniteMeasure h1,
    measureEntropy_of_not_isFiniteMeasure h2]
  simp
lemma _root_.ProbabilityTheory.measureMutualInfo_univ_smul
    (μ : Measure (S × U)) : Im[(μ Set.univ)⁻¹ • μ] =
  Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  rcases eq_zero_or_neZero μ with hμ | _
  · simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1
  · congr 1
    · have hfst : (Measure.map Prod.fst μ) Set.univ = μ Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      rw [Measure.map_smul _ μ Prod.fst, ← hfst]
      exact measureEntropy_univ_smul
    · have hsnd : (Measure.map Prod.snd μ) Set.univ = μ Set.univ := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ]
      rw [Measure.map_smul _ μ Prod.snd, ← hsnd]
      exact measureEntropy_univ_smul
  convert measureEntropy_univ_smul
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
@[simp]
lemma _root_.ProbabilityTheory.measureMutualInfo_prod
    {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Im[μ.prod ν] = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp
lemma _root_.ProbabilityTheory.measureMutualInfo_nonneg_aux
    {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    0 ≤ Im[μ] ∧
    (Im[μ] = 0 ↔ ∀ p,
      μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  let E := μ.finiteSupport
  have hE := measure_compl_support μ
  classical
  set E1 : Finset S := Finset.image Prod.fst E
  set E2 : Finset U := Finset.image Prod.snd E
  have hE' : μ (E1 ×ˢ E2 : Finset (S × U))ᶜ = 0 := by
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    contrapose!
    intro h
    simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
      Finset.coe_product, mem_prod, not_and, Classical.not_imp] at h ⊢
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E, E2,
      mem_support]
    constructor
    · use u
    · use s
  have hE1 : (μ.map Prod.fst) E1ᶜ = 0 := by
    rw [Measure.map_apply measurable_fst (MeasurableSet.compl (Finset.measurableSet E1))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
      mem_support]
    intro h; use u
  letI : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hE1' : (μ.map Prod.fst).real E1 = 1 := by
    rw [prob_compl_eq_zero_iff E1.measurableSet] at hE1
    unfold Measure.real
    simp_all
  have hE2 : (μ.map Prod.snd) E2ᶜ = 0 := by
    rw [Measure.map_apply measurable_snd (MeasurableSet.compl (Finset.measurableSet E2))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
    intro h; use s
  letI : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hE2' : (μ.map Prod.snd).real E2 = 1 := by
    rw [prob_compl_eq_zero_iff E2.measurableSet] at hE2
    unfold Measure.real
    simp_all
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (.singleton _)]
    refine fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (.singleton _)]
    exact fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z ∈ E2, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_eq_right, iUnion_exists, mem_iUnion,
          mem_singleton_iff, Prod.mk.injEq, true_and, exists_prop, exists_and_right,
          exists_eq_right', E2, E] at h2 ⊢
        use s
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  have h2 z : (μ.map Prod.snd).real {z} = ∑ y ∈ E1, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, iUnion_exists,
          mem_iUnion, mem_singleton_iff, Prod.mk.injEq, and_true, exists_prop, exists_eq_right', E1,
          E] at h2 ⊢
        use u
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) :=
    ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p ∈ (E1 ×ˢ E2), 0 ≤ w p := by intros; positivity
  have hw2 : ∑ p ∈ E1 ×ˢ E2, w p = 1 := by
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, sum_measureReal_singleton, w]
    rw [← Finset.sum_mul]
    rw [show (1 : ℝ) = 1 * 1 by norm_num]
    congr
    convert hE1'
    simp
  have hf : ∀ p ∈ E1 ×ˢ E2, 0 ≤ f p := by intros; positivity
  have H :=
  calc
    ∑ p ∈ E1 ×ˢ E2, w p * f p
        = ∑ p ∈ E1 ×ˢ E2, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [f, hp]
          · simp [w, f]
            field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
      _ = 1 := by
        simp only [sum_measureReal_singleton, Finset.coe_product]
        rw [show 1 = μ.real Set.univ by simp]
        apply measureReal_congr
        simpa using hE'
  have H1 : -measureMutualInfo (μ := μ) = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := calc
    _ = ∑ p ∈ E1 ×ˢ E2,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        have H0 : Hm[μ] = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log (μ.real {p}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE', negMulLog, neg_mul,
            Finset.sum_neg_distrib]
        have H1 : Hm[μ.map Prod.fst] = -∑ p ∈ E1 ×ˢ E2,
            μ.real {p} * log ((μ.map Prod.fst).real {p.1}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE1, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product, ← Finset.sum_mul]
          simp_all
        have H2 : Hm[μ.map Prod.snd] =
            -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log ((μ.map Prod.snd).real {p.2}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE2, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product_right, ← Finset.sum_mul]
          simp_all
        simp_rw [measureMutualInfo_def, H0, H1, H2]
        simp [Finset.sum_add_distrib]
    _ = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := by
        congr! 1 with p _
        by_cases hp : μ.real {p} = 0
        · simp [f, hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        simp [negMulLog, log_mul, log_inv, h_fst_ne_zero p hp, h_snd_ne_zero p hp, hp, w, f]
        field_simp
        ring
  have H2 : 0 = negMulLog (∑ s ∈ (E1 ×ˢ E2), w s * f s) := by
    rw [H, negMulLog_one]
  constructor
  · rw [← neg_nonpos, H1]
    have key := concaveOn_negMulLog.le_map_sum hw1 hw2 hf
    simp only [smul_eq_mul] at key
    rw [← H2] at key
    exact key
  rw [← neg_eq_zero, H1, H2, eq_comm]
  refine (strictConcaveOn_negMulLog.map_sum_eq_iff' hw1 hw2 hf).trans ?_
  have w0 (p : S × U) (hp: w p = 0) : μ.real {p} = 0 := by
    simp only [mul_eq_zero, w] at hp
    rcases hp with hp | hp
    · contrapose! hp; exact (h_fst_ne_zero p) hp
    · contrapose! hp; exact (h_snd_ne_zero p) hp
  constructor
  · intro hyp p
    by_cases hp1 : p.1 ∈ E1
    · by_cases hp2 : p.2 ∈ E2
      · have hp : p ∈ E1 ×ˢ E2 := Finset.mem_product.mpr ⟨hp1, hp2⟩
        by_cases hw : w p = 0
        · rw [w0 p hw]
          exact hw.symm
        replace hyp := hyp p hp hw
        simp_rw [smul_eq_mul, H] at hyp
        have := eq_of_inv_mul_eq_one hyp
        convert this.symm
      have : {p.2} ⊆ (E2 : Set U)ᶜ := by
        simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp2
      replace : (Measure.map Prod.snd μ).real {p.2} = 0 := by
        rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE2
      have hp : μ.real {p} = 0 := by contrapose! this; exact (h_snd_ne_zero p) this
      simp [hp, this]
    have : {p.1} ⊆ (E1 : Set S)ᶜ := by
      simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp1
    replace : (Measure.map Prod.fst μ).real {p.1} = 0 := by
      rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE1
    have hp : μ.real {p} = 0 := by contrapose! this; exact (h_fst_ne_zero p) this
    simp [hp, this]
  intro hyp ⟨s, u⟩ _ hw
  simp_rw [smul_eq_mul, H]
  change (w (s,u))⁻¹ * (μ.real {(s,u)}) = 1
  have : w (s,u) ≠ 0 := by exact hw
  field_simp [this]
  rw [hyp (s,u)]
lemma _root_.ProbabilityTheory.measureMutualInfo_nonneg {μ : Measure (S × U)} [FiniteSupport μ] :
    0 ≤ Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureMutualInfo_univ_smul μ]
    apply measureMutualInfo_nonneg_aux.1
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
end measureMutualInfo
end ProbabilityTheory
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function ProbabilityTheory
example {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] {μ : Measure (S × T)} [FiniteSupport μ] : 0 ≤ Im[μ] := by
  exact ProbabilityTheory.measureMutualInfo_nonneg
end Mathlib.Meta.Positivity


