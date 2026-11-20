-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F001
-- name    : BrownianMotion_Continuity_KolmogorovChentsov_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:51:23.178179+00:00
-- url     : https://prove2.me/theorems/cd53fc4b-e7f9-4596-8c42-77464c779876
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsov
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsov. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000
import Definitions.Def_SourceProof_11bb60daeeb4a4b137b43a03
import Definitions.Def_SourceProof_27cd69ca80d6c18aaca80d6a
import Definitions.Def_SourceProof_3cb59e664eda6af2b0a5ab70
import Definitions.Def_SourceProof_62dfde857e76a0eeed3ee854
import Definitions.Def_SourceProof_dfed2a2c41cef06acf5bb665

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

/-- A set on which the process is Hölder continuous. -/
def holderSet (X : T → Ω → E) (T' : Set T) (p β : ℝ) (U : Set T) : Set Ω :=
  {ω | ⨆ (s : (T' ∩ U : Set T)) (t : (T' ∩ U : Set T)),
      edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞
      ∧ ∀ (s t : (T' ∩ U : Set T)), edist s t = 0 → edist (X s ω) (X t ω) = 0}
lemma IsKolmogorovProcess.measurableSet_holderSet
    (hX : IsKolmogorovProcess X P p q M) {T' : Set T} (hT' : T'.Countable) :
    MeasurableSet (holderSet X T' p β U) := by
  have : Countable T' := hT'
  have : Countable (T' ∩ U : Set T) := hT'.mono Set.inter_subset_left
  let C ω := ⨆ (s : (T' ∩ U : Set T)) (t : (T' ∩ U : Set T)),
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  refine MeasurableSet.inter ?_ ?_
  · change MeasurableSet {ω | C ω < ∞}
    refine measurableSet_lt ?_ (by fun_prop)
    refine Measurable.iSup (fun s ↦ Measurable.iSup (fun t ↦ ?_))
    exact Measurable.div (hX.measurable_edist.pow_const _) (by fun_prop)
  · have h_eq (A : Set T) : {ω | ∀ (s t : A), edist s t = 0 → edist (X s ω) (X t ω) = 0}
        = ⋂ (s : A) (t : A),
          ({ω | edist (X s ω) (X t ω) = 0} ∪ {ω | edist s t ≠ 0}) := by
      ext; simp [imp_iff_or_not]
    change MeasurableSet {ω | ∀ (s t : (T' ∩ U : Set T)),
      edist s t = 0 → edist (X s ω) (X t ω) = 0}
    rw [h_eq]
    refine MeasurableSet.iInter (fun s ↦ MeasurableSet.iInter (fun t ↦ ?_))
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSet.preimage (measurableSet_singleton 0) hX.measurable_edist
    · exact (MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)).compl
lemma holderOnWith_of_mem_holderSet (hT : HasBoundedCoveringNumber U c d)
    (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β U) :
    letI C ω := ⨆ (s : (T' ∩ U : Set T)) (t : (T' ∩ U : Set T)),
      edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
    HolderOnWith (C ω ^ p⁻¹).toNNReal β (fun (t : T') ↦ X t ω) {t' | (t' : T) ∈ U} := by
  intro s hs t ht
  have h_edist_lt_top : edist s t < ∞ := by
    calc edist s t ≤ Metric.ediam U := Metric.edist_le_ediam_of_mem hs ht
    _ < ∞ := hT.ediam_lt_top
  have h_dist_top : edist s t ^ (β : ℝ) ≠ ∞ := by
    simp only [ne_eq, ENNReal.rpow_eq_top_iff, NNReal.coe_pos, not_or, not_and, not_lt,
      NNReal.zero_le_coe, implies_true, nonpos_iff_eq_zero, true_and]
    exact fun h_eq_top ↦ absurd h_eq_top h_edist_lt_top.ne
  by_cases h_dist_zero : edist s t = 0
  · simpa [h_dist_zero, hβ_pos] using hω.2 ⟨s, ⟨s.2, hs⟩⟩ ⟨t, ⟨t.2, ht⟩⟩ h_dist_zero
  rw [← ENNReal.div_le_iff (by simp [h_dist_zero]) h_dist_top]
  rw [ENNReal.coe_toNNReal]
  swap; · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hω.1.ne
  rw [ENNReal.le_rpow_inv_iff hp_pos, ENNReal.div_rpow_of_nonneg _ _ hp_pos.le,
    ← ENNReal.rpow_mul]
  exact le_iSup₂ ⟨s, ⟨s.2, hs⟩⟩ ⟨t, ⟨t.2, ht⟩⟩ (f := fun (s t : (T' ∩ U : Set T)) ↦
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p))
lemma uniformContinuousOn_of_mem_holderSet
    (hT : HasBoundedCoveringNumber U c d)
    (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β U) :
    UniformContinuousOn (fun (t : T') ↦ X t ω) {x : T' | ↑x ∈ U} :=
      (holderOnWith_of_mem_holderSet hT hp_pos hβ_pos hω).uniformContinuousOn hβ_pos
lemma continuousOn_of_mem_holderSet (hT : HasBoundedCoveringNumber U c d)
    (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β U) :
    ContinuousOn (fun (t : T') ↦ X t ω) {x : T' | ↑x ∈ U} :=
  (holderOnWith_of_mem_holderSet hT hp_pos hβ_pos hω).continuousOn hβ_pos
lemma exists_tendsto_of_mem_holderSet [CompleteSpace E]
    (hT : HasBoundedCoveringNumber U c d) (hU : IsOpen U)
    (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') {ω : Ω} (hω : ω ∈ holderSet X T' p β U)
    (t : T) (htU : t ∈ U) :
    ∃ c, Tendsto (fun t' : T' ↦ X t' ω) (comap Subtype.val (𝓝 t)) (𝓝 c) :=
  (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_62dfde857e76a0eeed3ee854 p2mMethodArg0 p2mMethodArg1 (uniformContinuousOn_of_mem_holderSet hT hp_pos hβ_pos hω)) hT'_dense hU t
    htU
lemma ae_mem_holderSet [MeasurableSpace E] [BorelSpace E]
    (hT : HasBoundedCoveringNumber U c d) (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT'_countable : T'.Countable) :
    ∀ᵐ ω ∂P, ω ∈ holderSet X T' p β U := by
  have : Countable T' := hT'_countable
  have hT'U : (T' ∩ U).Countable := hT'_countable.mono Set.inter_subset_left
  have : Countable (T' ∩ U : Set T) := hT'U
  have h_ae_zero : ∀ᵐ ω ∂P, ∀ (s t : (T' ∩ U : Set T)),
      edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    simp_rw [ae_all_iff]
    exact fun s t hst ↦ hX.IsAEKolmogorovProcess.edist_eq_zero hst
  let C ω := ⨆ (s : (T' ∩ U : Set T)) (t : (T' ∩ U : Set T)),
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  have hC_lt_top : ∀ᵐ ω ∂P, C ω < ∞ :=
    hX.ae_iSup_rpow_edist_div_lt_top hT hc hd_pos hdq_lt hβ_pos hβ_lt hT'U Set.inter_subset_right
  filter_upwards [hC_lt_top, h_ae_zero] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
end HolderSet

lemma IsKolmogorovProcess.tendstoInMeasure (hX : IsKolmogorovProcess X P p q M)
    (hq_pos : 0 < q) {T' : Set T} {u : ℕ → T'} {t : T}
    (hu : Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t)) :
    TendstoInMeasure P (fun n ↦ X (u n)) atTop (X t) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
  have h_tendsto : Tendsto (fun n ↦ ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le)
      (fun n ↦ hX.kolmogorovCondition (u n) t)
    have : Tendsto (fun n ↦ edist (u n).1 t) atTop (𝓝 0) := by
      rwa [← tendsto_iff_edist_tendsto_0]
    rw [← mul_zero (M : ℝ≥0∞)]
    refine ENNReal.Tendsto.const_mul ?_ (by simp)
    change Tendsto ((fun x : ℝ≥0∞ ↦ x ^ q) ∘ (fun n ↦ edist (u n).1 t)) atTop (𝓝 0)
    refine Tendsto.comp ?_ this
    convert ENNReal.continuous_rpow_const.tendsto 0
    simp [hq_pos]
  suffices Tendsto (fun n ↦ P {ω | ε ^ p ≤ edist (X (u n) ω) (X t ω) ^ p}) atTop (𝓝 0) by
    convert this using 3 with n
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.rpow_le_rpow_iff hX.p_pos]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) ?_
    (h := fun n ↦ (ε ^ p)⁻¹ * ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P)
  · rw [← mul_zero (ε ^ p)⁻¹]
    exact ENNReal.Tendsto.const_mul h_tendsto (by simp [hε_top, hε.ne'])
  · refine fun n ↦ (meas_ge_le_lintegral_div ?_ ?_ ?_).trans_eq ?_
    · exact (hX.measurable_edist.pow_const _).aemeasurable
    · simp [hε.ne', hX.p_pos.le]
    · simp [hε.ne', hε_top]
    · rw [ENNReal.div_eq_inv_mul]
variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

/-- A Hölder continuous modification of a process `X`. -/
noncomputable
def holderModification (X : T → Ω → E) (β : ℝ≥0) (p : ℝ) (U : Set T) [DecidablePred (· ∈ U)] :
    T → Ω → E :=
  fun t ω ↦ if t ∈ U then limUnder (comap Subtype.val (𝓝 t))
    (fun t' : denseCountable T ↦ indicatorProcess X (holderSet X (denseCountable T) p β U) t' ω)
    else hE.some
lemma isLimitOfIndicator_holderModification
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    IsLimitOfIndicator (holderModification X β p U) X P U := by
  let A := holderSet X (denseCountable T) p β U
  have hA_meas : MeasurableSet A := hX.measurableSet_holderSet countable_denseCountable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := ae_mem_holderSet hT hX hc hd_pos hdq_lt hβ_pos hβ_lt
    countable_denseCountable
  refine ⟨A, hA_meas, hA_ae, fun t htU ω hω ↦ ?_, fun t htU ω ↦ ?_, fun t htUc ω ↦ ?_⟩
  · exact exists_tendsto_of_mem_holderSet hT hU hX.p_pos hβ_pos dense_denseCountable
      hω t htU
  · simp only [holderModification, htU, ↓reduceIte, Dense.extend, IsDenseInducing.extend, A]
    exact edist_self _
  · simp [holderModification, htUc]
omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology T] in
lemma exists_tendsto_indicatorProcess_holderSet
    (hT : HasBoundedCoveringNumber U c d) (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β)
    {T' : Set T} (hT'_dense : Dense T') (t : T) (htU : t ∈ U) (ω : Ω) :
    ∃ c, Tendsto (fun x : T' ↦ indicatorProcess X (holderSet X T' p β U) x ω)
      (comap Subtype.val (𝓝 t)) (𝓝 c) := by
  classical
  by_cases hω : ω ∈ holderSet X T' p β U
  · have : (fun x : T' ↦ indicatorProcess X (holderSet X T' p β U) x ω)
        =ᶠ[comap Subtype.val (𝓝 t)] (fun x : T' ↦ X x ω) := by
      suffices ∀ᶠ (x : T') in (comap Subtype.val (𝓝 t)), ↑x ∈ U by
        filter_upwards [this] with x hx
        simp [hω]
      simp only [eventually_comap, Subtype.forall]
      suffices ∀ᶠ b in 𝓝 t, b ∈ U by
        filter_upwards [this] with x hx
        rintro x' hx' rfl
        exact hx
      rw [eventually_mem_set]
      exact hU.mem_nhds htU
    simp_rw [tendsto_congr' this]
    exact exists_tendsto_of_mem_holderSet hT hU hX.p_pos hβ_pos
      hT'_dense hω t htU
  · simp only [indicatorProcess_apply, hω, ↓reduceIte]
    exact ⟨hE.some, tendsto_const_nhds⟩
lemma measurable_holderModification (hT : HasBoundedCoveringNumber U c d)
    [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (t : T) :
    Measurable (holderModification X β p U t) :=
  _root_.Prove2MeSourceProof.h_dfed2a2c41cef06acf5bb665 hX.measurable
    (isLimitOfIndicator_holderModification hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt) t
omit [MeasurableSpace E] [BorelSpace E] in
lemma holderOnWith_holderModification
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β) (ω : Ω) :
    ∃ C : ℝ≥0, HolderOnWith C β (holderModification X β p U · ω) U := by
  let C ω := ⨆ (s : (denseCountable T ∩ U : Set T)) (t : (denseCountable T ∩ U : Set T)),
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  simp only [holderModification]
  suffices ∃ C, HolderOnWith C β
      (fun x ↦ limUnder (comap Subtype.val (𝓝 x))
        fun t' : denseCountable T ↦ indicatorProcess X (holderSet X (denseCountable T) p β U) t' ω)
      U by
    obtain ⟨C, hHolder⟩ := this
    refine ⟨C, ?_⟩
    -- missing congr lemma?
    intro s hs t ht
    specialize hHolder s hs t ht
    simpa only [hs, ↓reduceIte, ht]
  classical
  by_cases hω : ω ∈ holderSet X (denseCountable T) p β U
  · simp only [hω, ↓reduceIte, indicatorProcess_apply]
    refine ⟨(C ω ^ p⁻¹).toNNReal, ?_⟩
    refine (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_3cb59e664eda6af2b0a5ab70 p2mMethodArg0 dense_denseCountable) hU ?_ hβ_pos
    exact holderOnWith_of_mem_holderSet hT hX.p_pos hβ_pos hω
  · simp only [hω, ↓reduceIte, indicatorProcess_apply]
    refine ⟨0, HolderWith.holderOnWith ?_ _⟩
    exact (_root_.Prove2MeSourceProof.h_27cd69ca80d6c18aaca80d6a dense_denseCountable) (by simp [HolderWith]) hβ_pos
omit [MeasurableSpace E] [BorelSpace E] in
lemma uniformContinuousOn_holderModification
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β)
    (ω : Ω) :
    UniformContinuousOn (fun t : T ↦ holderModification X β p U t ω) U := by
  obtain ⟨C, hHolder⟩ := holderOnWith_holderModification hT hU hX hβ_pos ω
  exact hHolder.uniformContinuousOn hβ_pos
omit [MeasurableSpace E] [BorelSpace E] in
lemma continuousOn_holderModification
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β) (ω : Ω) :
    ContinuousOn (fun t : T ↦ holderModification X β p U t ω) U :=
  (uniformContinuousOn_holderModification hT hU hX hβ_pos ω).continuousOn
lemma measurable_pair_holderModification
    {U₁ U₂ : Set T} [DecidablePred (· ∈ U₁)] [DecidablePred (· ∈ U₂)]
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {X₁ X₂ : T → Ω → E} {c₁ c₂ : ℝ≥0∞} {p₁ p₂ q₁ q₂ d₁ d₂ : ℝ} {M₁ M₂ β₁ β₂ : ℝ≥0}
    (hT₁ : HasBoundedCoveringNumber U₁ c₁ d₁)
    (hT₂ : HasBoundedCoveringNumber U₂ c₂ d₂)
    (hX₁ : IsKolmogorovProcess X₁ P p₁ q₁ M₁)
    (hX₂ : IsKolmogorovProcess X₂ P p₂ q₂ M₂)
    (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (hdq₁_lt : d₁ < q₁) (hdq₂_lt : d₂ < q₂)
    (hβ₁_pos : 0 < β₁) (hβ₂_pos : 0 < β₂)
    (hβ₁_lt : β₁ < (q₁ - d₁) / p₁) (hβ₂_lt : β₂ < (q₂ - d₂) / p₂)
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s t : T) :
    Measurable[_, borel (E × E)]
      (fun ω ↦ (holderModification X₁ β₁ p₁ U₁ s ω, holderModification X₂ β₂ p₂ U₂ t ω)) :=
  _root_.Prove2MeSourceProof.h_1bd86707b36fe8af2e0c458d
    hX₁.measurable hX₂.measurable hX₁₂
    (isLimitOfIndicator_holderModification hT₁ hU₁ hX₁ hc₁ hd₁_pos hdq₁_lt hβ₁_pos hβ₁_lt)
    (isLimitOfIndicator_holderModification hT₂ hU₂ hX₂ hc₂ hd₂_pos hdq₂_lt hβ₂_pos hβ₂_lt) s t
lemma measurable_pair_holderModification_self
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (s t : T) :
    Measurable[_, borel (E × E)]
      (fun ω ↦ (holderModification X β p U s ω, holderModification X β p U t ω)) :=
  measurable_pair_holderModification hU hU hT hT hX hX hc hc hd_pos hd_pos hdq_lt hdq_lt
    hβ_pos hβ_pos hβ_lt hβ_lt hX.measurablePair s t
lemma measurable_edist_holderModification
    {U₁ U₂ : Set T} [DecidablePred (· ∈ U₁)] [DecidablePred (· ∈ U₂)]
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {X₁ X₂ : T → Ω → E} {c₁ c₂ : ℝ≥0∞} {p₁ p₂ q₁ q₂ d₁ d₂ : ℝ} {M₁ M₂ β₁ β₂ : ℝ≥0}
    (hT₁ : HasBoundedCoveringNumber U₁ c₁ d₁)
    (hT₂ : HasBoundedCoveringNumber U₂ c₂ d₂)
    (hX₁ : IsKolmogorovProcess X₁ P p₁ q₁ M₁)
    (hX₂ : IsKolmogorovProcess X₂ P p₂ q₂ M₂)
    (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (hdq₁_lt : d₁ < q₁) (hdq₂_lt : d₂ < q₂)
    (hβ₁_pos : 0 < β₁) (hβ₂_pos : 0 < β₂)
    (hβ₁_lt : β₁ < (q₁ - d₁) / p₁) (hβ₂_lt : β₂ < (q₂ - d₂) / p₂)
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s t : T) :
    Measurable (fun ω ↦ edist (holderModification X₁ β₁ p₁ U₁ s ω)
        (holderModification X₂ β₂ p₂ U₂ t ω)) :=
  IsLimitOfIndicator.measurable_edist
    hX₁.measurable hX₂.measurable hX₁₂
    (isLimitOfIndicator_holderModification hT₁ hU₁ hX₁ hc₁ hd₁_pos hdq₁_lt hβ₁_pos hβ₁_lt)
    (isLimitOfIndicator_holderModification hT₂ hU₂ hX₂ hc₂ hd₂_pos hdq₂_lt hβ₂_pos hβ₂_lt) s t
lemma measurable_edist_holderModification' {β₁ β₂ : ℝ≥0}
    (hT : HasBoundedCoveringNumber U c d) [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ₁_pos : 0 < β₁) (hβ₁_lt : β₁ < (q - d) / p)
    (hβ₂_pos : 0 < β₂) (hβ₂_lt : β₂ < (q - d) / p)
    (s t : T) :
    Measurable (fun ω ↦ edist (holderModification X β₁ p U s ω)
      (holderModification X β₂ p U t ω)) :=
  measurable_edist_holderModification hU hU hT hT hX hX hc hc hd_pos hd_pos hdq_lt hdq_lt
    hβ₁_pos hβ₂_pos hβ₁_lt hβ₂_lt hX.measurablePair s t
omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
lemma edist_holderModification_eq_zero (hT : HasBoundedCoveringNumber U c d) (hU : IsOpen U)
    [DecidablePred (· ∈ U)]
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β)
    (t' : denseCountable T) (ht'U : ↑t' ∈ U)
    {ω : Ω} (hω : ω ∈ holderSet X (denseCountable T) p β U) :
    edist (holderModification X β p U t' ω) (X t' ω) = 0 := by
  classical
  simp only [holderModification, ht'U, ↓reduceIte, indicatorProcess_apply, hω]
  have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 t')) := by
    rw [← nhds_subtype]
    infer_instance
  rw [← EMetric.inseparable_iff]
  have h_tendsto : Tendsto (fun (t' : denseCountable T) ↦ X t' ω) (𝓝 t') (𝓝 (X t' ω)) := by
    refine ContinuousOn.continuousAt ?_ ?_ (s := {x : denseCountable T | (x : T) ∈ U})
    · exact continuousOn_of_mem_holderSet hT hX.p_pos hβ_pos hω
    · refine IsOpen.mem_nhds ?_ ?_
      · exact Continuous.isOpen_preimage (by fun_prop) _ hU
      · simpa
  refine tendsto_nhds_unique_inseparable (f := fun t' : denseCountable T ↦ X t' ω)
    (l := comap Subtype.val (𝓝 t')) ?_ ?_
  · rw [← nhds_subtype]
    exact tendsto_nhds_limUnder ⟨X t' ω, h_tendsto⟩
  · rwa [← nhds_subtype]
variable [IsFiniteMeasure P]

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


