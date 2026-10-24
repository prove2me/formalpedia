-- Prove2me | solution 1 for ArtznerDEHK2007.thm4_3_time_consistency_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:49:30.998879+00:00
-- url     : https://prove2.me/submissions/9997f586-71b6-4a8f-be0c-1e1013e29d42

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps
import Theorems.Thm_MultiperiodRisk_Bellman_stable_tfae

open MeasureTheory MultiperiodRisk.Bellman Filter

namespace AR87

variable {Ω : Type*} {m : MeasurableSpace Ω}

lemma exists_isEssInf (μ : Measure Ω) [IsFiniteMeasure μ] (m' : MeasurableSpace Ω) (hm : m' ≤ m)
    (S : Set (Ω → ℝ)) (hne : S.Nonempty) (hmeas : ∀ h ∈ S, StronglyMeasurable[m'] h)
    (C : ℝ) (hC : ∀ h ∈ S, ∀ᵐ ω ∂μ, -C ≤ h ω) : ∃ g, IsEssInf μ m' S g := by
  classical
  obtain ⟨h₀, hh₀⟩ := hne
  have : Nonempty (ℕ → S) := ⟨fun _ => ⟨h₀, hh₀⟩⟩
  let T : (ℕ → S) → Ω → ℝ := fun s ω => ⨅ i, max ((s i : Ω → ℝ) ω) (-C)
  have hbdd : ∀ (s : ℕ → S) ω, BddBelow (Set.range fun i => max ((s i : Ω → ℝ) ω) (-C)) :=
    fun s ω => ⟨-C, by rintro _ ⟨j, rfl⟩; exact le_max_right _ _⟩
  have hTmeas : ∀ s, Measurable[m'] (T s) := fun s =>
    Measurable.iInf (fun i => ((hmeas _ (s i).2).measurable).max measurable_const)
  have hTle : ∀ s i ω, T s ω ≤ max ((s i : Ω → ℝ) ω) (-C) := fun s i ω => ciInf_le (hbdd s ω) i
  have hInt : ∀ s, Integrable (fun ω => Real.arctan (T s ω)) μ := by
    intro s
    refine Integrable.of_bound ?_ (Real.pi / 2) (Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_arctan.measurable.comp ((hTmeas s).mono hm le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  let I : (ℕ → S) → ℝ := fun s => ∫ ω, Real.arctan (T s ω) ∂μ
  have hIbdd : BddBelow (Set.range I) := ⟨∫ _, -(Real.pi / 2) ∂μ, by
    rintro _ ⟨s, rfl⟩
    exact integral_mono (integrable_const _) (hInt s) (fun ω => (Real.neg_pi_div_two_lt_arctan _).le)⟩
  let α := ⨅ s, I s
  have hαle : ∀ s, α ≤ I s := fun s => ciInf_le hIbdd s
  have hmono : ∀ s s', (∀ ω, T s ω ≤ T s' ω) → I s ≤ I s' := fun s s' h =>
    integral_mono (hInt s) (hInt s') (fun ω => Real.arctan_strictMono.monotone (h ω))
  have hex : ∀ k : ℕ, ∃ s, I s < α + 1 / (k + 1) := fun k =>
    exists_lt_of_ciInf_lt (by have : (0:ℝ) < 1 / (k + 1) := by positivity
                              linarith)
  choose s hs using hex
  let t : ℕ → S := fun n => s (Nat.unpair n).1 (Nat.unpair n).2
  have htle : ∀ k, I t ≤ I (s k) := by
    intro k
    refine hmono _ _ fun ω => le_ciInf fun i => ?_
    have := hTle t (Nat.pair k i) ω
    simpa [t, Nat.unpair_pair] using this
  have hIt : I t ≤ α := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have := htle k; have := hs k; linarith
  refine ⟨T t, (hTmeas t).stronglyMeasurable, ?_, ?_⟩
  · intro h hh
    let t' : ℕ → S := fun n => Nat.casesOn n ⟨h, hh⟩ (fun n => t n)
    have h1 : ∀ ω, T t' ω ≤ T t ω := fun ω => le_ciInf fun i => hTle t' (i + 1) ω
    have h2 : I t' = I t := le_antisymm (hmono _ _ h1) (hIt.trans (hαle t'))
    have h3 := (integral_eq_iff_of_ae_le (hInt t') (hInt t)
      (Eventually.of_forall fun ω => Real.arctan_strictMono.monotone (h1 ω))).1 h2
    filter_upwards [h3, hC h hh] with ω h3ω hCω
    have h4 : T t' ω = T t ω := Real.arctan_injective h3ω
    have h5 := hTle t' 0 ω
    rw [h4] at h5
    simpa [t', max_eq_left hCω] using h5
  · intro g' _ hg'
    have : ∀ᵐ ω ∂μ, ∀ i, g' ω ≤ (t i : Ω → ℝ) ω := ae_all_iff.2 fun i => hg' _ (t i).2
    filter_upwards [this] with ω hω
    exact le_ciInf fun i => (hω i).trans (le_max_left _ _)


lemma isEssInf_essInfFamily {μ : Measure Ω} {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)}
    (h : ∃ g, IsEssInf μ m' S g) : IsEssInf μ m' S (essInfFamily μ m' S) := by
  unfold essInfFamily; rw [dif_pos h]; exact h.choose_spec

lemma sm_essInfFamily (μ : Measure Ω) (m' : MeasurableSpace Ω) (S : Set (Ω → ℝ)) :
    StronglyMeasurable[m'] (essInfFamily μ m' S) := by
  unfold essInfFamily; split_ifs with h
  · exact h.choose_spec.1
  · exact stronglyMeasurable_const

lemma ei_le_of_dominates {μ : Measure Ω} {m' : MeasurableSpace Ω} {S T : Set (Ω → ℝ)}
    {g g' : Ω → ℝ} (hg : IsEssInf μ m' S g) (hg' : IsEssInf μ m' T g')
    (h : ∀ h' ∈ T, ∃ h ∈ S, h ≤ᵐ[μ] h') : g ≤ᵐ[μ] g' :=
  hg'.2.2 g hg.1 fun h' hh' => by
    obtain ⟨h, hS, hle⟩ := h h' hh'
    exact (hg.2.1 h hS).trans hle

lemma ei_ae_eq {μ : Measure Ω} {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)}
    {g g' : Ω → ℝ} (hg : IsEssInf μ m' S g) (hg' : IsEssInf μ m' S g') : g =ᵐ[μ] g' :=
  (ei_le_of_dominates hg hg' fun h hh => ⟨h, hh, EventuallyLE.refl _ _⟩).antisymm
    (ei_le_of_dominates hg' hg fun h hh => ⟨h, hh, EventuallyLE.refl _ _⟩)

lemma ei_abs_le {μ : Measure Ω} {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)}
    {g : Ω → ℝ} (hg : IsEssInf μ m' S g) (hne : S.Nonempty) (C : ℝ)
    (hC : ∀ h ∈ S, ∀ᵐ ω ∂μ, |h ω| ≤ C) : ∀ᵐ ω ∂μ, |g ω| ≤ C := by
  obtain ⟨h₀, hh₀⟩ := hne
  have h1 : (fun _ => -C) ≤ᵐ[μ] g := hg.2.2 _ stronglyMeasurable_const fun h hh => by
    filter_upwards [hC h hh] with ω hω
    exact (abs_le.1 hω).1
  filter_upwards [h1, hg.2.1 h₀ hh₀, hC h₀ hh₀] with ω h1 h2 h3
  exact abs_le.2 ⟨h1, h2.trans (abs_le.1 h3).2⟩

/-- shift lemma -/
lemma ei_shift {μ : Measure Ω} {m' : MeasurableSpace Ω} {S T : Set (Ω → ℝ)}
    {g Z : Ω → ℝ} (hg : IsEssInf μ m' T g) (hZ : StronglyMeasurable[m'] Z)
    (h1 : ∀ h ∈ S, ∃ h' ∈ T, h =ᵐ[μ] Z + h') (h2 : ∀ h' ∈ T, ∃ h ∈ S, h =ᵐ[μ] Z + h') :
    IsEssInf μ m' S (Z + g) := by
  refine ⟨hZ.add hg.1, fun h hh => ?_, fun g' hg' hle => ?_⟩
  · obtain ⟨h', hT, he⟩ := h1 h hh
    filter_upwards [hg.2.1 h' hT, he] with ω a b
    simp only [Pi.add_apply] at *; linarith
  · have : g' - Z ≤ᵐ[μ] g := hg.2.2 _ (hg'.sub hZ) fun h' hT => by
      obtain ⟨h, hS, he⟩ := h2 h' hT
      filter_upwards [hle h hS, he] with ω a b
      simp only [Pi.add_apply, Pi.sub_apply] at *; linarith
    filter_upwards [this] with ω a
    simp only [Pi.add_apply, Pi.sub_apply] at *; linarith

lemma coe_untopA_of_le {a : WithTop ℕ} {n : ℕ} (h : a ≤ n) : ((a.untopA : ℕ) : WithTop ℕ) = a := by
  have hne : a ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
  rw [WithTop.untopA_eq_untop hne]; exact WithTop.coe_untop a hne

section Q
variable {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

lemma Q_fin (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D) : IsFiniteMeasure (Q P₀ f) :=
  isFiniteMeasure_withDensity_ofReal (D.integrable f hf.1).2

lemma Q_ac (f : Ω → ℝ) : Q P₀ f ≪ P₀ := withDensity_absolutelyContinuous _ _

lemma P_ac (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D) : P₀ ≪ Q P₀ f := by
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp
      (((D.stronglyMeasurable f hf.1).mono (ℱ.le N)).measurable)).aemeasurable
  · filter_upwards [hf.2] with ω hω
    simpa using hω

end Q


section Proc
variable {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

def clampP (X : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ := fun n => X (min n N)
def prevP (X : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ := fun n => if n = 0 then 0 else X (min (n - 1) N)

def Good (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) (X : ℕ → Ω → ℝ) (C : ℝ) : Prop :=
  (∀ n ≤ N, StronglyMeasurable[ℱ n] (X n)) ∧ 0 ≤ C ∧ ∀ᵐ ω ∂P₀, ∀ n ≤ N, |X n ω| ≤ C

lemma good_of_vp {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) : ∃ C, Good P₀ ℱ N X C := by
  obtain ⟨hm, C, hC⟩ := hX
  refine ⟨max C 0, hm, le_max_right _ _, ?_⟩
  have : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → |X n ω| ≤ C := ae_all_iff.2 fun n => by
    by_cases hn : n ≤ N
    · filter_upwards [hC n hn] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hn
  filter_upwards [this] with ω h n hn using (h n hn).trans (le_max_left _ _)

lemma vp_of_good {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C) : IsValueProcess P₀ ℱ N X :=
  ⟨hX.1, C, fun n hn => by filter_upwards [hX.2.2] with ω h using h n hn⟩

lemma adapted_clampP {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n)) :
    StronglyAdapted ℱ (clampP X N) := fun n =>
  (hXm (min n N) (min_le_right _ _)).mono (ℱ.mono (min_le_left _ _))

lemma adapted_prevP {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n)) :
    StronglyAdapted ℱ (prevP X N) := fun n => by
  unfold prevP
  split_ifs with h
  · exact stronglyMeasurable_const
  · exact (hXm _ (min_le_right _ _)).mono (ℱ.mono (by omega))

lemma untopA_coe' (k : ℕ) : ((k : WithTop ℕ)).untopA = k := rfl

lemma ua_le {a : WithTop ℕ} {n : ℕ} (h : a ≤ (n : WithTop ℕ)) : a.untopA ≤ n := WithTop.untopA_le h

lemma stoppedValue_clamp (X : ℕ → Ω → ℝ) {ρ : Ω → WithTop ℕ} (hρ : ∀ ω, ρ ω ≤ N) :
    stoppedValue X ρ = stoppedValue (clampP X N) ρ := by
  funext ω
  simp only [stoppedValue, clampP]
  rw [min_eq_left (ua_le (hρ ω))]

lemma Xprev_eq (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ N) :
    Xprev X τ = stoppedValue (prevP X N) τ := by
  funext ω
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτ ω))
  have hk' : τ ω = (k : WithTop ℕ) := hk.symm
  have hkN : k ≤ N := by have := ua_le (hτ ω); rw [hk'] at this; exact this
  simp only [Xprev, stoppedValue, prevP, hk', untopA_coe']
  by_cases h0 : k = 0
  · subst h0; simp
  · have : ¬ ((k : WithTop ℕ) = 0) := fun h => h0 (by exact_mod_cast h)
    rw [if_neg this, if_neg h0, min_eq_left (by omega)]

lemma sm_stoppedValue {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n))
    {ρ : Ω → WithTop ℕ} (hρ : IsBddStoppingTime ℱ N ρ) :
    StronglyMeasurable[ℱ N] (stoppedValue X ρ) := by
  rw [stoppedValue_clamp X hρ.2]
  exact stronglyMeasurable_stoppedValue_of_le
    (adapted_clampP hXm).isStronglyProgressive_of_discrete hρ.1 hρ.2

lemma sm_Xprev {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n))
    {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[hτ.1.measurableSpace] (Xprev X τ) := by
  rw [Xprev_eq X hτ.2]
  exact (measurable_stoppedValue
    (adapted_prevP hXm).isStronglyProgressive_of_discrete hτ.1).stronglyMeasurable

lemma preStop_eq (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ N) (n : ℕ) :
    preStop X τ n = fun ω => if (n : WithTop ℕ) < τ ω then clampP X N n ω
      else stoppedValue (prevP X N) (fun ω => min (τ ω) n) ω := by
  funext ω
  simp only [preStop]
  split_ifs with h
  · have : n ≤ N := by have := h.trans_le (hτ ω); exact_mod_cast this.le
    simp [clampP, min_eq_left this]
  · rw [Xprev_eq X hτ]
    simp only [stoppedValue]
    rw [min_eq_left (not_lt.1 h)]

lemma sm_preStop {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n))
    {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (preStop X τ n) := by
  rw [preStop_eq X hτ.2 n]
  refine StronglyMeasurable.ite (hτ.1.measurableSet_gt n) (adapted_clampP hXm n) ?_
  exact stronglyMeasurable_stoppedValue_of_le
    (adapted_prevP hXm).isStronglyProgressive_of_discrete (hτ.1.min_const n) (fun ω => min_le_right _ _)

lemma sm_ite_le {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {g : Ω → ℝ}
    (hg : StronglyMeasurable[hτ.measurableSpace] g) (n : ℕ) :
    StronglyMeasurable[ℱ n] (fun ω => if τ ω ≤ (n : WithTop ℕ) then g ω else 0) := by
  have hgm := hg.measurable
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  have h1 : MeasurableSet[ℱ n] (g ⁻¹' B ∩ {ω | τ ω ≤ n}) := (hgm hB).2 n
  have h2 : MeasurableSet[ℱ n] {ω | τ ω ≤ n} := hτ n
  by_cases h0 : (0:ℝ) ∈ B
  · convert h1.union h2.compl using 1; ext ω; by_cases h : τ ω ≤ n <;> simp [h, h0]
  · convert h1 using 1; ext ω; by_cases h : τ ω ≤ n <;> simp [h, h0]

lemma fromStop_eq (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} {n : ℕ} :
    fromStop X τ n = fun ω => if τ ω ≤ (n : WithTop ℕ) then X n ω - preStop X τ n ω else 0 := by
  funext ω
  simp only [fromStop, preStop]
  split_ifs with h1 h2 <;> try rfl
  exact absurd h1 (not_le.2 h2)

lemma sm_fromStop {X : ℕ → Ω → ℝ} (hXm : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n))
    {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) (n : ℕ) (hn : n ≤ N) :
    StronglyMeasurable[ℱ n] (fromStop X τ n) := by
  rw [fromStop_eq]
  exact StronglyMeasurable.ite (hτ.1 n) ((hXm n hn).sub (sm_preStop hXm hτ n))
    stronglyMeasurable_const

end Proc


section Bounds
variable {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

lemma pw_Xprev {X : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ N)
    {ω : Ω} (hω : ∀ n ≤ N, |X n ω| ≤ C) : |Xprev X τ ω| ≤ C := by
  unfold Xprev
  split_ifs
  · simpa using hC
  · exact hω _ (by have := ua_le (hτ ω); omega)

lemma pw_preStop {X : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ N)
    {ω : Ω} (hω : ∀ n ≤ N, |X n ω| ≤ C) (n : ℕ) : |preStop X τ n ω| ≤ C := by
  unfold preStop
  split_ifs with h
  · exact hω n (by have := h.trans_le (hτ ω); exact_mod_cast this.le)
  · exact pw_Xprev hC hτ hω

lemma pw_fromStop {X : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ N)
    {ω : Ω} (hω : ∀ n ≤ N, |X n ω| ≤ C) (n : ℕ) (hn : n ≤ N) : |fromStop X τ n ω| ≤ 2 * C := by
  unfold fromStop
  split_ifs
  · have h1 := hω n hn; have h2 := pw_Xprev hC hτ hω
    calc |X n ω - Xprev X τ ω| ≤ |X n ω| + |Xprev X τ ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  · simp; linarith

lemma pw_sv {X : ℕ → Ω → ℝ} {C : ℝ} {ρ : Ω → WithTop ℕ} (hρ : ∀ ω, ρ ω ≤ N)
    {ω : Ω} (hω : ∀ n ≤ N, |X n ω| ≤ C) : |stoppedValue X ρ ω| ≤ C :=
  hω _ (ua_le (hρ ω))

lemma good_fromStop {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C) {τ : Ω → WithTop ℕ}
    (hτ : IsBddStoppingTime ℱ N τ) : Good P₀ ℱ N (fromStop X τ) (2 * C) :=
  ⟨fun n hn => sm_fromStop hX.1 hτ n hn, by linarith [hX.2.1], by
    filter_upwards [hX.2.2] with ω hω n hn using pw_fromStop hX.2.1 hτ.2 hω n hn⟩

lemma ae_sv {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C) {ρ : Ω → WithTop ℕ}
    (hρ : ∀ ω, ρ ω ≤ N) : ∀ᵐ ω ∂P₀, |stoppedValue X ρ ω| ≤ C := by
  filter_upwards [hX.2.2] with ω hω using pw_sv hρ hω

lemma integrable_sv (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {ρ : Ω → WithTop ℕ} (hρ : IsBddStoppingTime ℱ N ρ) {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Integrable (stoppedValue X ρ) (Q P₀ f) := by
  have := Q_fin D hf
  refine Integrable.of_bound ((sm_stoppedValue hX.1 hρ).mono (ℱ.le N)).aestronglyMeasurable C ?_
  refine (Q_ac f).ae_le ?_
  filter_upwards [ae_sv hX hρ.2] with ω h
  simpa [Real.norm_eq_abs] using h

lemma member_bound (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) {h : Ω → ℝ} (hh : h ∈ psiFamily D X σ hσ) :
    ∀ᵐ ω ∂P₀, |h ω| ≤ C := by
  obtain ⟨ρ, hρ, _, f, hf, rfl⟩ := hh
  exact (P_ac D hf).ae_le (ae_bdd_abs_condExp_of_ae_bdd_abs ((Q_ac f).ae_le (ae_sv hX hρ.2)))

lemma isEssInf_Psi [IsProbabilityMeasure P₀] (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {σ : Ω → WithTop ℕ} (hσ : IsBddStoppingTime ℱ N σ) :
    IsEssInf P₀ hσ.1.measurableSpace (psiFamily D X σ hσ.1) (Psi D X σ hσ.1) := by
  apply isEssInf_essInfFamily
  obtain ⟨f, hf⟩ := hPe
  refine exists_isEssInf P₀ _ hσ.1.measurableSpace_le _ ⟨_, σ, hσ, fun _ => le_rfl, f, hf, rfl⟩
    ?_ C ?_
  · rintro h ⟨ρ, hρ, _, f, hf, rfl⟩
    exact stronglyMeasurable_condExp
  · intro h hh
    filter_upwards [member_bound D hX hσ.1 hh] with ω hω using (abs_le.1 hω).1

lemma psiFamily_nonempty (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ)
    {σ : Ω → WithTop ℕ} (hσ : IsBddStoppingTime ℱ N σ) : (psiFamily D X σ hσ.1).Nonempty := by
  obtain ⟨f, hf⟩ := hPe
  exact ⟨_, σ, hσ, fun _ => le_rfl, f, hf, rfl⟩

lemma Psi_bound [IsProbabilityMeasure P₀] (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {σ : Ω → WithTop ℕ} (hσ : IsBddStoppingTime ℱ N σ) :
    ∀ᵐ ω ∂P₀, |Psi D X σ hσ.1 ω| ≤ C :=
  ei_abs_le (isEssInf_Psi D hPe hX hσ) (psiFamily_nonempty D hPe X hσ) C
    fun _ hh => member_bound D hX hσ.1 hh

end Bounds


section MC
variable {P₀ : Measure Ω} [IsProbabilityMeasure P₀] {ℱ : Filtration ℕ m} {N : ℕ}

lemma Psi_mono (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) {X Y : ℕ → Ω → ℝ} {C C' : ℝ}
    (hX : Good P₀ ℱ N X C) (hY : Good P₀ ℱ N Y C') (hle : ∀ n ≤ N, X n ≤ᵐ[P₀] Y n)
    {σ : Ω → WithTop ℕ} (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 ≤ᵐ[P₀] Psi D Y σ hσ.1 := by
  refine ei_le_of_dominates (isEssInf_Psi D hPe hX hσ) (isEssInf_Psi D hPe hY hσ) ?_
  rintro _ ⟨ρ, hρ, hσρ, f, hf, rfl⟩
  refine ⟨_, ⟨ρ, hρ, hσρ, f, hf, rfl⟩, ?_⟩
  have := Q_fin D hf
  refine (P_ac D hf).ae_le ?_
  refine condExp_mono (integrable_sv D hX hρ hf) (integrable_sv D hY hρ hf) ?_
  refine (Q_ac f).ae_le ?_
  have : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → X n ω ≤ Y n ω := ae_all_iff.2 fun n => by
    by_cases hn : n ≤ N
    · filter_upwards [hle n hn] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hn
  filter_upwards [this] with ω hω using hω _ (ua_le (hρ.2 ω))

omit [IsProbabilityMeasure P₀] in
lemma integrable_Xprev (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Integrable (Xprev X τ) (Q P₀ f) := by
  have := Q_fin D hf
  refine Integrable.of_bound ((sm_Xprev hX.1 hτ).mono hτ.1.measurableSpace_le).aestronglyMeasurable
    C ?_
  refine (Q_ac f).ae_le ?_
  filter_upwards [hX.2.2] with ω h
  simpa [Real.norm_eq_abs] using pw_Xprev hX.2.1 hτ.2 h

lemma sv_fromStop (X : ℕ → Ω → ℝ) {τ ρ : Ω → WithTop ℕ} (hρ : ∀ ω, ρ ω ≤ N)
    (hτρ : ∀ ω, τ ω ≤ ρ ω) :
    stoppedValue X ρ = Xprev X τ + stoppedValue (fromStop X τ) ρ := by
  funext ω
  simp only [stoppedValue, fromStop, Pi.add_apply]
  rw [if_pos (by rw [coe_untopA_of_le (hρ ω)]; exact hτρ ω)]
  ring

omit [IsProbabilityMeasure P₀] in
lemma cash_core (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ N X C)
    {τ ρ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) (hρ : IsBddStoppingTime ℱ N ρ)
    (hτρ : ∀ ω, τ ω ≤ ρ ω) {f : Ω → ℝ} (hf : f ∈ Pe D) :
    (Q P₀ f)[stoppedValue X ρ | hτ.1.measurableSpace] =ᵐ[P₀]
      Xprev X τ + (Q P₀ f)[stoppedValue (fromStop X τ) ρ | hτ.1.measurableSpace] := by
  have := Q_fin D hf
  refine (P_ac D hf).ae_eq ?_
  rw [sv_fromStop X hρ.2 hτρ]
  have h1 := condExp_add (integrable_Xprev D hX hτ hf)
    (integrable_sv D (good_fromStop hX hτ) hρ hf) hτ.1.measurableSpace
  rw [condExp_of_stronglyMeasurable hτ.1.measurableSpace_le (sm_Xprev hX.1 hτ)
    (integrable_Xprev D hX hτ hf)] at h1
  exact h1

lemma Psi_cash (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hX : Good P₀ ℱ N X C) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D X τ hτ.1 =ᵐ[P₀] Xprev X τ + Psi D (fromStop X τ) τ hτ.1 := by
  refine ei_ae_eq (isEssInf_Psi D hPe hX hτ)
    (ei_shift (isEssInf_Psi D hPe (good_fromStop hX hτ) hτ) (sm_Xprev hX.1 hτ) ?_ ?_)
  · rintro _ ⟨ρ, hρ, hτρ, f, hf, rfl⟩
    exact ⟨_, ⟨ρ, hρ, hτρ, f, hf, rfl⟩, cash_core D hX hτ hρ hτρ hf⟩
  · rintro _ ⟨ρ, hρ, hτρ, f, hf, rfl⟩
    exact ⟨_, ⟨ρ, hρ, hτρ, f, hf, rfl⟩, cash_core D hX hτ hρ hτρ hf⟩

end MC


section BX
variable {P₀ : Measure Ω} [IsProbabilityMeasure P₀] {ℱ : Filtration ℕ m} {N : ℕ}

lemma good_bellman (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hX : Good P₀ ℱ N X C) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    Good P₀ ℱ N (bellmanProcess D X τ hτ.1) (3 * C) := by
  refine ⟨fun n _ => (sm_preStop hX.1 hτ n).add (sm_ite_le hτ.1 (sm_essInfFamily _ _ _) n),
    by linarith [hX.2.1], ?_⟩
  filter_upwards [hX.2.2, Psi_bound D hPe (good_fromStop hX hτ) hτ] with ω hω hP n _
  simp only [bellmanProcess]
  have h1 := pw_preStop hX.2.1 hτ.2 hω n
  split_ifs
  · calc _ ≤ |preStop X τ n ω| + |Psi D (fromStop X τ) τ hτ.1 ω| := abs_add_le _ _
      _ ≤ 3 * C := by linarith
  · simp only [add_zero]; linarith [hX.2.1]

omit [IsProbabilityMeasure P₀] in
lemma Xprev_bellman (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ}
    (hτ : IsBddStoppingTime ℱ N τ) :
    Xprev (bellmanProcess D X τ hτ.1) τ = Xprev X τ := by
  funext ω
  unfold Xprev
  split_ifs with h0
  · rfl
  · have hu := coe_untopA_of_le (hτ.2 ω)
    have hu0 : (τ ω).untopA ≠ 0 := by
      intro h; apply h0; rw [← hu, h]; rfl
    have hlt : ((((τ ω).untopA - 1 : ℕ)) : WithTop ℕ) < τ ω := by
      have key : ∀ u : ℕ, u ≠ 0 → ((u - 1 : ℕ) : WithTop ℕ) < (u : WithTop ℕ) :=
        fun u hu => by exact_mod_cast (by omega : u - 1 < u)
      have := key _ hu0
      rwa [hu] at this
    simp only [bellmanProcess, preStop]
    rw [if_pos hlt, if_neg (not_le.2 hlt), add_zero]

omit [IsProbabilityMeasure P₀] in
lemma preStop_bellman (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ}
    (hτ : IsBddStoppingTime ℱ N τ) (n : ℕ) :
    preStop (bellmanProcess D X τ hτ.1) τ n = preStop X τ n := by
  funext ω
  have := congrFun (Xprev_bellman D X hτ) ω
  simp only [preStop] at *
  split_ifs with h
  · simp only [bellmanProcess, preStop, if_pos h, if_neg (not_le.2 h), add_zero]
  · exact this

omit [IsProbabilityMeasure P₀] in
lemma sv_bellman (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) {τ ρ : Ω → WithTop ℕ}
    (hτ : IsBddStoppingTime ℱ N τ) (hρ : ∀ ω, ρ ω ≤ N) (hτρ : ∀ ω, τ ω ≤ ρ ω) :
    stoppedValue (bellmanProcess D X τ hτ.1) ρ = Xprev X τ + Psi D (fromStop X τ) τ hτ.1 := by
  funext ω
  simp only [stoppedValue, bellmanProcess, preStop, Pi.add_apply]
  rw [coe_untopA_of_le (hρ ω), if_neg (not_lt.2 (hτρ ω)), if_pos (hτρ ω)]

lemma Psi_bellman_tau (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hX : Good P₀ ℱ N X C) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D (bellmanProcess D X τ hτ.1) τ hτ.1 =ᵐ[P₀] Xprev X τ + Psi D (fromStop X τ) τ hτ.1 := by
  set G := Xprev X τ + Psi D (fromStop X τ) τ hτ.1
  have hGm : StronglyMeasurable[hτ.1.measurableSpace] G :=
    (sm_Xprev hX.1 hτ).add (sm_essInfFamily _ _ _)
  have hmem : ∀ h ∈ psiFamily D (bellmanProcess D X τ hτ.1) τ hτ.1, h = G := by
    rintro _ ⟨ρ, hρ, hτρ, f, hf, rfl⟩
    have := Q_fin D hf
    rw [sv_bellman D X hτ hρ.2 hτρ]
    refine condExp_of_stronglyMeasurable hτ.1.measurableSpace_le hGm ?_
    refine (integrable_Xprev D hX hτ hf).add ?_
    refine Integrable.of_bound ((sm_essInfFamily _ _ _).mono
      hτ.1.measurableSpace_le).aestronglyMeasurable (2 * C) ?_
    refine (Q_ac f).ae_le ?_
    filter_upwards [Psi_bound D hPe (good_fromStop hX hτ) hτ] with ω h
    simpa [Real.norm_eq_abs] using h
  have hG : IsEssInf P₀ hτ.1.measurableSpace
      (psiFamily D (bellmanProcess D X τ hτ.1) τ hτ.1) G := by
    refine ⟨hGm, fun h hh => by rw [hmem h hh], fun g' _ hg' => ?_⟩
    obtain ⟨h₀, hh₀⟩ := psiFamily_nonempty D hPe (bellmanProcess D X τ hτ.1) hτ
    have := hg' h₀ hh₀
    rwa [hmem h₀ hh₀] at this
  exact ei_ae_eq (isEssInf_Psi D hPe (good_bellman D hPe hX hτ) hτ) hG

end BX

end AR87

open AR87 in
theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    (P₀ : Measure Ω) [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (hℱ₀ : ∀ s, MeasurableSet[ℱ 0] s → P₀ s = 0 ∨ P₀ s = 1)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    IsStable D ↔
      ∀ X Y : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X → IsValueProcess P₀ ℱ N Y →
        ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
          (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
          (∀ n ≤ N, preStop X τ n =ᵐ[P₀] preStop Y τ n) →
          Psi D X τ hτ.1 ≤ᵐ[P₀] Psi D Y τ hτ.1 →
          Psi D X σ hσ.1 ≤ᵐ[P₀] Psi D Y σ hσ.1 := by
  have hBP := (stable_tfae P₀ ℱ N hℱ₀ D hPe).out 0 3
  constructor
  · intro hS X Y hXv hYv σ τ hσ hτ hστ hpre hPsi
    have bp := hBP.1 hS
    obtain ⟨C, hX⟩ := good_of_vp hXv
    obtain ⟨C', hY⟩ := good_of_vp hYv
    have e1 := bp X hXv σ τ hσ hτ hστ
    have e2 := bp Y hYv σ τ hσ hτ hστ
    have hxp : Xprev X τ =ᵐ[P₀] Xprev Y τ := by
      filter_upwards [hpre N le_rfl] with ω h
      simpa [preStop, not_lt.2 (hτ.2 ω)] using h
    have hfs : Psi D (fromStop X τ) τ hτ.1 ≤ᵐ[P₀] Psi D (fromStop Y τ) τ hτ.1 := by
      filter_upwards [Psi_cash D hPe hX hτ, Psi_cash D hPe hY hτ, hxp, hPsi] with ω a b c d
      simp only [Pi.add_apply] at a b
      linarith
    have hle : ∀ n ≤ N, bellmanProcess D X τ hτ.1 n ≤ᵐ[P₀] bellmanProcess D Y τ hτ.1 n :=
      fun n hn => by
        filter_upwards [hpre n hn, hfs] with ω a b
        simp only [bellmanProcess]
        rw [a]
        split_ifs
        · linarith
        · exact le_rfl
    filter_upwards [e1, e2, Psi_mono D hPe (good_bellman D hPe hX hτ) (good_bellman D hPe hY hτ)
      hle hσ] with ω a b c
    rw [a, b]; exact c
  · intro hTC
    apply hBP.2
    intro X hXv σ τ hσ hτ hστ
    obtain ⟨C, hX⟩ := good_of_vp hXv
    have hY := good_bellman D hPe hX hτ
    have hpre : ∀ n ≤ N, preStop X τ n =ᵐ[P₀] preStop (bellmanProcess D X τ hτ.1) τ n :=
      fun n _ => by rw [preStop_bellman D X hτ n]
    have hτeq : Psi D X τ hτ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) τ hτ.1 :=
      (Psi_cash D hPe hX hτ).trans (Psi_bellman_tau D hPe hX hτ).symm
    exact (hTC X _ hXv (vp_of_good hY) σ τ hσ hτ hστ hpre hτeq.le).antisymm
      (hTC _ X (vp_of_good hY) hXv σ τ hσ hτ hστ (fun n hn => (hpre n hn).symm) hτeq.symm.le)
