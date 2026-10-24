-- Prove2me | solution 1 for ArtznerDEHK2007.thm4_2_stable_tfae_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:16:07.613978+00:00
-- url     : https://prove2.me/submissions/cbd0785d-da8d-4a18-abe0-b430f31c67b5

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps

open MeasureTheory MultiperiodRisk.Bellman Filter Topology
open scoped ENNReal

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


end AR87

namespace AT88
open AR87

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
  {ℱ : Filtration ℕ m}

lemma condExp_self (D : TestSet P₀ ℱ 1) {X : ℕ → Ω → ℝ} {C : ℝ} (hX : Good P₀ ℱ 1 X C)
    {f : Ω → ℝ} (hf : f ∈ Pe D) {n : ℕ} (hn : n ≤ 1) :
    (Q P₀ f)[X n | ℱ n] = X n := by
  have := Q_fin D hf
  have hρ : IsBddStoppingTime ℱ 1 (fun _ => ((n : ℕ) : WithTop ℕ)) :=
    ⟨isStoppingTime_const ℱ n, fun _ => WithTop.coe_le_coe.2 hn⟩
  exact condExp_of_stronglyMeasurable (ℱ.le n) (hX.1 n hn) (integrable_sv D hX hρ hf)

lemma case_one (D : TestSet P₀ ℱ 1) (hPe : (Pe D).Nonempty) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hX : Good P₀ ℱ 1 X C) : PsiN D X 1 =ᵐ[P₀] PsiBar D X 1 := by
  have hσ : IsBddStoppingTime ℱ 1 (fun _ => ((1:ℕ) : WithTop ℕ)) :=
    ⟨isStoppingTime_const ℱ 1, fun _ => le_rfl⟩
  have hE := isEssInf_Psi D hPe hX hσ
  have hbar : PsiBar D X 1 = X 1 := by simp [PsiBar, psiBarAux]
  rw [hbar]
  refine ei_ae_eq hE ?_
  rw [IsStoppingTime.measurableSpace_const]
  have hmem : ∀ h ∈ psiFamily D X (fun _ => ((1:ℕ) : WithTop ℕ)) hσ.1, h = X 1 := by
    rintro h ⟨τ, hτ, hστ, f, hf, rfl⟩
    have hτ1 : ∀ ω, τ ω = 1 := fun ω => le_antisymm (hτ.2 ω) (hστ ω)
    have : stoppedValue X τ = X 1 := by
      funext ω; simp [stoppedValue, hτ1 ω]
    rw [this, IsStoppingTime.measurableSpace_const]
    exact condExp_self D hX hf le_rfl
  refine ⟨hX.1 1 le_rfl, fun h hh => by rw [hmem h hh], fun g' _ hg' => ?_⟩
  obtain ⟨h, hh⟩ := psiFamily_nonempty D hPe X hσ
  have := hg' h hh
  rwa [hmem h hh] at this

lemma case_zero (D : TestSet P₀ ℱ 1) (hPe : (Pe D).Nonempty) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hX : Good P₀ ℱ 1 X C) : PsiN D X 0 =ᵐ[P₀] PsiBar D X 0 := by
  have hσ : IsBddStoppingTime ℱ 1 (fun _ => ((0:ℕ) : WithTop ℕ)) :=
    ⟨isStoppingTime_const ℱ 0, fun _ => by exact_mod_cast zero_le_one⟩
  have h1 : IsBddStoppingTime ℱ 1 (fun _ => ((1:ℕ) : WithTop ℕ)) :=
    ⟨isStoppingTime_const ℱ 1, fun _ => le_rfl⟩
  have hPs := isEssInf_Psi D hPe hX hσ
  set T : Set (Ω → ℝ) := {h | ∃ f ∈ Pe D, h = (Q P₀ f)[X 1 | ℱ 0]} with hTdef
  have hbar : PsiBar D X 0 = fun ω => min (X 0 ω) (essInfFamily P₀ (ℱ 0) T ω) := by
    simp [PsiBar, psiBarAux, hTdef]
  rw [hbar]
  have hTb : ∀ h ∈ T, ∀ᵐ ω ∂P₀, |h ω| ≤ C := by
    rintro h ⟨f, hf, rfl⟩
    have hb : ∀ᵐ ω ∂P₀, |X 1 ω| ≤ C := by
      filter_upwards [hX.2.2] with ω hω using hω 1 le_rfl
    exact (P_ac D hf).ae_le (ae_bdd_abs_condExp_of_ae_bdd_abs ((Q_ac f).ae_le hb))
  obtain ⟨f₀, hf₀⟩ := hPe
  have hT : IsEssInf P₀ (ℱ 0) T (essInfFamily P₀ (ℱ 0) T) := by
    apply isEssInf_essInfFamily
    refine exists_isEssInf P₀ (ℱ 0) (ℱ.le 0) T ⟨_, f₀, hf₀, rfl⟩ ?_ C ?_
    · rintro h ⟨f, hf, rfl⟩; exact stronglyMeasurable_condExp
    · intro h hh
      filter_upwards [hTb h hh] with ω hω using (abs_le.1 hω).1
  set E := essInfFamily P₀ (ℱ 0) T
  refine ei_ae_eq hPs ?_
  rw [IsStoppingTime.measurableSpace_const]
  refine ⟨((hX.1 0 zero_le_one).measurable.min hT.1.measurable).stronglyMeasurable, ?_, ?_⟩
  · rintro h ⟨τ, hτ, -, f, hf, rfl⟩
    have := Q_fin D hf
    rw [IsStoppingTime.measurableSpace_const]
    set S : Set Ω := {ω | τ ω ≤ ((0:ℕ) : WithTop ℕ)}
    have hS : MeasurableSet[ℱ 0] S := hτ.1.measurableSet_le 0
    have hsv : stoppedValue X τ = S.indicator (X 0) + Sᶜ.indicator (X 1) := by
      funext ω
      have h01 : τ ω = 0 ∨ τ ω = 1 := by
        have := hτ.2 ω
        obtain ⟨k, hk⟩ : ∃ k : ℕ, τ ω = k := ⟨(τ ω).untopA, (coe_untopA_of_le this).symm⟩
        rw [hk] at this ⊢
        have : k ≤ 1 := by exact_mod_cast this
        interval_cases k <;> simp
      rcases h01 with h0 | h0
      · have : ω ∈ S := by simp [S, h0]
        simp [stoppedValue, h0, this]
      · have : ω ∉ S := by simp [S, h0]
        simp [stoppedValue, h0, this]
    have hρ0 : IsBddStoppingTime ℱ 1 (fun _ => ((0:ℕ) : WithTop ℕ)) := hσ
    have hi0 : Integrable (X 0) (Q P₀ f) := integrable_sv D hX hρ0 hf
    have hi1 : Integrable (X 1) (Q P₀ f) := integrable_sv D hX h1 hf
    have hce : (Q P₀ f)[stoppedValue X τ | ℱ 0] =ᵐ[Q P₀ f]
        S.indicator (X 0) + Sᶜ.indicator ((Q P₀ f)[X 1 | ℱ 0]) := by
      rw [hsv]
      refine (condExp_add (hi0.indicator ((ℱ.le 0) _ hS))
        (hi1.indicator ((ℱ.le 0) _ hS.compl)) _).trans ?_
      refine (condExp_indicator hi0 hS).add (condExp_indicator hi1 hS.compl) |>.trans ?_
      have : (Q P₀ f)[X 0 | ℱ 0] = X 0 := condExp_self D hX hf zero_le_one
      rw [this]
    have hce' := (P_ac D hf).ae_le hce
    filter_upwards [hce', hT.2.1 _ ⟨f, hf, rfl⟩] with ω hω hEω
    simp only [Nat.cast_id] at *
    rw [hω]
    by_cases hωS : ω ∈ S
    · simp [hωS]
    · simp [hωS]; exact Or.inr hEω
  · intro g' _ hg'
    have hA : g' ≤ᵐ[P₀] X 0 := by
      have := hg' _ ⟨fun _ => ((0:ℕ) : WithTop ℕ), hσ, fun _ => le_rfl, f₀, hf₀, rfl⟩
      have e : stoppedValue X (fun _ => ((0:ℕ) : WithTop ℕ)) = X 0 := by
        funext ω; simp [stoppedValue]
      rw [e, IsStoppingTime.measurableSpace_const] at this
      simp only [Nat.cast_id] at this
      rwa [condExp_self D hX hf₀ zero_le_one] at this
    have hB : g' ≤ᵐ[P₀] E := hT.2.2 g' (by assumption) fun h ⟨f, hf, hh⟩ => by
      have := hg' _ ⟨fun _ => ((1:ℕ) : WithTop ℕ), h1, fun _ => by simp, f, hf, rfl⟩
      have e : stoppedValue X (fun _ => ((1:ℕ) : WithTop ℕ)) = X 1 := by
        funext ω; simp [stoppedValue]
      rw [e, IsStoppingTime.measurableSpace_const] at this
      simp only [Nat.cast_id] at this
      rwa [← hh] at this
    filter_upwards [hA, hB] with ω a b using le_min a b

theorem item3 (D : TestSet P₀ ℱ 1) (hPe : (Pe D).Nonempty) :
    ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ 1 X → ∀ n ≤ 1, PsiN D X n =ᵐ[P₀] PsiBar D X n := by
  intro X hX n hn
  obtain ⟨C, hC⟩ := good_of_vp hX
  interval_cases n
  · exact case_zero D hPe hC
  · exact case_one D hPe hC

end AT88

namespace AT88M

universe u

/-- four points -/
def W : Type u := ULift.{u} (Fin 4)

instance : Fintype W := inferInstanceAs (Fintype (ULift (Fin 4)))
instance : DecidableEq W := inferInstanceAs (DecidableEq (ULift (Fin 4)))
instance mW : MeasurableSpace W := ⊤
instance : DiscreteMeasurableSpace W := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def pt (i : Fin 4) : W := ULift.up i

lemma sum_W (F : W → ℝ) : ∑ ω, F ω = F (pt 0) + F (pt 1) + F (pt 2) + F (pt 3) := by
  rw [← Fin.sum_univ_four (f := fun i => F (pt i))]
  exact (Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl))

lemma sum_W' (F : W → ℝ≥0∞) : ∑ ω, F ω = F (pt 0) + F (pt 1) + F (pt 2) + F (pt 3) := by
  rw [← Fin.sum_univ_four (f := fun i => F (pt i))]
  exact (Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl))

noncomputable def P₀ : Measure W := (4 : ℝ≥0∞)⁻¹ • Measure.count

lemma P₀_single (x : W) : P₀ {x} = 4⁻¹ := by
  simp [P₀]

lemma P₀_real (x : W) : P₀.real {x} = 1 / 4 := by
  simp [Measure.real, P₀_single]

instance : IsProbabilityMeasure P₀ := ⟨by
  simp only [P₀, Measure.smul_apply, smul_eq_mul]
  rw [Measure.count_univ]
  rw [show (ENat.card W) = 4 by simp [ENat.card_eq_coe_fintype_card, Fintype.card_ulift, W]]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

lemma ae_all {p : W → Prop} (h : ∀ᵐ ω ∂P₀, p ω) (ω : W) : p ω := by
  by_contra hc
  have h0 : P₀ {ω | ¬ p ω} = 0 := ae_iff.1 h
  have : P₀ {ω} = 0 := measure_mono_null (by simpa using hc) h0
  rw [P₀_single] at this
  norm_num at this

lemma integral_W (F : W → ℝ) : ∫ ω, F ω ∂P₀ = (F (pt 0) + F (pt 1) + F (pt 2) + F (pt 3)) / 4 := by
  rw [integral_fintype (Integrable.of_finite), sum_W]
  simp only [P₀_real, smul_eq_mul]; ring

/-- the atom indicator: `true` on `{0,1}` -/
def a (ω : W) : Bool := decide ((ULift.down ω : Fin 4).val < 2)

def F0 : MeasurableSpace W := MeasurableSpace.comap a inferInstance

def ℱ : Filtration ℕ mW where
  seq n := if n = 0 then F0 else ⊤
  mono' i j hij := by
    simp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact le_top
    · omega
    · exact le_rfl
  le' i := le_top

lemma ℱ0 : ℱ 0 = F0 := rfl
lemma ℱ1 : ℱ 1 = ⊤ := rfl

noncomputable def f₂ : W → ℝ := fun ω => ![2/5, 4/5, 2/5, 12/5] (ULift.down ω)
noncomputable def g₂ : W → ℝ := fun ω => if a ω then 3/5 else 7/5

@[simp] lemma a0 : a (pt 0) = true := rfl
@[simp] lemma a1 : a (pt 1) = true := rfl
@[simp] lemma a2 : a (pt 2) = false := rfl
@[simp] lemma a3 : a (pt 3) = false := rfl
@[simp] lemma f0 : f₂ (pt 0) = 2/5 := rfl
@[simp] lemma f1 : f₂ (pt 1) = 4/5 := rfl
@[simp] lemma f2 : f₂ (pt 2) = 2/5 := rfl
@[simp] lemma f3 : f₂ (pt 3) = 12/5 := rfl

lemma ce_f2 : P₀[f₂ | ℱ 0] = g₂ := by
  have hm : ℱ 0 ≤ mW := ℱ.le 0
  have h := ae_eq_condExp_of_forall_setIntegral_eq (μ := P₀) hm (f := f₂) (g := g₂)
    (Integrable.of_finite) (fun s _ _ => Integrable.of_finite.integrableOn) ?_ ?_
  · funext ω; exact (ae_all h ω).symm
  · intro s hs _
    rw [ℱ0] at hs
    obtain ⟨t, -, rfl⟩ := hs
    rw [← integral_indicator (MeasurableSpace.measurableSet_top),
      ← integral_indicator (MeasurableSpace.measurableSet_top), integral_W, integral_W]
    by_cases ht : true ∈ t <;> by_cases hf : false ∈ t <;>
      simp [Set.indicator, g₂, ht, hf] <;> norm_num
  · have : Measurable[F0] g₂ :=
      (Measurable.of_discrete (f := fun b : Bool => if b then (3/5 : ℝ) else 7/5)).comp
        (comap_measurable a)
    rw [ℱ0]
    exact this.stronglyMeasurable.aestronglyMeasurable

def S : Set (W → ℝ) := {f | (∀ ω, 0 ≤ f ω) ∧ ∑ ω, f ω = 4 ∧ f (pt 0) = f (pt 2)}

lemma tend_pt {g : ℕ → W → ℝ} {f : W → ℝ}
    (h : Tendsto (fun k => eLpNorm (g k - f) 1 P₀) atTop (𝓝 0)) (ω : W) :
    Tendsto (fun k => g k ω) atTop (𝓝 (f ω)) := by
  rw [tendsto_iff_edist_tendsto_0]
  have hle : ∀ k, edist (g k ω) (f ω) ≤ 4 * eLpNorm (g k - f) 1 P₀ := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm, lintegral_fintype]
    have : ‖(g k - f) ω‖ₑ * P₀ {ω} ≤ ∑ x, ‖(g k - f) x‖ₑ * P₀ {x} :=
      Finset.single_le_sum (f := fun x => ‖(g k - f) x‖ₑ * P₀ {x}) (fun _ _ => zero_le)
        (Finset.mem_univ ω)
    rw [P₀_single] at this
    calc edist (g k ω) (f ω) = ‖(g k - f) ω‖ₑ * (4 * 4⁻¹) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one, edist_eq_enorm_sub]
          rfl
      _ = 4 * (‖(g k - f) ω‖ₑ * 4⁻¹) := by ring
      _ ≤ _ := by gcongr
  have h4 := ENNReal.Tendsto.const_mul h (a := 4) (Or.inr (by norm_num))
  rw [mul_zero] at h4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun _ => zero_le) hle

noncomputable def D : TestSet P₀ ℱ 1 where
  set := S
  stronglyMeasurable f _ := by
    rw [ℱ1]; exact (Measurable.of_discrete (f := f)).stronglyMeasurable
  nonneg f hf := Eventually.of_forall hf.1
  integrable f _ := Integrable.of_finite
  integral_eq_one f hf := by rw [integral_W, ← sum_W, hf.2.1]; norm_num
  convex := by
    intro f hf g hg s t hs ht hst
    refine ⟨fun ω => ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hf.1 ω; have := hg.1 ω; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2.1, hg.2.1]
      linear_combination 4 * hst
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hf.2.2, hg.2.2]
  closed g f hg _ hlim := by
    have ht := tend_pt hlim
    refine ⟨fun ω => ge_of_tendsto' (ht ω) fun k => (hg k).1 ω, ?_, ?_⟩
    · have : Tendsto (fun k => ∑ ω, g k ω) atTop (𝓝 (∑ ω, f ω)) :=
        tendsto_finsetSum _ fun ω _ => ht ω
      have e : (fun k => ∑ ω, g k ω) = fun _ => (4 : ℝ) := funext fun k => (hg k).2.1
      rw [e] at this
      exact tendsto_nhds_unique this tendsto_const_nhds
    · have h0 := ht (pt 0); have h2 := ht (pt 2)
      have e : (fun k => g k (pt 0)) = fun k => g k (pt 2) := funext fun k => (hg k).2.2
      rw [e] at h0; exact tendsto_nhds_unique h0 h2
  ae_saturated f hf g _ hgf := by
    have : g = f := funext fun ω => ae_all hgf ω
    rw [this]; exact hf

lemma one_mem : (fun _ => (1 : ℝ)) ∈ Pe D :=
  ⟨⟨fun _ => zero_le_one, by rw [sum_W]; norm_num, rfl⟩, Eventually.of_forall fun _ => one_pos⟩

lemma hPe : (Pe D).Nonempty := ⟨_, one_mem⟩

lemma f₂_pos (ω : W) : 0 < f₂ ω := by
  rcases ω with ⟨i⟩
  fin_cases i <;> simp [f₂]

lemma f₂_mem : f₂ ∈ Pe D :=
  ⟨⟨fun ω => (f₂_pos ω).le, by rw [sum_W]; simp; norm_num, rfl⟩, Eventually.of_forall f₂_pos⟩

lemma not_stable : ¬ IsStable D := by
  intro h
  have hτ : IsBddStoppingTime ℱ 1 (fun _ => ((0:ℕ) : WithTop ℕ)) :=
    ⟨isStoppingTime_const ℱ 0, fun _ => by simp⟩
  have hm := (h _ one_mem f₂ f₂_mem _ hτ).2.2
  have z1 : Z P₀ ℱ (fun _ => (1:ℝ)) 0 = fun _ => 1 := condExp_const (ℱ.le 0) _
  have z2 : Z P₀ ℱ f₂ 0 = g₂ := ce_f2
  simp only [pasteDensity, stoppedValue] at hm
  have hu : ((0:ℕ) : WithTop ℕ).untopA = 0 := rfl
  rw [hu, z1, z2] at hm
  simp [g₂] at hm
  norm_num at hm

end AT88M

theorem solution : ¬ (∀ {Ω : Type} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty),
    List.TFAE
      [ IsStable D,
        ∀ f ∈ D.set, ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f),
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n,
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
            (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
            Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 ] ) := by
  intro h
  exact AT88M.not_stable (((h AT88M.P₀ AT88M.ℱ 1 AT88M.D AT88M.hPe).out 0 2).2
    (AT88.item3 AT88M.D AT88M.hPe))
