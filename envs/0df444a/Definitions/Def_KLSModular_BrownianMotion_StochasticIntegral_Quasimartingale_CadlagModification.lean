-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
-- name    : KLSModular_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:52:08.320647+00:00
-- url     : https://prove2.me/theorems/f016612b-78f2-4a3a-ab26-161269ff85f2
-- title:
--   Càdlàg modifications of quasimartingales
-- statement:
--   `regularityTimes` is a countable dense set of times containing every time whose right-neighborhood filter is trivial. Given a regularity family, `rightContModifOf` is the right-limit modification along this set, taking value zero outside the relevant regularity event, while `cadlagModifOf` retains it only on sample points belonging to all such events; under the stated topological assumptions their paths are respectively right-continuous and càdlàg, and the relevant measurability and strong-adaptedness results are provided. The real specializations `rightContModifReal` and `cadlagModifReal` use `regularitySet` for a real quasimartingale. For a finite measure, these regularity events hold almost everywhere, and `rightContModifReal` is almost everywhere equal to $X_t$ at any time where $X$ converges in measure from the right to $X_t$; the càdlàg modification is almost everywhere equal to the corresponding right-continuous modification.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.ConvergenceInMeasure
--   public import BrownianMotion.Auxiliary.Jensen
--   public import BrownianMotion.Auxiliary.LeftLimWithin
--   public import BrownianMotion.Continuity.LimitModification
--   public import BrownianMotion.StochasticIntegral.Cadlag
--   public import BrownianMotion.StochasticIntegral.Predictable
--   public import BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
--   public import BrownianMotion.Auxiliary.Jensen
--   public import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
--     {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
--       (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/ConvergenceInMeasure`](https://prove2.me/theorems/884ba99c-f6fd-4155-bf8e-936dd517f9d3), [`BrownianMotion/Auxiliary/Jensen`](https://prove2.me/theorems/64bc905d-b33c-4e61-a626-8eccc1cf8d1f), [`BrownianMotion/Auxiliary/LeftLimWithin`](https://prove2.me/theorems/9ce2c305-4dcb-48bd-9e79-d5e3bc7ee72d), [`BrownianMotion/Continuity/LimitModification`](https://prove2.me/theorems/9ab8c90e-3308-48d6-b8e1-bb02aace32f0), [`BrownianMotion/StochasticIntegral/Cadlag`](https://prove2.me/theorems/018dc80a-f371-45a4-ad73-e4ef0a7c732d), [`BrownianMotion/StochasticIntegral/Predictable`](https://prove2.me/theorems/8e95b9f6-de16-4b50-a1bf-65e43acaf5fa), [`BrownianMotion/StochasticIntegral/Quasimartingale/MaximalInequality`](https://prove2.me/theorems/e20d8b34-0dbf-46f5-90fa-e44fc4fef760).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean) · `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`, definition bundle `KLSModular_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/BrownianMotion/BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean, lines 39-1415). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_ConvergenceInMeasure
import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Jensen
import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_LeftLimWithin
import Definitions.Def_KLSModular_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Predictable
import Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- Modified by kls-lean for the selected proved dependency closure; see formalization/vendor/port.patch.

/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess
/-- A dense set contains points above any point which is not maximal. -/
lemma Dense.exists_gt_of_not_isMax {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α]
    {s : Set α} (hs : Dense s) {a : α} (ha : ¬ IsMax a) :
    ∃ b ∈ s, a < b :=
  hs.exists_mem_open isOpen_Ioi (not_isMax_iff.1 ha)
/-- A dense set contains points in `Ioo a b` for `a < b`, if `a` is not isolated on the right.
Version of `Dense.exists_between` for an order which may not be densely ordered. -/
lemma Dense.exists_between_of_nhdsGT_neBot {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α]
    {s : Set α} (hs : Dense s) {a b : α} [(𝓝[>] a).NeBot] (hab : a < b) :
    ∃ c ∈ s, a < c ∧ c < b :=
  hs.exists_mem_open isOpen_Ioo (Filter.nonempty_of_mem (Ioo_mem_nhdsGT hab))
/-- A maximal element is isolated on the right. -/
lemma IsMax.nhdsGT_eq_bot {α : Type*} [Preorder α] [TopologicalSpace α] {a : α} (ha : IsMax a) :
    𝓝[>] a = ⊥ :=
  ha.Ioi_eq ▸ nhdsWithin_empty a
/-- A point which is not isolated on the right is not maximal. -/
lemma not_isMax_of_nhdsGT_neBot {α : Type*} [Preorder α] [TopologicalSpace α] {a : α}
    [h : (𝓝[>] a).NeBot] : ¬ IsMax a :=
  fun ha ↦ h.ne ha.nhdsGT_eq_bot
namespace ProbabilityTheory
variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
section RegularitySet
variable {X : ι → Ω → ℝ}
/-- In this set, the process is bounded and has finitely many upcrossings (of any interval) in `T`
before time `d` -/
def regularitySet (T : Set ι) (X : ι → Ω → ℝ) (d : ι) : Set Ω :=
  {ω | (∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r) ∧
    (∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1)}
lemma regularitySet_anti {T : Set ι} {X : ι → Ω → ℝ} {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySet T X d₂ ⊆ regularitySet T X d₁ := by
  intro ω hω
  simp only [regularitySet, Set.mem_ofPred_eq] at hω ⊢
  constructor
  · intro q r hqr
    have hω' :=  hω.1 q r hqr
    refine fun h_mem ↦ hω' ?_
    exact infiniteAlt_mono'' hd h_mem
  · obtain ⟨M, hM⟩ := hω.2
    refine ⟨M, fun s hs ↦ ?_⟩
    specialize hM s (by grind)
    grind
section OrderBot
variable [OrderBot ι]
lemma ae_mem_all_regularitySet [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    {T T' : Set ι} (hT : T.Countable) (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ω ∈ regularitySet T X d := by
  filter_upwards [measure_all_infiniteAlt hX hT hT', ae_exists_bound hX hT hT'] with ω hω1 hω2 d hdT
  exact ⟨fun q r hqr ↦ hω1 d hdT q r (mod_cast hqr), hω2 d hdT⟩
lemma measurableSet_altSet (hX : IsRealQuasimartingale 𝓕 X μ)
    (d : ι) (F : Finset ι) (hF : ∀ i ∈ F, i ≤ d) {q r : ℚ} (_hqr : q < r) (m : ℕ) :
    MeasurableSet[𝓕 d] (altSet X F q r m) := by
  have hXmeas : ∀ s ∈ F, Measurable[𝓕 d] (X s) := fun s hs ↦
    (hX.adapted s).mono (𝓕.mono (hF s hs)) le_rfl
  have hset : altSet X F (q : ℝ) (r : ℝ) m
      = ⋃ g ∈ Fintype.piFinset (fun _ : Fin (2 * m) ↦ F),
          {ω | (∀ (i : Fin (2 * m)) (h : (i : ℕ) + 1 < 2 * m), g i < g ⟨(i : ℕ) + 1, h⟩)
            ∧ (∀ i : Fin m, X (g ⟨2 * (i : ℕ), by omega⟩) ω ≤ (q : ℝ))
            ∧ (∀ i : Fin m, (r : ℝ) ≤ X (g ⟨2 * (i : ℕ) + 1, by omega⟩) ω)} := by
    ext ω
    simp only [altSet, Set.mem_ofPred_eq, Set.mem_iUnion, Fintype.mem_piFinset, exists_prop]
    constructor
    · rintro ⟨c, hc1, hc2, hc3, hc4⟩
      exact ⟨fun i ↦ c (i : ℕ), fun i ↦ hc2 (i : ℕ) i.2,
        fun i h ↦ hc1 (i : ℕ) h, fun i ↦ hc3 (i : ℕ) i.2, fun i ↦ hc4 (i : ℕ) i.2⟩
    · rintro ⟨g, hgF, hg1, hg3, hg4⟩
      refine ⟨fun k ↦ if h : k < 2 * m then g ⟨k, h⟩ else ⊥, by grind, by grind, ?_, ?_⟩
      · intro i hi
        have h2i : 2 * i < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg3 ⟨i, hi⟩
      · intro i hi
        have h2i : 2 * i + 1 < 2 * m := by lia
        simp only [dif_pos h2i]
        exact hg4 ⟨i, hi⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun g hg ↦ ?_
  have hgF : ∀ i, g i ∈ F := Fintype.mem_piFinset.mp hg
  -- Split off the (measure-space independent) monotonicity condition, then recognise the event
  -- as a finite intersection of measurable half-lines `{X s ≤ q}` and `{r ≤ X s}`, `s ∈ F`.
  rw [Set.ofPred_and]
  refine (MeasurableSet.const _).inter ?_
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ ?_) (MeasurableSet.iInter fun i ↦ ?_)
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ), by lia⟩) measurableSet_Iic
  · exact hXmeas _ (hgF ⟨2 * (i : ℕ) + 1, by lia⟩) measurableSet_Ici
lemma measurableSet_infiniteAlt (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) {q r : ℚ} (hqr : q < r) :
    MeasurableSet[𝓕 d] (infiniteAlt T d X q r) := by
  unfold infiniteAlt
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.biUnion ?_ fun F ↦ ?_
  · refine countable_setOf_finset_coe_subset ?_
    exact hT.mono (by grind)
  · intro hF
    refine measurableSet_altSet hX d F ?_ hqr m
    simp only [Set.subset_inter_iff, Set.mem_ofPred_eq] at hF
    intro i hi
    exact hF.2 hi
lemma measurableSet_regularitySet (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hT : T.Countable) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySet T X d) := by
  suffices MeasurableSet[𝓕 d]
        ((⋂ (q : ℚ) (r : ℚ) (hqr : q < r), {ω | ω ∉ infiniteAlt T d X q r}) ∩
        (⋃ M : ℕ, ⋂ s ∈ T ∩ Set.Iic d, {ω | |X s ω| ≤ M + 1})) by
      convert this
      ext ω
      simp [regularitySet]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun q ↦ ?_
    by_cases hpq : p < q
    · simp only [hpq, Set.iInter_true]
      refine MeasurableSet.compl ?_
      exact measurableSet_infiniteAlt hX hT d hpq
    · simp [hpq]
  · refine MeasurableSet.iUnion fun M ↦ MeasurableSet.biInter (hT.mono (by grind)) fun s hs ↦ ?_
    refine measurableSet_le ?_ (by fun_prop)
    simp only [Set.mem_inter_iff, Set.mem_Iic] at hs
    refine Measurable.mono ?_ (𝓕.mono hs.2) le_rfl
    simp_rw [← Real.norm_eq_abs]
    exact (hX.stronglyAdapted s).norm.measurable
end OrderBot
variable [TopologicalSpace ι] [OrderTopology ι]
lemma right_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxd : x < d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    simpa using hω.2
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_right hxd hfa hfb
  · refine ⟨((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Ioc x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x :=
      Filter.mem_of_superset (Ioo_inter_mem_nhdsWithin_inter_Ioi hxd) (by grind)
    filter_upwards [hU] with s' hs' using by grind
lemma left_limit_of_mem_regularitySet {T : Set ι}
    (x d : ι) {ω : Ω} (hxle : x ≤ d) (hω : ω ∈ regularitySet T X d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l) := by
  simp only [regularitySet, Set.mem_inter_iff, Set.mem_Iic, and_imp, Set.mem_ofPred_eq] at hω
  have h1 : ∀ (q r : ℚ), q < r → ω ∉ infiniteAlt T d X q r := hω.1
  have h2 : ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
    simpa using hω.2
  obtain ⟨M, hM⟩ := h2
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hqr ⟨hfa, hfb⟩
    refine h1 p p' (mod_cast hqr) ?_
    exact mem_infiniteAlt_of_frequently_left hxle hfa hfb
  · refine ⟨(M : ℝ) + 1, ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
  · refine ⟨-((M : ℝ) + 1), ?_⟩
    rw [Filter.eventually_map]
    have hU : Set.Iio x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
      rw [Set.inter_comm]
      exact self_mem_nhdsWithin
    filter_upwards [hU] with s' hs' using by grind
end RegularitySet
section RegularityFamily
variable [TopologicalSpace ι] {T : Set ι} {R : ι → Set Ω} {d : ι} {ω : Ω}
/-- The set of `ω` that belong to some `R s`, for `s ∈ T` with `s > d` or for `s ≥ d` isolated on
the right (`𝓝[>] s = ⊥`: `s` is maximal or has a successor). Here `R` is an antitone family of
sets, for example `regularitySet T X` for a real process `X`.

If `d` is not isolated on the right and `T` is dense, this is the set of `ω` that belong to
`R s` for some `s ∈ T` with `s > d` (see `regularitySetRight_eq_biUnion_gt`).
If `d` is isolated on the right, this is `R d` (see `regularitySetRight_of_nhdsGT_eq_bot`). -/
def regularitySetRight (T : Set ι) (R : ι → Set Ω) (d : ι) : Set Ω :=
  ⋃ s ∈ (T ∩ Set.Ioi d) ∪ ({s | 𝓝[>] s = ⊥} ∩ Set.Ici d), R s
lemma mem_regularitySetRight_iff :
    ω ∈ regularitySetRight T R d
      ↔ ∃ s, ((s ∈ T ∧ d < s) ∨ (𝓝[>] s = ⊥ ∧ d ≤ s)) ∧ ω ∈ R s := by
  simp [regularitySetRight]
lemma regularitySetRight_of_nhdsGT_eq_bot (hR : Antitone R) (hd : 𝓝[>] d = ⊥) :
    regularitySetRight T R d = R d := by
  ext ω
  rw [mem_regularitySetRight_iff]
  refine ⟨fun ⟨s, hs, hω⟩ ↦ ?_, fun hω ↦ ⟨d, .inr ⟨hd, le_rfl⟩, hω⟩⟩
  rcases hs with ⟨-, hds⟩ | ⟨-, hds⟩
  · exact hR hds.le hω
  · exact hR hds hω
lemma regularitySetRight_eq_biUnion_lt (hR : Antitone R) {t : ι} [hd : (𝓝[>] d).NeBot]
    (hdt : d < t) (hT : ∀ s, d < s → ∃ u ∈ T, d < u ∧ u ≤ s) :
    regularitySetRight T R d = ⋃ d' ∈ T ∩ Set.Ioc d t, R d' := by
  ext ω
  simp only [mem_regularitySetRight_iff, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
    Set.mem_Ioc]
  refine ⟨fun ⟨i, hi, hωi⟩ ↦ ?_, fun ⟨i, ⟨hiT, hdi, hit⟩, hωi⟩ ↦ ⟨i, .inl ⟨hiT, hdi⟩, hωi⟩⟩
  -- `d` is not isolated on the right, hence `d < i` in both cases
  have hdi : d < i := by
    rcases hi with ⟨-, hdi⟩ | ⟨hi, hdi⟩
    · exact hdi
    · exact lt_of_le_of_ne hdi fun h ↦ hd.ne (h ▸ hi)
  obtain ⟨u, huT, hdu, hu⟩ := hT (min i t) (lt_min hdi hdt)
  exact ⟨u, ⟨huT, hdu, hu.trans (min_le_right _ _)⟩, hR (hu.trans (min_le_left _ _)) hωi⟩
lemma regularitySetRight_anti {d₁ d₂ : ι} (hd : d₁ ≤ d₂) :
    regularitySetRight T R d₂ ⊆ regularitySetRight T R d₁ := by
  intro ω hω
  rw [mem_regularitySetRight_iff] at hω ⊢
  obtain ⟨s, hs, hω⟩ := hω
  exact ⟨s, hs.imp (fun h ↦ ⟨h.1, hd.trans_lt h.2⟩) (fun h ↦ ⟨h.1, hd.trans h.2⟩), hω⟩
/-- If almost surely `ω` belongs to `R d` for all `d ∈ T` and all `d` isolated on the right, then
almost surely `ω` belongs to all the sets `regularitySetRight T R d`. -/
lemma ae_mem_regularitySetRight
    (hR : ∀ᵐ ω ∂μ, ∀ d ∈ T ∪ {s | 𝓝[>] s = ⊥}, ω ∈ R d)
    (hTcof : ∀ x, ¬ IsMax x → ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T R d := by
  filter_upwards [hR] with ω hω d
  rw [mem_regularitySetRight_iff]
  by_cases hd : 𝓝[>] d = ⊥
  · exact ⟨d, .inr ⟨hd, le_rfl⟩, hω d (.inr hd)⟩
  · obtain ⟨s, hs, hsd⟩ := hTcof d fun hd' ↦ hd hd'.nhdsGT_eq_bot
    exact ⟨s, .inl ⟨hs, hsd⟩, hω s (.inl hs)⟩
variable [OrderTopology ι]
/-- For a right-continuous filtration and a time `t` that is not isolated on the right, a set that
is `𝓕 s`-measurable for every `s > t` is already `𝓕 t`-measurable, since `𝓕 t = ⨅ s > t, 𝓕 s`. -/
lemma measurableSet_of_forall_gt [𝓕.IsRightContinuous]
    {t : ι} [(𝓝[>] t).NeBot] {A : Set Ω}
    (h : ∀ s, t < s → MeasurableSet[𝓕 s] A) :
    MeasurableSet[𝓕 t] A := by
  have hrc : (𝓕 t : MeasurableSpace Ω) = ⨅ j > t, 𝓕 j := by
    have h1 := 𝓕.rightCont_eq_of_neBot_nhdsGT t
    rwa [Filtration.IsRightContinuous.eq] at h1
  rw [hrc, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  exact h j
lemma measurableSet_regularitySetRight [𝓕.IsRightContinuous] (hR : Antitone R)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) (hT : T.Countable) (hTd : Dense T) (d : ι) :
    MeasurableSet[𝓕 d] (regularitySetRight T R d) := by
  -- if `d` is isolated on the right, the set is `R d`
  rcases (𝓝[>] d).eq_or_neBot with hd | hd
  · rw [regularitySetRight_of_nhdsGT_eq_bot hR hd]
    exact hRm d
  refine measurableSet_of_forall_gt fun s hs ↦ ?_
  rw [regularitySetRight_eq_biUnion_lt hR hs]
  swap
  · intro u hu
    obtain ⟨z, hz1, hz2, hz3⟩ := hTd.exists_between_of_nhdsGT_neBot hu
    exact ⟨z, hz1, hz2, hz3.le⟩
  refine MeasurableSet.biUnion (hT.mono Set.inter_subset_left) fun t ht ↦ ?_
  exact 𝓕.mono ht.2.2 _ (hRm t)
lemma eventually_mem_regularitySetRight_of_mem (hω : ω ∈ regularitySetRight T R d) :
    ∀ᶠ y in 𝓝[>] d, ω ∈ regularitySetRight T R y := by
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  rcases hs with ⟨hsT, hds⟩ | ⟨hs, hds⟩
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hds] with y hy hxy
    exact mem_regularitySetRight_iff.2 ⟨s, .inl ⟨hsT, hy⟩, hω'⟩
  · rcases hds.eq_or_lt with rfl | hds
    · -- `d` is isolated on the right
      simp [hs]
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [eventually_lt_nhds hds] with y hy hxy
      exact mem_regularitySetRight_iff.2 ⟨s, .inr ⟨hs, hy.le⟩, hω'⟩
variable {E : Type*} [TopologicalSpace E] {X : ι → Ω → E}
/-- An antitone family of events `R d` is a regularity family for a process `X` along a set of
times `T` if on `R d`, the path of `X` along `T` has right limits at all times before `d` and left
limits at all times up to `d`. -/
structure IsRegularityFamily (T : Set ι) (X : ι → Ω → E) (R : ι → Set Ω) : Prop where
  anti : Antitone R
  exists_tendsto_nhdsGT ⦃x d : ι⦄ ⦃ω : Ω⦄ (hxd : x < d) (hω : ω ∈ R d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi x] x) (𝓝 l)
  exists_tendsto_nhdsLT ⦃x d : ι⦄ ⦃ω : Ω⦄ (hxd : x ≤ d) (hω : ω ∈ R d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio x] x) (𝓝 l)
namespace IsRegularityFamily
variable (hR : IsRegularityFamily T X R) {y : ι}
include hR
omit [OrderTopology ι] in
lemma right_limit_of_mem_regularitySetRight (hω : ω ∈ regularitySetRight T R d) (hyd : y ≤ d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi y] y) (𝓝 l) := by
  by_cases hy : 𝓝[>] y = ⊥
  · exact ⟨X y ω, by simp [eq_bot_mono (nhdsWithin_mono _ Set.inter_subset_right) hy]⟩
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine hR.exists_tendsto_nhdsGT ?_ hω'
  rcases hs with ⟨-, hds⟩ | ⟨hs, hds⟩
  · exact hyd.trans_lt hds
  · exact lt_of_le_of_ne (hyd.trans hds) fun h ↦ hy (h ▸ hs)
omit [OrderTopology ι] in
lemma left_limit_of_mem_regularitySetRight (hω : ω ∈ regularitySetRight T R d) (hyd : y ≤ d) :
    ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Iio y] y) (𝓝 l) := by
  obtain ⟨s, hs, hω'⟩ := mem_regularitySetRight_iff.1 hω
  refine hR.exists_tendsto_nhdsLT ?_ hω'
  rcases hs with ⟨-, hds⟩ | ⟨-, hds⟩
  · exact hyd.trans hds.le
  · exact hyd.trans hds
lemma tendsto_nhdsGT_rightLimWithin (hω : ω ∈ regularitySetRight T R d) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Ioi d] d) (𝓝 (Function.rightLimWithin (X · ω) T d)) := by
  have h := hR.right_limit_of_mem_regularitySetRight hω le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_rightLimWithin_of_tendsto h
lemma tendsto_nhdsLT_leftLimWithin (hω : ω ∈ regularitySetRight T R d) :
    Tendsto (X · ω) (𝓝[T ∩ Set.Iio d] d) (𝓝 (Function.leftLimWithin (X · ω) T d)) := by
  have h := hR.left_limit_of_mem_regularitySetRight hω le_rfl
  rw [Set.inter_comm] at h ⊢
  exact tendsto_leftLimWithin_of_tendsto h
lemma continuousWithinAt_rightLimWithin [T3Space E] (hTd : Dense T)
    (hT : ∀ y, 𝓝[>] y = ⊥ → y ∈ T) (hω : ω ∈ regularitySetRight T R d) :
    ContinuousWithinAt (Function.rightLimWithin (X · ω) T) (Set.Ici d) d := by
  refine continuousWithinAt_rightLimWithin_Ici_of_dense hTd (.of_forall hT) ?_ ?_
  · rw [Set.inter_comm]
    exact hR.tendsto_nhdsGT_rightLimWithin hω
  · filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
    rw [Set.inter_comm]
    exact hR.tendsto_nhdsGT_rightLimWithin hy
end IsRegularityFamily
end RegularityFamily
variable [TopologicalSpace ι] [OrderTopology ι]
section PathRegularization
variable {F : Type*} [TopologicalSpace F] [RegularSpace F] {T : Set ι} {h r : ι → F} {x : ι}
/-- The right-limit regularization inherits left limits of `h` along `T`. -/
lemma tendsto_rightLim_nhdsLT (hTd : Dense T) (hT : ∀ y, 𝓝[>] y = ⊥ → y ∈ T)
    (hr : ∀ᶠ y in 𝓝[<] x, Tendsto h (𝓝[T ∩ Set.Ioi y] y) (𝓝 (r y)))
    (hr' : ∀ y, 𝓝[>] y = ⊥ → r y = h y) {L : F}
    (hL : Tendsto h (𝓝[T ∩ Set.Iio x] x) (𝓝 L)) :
    Tendsto r (𝓝[<] x) (𝓝 L) := by
  by_cases hex : ∃ u, u < x
  swap
  · have hempty : Set.Iio x = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun u hu ↦ hex ⟨u, hu⟩)
    rw [nhdsWithin, hempty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro C ⟨hCmem, hCclosed⟩
  have hev : ∀ᶠ s in 𝓝[<] x ⊓ 𝓟 T, h s ∈ C := by
    rw [nhdsWithin_inf_principal, Set.inter_comm]; exact hL.eventually hCmem
  obtain ⟨v, hvx, hv⟩ := (nhdsLT_basis_of_exists_lt hex).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hvx, hr] with y hy hr
  -- if `y` is isolated on the right, then `r y = h y` and `y ∈ T`
  rcases (𝓝[>] y).eq_or_neBot with hy' | hy'
  · rw [hr' y hy']
    exact hv hy (hT y hy')
  have hne := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd y
  rw [Set.inter_comm] at hne
  refine hCclosed.mem_of_tendsto hr ?_
  rw [Set.inter_comm, ← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsGT hy.2] with s hs hsT
  exact hv ⟨hy.1.trans hs.1, hs.2⟩ hsT
end PathRegularization
open Function
section RealRegularity
variable {X : ι → Ω → ℝ} {T : Set ι}
/-- The events `regularitySet T X d` form a regularity family for the real process `X`. -/
lemma isRegularityFamily_regularitySet : IsRegularityFamily T X (regularitySet T X) :=
  ⟨fun _ _ hd ↦ regularitySet_anti hd,
    fun x d _ hxd hω ↦ right_limit_of_mem_regularitySet x d hxd hω,
    fun x d _ hxd hω ↦ left_limit_of_mem_regularitySet x d hxd hω⟩
variable [OrderBot ι]
/-- Almost surely, `ω` belongs to `regularitySet T X d` for all `d ∈ T` and all `d` isolated on
the right. -/
lemma ae_mem_all_regularitySet_union_nhdsGT_eq_bot [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T ∪ {s | 𝓝[>] s = ⊥}, ω ∈ regularitySet T X d :=
  ae_mem_all_regularitySet hX hT (hT.union countable_setOfPred_isolated_right)
lemma IsRealQuasimartingale.ae_mem_regularitySetRight [SecondCountableTopology ι]
    [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (hTcof : ∀ x, ¬ IsMax x → ∃ s ∈ T, x < s) :
    ∀ᵐ ω ∂μ, ∀ d, ω ∈ regularitySetRight T (regularitySet T X) d :=
  ProbabilityTheory.ae_mem_regularitySetRight
    (ae_mem_all_regularitySet_union_nhdsGT_eq_bot hX hT) hTcof
end RealRegularity
section RegularityTimes
/-- A countable dense set of times which contains all the times that are isolated on the right
(the maximal element and the times which have a successor, if any). The modifications of a
quasimartingale are defined from the limits of the process along this set.

At a time `t` isolated on the right, the modification is `X t`: we need those times in the set
to ensure that the paths of the process restricted to the set, which have one-sided limits almost
surely, control these values. If `ι` is densely ordered without maximal element, this set is
`denseCountable ι`. -/
def regularityTimes (ι : Type*) [Preorder ι] [TopologicalSpace ι] [SecondCountableTopology ι] :
    Set ι :=
  denseCountable ι ∪ {t | 𝓝[>] t = ⊥}
omit [OrderTopology ι] in
lemma mem_regularityTimes_of_nhdsGT_eq_bot [SecondCountableTopology ι] {t : ι}
    (ht : 𝓝[>] t = ⊥) :
    t ∈ regularityTimes ι := .inr ht
omit [OrderTopology ι] in
lemma dense_regularityTimes [SecondCountableTopology ι] : Dense (regularityTimes ι) :=
  dense_denseCountable.mono Set.subset_union_left
lemma countable_regularityTimes [SecondCountableTopology ι] : (regularityTimes ι).Countable :=
  countable_denseCountable.union countable_setOfPred_isolated_right
end RegularityTimes
section Measurability
variable {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E} {T : Set ι}
/-- For a right-continuous filtration and a time `t` that is not isolated on the right, a function
that is `𝓕 s`-strongly measurable for every `s > t` is `𝓕 t`-strongly measurable. -/
lemma stronglyMeasurable_of_forall_gt [𝓕.IsRightContinuous] {t : ι} [(𝓝[>] t).NeBot]
    {f : Ω → E} (h : ∀ s, t < s → StronglyMeasurable[𝓕 s] f) :
    StronglyMeasurable[𝓕 t] f := by
  borelize E
  obtain ⟨s, hs⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  refine stronglyMeasurable_iff_measurable_separable.2
    ⟨fun B hB ↦ ?_, (h s hs).isSeparable_range⟩
  exact measurableSet_of_forall_gt fun s hs ↦ (h s hs).measurable hB
/-- The right limit of a process along `T` at time `t`, restricted to a measurable set on which
that limit exists, is strongly measurable with respect to a sigma-algebra `m` as soon as the process
is `m`-strongly measurable at all times of a right neighborhood of `t` in `T`. -/
lemma stronglyMeasurable_indicator_rightLimWithin [FirstCountableTopology ι]
    {m : MeasurableSpace Ω} {G : Set Ω} (hG : MeasurableSet[m] G) {t : ι} {S : Set ι}
    (hS : S ∈ 𝓝[T ∩ Set.Ioi t] t) (hXS : ∀ s ∈ S, StronglyMeasurable[m] (X s))
    (hXt : StronglyMeasurable[m] (X t))
    (hlim : ∀ ω ∈ G, ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) :
    StronglyMeasurable[m] (G.indicator fun ω ↦ rightLimWithin (X · ω) T t) := by
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hbot | hne
  · -- if the right neighbourhood filter is trivial, the right limit is `X t`
    have heq : (fun ω ↦ rightLimWithin (X · ω) T t) = X t := by
      ext ω
      exact rightLimWithin_eq_of_eq_bot _ (by rwa [Set.inter_comm])
    rw [heq]
    exact hXt.indicator hG
  -- otherwise, the right limit is the limit along a sequence of times in `S`
  obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi t] t)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv.eventually hS)
  have hv' : Tendsto (fun n ↦ v (n + N)) atTop (𝓝[T ∩ Set.Ioi t] t) :=
    (tendsto_add_atTop_iff_nat N).2 hv
  refine stronglyMeasurable_of_tendsto atTop
    (fun n ↦ (hXS (v (n + N)) (hN _ (by lia))).indicator hG) (tendsto_pi_nhds.2 fun ω ↦ ?_)
  by_cases hω : ω ∈ G
  · simp only [Set.indicator_of_mem hω]
    have h := hlim ω hω
    rw [Set.inter_comm] at h
    have h' := tendsto_rightLimWithin_of_tendsto h
    rw [Set.inter_comm] at h'
    exact h'.comp hv'
  · simp only [Set.indicator_of_notMem hω]
    exact tendsto_const_nhds
end Measurability
section RightContModifOf
variable [SecondCountableTopology ι] {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E}
  {R : ι → Set Ω}
/-- The right-continuous modification of a process `X` with regularity family `R`, defined from
the right limits of `X` along the countable dense set `regularityTimes ι`. -/
noncomputable
def rightContModifOf (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) (ω : Ω) : E :=
  open Classical in
  if ω ∈ regularitySetRight (regularityTimes ι) R t
    then rightLimWithin (X · ω) (regularityTimes ι) t else 0
omit [OrderTopology ι] in
lemma rightContModifOf_eq_indicator (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) :
    rightContModifOf R X t = (regularitySetRight (regularityTimes ι) R t).indicator
      fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t := by
  ext ω
  simp [rightContModifOf, Set.indicator]
omit [OrderTopology ι] in
lemma rightContModifOf_eq_zero {x : ι} {ω : Ω}
    (hω : ω ∉ regularitySetRight (regularityTimes ι) R x) :
    (rightContModifOf R X · ω) =ᶠ[𝓝[>] x] 0 := by
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  have hy' : ω ∉ regularitySetRight (regularityTimes ι) R y :=
    fun hω' ↦ hω (regularitySetRight_anti (le_of_lt hy) hω')
  simp [rightContModifOf, hy']
section Pathwise
variable (hR : IsRegularityFamily (regularityTimes ι) X R)
include hR
lemma tendsto_rightContModifOf_rightLimWithin {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (regularityTimes ι) R x) :
    Tendsto (rightContModifOf R X · ω) (𝓝[>] x)
      (𝓝 (rightLimWithin (X · ω) (regularityTimes ι) x)) := by
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (regularityTimes ι))]
  swap
  · filter_upwards [eventually_mem_regularitySetRight_of_mem hω] with y hy
      using by simp [rightContModifOf, hy]
  suffices ContinuousWithinAt (rightLimWithin (X · ω) (regularityTimes ι)) (Set.Ici x) x by
    rwa [← continuousWithinAt_Ioi_iff_Ici] at this
  exact hR.continuousWithinAt_rightLimWithin dense_regularityTimes
    (fun _ ↦ mem_regularityTimes_of_nhdsGT_eq_bot) hω
lemma tendsto_rightContModifOf_leftLimWithin {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (regularityTimes ι) R x) :
    Tendsto (rightContModifOf R X · ω) (𝓝[<] x)
      (𝓝 (leftLimWithin (X · ω) (regularityTimes ι) x)) := by
  have h_mem y (hyx : y ≤ x) : ω ∈ regularitySetRight (regularityTimes ι) R y :=
    regularitySetRight_anti hyx hω
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (regularityTimes ι))]
  swap
  · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    simp [rightContModifOf, h_mem y (le_of_lt hy)]
  refine tendsto_rightLim_nhdsLT dense_regularityTimes
    (fun _ ↦ mem_regularityTimes_of_nhdsGT_eq_bot) ?_
    (fun y hy ↦ rightLimWithin_eq_of_nhdsGT_eq_bot _ _ hy) (hR.tendsto_nhdsLT_leftLimWithin hω)
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  exact hR.tendsto_nhdsGT_rightLimWithin (h_mem y (le_of_lt hy))
/-- The paths of `rightContModifOf R X` are right-continuous. -/
lemma continuousWithinAt_rightContModifOf (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModifOf R X · ω) (Set.Ioi x) x := by
  by_cases hω : ω ∈ regularitySetRight (regularityTimes ι) R x
  · have hYx : rightContModifOf R X x ω = rightLimWithin (X · ω) (regularityTimes ι) x := by
      simp only [rightContModifOf, if_pos hω]
    rw [ContinuousWithinAt, hYx]
    exact tendsto_rightContModifOf_rightLimWithin hR hω
  · refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (rightContModifOf_eq_zero hω) ?_
    · fun_prop
    · simp [rightContModifOf, hω]
lemma stronglyAdapted_rightContModifOf [𝓕.IsRightContinuous] (hX : StronglyAdapted 𝓕 X)
    (hRm : ∀ d, MeasurableSet[𝓕 d] (R d)) :
    StronglyAdapted 𝓕 (rightContModifOf R X) := by
  intro t
  have hG s (hts : t ≤ s) : MeasurableSet[𝓕 s] (regularitySetRight (regularityTimes ι) R t) :=
    𝓕.mono hts _ (measurableSet_regularitySetRight hR.anti hRm countable_regularityTimes
      dense_regularityTimes t)
  have hlim ω (hω : ω ∈ regularitySetRight (regularityTimes ι) R t) :
      ∃ l, Tendsto (X · ω) (𝓝[regularityTimes ι ∩ Set.Ioi t] t) (𝓝 l) :=
    hR.right_limit_of_mem_regularitySetRight hω le_rfl
  rw [rightContModifOf_eq_indicator]
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · -- if `t` is isolated on the right, the right limit is `X t`
    refine stronglyMeasurable_indicator_rightLimWithin (S := ∅) (hG t le_rfl) ?_ (by simp)
      (hX t) hlim
    simp [eq_bot_mono (nhdsWithin_mono _ Set.inter_subset_right) ht]
  -- otherwise, it suffices to show `𝓕 s`-measurability for every `s > t`
  refine stronglyMeasurable_of_forall_gt fun s hts ↦ ?_
  refine stronglyMeasurable_indicator_rightLimWithin (S := Set.Iio s) (hG s hts.le) ?_
    (fun u hu ↦ (hX u).mono (𝓕.mono (le_of_lt hu))) ((hX t).mono (𝓕.mono hts.le)) hlim
  exact nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hts)
end Pathwise
section AlmostSure
variable (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t)
include hRae
omit [OrderTopology ι] in
lemma rightContModifOf_ae_eq_of_rightLimWithin_ae_eq {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (regularityTimes ι) t) =ᵐ[μ] X t) :
    rightContModifOf R X t =ᵐ[μ] X t := by
  filter_upwards [hRae, ht] with ω hω hωR
  simpa only [rightContModifOf, if_pos (hω _)]
/-- At a time `t` which is isolated on the right, `rightContModifOf R X t` is a.e. equal to
`X t`. -/
lemma rightContModifOf_ae_eq_of_nhdsGT_eq_bot {t : ι} (ht : 𝓝[>] t = ⊥) :
    rightContModifOf R X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_rightLimWithin_ae_eq hRae
    (ae_of_all _ fun _ ↦ rightLimWithin_eq_of_nhdsGT_eq_bot _ _ ht)
/-- If `t` is not isolated on the right, there is a sequence of times `w n ∈ (t, u]` tending to `t`
along which `X` converges almost surely to `rightContModifOf R X t`. -/
lemma exists_seq_tendsto_rightContModifOf (hR : IsRegularityFamily (regularityTimes ι) X R)
    {t u : ι} [(𝓝[>] t).NeBot] (htu : t < u) :
    ∃ w : ℕ → ι, (∀ n, t < w n) ∧ (∀ n, w n ≤ u) ∧ Tendsto w atTop (𝓝[>] t) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (w n) ω) atTop (𝓝 (rightContModifOf R X t ω)) := by
  let T := regularityTimes ι
  have hTd : Dense T := dense_regularityTimes
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot := nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot hTd t
  obtain ⟨w₀, hw₀⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  have h_ev : ∀ᶠ n in atTop, w₀ n ≤ u ∧ w₀ n ∈ Set.Ioi t ∩ T := by
    rw [tendsto_nhdsWithin_iff] at hw₀
    filter_upwards [hw₀.1.eventually (eventually_lt_nhds htu), hw₀.2] with n hn1 hn2
      using ⟨hn1.le, hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 h_ev
  have hw : Tendsto (fun n ↦ w₀ (n + N)) atTop (𝓝[T ∩ Set.Ioi t] t) := by
    rw [Set.inter_comm]
    exact (tendsto_add_atTop_iff_nat N).2 hw₀
  refine ⟨fun n ↦ w₀ (n + N), fun n ↦ (hN (n + N) (by lia)).2.1, fun n ↦ (hN (n + N) (by lia)).1,
    hw.mono_right (nhdsWithin_mono _ Set.inter_subset_right), ?_⟩
  filter_upwards [hRae] with ω hω
  have hYω : rightContModifOf R X t ω = rightLimWithin (X · ω) T t := by
    simp only [rightContModifOf, T, if_pos (hω t)]
  rw [hYω]
  exact (hR.tendsto_nhdsGT_rightLimWithin (hω t)).comp hw
/-- At a time `t` at which `X` is right-continuous in probability, `rightContModifOf R X t` is a.e.
equal to `X t`. -/
lemma rightContModifOf_ae_eq_of_tendstoInMeasure [IsFiniteMeasure μ]
    (hR : IsRegularityFamily (regularityTimes ι) X R) (hX : StronglyAdapted 𝓕 X) (t : ι)
    (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModifOf R X t =ᵐ[μ] X t := by
  -- if `t` is isolated on the right, the right limit is `X t`
  rcases (𝓝[>] t).eq_or_neBot with ht | ht
  · exact rightContModifOf_ae_eq_of_nhdsGT_eq_bot hRae ht
  -- a sequence `w n > t` which tends to `t`, with `X (w n) → rightContModifOf R X t` a.e.
  obtain ⟨u, htu⟩ := not_isMax_iff.1 (not_isMax_of_nhdsGT_neBot (a := t))
  obtain ⟨w, -, -, hw, h_tendsto⟩ := exists_seq_tendsto_rightContModifOf hRae hR htu
  refine tendstoInMeasure_ae_unique ?_ (hXRC.comp hw)
  exact tendstoInMeasure_of_tendsto_ae
    (fun n ↦ ((hX (w n)).mono (𝓕.le _)).aestronglyMeasurable) h_tendsto
end AlmostSure
end RightContModifOf
section CadlagModifOf
variable [SecondCountableTopology ι] {E : Type*} [NormedAddCommGroup E] {X : ι → Ω → E}
  {R : ι → Set Ω}
/-- The càdlàg modification of a process `X` with regularity family `R`, defined from the right
limits of `X` along the countable dense set `regularityTimes ι`. -/
noncomputable
def cadlagModifOf (R : ι → Set Ω) (X : ι → Ω → E) (t : ι) (ω : Ω) : E :=
  open Classical in
  if ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t then rightContModifOf R X t ω else 0
omit [OrderTopology ι] in
lemma cadlagModifOf_ae_eq_rightContModifOf
    (hRae : ∀ᵐ ω ∂μ, ∀ t, ω ∈ regularitySetRight (regularityTimes ι) R t) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModifOf R X t ω = rightContModifOf R X t ω := by
  filter_upwards [hRae] with ω hω
  simp [cadlagModifOf, if_pos hω]
variable (hR : IsRegularityFamily (regularityTimes ι) X R)
include hR
lemma continuousWithinAt_cadlagModifOf (x : ι) (ω : Ω) :
    ContinuousWithinAt (cadlagModifOf R X · ω) (Set.Ioi x) x := by
  unfold cadlagModifOf
  split_ifs with hω
  · exact continuousWithinAt_rightContModifOf hR x ω
  · fun_prop
lemma exists_tendsto_nhdsLT_cadlagModifOf (x : ι) (ω : Ω) :
    ∃ l, Tendsto (cadlagModifOf R X · ω) (𝓝[<] x) (𝓝 l) := by
  unfold cadlagModifOf
  split_ifs with hω
  · exact ⟨leftLimWithin (X · ω) (regularityTimes ι) x,
      tendsto_rightContModifOf_leftLimWithin hR (hω x)⟩
  · exact ⟨0, tendsto_const_nhds⟩
/-- The paths of `cadlagModifOf R X` are càdlàg. -/
theorem isCadlag_cadlagModifOf (ω : Ω) : IsCadlag (cadlagModifOf R X · ω) :=
  ⟨fun x ↦ continuousWithinAt_cadlagModifOf hR x ω,
    fun x ↦ exists_tendsto_nhdsLT_cadlagModifOf hR x ω⟩
end CadlagModifOf
section RightContModif
variable [SecondCountableTopology ι] {X : ι → Ω → ℝ}
/-- The right-continuous modification of a real quasimartingale, defined from the right limits
along the countable dense set `regularityTimes ι`. -/
noncomputable
def rightContModifReal (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  rightContModifOf (regularitySet (regularityTimes ι) X) X
variable [OrderBot ι]
lemma stronglyAdapted_rightContModifReal [𝓕.IsRightContinuous] (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (rightContModifReal X) :=
  stronglyAdapted_rightContModifOf isRegularityFamily_regularitySet hX.stronglyAdapted
    (measurableSet_regularitySet hX countable_regularityTimes)
lemma adapted_rightContModifReal [𝓕.IsRightContinuous] (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (rightContModifReal X) :=
  fun t ↦ (stronglyAdapted_rightContModifReal hX t).measurable
variable [IsFiniteMeasure μ]
/-- Almost surely, `ω` belongs to all the events used to define the modifications of a real
quasimartingale. -/
lemma IsRealQuasimartingale.ae_mem_regularitySetRight_regularityTimes
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t,
      ω ∈ regularitySetRight (regularityTimes ι) (regularitySet (regularityTimes ι) X) t :=
  hX.ae_mem_regularitySetRight countable_regularityTimes
    fun _ ↦ dense_regularityTimes.exists_gt_of_not_isMax
lemma rightContModifReal_ae_eq_of_tendstoInMeasure (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModifReal X t =ᵐ[μ] X t :=
  rightContModifOf_ae_eq_of_tendstoInMeasure hX.ae_mem_regularitySetRight_regularityTimes
    isRegularityFamily_regularitySet hX.stronglyAdapted t hXRC
end RightContModif
section CadlagModif
variable [SecondCountableTopology ι] {X : ι → Ω → ℝ}
/-- The càdlàg modification of a real quasimartingale, defined from the right limits
along the countable dense set `regularityTimes ι`. -/
noncomputable
def cadlagModifReal (X : ι → Ω → ℝ) : ι → Ω → ℝ :=
  cadlagModifOf (regularitySet (regularityTimes ι) X) X
theorem isCadlag_cadlagModifReal (ω : Ω) : IsCadlag (cadlagModifReal X · ω) :=
  isCadlag_cadlagModifOf isRegularityFamily_regularitySet ω
variable [OrderBot ι]
variable [IsFiniteMeasure μ]
lemma cadlagModifReal_ae_eq_rightContModifReal (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModifReal X t ω = rightContModifReal X t ω :=
  cadlagModifOf_ae_eq_rightContModifOf hX.ae_mem_regularitySetRight_regularityTimes
end CadlagModif
end ProbabilityTheory


