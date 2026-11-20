-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:14:56.984933+00:00
-- url     : https://prove2.me/theorems/5f9ad887-1c5d-44b8-92d0-587a6b6e5a6a
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F000
import Definitions.Def_SourceProof_17683012ceda8988fdc379c5
import Definitions.Def_SourceProof_2a8aafc9167b053f609af742
import Definitions.Def_SourceProof_c03a31f539676260fe3238a1
import Definitions.Def_SourceProof_c62814fa18df3f1630c0e9da
import Definitions.Def_SourceProof_ceeeabf2e648d9a4d6fbcd82
import Definitions.Def_SourceProof_fe999cb8170900d5fe5aa7da

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

/-- An elementary predictable set representing upcrossings within a given interval. -/
noncomputable
def upcrossingWithinPredSet [OrderBot ι] (a b : ℝ) (F : Finset ι) (hF : ∀ s ∈ F, s ≤ t)
    (hX : StronglyAdapted 𝓕 X) :
    ElementaryPredictableSet 𝓕 :=
  letI f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  haveI hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F
    fun k _ ↦ (hadapt.upcrossingStrat k).measurable
lemma mul_upcrossingsBefore_le_integral_add_posPart [OrderBot ι]
    (hX : StronglyAdapted 𝓕 X) (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) (ω : Ω) :
    letI f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
    haveI hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
      fun j ↦ hX (finIdx F t j)
    letI S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k _ ↦
      (hadapt.upcrossingStrat k).measurable
    (b - a) * (upcrossingsBefore a b f #F ω : ℝ)
      ≤ (S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺ := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    fun j ↦ hX (finIdx F t j)
  let S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k hk ↦
    (hadapt.upcrossingStrat k).measurable
  rw [_root_.Prove2MeSourceProof.h_c62814fa18df3f1630c0e9da (𝓕 := 𝓕) (X := X) #F (finIdx_monotone hF) (finIdx_le hF)
    (W := upcrossingStrat a b f #F) (fun k _ ω ↦ _root_.Prove2MeSourceProof.h_c03a31f539676260fe3238a1 a b f #F k ω)
    (fun k _ ↦ (hadapt.upcrossingStrat k).measurable) ω]
  have h1 := _root_.Prove2MeSourceProof.h_ceeeabf2e648d9a4d6fbcd82 (f := f) (N := #F) (ω := ω) hab
  have hfn : f #F ω = X t ω := by unfold f; rw [finIdx_eq_of_card_le le_rfl]
  rwa [hfn] at h1
/-- Expectation bound on the number of upcrossings along a finite set of times `F ⊆ Iic t`,
from the boundedness of elementary stochastic integrals at time `t`. -/
lemma mul_integral_upcrossingsBefore_finIdx_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : Adapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator 1 ● X) t] ≤ C)
    (hab : a < b) (hF : ∀ s ∈ F, s ≤ t) :
    (b - a) * ∫ ω, (upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω : ℝ) ∂μ
      ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    Adapted.stronglyAdapted <| fun j ↦ hX (finIdx F t j)
  let S := elemPredSetOfSeq (W := upcrossingStrat a b f #F) (finIdx_monotone hF) #F fun k hk ↦
    (hadapt.upcrossingStrat k).measurable
  have hintS : Integrable ((S.indicator (1 : ℝ) ● X) t) μ :=
    _root_.Prove2MeSourceProof.h_2a8aafc9167b053f609af742 hXint S 1 t
  have hintmax : Integrable (fun ω ↦ (a - X t ω)⁺) μ :=
    (((integrable_const a).sub (hXint t))).pos_part
  have hintcount : Integrable (fun ω ↦ (upcrossingsBefore a b f #F ω : ℝ)) μ :=
    hadapt.integrable_upcrossingsBefore hab
  calc (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ
  _ = ∫ ω, (b - a) * (upcrossingsBefore a b f #F ω : ℝ) ∂μ := (integral_const_mul _ _).symm
  _ ≤ ∫ ω, ((S.indicator (1 : ℝ) ● X) t ω + (a - X t ω)⁺) ∂μ :=
    integral_mono (hintcount.const_mul _) (hintS.add hintmax)
      (mul_upcrossingsBefore_le_integral_add_posPart hX.stronglyAdapted hab hF)
  _ = μ[(S.indicator (1 : ℝ) ● X) t] + ∫ ω, (a - X t ω)⁺ ∂μ := integral_add hintS hintmax
  _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ := by gcongr; exact hC S
variable (X) in
/-- The event that `X` makes `m` alternations from at most `a` to at least `b` at
increasing times inside the finite time set `F`. The levels are non-strict (`X ≤ a`, `b ≤ X`) to
match the `Set.Iic a` / `Set.Ici b` hitting conditions of `MeasureTheory.upcrossingsBefore`; with
this convention `altSet` coincides with the event of at least `m` upcrossings (see
`altSet_eq_upcrossingsBefore`). -/
def altSet (F : Finset ι) (a b : ℝ) (m : ℕ) : Set Ω :=
  {ω | ∃ c : ℕ → ι, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i ∈ F)
    ∧ (∀ i < m, X (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ X (c (2 * i + 1)) ω)}
lemma altSet_mono {F G : Finset ι} (h : F ⊆ G) : altSet X F a b m ⊆ altSet X G a b m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, fun i hi ↦ h (hc2 i hi), hca, hcb⟩
lemma altSet_mono' {a' b' : ℝ} (hab : a ≤ a') (hba : b' ≤ b) :
    altSet X F a b m ⊆ altSet X F a' b' m :=
  fun _ ⟨c, hc1, hc2, hca, hcb⟩ ↦ ⟨c, hc1, hc2, by grind⟩
/-- `altSet X F a b m` is exactly the event of at least `m` upcrossings of `[a, b]` by the
monotone enumeration `finIdx F t` of `F`. -/
lemma altSet_eq_upcrossingsBefore (hab : a < b) :
    altSet X F a b m = {ω | m ≤ upcrossingsBefore a b (fun k ↦ X (finIdx F t k)) #F ω} := by
  refine subset_antisymm ?_ ?_
  · rintro ω ⟨c, hc1, hc2, hca, hcb⟩
    have hex : ∀ i, i < 2 * m → ∃ k, k < #F ∧ finIdx F t k = c i :=
      fun i hi ↦ exists_finIdx_eq (hc2 i hi)
    let c' : ℕ → ℕ := fun i ↦ if hi : i < 2 * m then (hex i hi).choose else 0
    have hc'spec : ∀ i (hi : i < 2 * m), c' i < #F ∧ finIdx F t (c' i) = c i := by grind
    refine _root_.Prove2MeSourceProof.h_fe999cb8170900d5fe5aa7da hab (c := c') ?_ (by grind) ?_ ?_
    · intro i hi
      obtain ⟨hlt1, heq1⟩ := hc'spec i (by lia)
      obtain ⟨hlt2, heq2⟩ := hc'spec (i + 1) hi
      rw [← finIdx_lt_finIdx_iff (t := t) hlt1 hlt2, heq1, heq2]
      exact hc1 i hi
    · intro i hi
      obtain ⟨_, heq⟩ := hc'spec (2 * i) (by lia)
      simp only [heq]
      exact hca i hi
    · intro i hi
      obtain ⟨_, heq⟩ := hc'spec (2 * i + 1) (by lia)
      simp only [heq]
      exact hcb i hi
  · intro ω hω
    obtain ⟨c, hmono, hcN, ha, hb⟩ := _root_.Prove2MeSourceProof.h_17683012ceda8988fdc379c5 hab hω
    exact ⟨fun i ↦ finIdx F t (c i), fun i hi ↦ finIdx_lt_of_lt (hmono i hi) (hcN (i + 1) hi),
      fun i hi ↦ finIdx_mem (hcN i hi), fun i hi ↦ ha i hi, fun i hi ↦ hb i hi⟩
/-- Quantitative alternation bound: the probability of `m` alternations along any finite
`F ⊆ Iic t` is at most `K / m` with `K` independent of `F` and `m`. -/
lemma measureReal_altSet_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : Adapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hab : a < b) (hm : 0 < m) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real (altSet X F a b m) ≤ (C + ∫ ω, (a - X t ω)⁺ ∂μ) / (b - a) / m := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ X (finIdx F t k) ω
  have hadapt : StronglyAdapted (𝓕.indexComap (finIdx_monotone hF)) f :=
    Adapted.stronglyAdapted <| fun j ↦ hX (finIdx F t j)
  rw [altSet_eq_upcrossingsBefore (t := t) hab, div_div, le_div_iff₀ (by positivity)]
  calc μ.real {ω | m ≤ upcrossingsBefore a b f #F ω} * ((b - a) * m)
  _ = μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)} * ((b - a) * m) := by norm_cast
  _ = (b - a) * ((m : ℝ) * μ.real {ω | (m : ℝ) ≤ (upcrossingsBefore a b f #F ω : ℝ)}) := by ring
  _ ≤ (b - a) * ∫ ω, (upcrossingsBefore a b f #F ω : ℝ) ∂μ := by
    gcongr
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω ↦ by positivity) (hadapt.integrable_upcrossingsBefore hab) m
  _ ≤ C + ∫ ω, (a - X t ω)⁺ ∂μ :=
    mul_integral_upcrossingsBefore_finIdx_le (μ := μ) hX hXint hC hab hF
/-- The set of outcomes where there are infinitely many alternations of `X` from below `a`
to above `b` at times in a set `T` below `t`. -/
def infiniteAlt (T : Set ι) (t : ι) (X : ι → Ω → ℝ) (a b : ℝ) : Set Ω :=
  ⋂ m : ℕ, ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, altSet X F a b m
lemma infiniteAlt_mono' {T : Set ι} {a' b' : ℝ} (h : a ≤ a') (h' : b' ≤ b) :
    infiniteAlt T t X a b ⊆ infiniteAlt T t X a' b' := by
  unfold infiniteAlt
  gcongr
  exact altSet_mono' h h'
lemma infiniteAlt_mono'' {T : Set ι} {s t : ι} (h : s ≤ t) :
    infiniteAlt T s X a b ⊆ infiniteAlt T t X a b := by
  unfold infiniteAlt
  gcongr with F
  refine Set.iUnion_mono' ?_
  intro hF
  simp only [Set.subset_inter_iff, Set.mem_setOf_eq] at hF
  simp only [subset_refl, Set.subset_inter_iff, Set.mem_setOf_eq, exists_prop, and_true]
  refine ⟨hF.1, hF.2.trans ?_⟩
  grind
end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

lemma Ioo_inter_mem_nhdsWithin_inter_Ioi (hxd : x < d) : Set.Ioo x d ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_lt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter
lemma Ioo_inter_mem_nhdsWithin_inter_Iio (hxd : d < x) : Set.Ioo d x ∩ T ∈ 𝓝[T ∩ Set.Iio x] x := by
  simp only [inter_mem_iff]
  constructor
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [eventually_gt_nhds hxd] with s hs
    grind
  · exact mem_nhdsWithin_self_inter
lemma exists_finset_altSet_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Ioo x d ∧ ω ∈ altSet X F a b m := by
  -- descending selection: even picks above `b`, odd picks below `a`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c (i + 1) < c i)
      ∧ (∀ i < k, c i ∈ T ∩ Set.Ioo x d)
      ∧ (∀ i < k, if Even i then b < X (c i) ω else X (c i) ω < a) := by
    induction k with
    | zero => exact ⟨fun _ ↦ d, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hdesc, hmem, hval⟩ := ih
      -- previous lower endpoint
      set u : ι := if hk : 0 < k then c (k - 1) else d with hu
      have hxu : x < u := by grind
      have hud : u ≤ d := by grind
      have hU : Set.Ioo x u ∩ T ∈ 𝓝[T ∩ Set.Ioi x] x := Ioo_inter_mem_nhdsWithin_inter_Ioi hxu
      have hpick : ∃ s, s ∈ Set.Ioo x u ∩ T
          ∧ if Even k then b < X s ω else X s ω < a := by
        by_cases hk : Even k
        · simp only [if_pos hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [if_neg hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      exact ⟨Function.update c k s, by grind⟩
  obtain ⟨c, hdesc, hmem, hval⟩ := hsel (2 * m)
  -- reverse the order
  set ca : ℕ → ι := fun j ↦ c (2 * m - 1 - j) with hca
  exact ⟨(range (2 * m)).image ca, by grind, ca, by grind⟩
lemma mem_infiniteAlt_of_frequently_right (hxd : x < d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Ioi x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_right hxd hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind
lemma exists_finset_altSet_of_frequently_left
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) (m : ℕ) :
    ∃ F : Finset ι, ↑F ⊆ T ∩ Set.Iio x ∧ ω ∈ altSet X F a b m := by
  -- ascending selection: even picks below `a`, odd picks above `b`
  have hsel k : ∃ c : ℕ → ι, (∀ i, i + 1 < k → c i < c (i + 1))
      ∧ (∀ i < k, c i ∈ T ∩ Set.Iio x)
      ∧ (∀ i < k, if Even i then X (c i) ω < a else b < X (c i) ω) := by
    induction k with
    | zero => exact ⟨fun _ ↦ x, by lia, by lia, by lia⟩
    | succ k ih =>
      obtain ⟨c, hasc, hmem, hval⟩ := ih
      have hU : (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∈ 𝓝[T ∩ Set.Iio x] x := by
        split_ifs with hk
        · exact Ioo_inter_mem_nhdsWithin_inter_Iio (hmem (k - 1) (by lia)).2
        · rw [Set.inter_comm]
          exact self_mem_nhdsWithin
      have hpick : ∃ s, s ∈ (if 0 < k then Set.Ioo (c (k - 1)) x else Set.Iio x) ∩ T
          ∧ if Even k then X s ω < a else b < X s ω := by
        by_cases hk : Even k
        · simp only [if_pos hk]
          obtain ⟨s, hs1, hs2⟩ := (hfa.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
        · simp only [if_neg hk]
          obtain ⟨s, hs1, hs2⟩ := (hfb.and_eventually (Filter.eventually_of_mem hU
            (fun s hs ↦ hs))).exists
          exact ⟨s, hs2, hs1⟩
      obtain ⟨s, ⟨hsIoo, hsT⟩, hsval⟩ := hpick
      have hsx : s < x := by grind
      refine ⟨Function.update c k s, ?_, by grind⟩
      intro i hi
      rcases Nat.lt_or_ge (i + 1) k with h | h
      · grind
      · have hik : i + 1 = k := by lia
        rw [hik, Function.update_self, Function.update_of_ne (by lia)]
        have hci : c i = c (k - 1) := by congr 1; lia
        grind
  obtain ⟨c, hasc, hmem, hval⟩ := hsel (2 * m)
  exact ⟨(range (2 * m)).image c, by grind, c, hasc, by grind⟩
lemma mem_infiniteAlt_of_frequently_left (hxd : x ≤ d)
    (hfa : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, X s ω < a)
    (hfb : ∃ᶠ s in 𝓝[T ∩ Set.Iio x] x, b < X s ω) :
    ω ∈ infiniteAlt T d X a b := by
  simp only [infiniteAlt, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro m
  obtain ⟨F, hFmem, hFalt⟩ := exists_finset_altSet_of_frequently_left hfa hfb m
  refine ⟨F, ?_, hFalt⟩
  simp only [Set.subset_inter_iff] at hFmem ⊢
  refine ⟨hFmem.1, hFmem.2.trans ?_⟩
  grind
end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name
lemma sum_indicator_mul_sub_eq_stopped'' (f : ℕ → Ω → ℝ) (s : Set ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ∉ s}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f s 0 n ω) ω - f 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases hhit : ∃ j ∈ Set.Icc 0 n, f j ω ∈ s
    · -- already hit by time `n`: the hitting time stabilizes and the last weight vanishes
      have hstab : hittingBtwn f s 0 n ω = hittingBtwn f s 0 (n + 1) ω :=
        hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ n) hhit
      obtain ⟨j, hj, hjs⟩ := hhit
      rw [Set.indicator_of_notMem]
      · grind
      · simp only [Set.mem_setOf_eq, not_forall, not_not]
        exact ⟨j, hj.2, hjs⟩
    · rw [hittingBtwn, if_neg hhit]
      have h2 : hittingBtwn f s 0 (n + 1) ω = n + 1 := by
        refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
        obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff (n + 1) le_rfl).1 hlt
        grind
      rw [h2, Set.indicator_of_mem (by simpa using hhit)]
      simp
/-- Discrete stopped telescoping identity: weighting the increments of `f` by the indicator of
"not yet above `lam`" telescopes to the value at the first time `f` exceeds `lam`. -/
lemma sum_indicator_mul_sub_eq_stopped (f : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω * (f (k + 1) ω - f k ω)
      = f (hittingBtwn f (Set.Ioi lam) 0 n ω) ω - f 0 ω := by
  convert sum_indicator_mul_sub_eq_stopped'' f (Set.Ioi lam) n ω
  simp
omit [LinearOrder ι] in
/-- Integrability of bounded-weight increment sums. -/
lemma integrable_sum_weight_increments {g : ι → Ω → ℝ} (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} {W : ℕ → Ω → ℝ}
    (hWmeas : ∀ k, k < n → AEStronglyMeasurable (W k) μ)
    (hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1) :
    Integrable (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
  integrable_finsetSum _ fun k hk ↦ Integrable.bdd_mul ((hgint _).sub (hgint _))
    (hWmeas k (mem_range.1 hk)) (ae_of_all _ (hWb k (mem_range.1 hk)))
end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


