-- Prove2me | Definitions.Def_Q238L000
-- name    : Q238L000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:40.325468+00:00
-- url     : https://prove2.me/theorems/6b74a4df-6490-4076-b6b1-919d16e7461b
-- title:
--   Definitions bundle Q238L000 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 34 definitions, 4 inductive types or structures and 36 theorems. The definitions and types are `OAI.BlueSubsetDP.Partition`, `OAI.BlueSubsetDP.Plan`, `OAI.BlueSubsetDP.Plan.reweight`, `OAI.BlueSubsetDP.best`, `OAI.BlueSubsetDP.blockCost`, `OAI.BlueSubsetDP.blocks`, `OAI.BlueSubsetDP.computedPlan`, `OAI.BlueSubsetDP.value`, `OAI.MetricKMedianRecovery.Anchoring.badCenters`, `OAI.MetricKMedianRecovery.Anchoring.ballFacilities`, `OAI.MetricKMedianRecovery.Anchoring.cluster`, `OAI.MetricKMedianRecovery.Anchoring.clusterScale`, `OAI.MetricKMedianRecovery.Anchoring.clusterWeight`, `OAI.MetricKMedianRecovery.Anchoring.countConstant`, `OAI.MetricKMedianRecovery.Anchoring.neighbor`, `OAI.MetricKMedianRecovery.Anchoring.rounds`, `OAI.MetricKMedianRecovery.Anchoring.separation`, `OAI.MetricKMedianRecovery.Anchoring.shortCenters`, `OAI.MetricKMedianRecovery.Anchoring.threshold`, `OAI.MetricKMedianRecovery.AtomicStep`, `OAI.MetricKMedianRecovery.BirdInteger.determinant`, `OAI.MetricKMedianRecovery.BirdInteger.freeze`, `OAI.MetricKMedianRecovery.BirdInteger.iterate`, `OAI.MetricKMedianRecovery.BitMachine.extractPrefix`, `OAI.MetricKMedianRecovery.ExecutionState`, `OAI.MetricKMedianRecovery.LocalSearch.connection`, `OAI.MetricKMedianRecovery.LocalSearch.nearest`, `OAI.MetricKMedianRecovery.activeAt`, `OAI.MetricKMedianRecovery.admissibleBids`, `OAI.MetricKMedianRecovery.bidRow`, `OAI.MetricKMedianRecovery.clippedAt`, `OAI.MetricKMedianRecovery.etaOpenable`, `OAI.MetricKMedianRecovery.freeUpdate`, `OAI.MetricKMedianRecovery.nearestDistance`, `OAI.MetricKMedianRecovery.openingDual`, `OAI.MetricKMedianRecovery.openingPayment`, `OAI.MetricKMedianRecovery.phaseUpdate`, `OAI.MetricKMedianRecovery.regularUpdate`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Branching_BranchObjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean), [`KMedianRecovery_Geometry_NearestDistance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/NearestDistance.lean), [`KMedianRecovery_Recovery_BestDesignation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BestDesignation.lean), [`KMedianRecovery_Recovery_Blocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Blocks.lean), [`KMedianRecovery_Recovery_Chosen`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Chosen.lean), [`KMedianRecovery_Recovery_ClassSlotsMem`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ClassSlotsMem.lean), [`KMedianRecovery_Recovery_ExecutionState`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ExecutionState.lean), [`KMedianRecovery_Recovery_Freeze`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Freeze.lean), [`KMedianRecovery_Recovery_Threshold`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Threshold.lean), [`KMedianRecovery_Recovery_ThresholdTimesPower`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ThresholdTimesPower.lean), [`KMedianRecovery_Recovery_TotalAssignmentExcess`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean), [`KMedianRecovery_Sampling_ExtractPrefix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/ExtractPrefix.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `Q238L006`, `Q238L007`, `Q238L008`, `Q238L009`, `Q238L010`, `Q238L011` and `Q238L012`; the proof of `OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def nearestDistance {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) : ℝ :=
  if h : S.Nonempty then S.inf' h (dist x) else 0

def activeAt {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t z : ℝ) (Q : Finset X) (j : D) : Prop :=
  ∀ f ∈ Q, z < t * dist (loc j) f

noncomputable def clippedAt {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t z : ℝ) (Q : Finset X) (j : D) : ℝ :=
  if Q.Nonempty then min z (t * nearestDistance (loc j) Q) else z

noncomputable def bidRow {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) : ℝ :=
  ∑ j, max (clippedAt loc t z Q j - dist i (loc j)) 0

def admissibleBids {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t K v z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) : Prop :=
  ∀ j, activeAt loc t z Q j →
    z ≤ tau j ∧ tau j ≤ K * z ∧ (∀ f ∈ Q, tau j ≤ t * dist (loc j) f) ∧
      (v * z < dist i (loc j) → tau j = z)

noncomputable def openingPayment {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) : ℝ := by
  classical
  exact ∑ j, max ((if activeAt loc t z Q j then tau j
    else t * nearestDistance (loc j) Q) - t * dist i (loc j)) 0

noncomputable def openingDual {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i₀ : X) (tau : D → ℝ) (a : D) : ℝ := by
  classical
  exact ∑ j, if activeAt loc t z Q j then max (tau j - dist i₀ (loc j)) 0
    else max (tau a - 2 * dist i₀ (loc j) - dist i₀ (loc a)) 0

def etaOpenable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ) (i : X) : Prop :=
  ∃ tau : D → ℝ, admissibleBids loc t K v z Q i tau ∧
    lam - (Fintype.card D : ℝ) * eta ≤ openingPayment loc t z Q i tau ∧
    ∀ i₀ ∈ F, ∀ a, activeAt loc t z Q a → openingDual loc t z Q i₀ tau a ≤ lam

lemma nearestDistance_attained {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) (hS : S.Nonempty) :
    ∃ f ∈ S, nearestDistance x S = dist x f := by
  classical
  simpa [nearestDistance, hS] using Finset.exists_mem_eq_inf' hS (dist x)

lemma nearestDistance_le_mem {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) (f : X) (hf : f ∈ S) : nearestDistance x S ≤ dist x f := by
  classical
  have hS : S.Nonempty := ⟨f, hf⟩
  rw [nearestDistance, dite_eq_left hS]
  exact Finset.inf'_le (dist x) hf

lemma nearestDistance_antitone {X : Type*} [PseudoMetricSpace X]
    (x : X) (S W : Finset X) (hS : S.Nonempty) (hSW : S ⊆ W) :
    nearestDistance x W ≤ nearestDistance x S := by
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained x S hS
  rw [heq]
  exact nearestDistance_le_mem x W f (hSW hf)

lemma activeAt_iff {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (hQ : Q.Nonempty) :
    activeAt loc t z Q j ↔ z < t * nearestDistance (loc j) Q := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) Q hQ
    rw [heq]
    exact h f hf
  · intro h f hf
    exact h.trans_le (mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hf) ht)

lemma inactive_nonempty {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (h : ¬activeAt loc t z Q j) : Q.Nonempty := by
  by_contra hQ
  apply h
  intro f hf
  exact (hQ ⟨f, hf⟩).elim

lemma clippedAt_of_active {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (h : activeAt loc t z Q j) : clippedAt loc t z Q j = z := by
  classical
  unfold clippedAt
  split_ifs with hQ
  · exact min_eq_left ((activeAt_iff loc t z Q j ht hQ).mp h).le
  · rfl

lemma clippedAt_of_inactive {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (h : ¬activeAt loc t z Q j) :
    clippedAt loc t z Q j = t * nearestDistance (loc j) Q := by
  classical
  have hQ := inactive_nonempty loc t z Q j h
  have hc : t * nearestDistance (loc j) Q ≤ z := by
    exact not_lt.mp (fun hh => h ((activeAt_iff loc t z Q j ht hQ).mpr hh))
  simp [clippedAt, hQ, min_eq_right hc]

lemma clippedAt_le_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) : clippedAt loc t z Q j ≤ z := by
  classical
  unfold clippedAt
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma clippedAt_le_connection {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) (f : X) (hf : f ∈ Q)
    (ht : 0 ≤ t) : clippedAt loc t z Q j ≤ t * dist (loc j) f := by
  classical
  have hQ : Q.Nonempty := ⟨f, hf⟩
  calc
    _ = min z (t * nearestDistance (loc j) Q) := by simp only [clippedAt, hQ, ↓reduceIte]
    _ ≤ t * nearestDistance (loc j) Q := min_le_right _ _
    _ ≤ t * dist (loc j) f := mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hf) ht

lemma clippedAt_mono_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (j : D) :
    Monotone (fun z => clippedAt loc t z Q j) := by
  classical
  intro z w hzw
  unfold clippedAt
  split_ifs
  · exact min_le_min hzw le_rfl
  · exact hzw

lemma clippedAt_antitone_open {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (j : D) (ht : 0 ≤ t) (hQW : Q ⊆ W) :
    clippedAt loc t z W j ≤ clippedAt loc t z Q j := by
  classical
  by_cases hQ : Q.Nonempty
  · have hW : W.Nonempty := hQ.mono hQW
    simp only [clippedAt, hQ, hW, ↓reduceIte]
    exact min_le_min le_rfl (mul_le_mul_of_nonneg_left (nearestDistance_antitone _ _ _ hQ hQW) ht)
  · simpa [clippedAt, hQ] using clippedAt_le_phase loc t z W j

lemma bidRow_antitone_open {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (i : X) (ht : 0 ≤ t) (hQW : Q ⊆ W) :
    bidRow loc t z W i ≤ bidRow loc t z Q i := by
  apply Finset.sum_le_sum
  intro j _
  exact max_le_max (sub_le_sub_right (clippedAt_antitone_open loc t z Q W j ht hQW) _) le_rfl

lemma continuous_clippedAt {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (j : D) :
    Continuous (fun z => clippedAt loc t z Q j) := by
  classical
  unfold clippedAt
  split_ifs
  · exact continuous_id.min continuous_const
  · exact continuous_id

lemma continuous_bidRow {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (i : X) :
    Continuous (fun z => bidRow loc t z Q i) := by
  apply continuous_finsetSum
  intro j _
  exact ((continuous_clippedAt loc t Q j).sub continuous_const).max continuous_const

lemma bidRow_eq_zero_of_open {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (hi : i ∈ Q)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : bidRow loc t z Q i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have h := clippedAt_le_connection loc t z Q j i hi ht
  have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := loc j) (y := i))
  rw [dist_comm (loc j) i] at h hd
  apply max_eq_right
  nlinarith only [h, hd]

lemma inactive_at_later_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z y : ℝ) (Q : Finset X) (j : D)
    (hzy : z ≤ y) (h : ¬activeAt loc t z Q j) : ¬activeAt loc t y Q j := by
  intro hy
  apply h
  intro f hf
  exact lt_of_le_of_lt hzy (hy f hf)

lemma capped_triangle_row {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t u : ℝ) (Q : Finset X) (i : X) (a j : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hQ : Q.Nonempty)
    (hcap : ∀ f ∈ Q, u ≤ t * dist (loc a) f) :
    u - 2 * dist i (loc j) - dist i (loc a) ≤
      t * nearestDistance (loc j) Q - dist i (loc j) := by
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) Q hQ
  have htri : dist (loc a) f ≤ dist i (loc a) + dist i (loc j) + dist (loc j) f := by
    calc
      _ ≤ dist (loc a) i + dist i f := dist_triangle _ _ _
      _ ≤ dist (loc a) i + (dist i (loc j) + dist (loc j) f) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ = _ := by rw [dist_comm (loc a) i]; ring
  have hm := mul_le_mul_of_nonneg_left htri ht
  have hd := mul_le_mul_of_nonneg_right ht1
    (add_nonneg (dist_nonneg (x := i) (y := loc a)) (dist_nonneg (x := i) (y := loc j)))
  rw [heq]
  nlinarith only [hcap f hf, hm, hd]

theorem crossing_openable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (v z y lam : ℝ) (i : X)
    (hv : 0 < v) (hvsmall : v < 1 / 6) (hz : 0 < z)
    (hzy : z ≤ y) (hyK : y ≤ (1 + v ^ 2) * z)
    (heq : bidRow loc (1 - 3 * v) y Q i = lam)
    (hrows : ∀ i₀ ∈ F, bidRow loc (1 - 3 * v) y Q i₀ ≤ lam) :
    etaOpenable loc F Q (1 - 3 * v) (1 + v ^ 2) v z lam 0 i := by
  classical
  let t : ℝ := 1 - 3 * v
  let tau : D → ℝ := fun j => if dist i (loc j) ≤ v * z then clippedAt loc t y Q j else z
  have ht : 0 ≤ t := by dsimp [t]; linarith only [hvsmall]
  have ht1 : t ≤ 1 := by dsimp [t]; linarith only [hv]
  have hKz : z ≤ (1 + v ^ 2) * z := hzy.trans hyK
  have hactiveLow : ∀ j, activeAt loc t z Q j → z ≤ clippedAt loc t y Q j := by
    intro j hj
    have h := clippedAt_mono_phase loc t Q j hzy
    change clippedAt loc t z Q j ≤ clippedAt loc t y Q j at h
    rwa [clippedAt_of_active loc t z Q j ht hj] at h
  have hadm : admissibleBids loc t (1 + v ^ 2) v z Q i tau := by
    intro j hj
    constructor
    · dsimp [tau]
      split_ifs
      · exact hactiveLow j hj
      · exact le_rfl
    constructor
    · dsimp [tau]
      split_ifs
      · exact (clippedAt_le_phase loc t y Q j).trans hyK
      · exact hKz
    constructor
    · intro f hf
      dsimp [tau]
      split_ifs
      · exact clippedAt_le_connection loc t y Q j f hf ht
      · exact (hj f hf).le
    · intro hfar
      simp [tau, not_le.mpr hfar]
  have htau : ∀ j, activeAt loc t z Q j → tau j ≤ clippedAt loc t y Q j := by
    intro j hj
    dsimp [tau]
    split_ifs
    · exact le_rfl
    · exact hactiveLow j hj
  have hpay : bidRow loc t y Q i ≤ openingPayment loc t z Q i tau := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc t z Q j
    · simp only [hj, ↓reduceIte]
      apply max_le_max _ le_rfl
      dsimp [tau]
      split_ifs with hnear
      · have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := i) (y := loc j))
        nlinarith only [hd]
      · have hfar : v * z ≤ dist i (loc j) := le_of_lt (not_le.mp hnear)
        have hm := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 3 * v)
        have hvz : 0 ≤ v ^ 2 * z := mul_nonneg (sq_nonneg v) hz.le
        have hclip := (clippedAt_le_phase loc t y Q j).trans hyK
        dsimp [t]
        nlinarith only [hm, hvz, hclip]
    · simp only [hj, ↓reduceIte]
      rw [clippedAt_of_inactive loc t y Q j ht (inactive_at_later_phase loc t z y Q j hzy hj)]
      apply max_le_max _ le_rfl
      have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := i) (y := loc j))
      nlinarith only [hd]
  refine ⟨tau, hadm, ?_, ?_⟩
  · simpa [← heq, t] using hpay
  · intro i₀ hi₀ a ha
    change openingDual loc t z Q i₀ tau a ≤ lam
    have htarget : bidRow loc t y Q i₀ ≤ lam := hrows i₀ hi₀
    apply le_trans _ htarget
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc t z Q j
    · simp only [hj, ↓reduceIte]
      exact max_le_max (sub_le_sub_right (htau j hj) _) le_rfl
    · simp only [hj, ↓reduceIte]
      rw [clippedAt_of_inactive loc t y Q j ht (inactive_at_later_phase loc t z y Q j hzy hj)]
      exact max_le_max (capped_triangle_row loc t (tau a) Q i₀ a j ht ht1
        (inactive_nonempty loc t z Q j hj) (hadm a ha).2.2.1) le_rfl

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExecutionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

theorem phase_update_no_overbid
    {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1 / 6) (hz : 0 < z) (hlam : 0 < lam)
    (hpre : ∀ i ∈ F, bidRow loc (1 - 3 * v) z Q i ≤ lam)
    (hmaximal : ∀ i ∈ F, i ∉ Q →
      ¬etaOpenable loc F Q (1 - 3 * v) (1 + v ^ 2) v z lam 0 i) :
    ∀ i ∈ F, bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q i ≤ lam := by
  classical
  intro i hi
  by_contra hbad
  have hbad' : lam < bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q i := not_le.mp hbad
  have hF : F.Nonempty := ⟨i, hi⟩
  let M : ℝ → ℝ := fun y => F.sup' hF (fun j => bidRow loc (1 - 3 * v) y Q j)
  have hcont : Continuous M :=
    Continuous.finset_sup'_apply hF (fun j _ => continuous_bidRow loc (1 - 3 * v) Q j)
  have hMz : M z ≤ lam := Finset.sup'_le hF _ hpre
  have hMend : lam ≤ M ((1 + v ^ 2) * z) :=
    hbad'.le.trans (Finset.le_sup' (fun j => bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q j) hi)
  have hzK : z ≤ (1 + v ^ 2) * z := by
    nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  obtain ⟨y, hy, hMy⟩ := intermediate_value_Icc hzK hcont.continuousOn ⟨hMz, hMend⟩
  obtain ⟨j, hj, hjM⟩ := Finset.exists_mem_eq_sup' hF (fun j => bidRow loc (1 - 3 * v) y Q j)
  have hjlam : bidRow loc (1 - 3 * v) y Q j = lam := hjM.symm.trans hMy
  have hrows : ∀ j ∈ F, bidRow loc (1 - 3 * v) y Q j ≤ lam := by
    intro j hj
    have h := Finset.le_sup' (fun j => bidRow loc (1 - 3 * v) y Q j) hj
    exact h.trans_eq hMy
  have hjnot : j ∉ Q := by
    intro hjQ
    have hzero := bidRow_eq_zero_of_open loc (1 - 3 * v) y Q j hjQ
      (by linarith only [hvsmall]) (by linarith only [hv])
    linarith only [hzero, hjlam, hlam]
  exact hmaximal j hj hjnot
    (crossing_openable loc F Q v z y lam j hv hvsmall hz hy.1 hy.2 hjlam hrows)

structure ExecutionState (D X : Type*) where
  opened : Finset X
  phase : ℝ
  budget : D → ℝ

noncomputable def regularUpdate {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X)
    (tau : D → ℝ) : ExecutionState D X := by
  classical
  exact ⟨insert i s.opened, s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then
      if activeAt loc t s.phase W j then tau j else s.phase
    else s.budget j⟩

noncomputable def freeUpdate {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (i : X) : ExecutionState D X := by
  classical
  exact ⟨insert i s.opened, s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then s.phase else s.budget j⟩

noncomputable def phaseUpdate {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t K : ℝ) (s : ExecutionState D X) : ExecutionState D X := by
  classical
  exact ⟨s.opened, K * s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then
      clippedAt loc t (K * s.phase) s.opened j else s.budget j⟩

inductive AtomicStep {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam eta : ℝ) :
    ExecutionState D X → ExecutionState D X → Prop
  | regular (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
      (hi : i ∈ F) (hW : s.opened ⊆ W)
      (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
      (hpayment : lam - (Fintype.card D : ℝ) * eta ≤
        openingPayment loc (1 - 3 * v) s.phase W i tau)
      (hdual : ∀ i₀ ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase W a →
        openingDual loc (1 - 3 * v) s.phase W i₀ tau a ≤ lam) :
      AtomicStep loc F v lam eta s (regularUpdate loc (1 - 3 * v) s i W tau)
  | free (s : ExecutionState D X) (i : X) :
      AtomicStep loc F v lam eta s (freeUpdate loc (1 - 3 * v) s i)
  | update (s : ExecutionState D X)
      (hmaximal : ∀ i ∈ F, i ∉ s.opened →
        ¬etaOpenable loc F s.opened (1 - 3 * v) (1 + v ^ 2) v s.phase lam 0 i) :
      AtomicStep loc F v lam eta s (phaseUpdate loc (1 - 3 * v) (1 + v ^ 2) s)

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma opened_subset : s.opened ⊆ s'.opened := by
  cases H <;> simp only [regularUpdate, freeUpdate, phaseUpdate] <;> simp

lemma phase_le (hz : 0 ≤ s.phase) : s.phase ≤ s'.phase := by
  cases H with
  | regular => exact le_rfl
  | free => exact le_rfl
  | update =>
    change s.phase ≤ (1 + v ^ 2) * s.phase
    nlinarith only [mul_nonneg (sq_nonneg v) hz]

lemma positive_phase (hz : 0 < s.phase) : 0 < s'.phase :=
  hz.trans_le (H.phase_le hz.le)

lemma inactive_frozen (j : D) (hj : ¬activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s'.budget j = s.budget j := by
  cases H <;> simp only [regularUpdate, freeUpdate, phaseUpdate, hj, ↓reduceIte]

lemma active_budget_cap (hz : 0 ≤ s.phase) (j : D)
    (hj : activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s'.budget j ≤ (1 + v ^ 2) * s.phase := by
  have hzK : s.phase ≤ (1 + v ^ 2) * s.phase := by
    nlinarith only [mul_nonneg (sq_nonneg v) hz]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hj, ↓reduceIte]
    split_ifs with hw
    · exact (hbid j hw).2.1
    · exact hzK
  | free => simpa only [freeUpdate, hj, ↓reduceIte] using hzK
  | update =>
    simpa only [phaseUpdate, hj, ↓reduceIte] using
      clippedAt_le_phase loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j

end AtomicStep
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def extractPrefix : List Bool → List Bool
  | true :: b :: bits => b :: extractPrefix bits
  | _ => []

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Freeze
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

def freeze {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  Matrix.ofArray ar Array.size_ofFn

@[simp] lemma freeze_eq {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : freeze A=A :=
  Matrix.ofArray_ofFn A

def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ
  | 0 => freeze A
  | t+1 => freeze (BirdDet.Spec.stepEntry A (iterate A t))

def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0,_ => 1
  | k+1,A => (-1)^k * iterate A k 0 0

end MetricKMedianRecovery.BirdInteger

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BlueSubsetDP
open Finset
variable {L : Type*} [DecidableEq L]

def blocks (U : Finset L) : Finset (Finset L) := U.powerset.erase ∅

lemma mem_blocks {U V : Finset L} : V ∈ blocks U ↔ V.Nonempty ∧ V ⊆ U := by
  simp [blocks, Finset.nonempty_iff_ne_empty]

inductive Partition : Finset L → List (Finset L) → Prop
  | nil : Partition ∅ []
  | cons {U V : Finset L} {P : List (Finset L)}
      (hne : V.Nonempty) (hsub : V ⊆ U) (tail : Partition (U \ V) P) :
      Partition U (V :: P)

noncomputable def value (C : Finset L → WithTop ℝ) : ℕ → Finset L → WithTop ℝ
  | 0, U => if U = ∅ then 0 else ⊤
  | t + 1, U => (blocks U).inf (fun V => C V + value C t (U \ V))

lemma value_attained (C : Finset L → WithTop ℝ) (t : ℕ) (U : Finset L)
    (hfin : value C t U ≠ ⊤) :
    ∃ P, Partition U P ∧ P.length = t ∧ (P.map C).sum = value C t U := by
  induction t generalizing U with
  | zero =>
    have hu : U = ∅ := by
      by_contra hn
      exact hfin (by simp [value, hn])
    subst U
    exact ⟨[], Partition.nil, rfl, by simp [value]⟩
  | succ t ih =>
    have hb : (blocks U).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hfin (by simp [value, he])
    obtain ⟨V, hV, hv⟩ := Finset.exists_mem_eq_inf (blocks U) hb
      (fun V => C V + value C t (U \ V))
    change value C (t + 1) U = C V + value C t (U \ V) at hv
    have htail : value C t (U \ V) ≠ ⊤ := by
      intro ht
      apply hfin
      simp [hv, ht]
    obtain ⟨P, hP, hlen, heq⟩ := ih (U \ V) htail
    refine ⟨V :: P, Partition.cons (mem_blocks.mp hV).1 (mem_blocks.mp hV).2 hP,
      by simp [hlen], ?_⟩
    simp only [List.map_cons, List.sum_cons, heq, ← hv]

noncomputable def best (C : Finset L → WithTop ℝ) (c : ℕ) (U : Finset L) : WithTop ℝ :=
  if U = ∅ then 0 else (Finset.Icc 1 c).inf (fun t => value C t U)

lemma best_attained (C : Finset L → WithTop ℝ) (c : ℕ) (U : Finset L)
    (hfin : best C c U ≠ ⊤) :
    ∃ P, Partition U P ∧ P.length ≤ c ∧ (P.map C).sum = best C c U := by
  by_cases hu : U = ∅
  · subst U
    exact ⟨[], Partition.nil, by simp, by simp [best]⟩
  · have hi : (Finset.Icc 1 c).Nonempty := by
      by_contra hn
      exact hfin (by simp [best, hu, Finset.not_nonempty_iff_eq_empty.mp hn])
    obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_inf (Finset.Icc 1 c) hi
      (fun t => value C t U)
    have he : best C c U = value C t U := by simp [best, hu, heq]
    obtain ⟨P, hP, hlen, hval⟩ := value_attained C t U (he ▸ hfin)
    exact ⟨P, hP, hlen ▸ (Finset.mem_Icc.mp ht).2, by simpa [he] using hval⟩

variable {R Y : Type*} [DecidableEq R] [DecidableEq Y]

noncomputable def blockCost (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) : WithTop ℝ :=
  F.inf (fun y => ∑ l ∈ U, (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)))

omit [DecidableEq R] [DecidableEq Y] in
lemma blockCost_attained [Nonempty R] (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (h : blockCost B F label q U ≠ ⊤) :
    ∃ y ∈ F, ∃ sel : L → R, (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l) ∧
      blockCost B F label q U = (∑ l ∈ U, q (sel l) y : ℝ) := by
  have hF : F.Nonempty := by
    by_contra hn
    exact h (by simp [blockCost, Finset.not_nonempty_iff_eq_empty.mp hn])
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf F hF
    (fun y => ∑ l ∈ U, (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)))
  change blockCost B F label q U = _ at he
  have hlab : ∀ l ∈ U, ∃ r ∈ B, label r = l ∧
      (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) = q r y := by
    intro l hl
    have hn : (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) ≠ ⊤ :=
      WithTop.sum_ne_top.mp (he ▸ h) l hl
    have hb : (B.filter (label · = l)).Nonempty := by
      by_contra hh
      exact hn (by simp [Finset.not_nonempty_iff_eq_empty.mp hh])
    obtain ⟨r, hr, hmin⟩ := Finset.exists_mem_eq_inf _ hb (fun r => (q r y : WithTop ℝ))
    exact ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2, hmin⟩
  classical
  let sel : L → R := fun l => if hl : l ∈ U then (hlab l hl).choose else Classical.choice ‹Nonempty R›
  have hs : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧
      (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) = q (sel l) y := by
    intro l hl
    simpa only [sel, dite_eq_left hl] using (hlab l hl).choose_spec
  refine ⟨y, hy, sel, fun l hl => ⟨(hs l hl).1, (hs l hl).2.1⟩, ?_⟩
  rw [he, WithTop.coe_sum]
  exact Finset.sum_congr rfl (fun l hl => (hs l hl).2.2)

omit [DecidableEq R] in
lemma partition_routing [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ)
    {U : Finset L} {P : List (Finset L)} (hP : Partition U P)
    (hfin : (P.map (blockCost B F label q)).sum ≠ ⊤) :
    ∃ sel : L → R, ∃ dst : L → Y,
      (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F) ∧
      (U.image dst).card ≤ P.length ∧
      ((∑ l ∈ U, q (sel l) (dst l) : ℝ) : WithTop ℝ) =
        (P.map (blockCost B F label q)).sum := by
  classical
  induction hP with
  | nil =>
    exact ⟨fun _ => Classical.choice ‹Nonempty R›, fun _ => Classical.choice ‹Nonempty Y›,
      by simp, by simp, by simp⟩
  | @cons U V P hne hsub tail ih =>
    simp only [List.map_cons, List.sum_cons] at hfin ⊢
    obtain ⟨y, hy, sel₁, hs₁, hcost₁⟩ := blockCost_attained B F label q V
      (WithTop.add_ne_top.mp hfin).1
    obtain ⟨sel₂, dst₂, hs₂, hcard₂, hcost₂⟩ := ih (WithTop.add_ne_top.mp hfin).2
    let sel : L → R := fun l => if l ∈ V then sel₁ l else sel₂ l
    let dst : L → Y := fun l => if l ∈ V then y else dst₂ l
    have hs : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F := by
      intro l hl
      by_cases hv : l ∈ V
      · simpa only [sel, dst, ite_eq_left hv] using ⟨(hs₁ l hv).1, (hs₁ l hv).2, hy⟩
      · simpa only [sel, dst, ite_eq_right hv] using hs₂ l (Finset.mem_sdiff.mpr ⟨hl, hv⟩)
    have himage : U.image dst ⊆ insert y ((U \ V).image dst₂) := by
      intro z hz
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
      by_cases hv : l ∈ V
      · simp [dst, hv]
      · exact Finset.mem_insert_of_mem (by
          simpa only [dst, ite_eq_right hv] using Finset.mem_image.mpr
            ⟨l, Finset.mem_sdiff.mpr ⟨hl, hv⟩, rfl⟩)
    have hcard : (U.image dst).card ≤ (V :: P).length := by
      have h₁ := Finset.card_le_card himage
      have h₂ := Finset.card_insert_le y ((U \ V).image dst₂)
      simp only [List.length_cons]
      omega
    refine ⟨sel, dst, hs, hcard, ?_⟩
    have hvsum : ∑ l ∈ V, q (sel l) (dst l) = ∑ l ∈ V, q (sel₁ l) y := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [sel, dst, ite_eq_left hl]
    have hrest : ∑ l ∈ U \ V, q (sel l) (dst l) =
        ∑ l ∈ U \ V, q (sel₂ l) (dst₂ l) := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [sel, dst, ite_eq_right (Finset.mem_sdiff.mp hl).2]
    rw [← Finset.sum_sdiff hsub, WithTop.coe_add, hrest, hvsum, hcost₂, ← hcost₁, add_comm]

lemma best_routing [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ)
    (U : Finset L) (c : ℕ) (hfin : best (blockCost B F label q) c U ≠ ⊤) :
    ∃ sel : L → R, ∃ dst : L → Y,
      (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F) ∧
      (U.image sel).card = U.card ∧ (U.image dst).card ≤ c ∧
      ((∑ l ∈ U, q (sel l) (dst l) : ℝ) : WithTop ℝ) = best (blockCost B F label q) c U := by
  obtain ⟨P, hP, hlen, he⟩ := best_attained (blockCost B F label q) c U hfin
  obtain ⟨sel, dst, hs, hc, hcost⟩ := partition_routing B F label q hP (he ▸ hfin)
  refine ⟨sel, dst, hs, ?_, hc.trans hlen, hcost.trans he⟩
  apply Finset.card_image_of_injOn
  intro l hl l' hl' hh
  exact ((hs l hl).2.1).symm.trans ((congrArg label hh).trans (hs l' hl').2.1)

end BlueSubsetDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestDesignation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]

structure Plan (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (c : ℕ) where
  sel : L → R
  dst : L → Y
  selection : ∀ l, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F
  selected_injective : Function.Injective sel
  destination_count : (Finset.univ.image dst).card ≤ c
  value_eq : ((∑ l, q (sel l) (dst l) : ℝ) : WithTop ℝ) =
    best (blockCost B F label q) c Finset.univ

lemma plan_exists [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ) (c : ℕ)
    (hfin : best (blockCost B F label q) c Finset.univ ≠ ⊤) :
    Nonempty (Plan B F label q c) := by
  obtain ⟨sel,dst,hs,_,hc,hval⟩ := best_routing B F label q Finset.univ c hfin
  refine ⟨⟨sel,dst,fun l => hs l (Finset.mem_univ l),?_,hc,hval⟩⟩
  intro l l' he
  exact (hs l (Finset.mem_univ l)).2.1.symm.trans
    ((congrArg label he).trans (hs l' (Finset.mem_univ l')).2.1)

noncomputable def computedPlan [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ) (c : ℕ) :
    Option (Plan B F label q c) :=
  if h : best (blockCost B F label q) c Finset.univ = ⊤ then none
  else some (Classical.choice (plan_exists B F label q c h))

end BlueSubsetDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]
def Plan.reweight {B : Finset R} {F : Finset Y} {label : R→L} {q : R→Y→ℝ} {c : ℕ}
    (P : Plan B F label q c) (q' : R→Y→ℝ) (h : q'=q) : Plan B F label q' c :=
  ⟨P.sel,P.dst,P.selection,P.selected_injective,P.destination_count,by simpa only [h] using P.value_eq⟩
end BlueSubsetDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def connection (S : Finset V) (p : V) : ℝ :=
  if h : S.Nonempty then S.inf' h (dist p) else 0

noncomputable def nearest (S : Finset V) (hS : S.Nonempty) (p : V) : V :=
  Classical.choose (Finset.exists_min_image S (dist p) hS)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring

noncomputable def threshold (mu : ℝ) (a : ℕ) : ℝ := (mu/100)*(1/2:ℝ)^a
noncomputable def rounds (mu : ℝ) : ℕ := ⌈40/mu⌉₊
noncomputable def countConstant (mu : ℝ) : ℝ :=
  10+(600/mu)*(2:ℝ)^(rounds mu-1)

variable {I : Type*}

noncomputable def shortCenters (O : Finset I) (scale : I → ℝ) (b : ℝ) : Finset I :=
  O.filter (fun i => scale i < b)
noncomputable def badCenters (O : Finset I) (scale V : I → ℝ) (b t : ℝ) : Finset I :=
  O.filter (fun i => scale i < b ∨ t*b < V i)

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ThresholdTimesPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

noncomputable def separation (O : Finset V) (i : V) : ℝ := connection (O.erase i) i
noncomputable def cluster (D : Finset V) (assign : V → V) (i : V) : Finset V :=
  D.filter (fun p => assign p = i)
noncomputable def clusterWeight (D S : Finset V) (assign : V → V) (i : V) : ℝ :=
  ∑ p ∈ cluster D assign i, (connection S p + dist p i)
noncomputable def ballFacilities (O S : Finset V) (i : V) : Finset V :=
  S.filter (fun s => dist i s < separation O i/4)

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Chosen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

omit [MetricSpace V] in
lemma erase_nonempty_of_two (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) :
    (O.erase i).Nonempty := by
  have hc : 0 < (O.erase i).card := by
    by_cases hi : i ∈ O
    · have he := Finset.card_erase_add_one hi; omega
    · simpa only [Finset.erase_eq_of_notMem hi] using (lt_of_lt_of_le (by omega : 0 < 2) hO2)
  exact Finset.card_pos.mp hc

noncomputable def neighbor (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : V :=
  nearest (O.erase i) (erase_nonempty_of_two O hO2 i) i

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TotalAssignmentExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

noncomputable def clusterScale (D O : Finset V) (assign : V → V) (i : V) : ℝ :=
  (cluster D assign i).card * separation O i

end MetricKMedianRecovery.Anchoring

end OAI
end


