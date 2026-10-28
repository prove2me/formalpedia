-- Prove2me | Definitions.Def_OAIQ077T003
-- name    : OAIQ077T003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:53:21.044062+00:00
-- url     : https://prove2.me/theorems/b0bc3b49-7ea7-47e1-8508-ff1cead00f28
-- title:
--   Definitions bundle OAIQ077T003 of the split of OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 70 definitions, 1 instance and 71 theorems. The definitions and types are `OAI.ThorpNine.Casimir.Thorp.blockGap`, `OAI.ThorpNine.Casimir.Thorp.carryCoins`, `OAI.ThorpNine.Casimir.Thorp.centralBlock`, `OAI.ThorpNine.Casimir.Thorp.centralDistance`, `OAI.ThorpNine.Casimir.Thorp.centralFactor`, `OAI.ThorpNine.Casimir.Thorp.closingDomain`, `OAI.ThorpNine.Casimir.Thorp.closingValue`, `OAI.ThorpNine.Casimir.Thorp.conjugateCycle`, `OAI.ThorpNine.Casimir.Thorp.cutoffMass`, `OAI.ThorpNine.Casimir.Thorp.encounters`, `OAI.ThorpNine.Casimir.Thorp.exceptionChild`, `OAI.ThorpNine.Casimir.Thorp.freshPost`, `OAI.ThorpNine.Casimir.Thorp.freshPre`, `OAI.ThorpNine.Casimir.Thorp.headAverage`, `OAI.ThorpNine.Casimir.Thorp.highStepEquiv`, `OAI.ThorpNine.Casimir.Thorp.insertionPerm`, `OAI.ThorpNine.Casimir.Thorp.inverseButterflyMarks`, `OAI.ThorpNine.Casimir.Thorp.localModifiedPerm`, `OAI.ThorpNine.Casimir.Thorp.modifiedAssignmentCost`, `OAI.ThorpNine.Casimir.Thorp.modifiedBoundary`, `OAI.ThorpNine.Casimir.Thorp.modifiedCost`, `OAI.ThorpNine.Casimir.Thorp.modifiedInputTree`, `OAI.ThorpNine.Casimir.Thorp.modifiedNormalization`, `OAI.ThorpNine.Casimir.Thorp.modifiedPerm`, `OAI.ThorpNine.Casimir.Thorp.modifiedReverseCoins`, `OAI.ThorpNine.Casimir.Thorp.modifiedReverseEquiv`, `OAI.ThorpNine.Casimir.Thorp.modifiedRoutingMoment`, `OAI.ThorpNine.Casimir.Thorp.modifiedRowMoment`, `OAI.ThorpNine.Casimir.Thorp.modifiedStageEquiv`, `OAI.ThorpNine.Casimir.Thorp.modifiedStepEquiv`, `OAI.ThorpNine.Casimir.Thorp.outerPerm`, `OAI.ThorpNine.Casimir.Thorp.palindromeFamilyCost`, `OAI.ThorpNine.Casimir.Thorp.palindromeLevelCost`, `OAI.ThorpNine.Casimir.Thorp.palindromeLowCost`, `OAI.ThorpNine.Casimir.Thorp.palindromeMinorant`, `OAI.ThorpNine.Casimir.Thorp.palindromeSlabCost`, `OAI.ThorpNine.Casimir.Thorp.palindromeStageEquiv`, `OAI.ThorpNine.Casimir.Thorp.parallelClose`, `OAI.ThorpNine.Casimir.Thorp.parallelFollow`, `OAI.ThorpNine.Casimir.Thorp.parallelNetwork` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `ThorpRouting_Casimir_AlternatingPerm`, `ThorpRouting_Casimir_AverageMap`, `ThorpRouting_Casimir_BlockProduct`, `ThorpRouting_Casimir_CutoffMass`, `ThorpRouting_Casimir_Distance`, `ThorpRouting_Casimir_ExposedCoins`, `ThorpRouting_Casimir_InputTree`, `ThorpRouting_Casimir_InsertionPerm`, `ThorpRouting_Casimir_ModifiedReverseCoins`, `ThorpRouting_Casimir_ModifiedRoutingMoment`, `ThorpRouting_Casimir_PairAssembleEquiv`, `ThorpRouting_Casimir_PalindromeFamilyCost`, `ThorpRouting_Casimir_ParallelFollow`, `ThorpRouting_Casimir_PriorPaths`, `ThorpRouting_Casimir_RotationMeeting`, `ThorpRouting_Casimir_SandwichShuffle`, `ThorpRouting_Dense_ExposedCoins`, `ThorpRouting_Dense_ParallelFollow`, `ThorpRouting_Harmonic_AverageMap`, `ThorpRouting_Harmonic_ExposedCoins`, `ThorpRouting_Harmonic_ParallelFollow`, `ThorpRouting_HighTail_ExposedCoins`, `ThorpRouting_HighTail_ParallelFollow`, `ThorpRouting_Smoothing_ExposedCoins`, `ThorpRouting_Smoothing_ParallelFollow`, `ThorpRouting_SparseSaving_Coins`, `ThorpRouting_SparseSaving_ModifiedStageEquiv`, `ThorpRouting_SparseSaving_Representative`, `ThorpRouting_Tail_BenesCoins`, `ThorpRouting_Tail_ExposedCoins`, `ThorpRouting_Tail_ParallelFollow`, `ThorpRouting_Tail_Representative`.
--
--   **Imports.** It imports the published bundle `Def_ThorpRouting`; the bundles `OAIQ077T000`, `OAIQ077T001` and `OAIQ077T002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_ThorpNine_Harmonic_Thorp_UnitaryFinite_medium_exception_decay` and `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.medium_exception_decay_q77`; the proofs of `OAI_ThorpNine_Casimir_Thorp_CasimirBounds_casimir_main`, `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.casimir_main_q77`, `OAI_ThorpNine_Casimir_Thorp_CasimirBounds_trace_bound`, `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77`, `OAI_ThorpNine_Casimir_Thorp_Specht_exponential_dimension_spectral`, `OAI.ThorpNine.Casimir.Thorp.Specht.exponential_dimension_spectral_q77`, `OAI_ThorpNine_Casimir_Thorp_Specht_spectral_regimes`, `OAI.ThorpNine.Casimir.Thorp.Specht.spectral_regimes_q77`, `OAI_ThorpNine_Harmonic_Thorp_Casimir_level_contraction`, `OAI.ThorpNine.Harmonic.Thorp.Casimir.level_contraction_q77`, `OAI_ThorpNine_Harmonic_Thorp_HarmonicBounds_dimension_contraction`, `OAI.ThorpNine.Harmonic.Thorp.HarmonicBounds.dimension_contraction_q77`, `OAI_ThorpNine_Harmonic_Thorp_HarmonicBounds_harmonic_cycle_main`, `OAI.ThorpNine.Harmonic.Thorp.HarmonicBounds.harmonic_cycle_main_q77`, `OAI_ThorpNine_Harmonic_Thorp_Specht_exponential_dimension_spectral`, `OAI.ThorpNine.Harmonic.Thorp.Specht.exponential_dimension_spectral_q77`, `OAI_ThorpNine_Harmonic_Thorp_Specht_near_row_amplification`, `OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification_q77`, `OAI_ThorpNine_Harmonic_Thorp_UnitaryFinite_medium_exception_decay`, `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.medium_exception_decay_q77`, `OAI_ThorpNine_SparseSaving_Thorp_SparseRegime_exponential_sparse_saving`, `OAI.ThorpNine.SparseSaving.Thorp.SparseRegime.exponential_sparse_saving_q77`, `OAI_ThorpNine_Tail_Thorp_Specht_exponential_dimension_spectral`, `OAI.ThorpNine.Tail.Thorp.Specht.exponential_dimension_spectral_q77`, `OAI_ThorpNine_Tail_Thorp_Specht_spectral_regimes`, `OAI.ThorpNine.Tail.Thorp.Specht.spectral_regimes_q77`, `OAI_ThorpNine_Tail_Thorp_StrongTail_strong_tail`, `OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail_q77` and `OAI.ThorpNine.main`.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000
import Definitions.Def_OAIQ077T001
import Definitions.Def_OAIQ077T002

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Distance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

open scoped BigOperators
open Filter

lemma card_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    (childMarks s ε).card = (s.filter (fun x => x 0 = ε)).card := by
  classical
  unfold childMarks
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hx0 := (Finset.mem_filter.mp hx).2
  have hy0 := (Finset.mem_filter.mp hy).2
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hx0, hy0, hxy]

lemma card_childMarks_add {d : ℕ} (s : Finset (Card (d + 1))) :
    (childMarks s false).card + (childMarks s true).card = s.card := by
  classical
  rw [card_childMarks, card_childMarks]
  simpa only [Bool.not_eq_false] using
    (Finset.card_filter_add_card_filter_not (s := s) (fun x => x 0 = false))

noncomputable def topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) : Finset (Card d) :=
  ((childMarks s false).image (butterflyPerm d (b.2 false))) ∩
    ((childMarks s true).image (butterflyPerm d (b.2 true)))

lemma card_topMeetings_le {d : ℕ} (b : Butterfly (d + 1)) (s : Finset (Card (d + 1))) :
    (topMeetings b s).card ≤ min (childMarks s false).card (childMarks s true).card := by
  classical
  apply le_min
  · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 false)).injective)
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 true)).injective)

noncomputable def encounters : (d : ℕ) → Butterfly d → Finset (Card d) → ℕ
  | 0, _, _ => 0
  | d + 1, b, s => encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card

lemma butterfly_encounters (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (encounters d b s : ℝ) ≤ (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  induction d with
  | zero =>
    simp only [encounters, Nat.cast_zero]
    have hs : s.card ≤ 1 := by
      simpa [Card] using Finset.card_le_univ s
    interval_cases s.card <;> simp
  | succ d ih =>
    have h₀ := ih (b.2 false) (childMarks s false)
    have h₁ := ih (b.2 true) (childMarks s true)
    have ht : ((topMeetings b s).card : ℝ) ≤
        min ((childMarks s false).card : ℝ) ((childMarks s true).card : ℝ) := by
      exact_mod_cast card_topMeetings_le b s
    have he := split_entropy_lower ((childMarks s false).card : ℝ)
      ((childMarks s true).card : ℝ) (by positivity) (by positivity)
    have hs : ((childMarks s false).card : ℝ) + (childMarks s true).card = s.card := by
      exact_mod_cast card_childMarks_add s
    rw [hs] at he
    have hL : 0 < 2 * Real.log 2 := by positivity
    rw [le_div_iff₀ hL] at h₀ h₁ ⊢
    simp only [encounters, Nat.cast_add]
    nlinarith [mul_le_mul_of_nonneg_right ht hL.le]

def routeValue : (d : ℕ) → Card d → Card d → SwitchIndex d → Bool
  | 0, _, _, i => nomatch i
  | _d + 1, x, y, Sum.inl _ => Bool.xor (x 0) (y 0)
  | d + 1, x, y, Sum.inr (_,i) => routeValue d (Fin.tail x) (Fin.tail y) i

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

lemma card_routeDomain (d : ℕ) (x y : Card d) : (routeDomain d x y).card = d := by
  classical
  induction d with
  | zero => rfl
  | succ d ih =>
    change (insert (Sum.inl (Fin.tail y))
      ((routeDomain d (Fin.tail x) (Fin.tail y)).image
        (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
      Finset (Sum (Card d) (Bool × SwitchIndex d))).card = d + 1
    rw [Finset.card_insert_of_notMem (by simp)]
    rw [Finset.card_image_of_injective _ (by intro i j h; cases h; rfl), ih]

lemma butterfly_endpoint_iff (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d) :
    butterflyPerm d (decodeButterfly d ω) x = y ↔
      ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i := by
  classical
  induction d with
  | zero =>
    have he : butterflyPerm 0 (decodeButterfly 0 ω) x = y := Subsingleton.elim _ _
    simp [he, routeDomain]
  | succ d ih =>
    let v := butterflyPerm d (decodeButterfly d (fun i => ω (Sum.inr (x 0,i)))) (Fin.tail x)
    change Fin.cons (Bool.xor (x 0) (ω (Sum.inl v))) v = y ↔ _
    have hv : v = Fin.tail y ↔
        ∀ i ∈ routeDomain d (Fin.tail x) (Fin.tail y),
          ω (Sum.inr (x 0,i)) = routeValue d (Fin.tail x) (Fin.tail y) i :=
      ih _ _ _
    constructor
    · intro h i hi
      have ht : v = Fin.tail y := by simpa using congrArg Fin.tail h
      have hh : ω (Sum.inl (Fin.tail y)) = Bool.xor (x 0) (y 0) := by
        have he := congrFun h 0
        simp only [Fin.cons_zero, ht] at he
        exact (xor_eq_iff _ _ _).mp he
      rcases Finset.mem_insert.mp hi with htop | hchild
      · subst i
        exact hh
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hchild
        exact hv.mp ht j hj
    · intro h
      have hh := h (Sum.inl (Fin.tail y)) (Finset.mem_insert_self _ _)
      have ht : v = Fin.tail y := hv.mpr (fun i hi =>
        h (Sum.inr (x 0,i)) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))
      have hh' : Bool.xor (x 0) (ω (Sum.inl (Fin.tail y))) = y 0 :=
        (xor_eq_iff _ _ _).mpr hh
      rw [ht, hh', Fin.cons_self_tail]

lemma mem_routeDomain_iff_user (d : ℕ) (b : Butterfly d) (x : Card d) (i : SwitchIndex d) :
    i ∈ routeDomain d x (butterflyPerm d b x) ↔
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x := by
  classical
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      change Sum.inl y ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq, Finset.mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false]
      change y = butterflyPerm d (b.2 (x 0)) (Fin.tail x) ↔ _
      simp only [switchUsers, cons_eq_iff]
      cases x 0 <;> simp [Equiv.symm_apply_eq]
    | inr z =>
      obtain ⟨ε,i⟩ := z
      change Sum.inr (ε,i) ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or, Finset.mem_image,
        Sum.inr.injEq, Prod.mk.injEq]
      change (∃ j, j ∈ routeDomain d (Fin.tail x) (butterflyPerm d (b.2 (x 0)) (Fin.tail x)) ∧
        x 0 = ε ∧ j = i) ↔ _
      simp only [switchUsers, cons_eq_iff]
      constructor
      · rintro ⟨j,hj,hε,rfl⟩
        subst ε
        rcases (ih (b.2 (x 0)) (Fin.tail x) j).mp hj with h | h
        · exact Or.inl ⟨rfl,h⟩
        · exact Or.inr ⟨rfl,h⟩
      · rintro (⟨hε,h⟩ | ⟨hε,h⟩)
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inl h),rfl,rfl⟩
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inr h),rfl,rfl⟩

lemma mem_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) (x : Card d) :
    x ∈ childMarks s ε ↔ Fin.cons ε x ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hys,hyε⟩ := Finset.mem_filter.mp hy
    rw [← hxy, ← hyε, Fin.cons_self_tail]
    exact hys
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons ε x,
      Finset.mem_filter.mpr ⟨h,by simp⟩,by simp⟩

lemma mem_topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) (y : Card d) :
    y ∈ topMeetings b s ↔
      (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
      (switchUsers (d+1) b (Sum.inl y)).2 ∈ s := by
  classical
  have he (ε : Bool) : y ∈ (childMarks s ε).image (butterflyPerm d (b.2 ε)) ↔
      (butterflyPerm d (b.2 ε)).symm y ∈ childMarks s ε := by
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      simpa only [Equiv.symm_apply_apply] using hx
    · intro h
      exact Finset.mem_image.mpr ⟨_,h,Equiv.apply_symm_apply _ _⟩
  simp only [topMeetings, Finset.mem_inter, he, mem_childMarks, switchUsers]

lemma encounters_eq_switch_sum (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    encounters d b s = ∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then 1 else 0 := by
  classical
  induction d with
  | zero =>
    simp only [encounters]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact Empty.elim i
  | succ d ih =>
    change encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card =
        ∑ i : Sum (Card d) (Bool × SwitchIndex d), _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [ih,ih]
    have ht : (∑ y : Card d,
        if (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
          (switchUsers (d+1) b (Sum.inl y)).2 ∈ s then 1 else 0) =
        (topMeetings b s).card := by
      simp only [← mem_topMeetings]
      simp
    rw [ht]
    simp only [mem_childMarks, switchUsers]
    ac_rfl

lemma marked_switch_entropy_bound (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0) ≤
      (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  classical
  have he : (encounters d b s : ℝ) =
      ∑ i : SwitchIndex d,
        if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0 := by
    rw [encounters_eq_switch_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [← he]
  exact butterfly_encounters d b s

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

variable {d A : ℕ}

noncomputable instance instFintypeSelectedCycle (p : Equiv.Perm (Card d)) (S : Finset (Card d)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

noncomputable def parallelPath (pre : α ≃ B × Card d)
    (ω : B × SwitchIndex d → Bool) (x : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2
    (butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2)).image
      (fun i => ((pre x).1,i))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma mem_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (x : α) (i : B × SwitchIndex d) :
    i ∈ parallelPath pre ω x ↔ (parallelUsers pre ω i).1 = x ∨ (parallelUsers pre ω i).2 = x := by
  classical
  obtain ⟨b,j⟩ := i
  simp only [parallelPath,Finset.mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨k,hk,hb,rfl⟩
    subst b
    rcases (mem_routeDomain_iff_user d _ _ _).mp hk with h | h
    · left
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
    · right
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
  · intro h
    have hh : (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).1) = pre x ∨
        (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).2) = pre x := by
      rcases h with h | h
      · exact Or.inl (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
      · exact Or.inr (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
    have hb : b = (pre x).1 := hh.elim (congrArg Prod.fst) (congrArg Prod.fst)
    subst b
    refine ⟨j,?_,rfl,rfl⟩
    apply (mem_routeDomain_iff_user d _ _ _).mpr
    exact hh.elim (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma card_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (x : α) :
    (parallelPath pre ω x).card = d := by
  classical
  rw [parallelPath,Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),card_routeDomain]

omit [DecidableEq B] in
lemma sum_card_blockMarks (pre : α ≃ B × Card d) (S : Finset α) :
    ∑ b : B, (blockMarks pre S b).card = S.card := by
  classical
  calc
    _ = ∑ b : B, ∑ x : Card d, if pre.symm (b,x) ∈ S then 1 else 0 := by
      simp only [blockMarks,Finset.card_filter]
    _ = ∑ u : B × Card d, if pre.symm u ∈ S then 1 else 0 := (Fintype.sum_prod_type (fun u : B × Card d => if pre.symm u ∈ S then (1:ℕ) else 0)).symm
    _ = ∑ x : α, if x ∈ S then 1 else 0 := Equiv.sum_comp pre.symm (fun x : α => if x ∈ S then (1:ℕ) else 0)
    _ = _ := by simp

omit [DecidableEq B] in
lemma card_blockMarks_le (pre : α ≃ B × Card d) (S : Finset α) (b : B) :
    (blockMarks pre S b).card ≤ S.card := by
  rw [←sum_card_blockMarks pre S]
  exact Finset.single_le_sum (f := fun b : B => (blockMarks pre S b).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}
omit [DecidableEq B] in
lemma parallel_entropy (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (S : Finset α) :
    (∑ i : B × SwitchIndex d,
      if (parallelUsers pre ω i).1 ∈ S ∧ (parallelUsers pre ω i).2 ∈ S then (1:ℝ) else 0) ≤
      (S.card : ℝ) * Real.log S.card / (2 * Real.log 2) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log (blockMarks pre S b).card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [←mem_blockMarks,parallelUsers] using
        marked_switch_entropy_bound d (decodeButterfly d (fun i => ω (b,i))) (blockMarks pre S b)
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log S.card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hz : (blockMarks pre S b).card = 0
      · simp [hz]
      · apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
          (by exact_mod_cast card_blockMarks_le pre S b)
    _ = _ := by rw [←Finset.sum_div,←Finset.sum_mul,←Nat.cast_sum,sum_card_blockMarks]

noncomputable def parallelFollow (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  QueryTree.followPath d (fun i => ((pre x).1,i)) (pre x).2 (fun y => k (post ((pre x).1,y)))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).succeeds ω = (k (relabeledPerm pre post ω x)).succeeds ω := by
  exact QueryTree.followPath_succeeds _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).charge ω = (k (relabeledPerm pre post ω x)).charge ω := by
  exact QueryTree.followPath_raw_charge _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelFollow_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).staleCharge R ω =
      (k (relabeledPerm pre post ω x)).staleCharge (R ∪ parallelPath pre ω x) ω := by
  exact QueryTree.followPath_stale_charge _ _ _ _ _ _

noncomputable def closingDomain (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2 (post.symm y).2).image (fun i => ((pre x).1,i))

def closingValue (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (i : B × SwitchIndex d) : Bool := routeValue d (pre x).2 (post.symm y).2 i.2

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma relabeled_endpoint_pair (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
      butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2 = (post.symm y).2 := by
  change post ((pre x).1,_) = y ↔ _
  rw [←post.eq_symm_apply,Prod.mk.injEq]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma relabeled_endpoint_iff (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
        ∀ i ∈ closingDomain pre post x y, ω i = closingValue pre post x y i := by
  classical
  rw [relabeled_endpoint_pair,butterfly_endpoint_iff]
  simp only [closingDomain,Finset.forall_mem_image,closingValue]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma closingDomain_eq (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) (h : relabeledPerm pre post ω x = y) :
    closingDomain pre post x y = parallelPath pre ω x := by
  rw [closingDomain,parallelPath,(relabeled_endpoint_pair _ _ _ _ _).mp h |>.2]

noncomputable def parallelClose (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  if (pre x).1 = (post.symm y).1 then
    QueryTree.forceList (closingDomain pre post x y).toList (closingValue pre post x y) k
  else QueryTree.reject

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

def splitSwitch : (r s : ℕ) → SwitchIndex (s+r) ≃
    (Card r × SwitchIndex s) ⊕ (Card s × SwitchIndex r)
  | 0, _ =>
    { toFun := fun i => Sum.inl ((fun j => Fin.elim0 j),i)
      invFun := fun i => match i with
        | Sum.inl (_,j) => j
        | Sum.inr (_,j) => nomatch j
      left_inv := fun _ => rfl
      right_inv := by
        intro i
        rcases i with ⟨x,j⟩ | ⟨x,j⟩
        · exact congrArg Sum.inl (Prod.ext (Subsingleton.elim _ _) rfl)
        · exact Empty.elim j }
  | r+1, s =>
    { toFun := fun i => match i with
        | Sum.inl y => Sum.inr ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
        | Sum.inr (b,j) => match splitSwitch r s j with
          | Sum.inl (p,j) => Sum.inl (Fin.cons b p,j)
          | Sum.inr (q,j) => Sum.inr (q,Sum.inr (b,j))
      invFun := fun i => match i with
        | Sum.inl (p,j) => Sum.inr (p 0,(splitSwitch r s).symm (Sum.inl (Fin.tail p,j)))
        | Sum.inr (q,Sum.inl p) => Sum.inl ((cardSplit r s).symm (p,q))
        | Sum.inr (q,Sum.inr (b,j)) => Sum.inr (b,(splitSwitch r s).symm (Sum.inr (q,j)))
      left_inv := by
        intro i
        rcases i with y | ⟨b,j⟩
        · dsimp only
          rw [Prod.mk.eta, Equiv.symm_apply_apply]
        · dsimp only
          cases hz : splitSwitch r s j with
          | inl z =>
            rcases z with ⟨p,k⟩
            simp only [Fin.cons_zero, Fin.tail_cons]
            rw [←hz,Equiv.symm_apply_apply]
          | inr z =>
            rcases z with ⟨q,k⟩
            dsimp only
            rw [←hz,Equiv.symm_apply_apply]
      right_inv := by
        intro i
        rcases i with ⟨p,j⟩ | ⟨q,j⟩
        · simp only [Equiv.apply_symm_apply, Fin.cons_self_tail]
        · rcases j with p | ⟨b,j⟩ <;> simp only [Equiv.apply_symm_apply] }

def splitCoinEquiv (r s : ℕ) :
    ((Card r × SwitchIndex s → Bool) × (Card s × SwitchIndex r → Bool)) ≃
      (SwitchIndex (s+r) → Bool) :=
  (Equiv.sumArrowEquivProdArrow _ _ Bool).symm.trans
    (Equiv.arrowCongr (splitSwitch r s).symm (Equiv.refl Bool))

section PartiallyExposed
variable {α : Type*} {r s : ℕ}

def freshPre (pre : α ≃ Card (s+r)) (lo : Card r × SwitchIndex s → Bool) :
    α ≃ Card s × Card r :=
  ((pre.trans (cardSplit r s)).trans (parallelPerm lo)).trans (Equiv.prodComm _ _)

def freshPost (post : Card (s+r) ≃ α) : Card s × Card r ≃ α :=
  ((Equiv.prodComm _ _).trans (cardSplit r s).symm).trans post

end PartiallyExposed

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

noncomputable def headAverage {d : ℕ} (p : Card (d+1) → ℝ) (y : Card d) : ℝ :=
  (p (Fin.cons false y)+p (Fin.cons true y))/2

noncomputable def inverseButterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω)).symm

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_SandwichShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

noncomputable def routingMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : BenesCoins d =>
    if ∀ i, palindromePerm d ω (e i) = f i then (2:ℝ)^((palindromeCost d e ω:ℝ)*a) else 0)

end Thorp
namespace Thorp

noncomputable def palindromeLowCost (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if d+1 ≤ H then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def cutoffMass (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, ι, _, e, ω =>
      if d+1 ≤ H then crowdedMass (Fintype.card ι) else
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      cutoffMass H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        cutoffMass H d (PairRouting.childEmbedding x c hc true) σ.1.2


noncomputable def centralBlock (r H : ℕ) (b : Card r) : Finset (Card (H+r)) :=
  Finset.univ.image (fun z : Card H => (cardSplit r H).symm (b,z))

end Thorp
namespace Thorp
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_conjugate (p g : Equiv.Perm α) (x : α) :
    orbitSet (g*p*g⁻¹) (g x) = (orbitSet p x).image g := by
  ext y
  simp only [mem_orbitSet,Finset.mem_image]
  rw [Equiv.Perm.sameCycle_conj]
  change p.SameCycle (g.symm (g x)) (g.symm y) ↔ ∃ z, p.SameCycle x z ∧ g z = y
  rw [Equiv.symm_apply_apply]
  constructor
  · intro h
    exact ⟨g.symm y,h,g.apply_symm_apply y⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hz

noncomputable def conjugateCycle (p g : Equiv.Perm α) (S : Finset α)
    (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle (g*p*g⁻¹) (S.image g) := by
  refine ⟨C.val.image g,?_,Finset.image_subset_image C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  exact ⟨g x,by rw [hx,orbitSet_conjugate]⟩

end Thorp
namespace Thorp


def highStepEquiv (r s : ℕ) : (Card s × SwitchIndex (r+1) → Bool) ≃
    (((Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool)) ×
      (Card s × Card r → Bool)) where
  toFun hi := ((fun j => hi (j.1,Sum.inr (false,j.2)),
    fun j => hi (j.1,Sum.inr (true,j.2))),fun j => hi (j.1,Sum.inl j.2))
  invFun c := fun j => match j.2 with
    | Sum.inl y => c.2 (j.1,y)
    | Sum.inr (b,i) => if b then c.1.2 (j.1,i) else c.1.1 (j.1,i)
  left_inv hi := by
    funext j
    rcases j with ⟨z,y|⟨b,i⟩⟩
    · rfl
    · cases b <;> rfl
  right_inv c := by
    rcases c with ⟨⟨h₀,h₁⟩,η⟩
    rfl

noncomputable def palindromeLevelCost (t : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
          palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2

noncomputable def palindromeSlabCost (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ i : Fin l, palindromeLevelCost (l+i.1+1) d e ω

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PalindromeFamilyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_eq_of_agree (p q : Equiv.Perm α) (x : α)
    (h : ∀ z ∈ orbitSet p x, p z = q z) : orbitSet p x = orbitSet q x := by
  have hp (n : ℕ) : (p^n) x ∈ orbitSet p x := by
    apply (mem_orbitSet _ _ _).mpr
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have he (n : ℕ) : (p^n) x = (q^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,←ih]
      exact h _ (hp n)
  ext y
  simp only [mem_orbitSet]
  constructor
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,←he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

noncomputable def survivingCycle (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S)
    (hC : ∀ x ∈ C.val, x ∉ B) : RoutingNetwork.SelectedCycle q S := by
  refine ⟨C.val,?_,C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  refine ⟨x,hx.trans (orbitSet_eq_of_agree p q x ?_)⟩
  intro z hz
  exact h z (hC z (hx ▸ hz))

noncomputable def perturbCycleMap (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle q S ⊕ {x // x ∈ B} := by
  classical
  by_cases hb : ∃ x ∈ C.val, x ∈ B
  · exact Sum.inr ⟨hb.choose,hb.choose_spec.2⟩
  · exact Sum.inl (survivingCycle p q S B h C (by simpa only [not_exists,not_and] using hb))

end Thorp
namespace Thorp

noncomputable def centralDistance (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) : ℕ :=
  ∑ u : Card r, permDistance (C u) (D u)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_InputTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def modifiedBoundary (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    Card r → Equiv.Perm (Card L) := fun u => if u ∈ E then boundaryOutput L r Y u else U u


noncomputable def modifiedInputTree (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X Y : SwitchIndex (L+r) → Bool) : InputTree (L+r) :=
  boundaryTree L r (modifiedBoundary L r E U Y) X


noncomputable def exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) : Finset (Card r) :=
  Finset.univ.filter (fun u => Fin.cons b u ∈ E)

def seedSplitEquiv (r : ℕ) (A : Type*) : (Card (r+1) → A) ≃ (Card r → A) × (Card r → A) where
  toFun U := (fun u => U (Fin.cons false u),fun u => U (Fin.cons true u))
  invFun U := fun u => if u 0 then U.2 (Fin.tail u) else U.1 (Fin.tail u)
  left_inv U := by
    funext u
    dsimp only
    split_ifs with h
    · rw [←h,Fin.cons_self_tail]
    · have h' : u 0 = false := by cases hh : u 0 <;> simp_all
      rw [←h',Fin.cons_self_tail]
  right_inv U := by simp only [Fin.cons_zero,Fin.tail_cons,Bool.false_eq_true,↓reduceIte]

def modifiedStepEquiv (L r : ℕ) : ModifiedCoins L (r+1) ≃
    (ModifiedCoins L r × ModifiedCoins L r) × ((Card (L+r) → Bool) × (Card (L+r) → Bool)) :=
  (Equiv.prodCongr (seedSplitEquiv r (Equiv.Perm (Card L))) (benesStepEquiv (L+r))).trans
    seedSandwichShuffle

noncomputable def modifiedPerm (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.2.1) *
    (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1).perm⁻¹

noncomputable def modifiedCost (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : ModifiedCoins L r) : ℕ :=
  InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1) e ω.2.1

noncomputable def modifiedAssignmentCost (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hc : PairRouting.Compatible x c) (ω : ModifiedCoins L r × ModifiedCoins L r) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
    (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) +
  modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hc false) ω.1 +
  modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hc true) ω.2

noncomputable def centralFactor (L r : ℕ) (E : Finset (Card r)) (a : ℝ) : ℝ :=
  (Nat.factorial (2^L):ℝ)^(-((2:ℝ)^r-E.card)*a)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def modifiedRoutingMoment (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : ModifiedCoins L r =>
    if ∀ i, modifiedPerm L r E ω (e i) = f i then (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a) else 0)

noncomputable def modifiedRowMoment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card (L+r) =>
    ((Fintype.card (ι ↪ Card (L+r)):ℝ)*PairRouting.tupleProbability (modifiedPerm L r E) e f)^(1+a))

noncomputable def modifiedNormalization (L r : ℕ) (E : Finset (Card r)) : ℝ :=
  (Nat.factorial (2^(L+r)):ℝ) /
    (((2:ℝ)^r)^(2^(L+r)) * (Nat.factorial (2^L):ℝ)^(2^r-E.card))

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ModifiedReverseCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def modifiedReverseCoins (L : ℕ) : (r : ℕ) → ModifiedCoins L r → ModifiedCoins L r
  | 0, ω => ((fun u => butterflyPerm L (decodeButterfly L ω.2.1) * (ω.1 u)⁻¹ *
      butterflyPerm L (decodeButterfly L ω.2.1)),ω.2)
  | r+1, ω =>
      let z := modifiedStepEquiv L r ω
      (modifiedStepEquiv L r).symm
        ((modifiedReverseCoins L r z.1.1,modifiedReverseCoins L r z.1.2),(z.2.2,z.2.1))

lemma modifiedReverseCoins_involutive (L r : ℕ) :
    Function.Involutive (modifiedReverseCoins L r) := by
  induction r with
  | zero =>
      intro ω
      apply Prod.ext
      · funext u
        simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp [mul_assoc]
      · rfl
  | succ r ih =>
      change ∀ ω, modifiedReverseCoins L r (modifiedReverseCoins L r ω) = ω at ih
      intro ω
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,ih]
      exact (modifiedStepEquiv L r).symm_apply_apply ω

noncomputable def modifiedReverseEquiv (L r : ℕ) : Equiv.Perm (ModifiedCoins L r) where
  toFun := modifiedReverseCoins L r
  invFun := modifiedReverseCoins L r
  left_inv := modifiedReverseCoins_involutive L r
  right_inv := modifiedReverseCoins_involutive L r

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_AverageMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

omit [Fintype G] in
lemma sampleLaw_nonneg (P : Ω → G) (g : G) : 0 ≤ sampleLaw P g :=
  finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma sampleLaw_sum [Nonempty Ω] (P : Ω → G) : ∑ g,sampleLaw P g=1 := by
  unfold sampleLaw
  rw [←finiteMean_sum]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0 < sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

noncomputable def splitPerm (r L : ℕ) : Equiv.Perm (Card (L+r)) ≃* Equiv.Perm (Card r × Card L) :=
  (cardSplit r L).permCongrHom

noncomputable def outerPerm (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) :
    Equiv.Perm (Card r × Card L) :=
  (Equiv.prodComm (Card L) (Card r)).permCongrHom
    (ParallelBlocks.lift (fun x => butterflyPerm r (decodeButterfly r (fun i => hi (x,i)))))

def parallelSplitCoinEquiv (r L : ℕ) :
    ((Card r → LocalCoins L) × OuterCoins r L) ≃ LocalCoins (L+r) :=
  (Equiv.prodCongr (Equiv.curry (Card r) (SwitchIndex L) Bool).symm (Equiv.refl _)).trans
    (splitCoinEquiv r L)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PairAssembleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

def palindromeStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) ≃ BenesCoins (L+r) :=
  (pairAssembleEquiv _ _ _).trans
    (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L))

def modifiedStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) ≃
      ModifiedCoins L r :=
  (modifiedAssembleEquiv _ _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L)))

noncomputable def localModifiedPerm (L : ℕ) (e : Bool)
    (w : Equiv.Perm (Card L) × BenesCoins L) : Equiv.Perm (Card L) :=
  if e then 1 else butterflyPerm L (decodeButterfly L w.2.1)*w.1⁻¹

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

def insertionPerm (d : ℕ) (i : Fin (d+1)) : Equiv.Perm (Card (d+1)) :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm.trans
    (Fin.insertNthEquiv (fun _ : Fin (d+1) => Bool) i)

end Thorp

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

def carryCoins (d : ℕ) (i : Fin (d+1)) : (Bool → Coins (d+1)) ≃ Coins (d+2) where
  toFun ξ y := ξ (y i) (Fin.removeNth i y)
  invFun ξ b y := ξ (Fin.insertNth i b y)
  left_inv ξ := by funext b y; simp
  right_inv ξ := by funext y; simp

end Thorp


end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

end CycleColoring
end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_AverageMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators Classical

lemma childInjection_swap (d : ℕ) (b : Bool) (u v : Card d) :
    childInjection d b (Equiv.swap u v)=Equiv.swap (Fin.cons b u) (Fin.cons b v) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change (Fin.cons c ((if c=b then Equiv.swap u v else 1) w) : Card (d+1))=_
  by_cases hc : c=b
  · subst c
    simp only [↓reduceIte]
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂
    · subst w; simp
    · subst w; simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => h₁ (by simpa using congrArg Fin.tail h)
      · exact fun h => h₂ (by simpa using congrArg Fin.tail h)
  · rw [ite_eq_right hc,Equiv.Perm.one_apply,Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)

theorem butterfly_generates (d : ℕ) (H : Subgroup (Equiv.Perm (Card d)))
    (hH : ∀ ω : Butterfly d, butterflyPerm d ω∈H) : H=⊤ := by
  induction d with
  | zero =>
    apply top_unique
    intro p _
    have hp : p=1 := Subsingleton.elim _ _
    rw [hp]
    exact H.one_mem
  | succ d ih =>
    have hchild (b : Bool) (p : Equiv.Perm (Card d)) : childInjection d b p∈H := by
      have hc : H.comap (childInjection d b)=⊤ := by
        apply ih
        intro ω
        change childLift (fun c => if c=b then butterflyPerm d ω else 1)∈H
        have h := hH ((fun _ => false),fun c => if c=b then ω else butterflyIdentity d)
        simpa only [butterflyPerm,pairSwitch_false,one_mul,apply_ite,butterflyIdentity_perm] using h
      have hp : p∈H.comap (childInjection d b) := by rw [hc]; trivial
      exact hp
    have hpair (u : Card d) : Equiv.swap (Fin.cons false u) (Fin.cons true u)∈H := by
      rw [←pairSwitch_single]
      have h := hH ((fun v => decide (v=u)),fun _ => butterflyIdentity d)
      simpa only [butterflyPerm,butterflyIdentity_perm,childLift_one,mul_one] using h
    have hswap (x y : Card (d+1)) : Equiv.swap x y∈H := by
      have ht (a b : Bool) (u : Card d) : Equiv.swap (Fin.cons a u) (Fin.cons b u)∈H := by
        cases a <;> cases b
        · rw [Equiv.swap_self]; exact H.one_mem
        · exact hpair _
        · rw [Equiv.swap_comm]; exact hpair _
        · rw [Equiv.swap_self]; exact H.one_mem
      have h₁ : Equiv.swap x (Fin.cons (y 0) (Fin.tail x))∈H := by
        convert ht (x 0) (y 0) (Fin.tail x) using 1
        all_goals try with_reducible_and_instances rfl
        rw [Fin.cons_self_tail]
      have h₂ := hchild (y 0) (Equiv.swap (Fin.tail x) (Fin.tail y))
      rw [childInjection_swap,Fin.cons_self_tail] at h₂
      exact SubmonoidClass.swap_mem_trans H h₁ h₂
    rw [eq_top_iff,←Equiv.Perm.closure_isSwap,Subgroup.closure_le]
    rintro _ ⟨x,y,_,rfl⟩
    exact hswap x y

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0 < sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

end CycleColoring
end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp

open scoped BigOperators
open Filter

noncomputable def inclusionMoment {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : ℝ := by
  classical
  exact finiteMean (fun ω => if s ⊆ F ω then 1 else 0)

end Thorp

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

noncomputable def coefficient (w v : V) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => inner ℂ (ρ (representative a x₀ ha x) w) v)

noncomputable def normalizedCoefficient (w v : V) : EuclideanSpace ℂ X :=
  (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ) • coefficient a x₀ ha ρ w v

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

noncomputable def sampleLaw (P : Ω → G) (g : G) : ℝ :=
  finiteMean (fun ω => if P ω=g then 1 else 0)

end Thorp

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

omit [Fintype α] in
lemma tupleAction_fixed_iff [DecidableEq α] (e : ι ↪ α) (p : Equiv.Perm α) :
    tupleAction p e=e ↔ ∀ x ∈ Finset.univ.image e, p x=x := by
  constructor
  · intro h x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact congrArg (fun f : ι ↪ α => f i) h
  · intro h
    ext i
    exact h (e i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_coe (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : hilbertSpace μ) :
    (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ)) =
      PermutationHilbert.act (tabloidAct p) v := by
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  change hilbertEquiv μ (tabloidRep μ p w) = _
  exact hilbert_action μ p w

noncomputable def unitaryEquiv (μ : YoungDiagram) :
    Representation.Equiv (representation μ) (unitaryRepresentation μ) :=
  Representation.Equiv.mk (spaceHilbertEquiv μ) (by
    intro p
    apply LinearMap.ext
    intro v
    change spaceHilbertEquiv μ (representation μ p v) =
      spaceHilbertEquiv μ (representation μ p ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])


noncomputable def tupleFixedEquiv (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ) ≃ₗ[ℂ]
      fixedHilbert μ (Finset.univ.image e) where
  toFun v := ⟨v.1.1,v.1.2,by
    intro p hp
    have h := v.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mpr hp)
    exact (unitaryRepresentation_coe μ p v.1).symm.trans (congrArg Subtype.val h)⟩
  invFun v := ⟨⟨v.1,v.2.1⟩,by
    intro p hp
    apply Subtype.ext
    exact (unitaryRepresentation_coe μ p _).trans
      (v.2.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mp hp))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Thorp.Specht

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Tail_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

end Thorp

end ThorpNine.Tail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Tail_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

end CycleColoring
end Thorp

end ThorpNine.Tail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Tail_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp

noncomputable def cutoffMass (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, ι, _, e, ω =>
      if d+1 ≤ H then crowdedMass (Fintype.card ι) else
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      cutoffMass H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        cutoffMass H d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

end ThorpNine.Tail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Tail_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators Classical

lemma childInjection_swap (d : ℕ) (b : Bool) (u v : Card d) :
    childInjection d b (Equiv.swap u v)=Equiv.swap (Fin.cons b u) (Fin.cons b v) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change (Fin.cons c ((if c=b then Equiv.swap u v else 1) w) : Card (d+1))=_
  by_cases hc : c=b
  · subst c
    simp only [↓reduceIte]
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂
    · subst w; simp
    · subst w; simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => h₁ (by simpa using congrArg Fin.tail h)
      · exact fun h => h₂ (by simpa using congrArg Fin.tail h)
  · rw [ite_eq_right hc,Equiv.Perm.one_apply,Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)

theorem butterfly_generates (d : ℕ) (H : Subgroup (Equiv.Perm (Card d)))
    (hH : ∀ ω : Butterfly d, butterflyPerm d ω∈H) : H=⊤ := by
  induction d with
  | zero =>
    apply top_unique
    intro p _
    have hp : p=1 := Subsingleton.elim _ _
    rw [hp]
    exact H.one_mem
  | succ d ih =>
    have hchild (b : Bool) (p : Equiv.Perm (Card d)) : childInjection d b p∈H := by
      have hc : H.comap (childInjection d b)=⊤ := by
        apply ih
        intro ω
        change childLift (fun c => if c=b then butterflyPerm d ω else 1)∈H
        have h := hH ((fun _ => false),fun c => if c=b then ω else butterflyIdentity d)
        simpa only [butterflyPerm,pairSwitch_false,one_mul,apply_ite,butterflyIdentity_perm] using h
      have hp : p∈H.comap (childInjection d b) := by rw [hc]; trivial
      exact hp
    have hpair (u : Card d) : Equiv.swap (Fin.cons false u) (Fin.cons true u)∈H := by
      rw [←pairSwitch_single]
      have h := hH ((fun v => decide (v=u)),fun _ => butterflyIdentity d)
      simpa only [butterflyPerm,butterflyIdentity_perm,childLift_one,mul_one] using h
    have hswap (x y : Card (d+1)) : Equiv.swap x y∈H := by
      have ht (a b : Bool) (u : Card d) : Equiv.swap (Fin.cons a u) (Fin.cons b u)∈H := by
        cases a <;> cases b
        · rw [Equiv.swap_self]; exact H.one_mem
        · exact hpair _
        · rw [Equiv.swap_comm]; exact hpair _
        · rw [Equiv.swap_self]; exact H.one_mem
      have h₁ : Equiv.swap x (Fin.cons (y 0) (Fin.tail x))∈H := by
        convert ht (x 0) (y 0) (Fin.tail x) using 1
        all_goals try with_reducible_and_instances rfl
        rw [Fin.cons_self_tail]
      have h₂ := hchild (y 0) (Equiv.swap (Fin.tail x) (Fin.tail y))
      rw [childInjection_swap,Fin.cons_self_tail] at h₂
      exact SubmonoidClass.swap_mem_trans H h₁ h₂
    rw [eq_top_iff,←Equiv.Perm.closure_isSwap,Subgroup.closure_le]
    rintro _ ⟨x,y,_,rfl⟩
    exact hswap x y

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0 < sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

end Thorp

end ThorpNine.Tail

end OAI
end


