-- Prove2me | Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc_PartA
-- name    : MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc_PartA
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:58:32.558184+00:00
-- url     : https://prove2.me/theorems/ff288cc7-268f-42d3-9d5e-2ef86751c3e7
-- title:
--   MarkovProcess: MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc_PartA
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelConcatenation_cb54f8d1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory


noncomputable section

namespace MixedPastFuture

/-- Past labels occurring in a finite mixed-coordinate set, viewed as dense absolute times. -/
def pastFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  I.toLeft.map
    ⟨(fun r ↦ r.1), fun _ _ h ↦ Subtype.ext h⟩

/-- Future labels occurring in a finite mixed-coordinate set. -/
def futureFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  I.toRight

@[simp]
theorem mem_pastFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : DenseTime) :
    r ∈ pastFinset S I ↔ ∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I := by
  rw [pastFinset, Finset.mem_map]
  constructor
  · rintro ⟨t, ht, htr⟩
    subst r
    refine ⟨t.property, ?_⟩
    exact Finset.mem_toLeft.mp ht
  · rintro ⟨hrS, hrI⟩
    exact ⟨⟨r, hrS⟩, Finset.mem_toLeft.mpr hrI, rfl⟩

@[simp]
theorem mem_futureFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (r : DenseTime) :
    r ∈ futureFinset S I ↔ Sum.inr r ∈ I := by
  exact Finset.mem_toRight

/-- The finite set of absolute dense times observed by a mixed past/future coordinate set. -/
def absoluteFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Finset DenseTime :=
  pastFinset S I ∪ DenseTime.addFinset S (futureFinset S I)

@[simp]
theorem mem_absoluteFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : DenseTime) :
    r ∈ absoluteFinset S I ↔
      (∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I) ∨
        ∃ t ∈ futureFinset S I, S + t = r := by
  rw [absoluteFinset, Finset.mem_union, mem_pastFinset, DenseTime.mem_addFinset]

/-- Send a mixed label to the absolute dense time which it observes.  This map need not be
injective: the terminal past label and future zero both map to `S`. -/
def absoluteTime (S : DenseTime) : Set.Iic S ⊕ DenseTime → DenseTime
  | Sum.inl r => r.1
  | Sum.inr t => S + t

@[simp]
theorem p2m_embedded_f8a0df28432e1302 (S : DenseTime) (r : Set.Iic S) :
    absoluteTime S (Sum.inl r) = r := rfl

@[simp]
theorem p2m_embedded_708732222cb3c3d3 (S t : DenseTime) :
    absoluteTime S (Sum.inr t) = S + t := rfl

@[simp]
theorem p2m_embedded_c782c32d3cf028e6 (S : DenseTime) :
    absoluteTime S (Sum.inl ⟨S, show S ≤ S from le_rfl⟩) =
      absoluteTime S (Sum.inr 0) := by
  simp only [_root_.MarkovProcess.MixedPastFuture.p2m_embedded_f8a0df28432e1302, _root_.MarkovProcess.MixedPastFuture.p2m_embedded_708732222cb3c3d3, add_zero]

/-- Every label in `I` has its absolute time in `absoluteFinset S I`. -/
def absoluteIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    absoluteFinset S I := by
  refine ⟨absoluteTime S i, ?_⟩
  cases hi : i.1 with
  | inl r =>
    have hir : Sum.inl r ∈ I := by simpa only [hi] using i.property
    change r.1 ∈ pastFinset S I ∪ DenseTime.addFinset S (futureFinset S I)
    apply Finset.mem_union_left
    rw [pastFinset, Finset.mem_map]
    exact ⟨r, Finset.mem_toLeft.mpr hir, rfl⟩
  | inr t =>
    have hit : Sum.inr t ∈ I := by simpa only [hi] using i.property
    apply Finset.mem_union_right
    rw [DenseTime.mem_addFinset]
    exact ⟨t, Finset.mem_toRight.mpr hit, rfl⟩

@[simp]
theorem p2m_embedded_db35525d22a491da (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    (absoluteIndex S I i : DenseTime) = absoluteTime S i := rfl

/-- The physical nonnegative-real times corresponding to a finite mixed-coordinate set. -/
def absolutePhysicalFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (absoluteFinset S I)

/-- The physical-time coordinate selected by a mixed label. -/
def absolutePhysicalIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    absolutePhysicalFinset S I :=
  DenseTime.physicalSetEquiv (absoluteFinset S I) (absoluteIndex S I i)

@[simp]
theorem absolutePhysicalIndex_val (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    (absolutePhysicalIndex S I i : NNReal) =
      DenseTime.castOrderEmbedding (absoluteTime S i) := rfl

/-- Pull physical absolute-time coordinates back to their mixed labels.  This merely duplicates a
coordinate when past terminal time and future zero both occur. -/
def pullbackAbsolutePhysical {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinset S I → alpha) : I → alpha :=
  fun i ↦ path (absolutePhysicalIndex S I i)

@[simp]
theorem p2m_embedded_795bc4de6d9bacdd {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinset S I → alpha) (i : I) :
    pullbackAbsolutePhysical S I path i = path (absolutePhysicalIndex S I i) := rfl

variable {alpha : Type*} [MeasurableSpace alpha]

/-- Pullback from absolute physical coordinates to mixed labels is measurable. -/
theorem measurable_pullbackAbsolutePhysical (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (pullbackAbsolutePhysical (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (absolutePhysicalIndex S I i)

end MixedPastFuture

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The rational past through `S` and the rational coordinates of the future shifted at `S`,
combined into a single sum-indexed path. -/
def mixedPastShiftedCoordinates (S : DenseTime) (omega : ContinuousPath alpha) :
    Set.Iic S ⊕ DenseTime → alpha
  | Sum.inl r => omega (DenseTime.castOrderEmbedding r)
  | Sum.inr t => denseRestriction (shift (DenseTime.castOrderEmbedding S) omega) t

@[simp]
theorem p2m_embedded_e081204883f3c84a (S : DenseTime) (omega : ContinuousPath alpha)
    (r : Set.Iic S) :
    mixedPastShiftedCoordinates S omega (Sum.inl r) =
      omega (DenseTime.castOrderEmbedding r) := rfl

@[simp]
theorem mixedPastShiftedCoordinates_inr (S t : DenseTime) (omega : ContinuousPath alpha) :
    mixedPastShiftedCoordinates S omega (Sum.inr t) =
      omega (DenseTime.castOrderEmbedding (S + t)) := by
  simp only [mixedPastShiftedCoordinates, denseRestriction_apply, shift_apply,
    DenseTime.castOrderEmbedding_add]

/-- Mixed shifted coordinates depend only on the corresponding absolute dense time. -/
theorem mixedPastShiftedCoordinates_eq_absoluteTime (S : DenseTime)
    (omega : ContinuousPath alpha) (i : Set.Iic S ⊕ DenseTime) :
    mixedPastShiftedCoordinates S omega i =
      omega (DenseTime.castOrderEmbedding (MixedPastFuture.absoluteTime S i)) := by
  rcases i with r | t
  · rfl
  · exact mixedPastShiftedCoordinates_inr S t omega

/-- Restricting the mixed rational past and shifted future is evaluation on the one finite set of
absolute physical times followed by the canonical (possibly noninjective) coordinate pullback. -/
theorem restrict_mixedPastShiftedCoordinates (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (omega : ContinuousPath alpha) :
    I.restrict (mixedPastShiftedCoordinates S omega) =
      MixedPastFuture.pullbackAbsolutePhysical S I
        (fun t : MixedPastFuture.absolutePhysicalFinset S I ↦ omega t) := by
  funext i
  change mixedPastShiftedCoordinates S omega i =
    omega (MixedPastFuture.absolutePhysicalIndex S I i)
  rw [mixedPastShiftedCoordinates_eq_absoluteTime]
  exact congrArg omega (MixedPastFuture.absolutePhysicalIndex_val S I i).symm

variable [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



end ContinuousPath
end

end MixedPastFutureCoordinates

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MixedPastFuture

noncomputable section

private theorem sort_union_eq_append {beta : Type*} [LinearOrder beta]
    (A B : Finset beta) (hAB : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (A ∪ B).sort = A.sort ++ B.sort := by
  apply (A ∪ B).sortedLT_sort.eq_of_mem_iff
  · rw [List.sortedLT_iff_pairwise, List.pairwise_append]
    exact ⟨A.sortedLT_sort.pairwise, B.sortedLT_sort.pairwise, fun a ha b hb ↦
      hAB a ((A.mem_sort (· ≤ ·)).mp ha) b ((B.mem_sort (· ≤ ·)).mp hb)⟩
  · intro x
    simp only [Finset.mem_sort, Finset.mem_union, List.mem_append]

/-- Past observation times with the cut inserted, whether or not the mixed labels observe it. -/
def pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  pastFinset S I ∪ {S}

@[simp]
theorem mem_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (r : DenseTime) :
    r ∈ pastWithTerminalFinset S I ↔
      (∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I) ∨ r = S := by
  simp only [pastWithTerminalFinset, Finset.mem_union, mem_pastFinset,
    Finset.mem_singleton]

/-- Strictly positive elapsed future times.  Future zero is represented by the terminal past
coordinate instead of a second coordinate in the ordered concatenation. -/
def positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  (futureFinset S I).filter (0 < ·)

@[simp]
theorem mem_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (t : DenseTime) :
    t ∈ positiveFutureFinset S I ↔ Sum.inr t ∈ I ∧ 0 < t := by
  simp only [positiveFutureFinset, Finset.mem_filter, mem_futureFinset]

/-- The absolute observation set after inserting the cut. -/
def absoluteFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  absoluteFinset S I ∪ {S}

/-- The cut-augmented absolute set is the union of the augmented past and the translate of the
strictly positive future.  Thus future zero creates no second ordered coordinate. -/
theorem absoluteFinsetWithTerminal_eq (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absoluteFinsetWithTerminal S I =
      pastWithTerminalFinset S I ∪ DenseTime.addFinset S (positiveFutureFinset S I) := by
  ext r
  simp only [absoluteFinsetWithTerminal, Finset.mem_union, mem_absoluteFinset,
    Finset.mem_singleton, mem_pastWithTerminalFinset, DenseTime.mem_addFinset,
    mem_positiveFutureFinset]
  constructor
  · rintro ((hp | ⟨t, htI, htr⟩) | hrS)
    · exact Or.inl (Or.inl hp)
    · by_cases ht0 : t = 0
      · exact Or.inl (Or.inr (by simpa only [ht0, add_zero] using htr.symm))
      · exact Or.inr ⟨t,
          ⟨(mem_futureFinset S I t).mp htI, bot_lt_iff_ne_bot.mpr ht0⟩, htr⟩
    · exact Or.inl (Or.inr hrS)
  · rintro ((hp | hrS) | ⟨t, ⟨htI, _⟩, htr⟩)
    · exact Or.inl (Or.inl hp)
    · exact Or.inr hrS
    · exact Or.inl (Or.inr ⟨t, (mem_futureFinset S I t).mpr htI, htr⟩)

theorem le_terminal_of_mem_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) {r : DenseTime}
    (hr : r ∈ pastWithTerminalFinset S I) : r ≤ S := by
  rcases (mem_pastWithTerminalFinset S I r).mp hr with ⟨h, _⟩ | rfl
  · exact h
  · exact le_rfl

theorem terminal_lt_of_mem_add_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) {r : DenseTime}
    (hr : r ∈ DenseTime.addFinset S (positiveFutureFinset S I)) : S < r := by
  obtain ⟨t, ht, rfl⟩ := (DenseTime.mem_addFinset S (positiveFutureFinset S I) r).mp hr
  exact lt_add_of_pos_right S ((mem_positiveFutureFinset S I t).mp ht).2

/-- The two sides of the cut are disjoint after future zero has been represented by the cut. -/
theorem disjoint_pastWithTerminalFinset_add_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Disjoint (pastWithTerminalFinset S I)
      (DenseTime.addFinset S (positiveFutureFinset S I)) := by
  rw [Finset.disjoint_left]
  intro r hrPast hrFuture
  exact (not_lt_of_ge (le_terminal_of_mem_pastWithTerminalFinset S I hrPast))
    (terminal_lt_of_mem_add_positiveFutureFinset S I hrFuture)

/-- Cardinality splits as strict future plus cut-augmented past.  The order matches the
`n + (m + 1)` convention of finite-time concatenation. -/
theorem card_absoluteFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (absoluteFinsetWithTerminal S I).card =
      (positiveFutureFinset S I).card + (pastWithTerminalFinset S I).card := by
  rw [absoluteFinsetWithTerminal_eq,
    Finset.card_union_of_disjoint
      (disjoint_pastWithTerminalFinset_add_positiveFutureFinset S I),
    DenseTime.addFinset, Finset.card_map, Nat.add_comm]

/-- Number of past coordinates strictly before the final slot occupied by the cut. -/
def pastPredecessorCard (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : ℕ :=
  (pastWithTerminalFinset S I).card - 1

theorem card_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (pastWithTerminalFinset S I).card = pastPredecessorCard S I + 1 := by
  symm
  exact Nat.sub_add_cancel
    (Finset.one_le_card.mpr ⟨S,
      Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩)

/-- Physical-time version of the cut-augmented absolute set. -/
def absolutePhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (absoluteFinsetWithTerminal S I)

/-- Physical coordinates of the cut-augmented past. -/
def pastPhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (pastWithTerminalFinset S I)

/-- Absolute physical coordinates of the strictly positive future. -/
def positiveFutureAbsolutePhysicalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet
    (DenseTime.addFinset S (positiveFutureFinset S I))

theorem absolutePhysicalFinsetWithTerminal_eq_union (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absolutePhysicalFinsetWithTerminal S I =
      pastPhysicalFinsetWithTerminal S I ∪ positiveFutureAbsolutePhysicalFinset S I := by
  simp only [absolutePhysicalFinsetWithTerminal, absoluteFinsetWithTerminal_eq,
    pastPhysicalFinsetWithTerminal, positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.map_union]

theorem pastPhysical_lt_positiveFutureAbsolutePhysical (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    ∀ a ∈ pastPhysicalFinsetWithTerminal S I,
      ∀ b ∈ positiveFutureAbsolutePhysicalFinset S I, a < b := by
  intro a ha b hb
  rw [pastPhysicalFinsetWithTerminal,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ha
  rw [positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at hb
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact DenseTime.castOrderEmbedding.strictMono
    (lt_of_le_of_lt (le_terminal_of_mem_pastWithTerminalFinset S I hr)
      (terminal_lt_of_mem_add_positiveFutureFinset S I ht))

theorem card_absolutePhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (absolutePhysicalFinsetWithTerminal S I).card =
      (positiveFutureFinset S I).card + (pastPredecessorCard S I + 1) := by
  rw [absolutePhysicalFinsetWithTerminal,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
    card_absoluteFinsetWithTerminal, card_pastWithTerminalFinset]

/-- Reindex the cut cardinality by the cardinality of the augmented absolute physical set. -/
def cutOrderEmbedding (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Fin ((positiveFutureFinset S I).card + (pastPredecessorCard S I + 1)) ↪o
      Fin (absolutePhysicalFinsetWithTerminal S I).card :=
  (Fin.castOrderIso (card_absolutePhysicalFinsetWithTerminal S I).symm).toOrderEmbedding

/-- Increasing physical times of the cut-augmented mixed set, cast to the cardinal convention
expected by finite-time concatenation. -/
def cutOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes
      ((positiveFutureFinset S I).card + (pastPredecessorCard S I + 1)) :=
  (cutOrderEmbedding S I).trans
    (SubMarkovKernelSemigroup.finiteSetTimes (absolutePhysicalFinsetWithTerminal S I))

/-- Sorted physical coordinates of the augmented past, with its cardinality written as a
successor. -/
def cutPastOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes (pastPredecessorCard S I + 1) :=
  (Fin.castOrderIso (by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset])).toOrderEmbedding.trans
    (SubMarkovKernelSemigroup.finiteSetTimes (pastPhysicalFinsetWithTerminal S I))

/-- Sorted physical elapsed times of the strictly positive future. -/
def positiveFutureOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes (positiveFutureFinset S I).card :=
  (Fin.castOrderIso (by
    rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map])).toOrderEmbedding.trans
    (SubMarkovKernelSemigroup.finiteSetTimes
      (SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)))

/-- The initial block of the sorted augmented absolute times is exactly the augmented past. -/
theorem p2m_embedded_b2ac0c93e582fa0b (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) =
      cutPastOrderedPhysicalTimes S I := by
  apply DFunLike.ext _ _
  intro i
  change
    (absolutePhysicalFinsetWithTerminal S I).orderEmbOfFin
      (card_absolutePhysicalFinsetWithTerminal S I)
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card i)) =
      (pastPhysicalFinsetWithTerminal S I).orderEmbOfFin
        (by rw [pastPhysicalFinsetWithTerminal,
          SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
          card_pastWithTerminalFinset]) i
  have hsort : (absolutePhysicalFinsetWithTerminal S I).sort =
      (pastPhysicalFinsetWithTerminal S I).sort ++
        (positiveFutureAbsolutePhysicalFinset S I).sort := by
    rw [absolutePhysicalFinsetWithTerminal_eq_union]
    exact sort_union_eq_append _ _
      (pastPhysical_lt_positiveFutureAbsolutePhysical S I)
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [hsort]
  have hcardPast : (pastPhysicalFinsetWithTerminal S I).card = pastPredecessorCard S I + 1 := by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  have hb : i.val < (pastPhysicalFinsetWithTerminal S I).sort.length := by
    rw [Finset.length_sort, hcardPast]
    exact i.isLt
  exact List.getElem_append_left hb

theorem p2m_embedded_dd9fcb00834a4bf8 (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    cutPastOrderedPhysicalTimes S I (Fin.last (pastPredecessorCard S I)) =
      DenseTime.castOrderEmbedding S := by
  let A := pastPhysicalFinsetWithTerminal S I
  have hcard : A.card = pastPredecessorCard S I + 1 := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  change A.orderEmbOfFin hcard (Fin.last (pastPredecessorCard S I)) = _
  have hi : Fin.last (pastPredecessorCard S I) =
      ⟨pastPredecessorCard S I + 1 - 1,
        Nat.sub_lt (Nat.succ_pos _) Nat.zero_lt_one⟩ := by
    apply Fin.ext
    simp only [Fin.last, Nat.add_sub_cancel_right]
  rw [hi]
  rw [Finset.orderEmbOfFin_last hcard (Nat.succ_pos _)]
  have hS : DenseTime.castOrderEmbedding S ∈ A := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
    exact ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S), rfl⟩
  have hA : A.Nonempty := ⟨DenseTime.castOrderEmbedding S, hS⟩
  apply (Finset.max'_eq_iff (s := A) (H := hA)
    (DenseTime.castOrderEmbedding S)).mpr
  constructor
  · exact hS
  · intro a ha
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    exact DenseTime.castOrderEmbedding.monotone
      (le_terminal_of_mem_pastWithTerminalFinset S I hr)

theorem cutOrderedPhysicalTimes_future_mem (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (i : Fin (positiveFutureFinset S I).card) :
    cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1) i)) ∈
      positiveFutureAbsolutePhysicalFinset S I := by
  change
    (absolutePhysicalFinsetWithTerminal S I).orderEmbOfFin
      (card_absolutePhysicalFinsetWithTerminal S I)
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.natAdd (pastPredecessorCard S I + 1) i)) ∈ _
  rw [Finset.orderEmbOfFin_apply]
  have hsort : (absolutePhysicalFinsetWithTerminal S I).sort =
      (pastPhysicalFinsetWithTerminal S I).sort ++
        (positiveFutureAbsolutePhysicalFinset S I).sort := by
    rw [absolutePhysicalFinsetWithTerminal_eq_union]
    exact sort_union_eq_append _ _
      (pastPhysical_lt_positiveFutureAbsolutePhysical S I)
  simp only [hsort]
  let k := pastPredecessorCard S I + 1 + i.val
  change
    (((pastPhysicalFinsetWithTerminal S I).sort ++
      (positiveFutureAbsolutePhysicalFinset S I).sort)[k]'(by
          dsimp only [k]
          simp only [List.length_append, Finset.length_sort,
            pastPhysicalFinsetWithTerminal,
            positiveFutureAbsolutePhysicalFinset,
            SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
            DenseTime.addFinset, Finset.card_map, card_pastWithTerminalFinset]
          exact Nat.add_lt_add_left i.isLt _))
      ∈ positiveFutureAbsolutePhysicalFinset S I
  rw [List.getElem_append_right (h₁ := by
    rw [Finset.length_sort, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
    dsimp only [k]
    omega)]
  apply (Finset.mem_sort (r := (· ≤ ·))).mp
  exact List.getElem_mem _

/-- The final block, shifted back by the cut, is exactly the sorted strictly positive relative
future. -/
theorem p2m_embedded_0d141d3b4a54a0f0 (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes.relativeFinalSegment
        (cutOrderedPhysicalTimes S I) =
      positiveFutureOrderedPhysicalTimes S I := by
  let F := SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)
  have hcard : F.card = (positiveFutureFinset S I).card := by
    simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map]
  change FiniteOrderedTimes.relativeFinalSegment
      (cutOrderedPhysicalTimes S I) = F.orderEmbOfFin hcard
  apply Finset.orderEmbOfFin_unique' hcard
  intro i
  have hcut : cutOrderedPhysicalTimes S I
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card
          (Fin.last (pastPredecessorCard S I)))) =
      DenseTime.castOrderEmbedding S := by
    change FiniteOrderedTimes.initialSegment
      (cutOrderedPhysicalTimes S I) (Fin.last (pastPredecessorCard S I)) = _
    rw [_root_.MarkovProcess.MixedPastFuture.p2m_embedded_b2ac0c93e582fa0b, _root_.MarkovProcess.MixedPastFuture.p2m_embedded_dd9fcb00834a4bf8]
  have hfut := cutOrderedPhysicalTimes_future_mem S I i
  rw [positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at hfut
  obtain ⟨u, hu, hu_eq⟩ := hfut
  obtain ⟨t, ht, hut⟩ :=
    (DenseTime.mem_addFinset S (positiveFutureFinset S I) u).mp hu
  subst u
  simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
  refine ⟨t, ht, ?_⟩
  rw [FiniteOrderedTimes.relativeFinalSegment_apply,
    hcut, ← hu_eq]
  change DenseTime.castOrderEmbedding t =
    DenseTime.castOrderEmbedding (S + t) - DenseTime.castOrderEmbedding S
  rw [DenseTime.castOrderEmbedding_add, add_tsub_cancel_left]

/-- Position of an augmented-past coordinate in the initial ordered block. -/
def pastCutOrderIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : pastWithTerminalFinset S I) : Fin (pastPredecessorCard S I + 1) :=
  Fin.cast (by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset])
    (((pastPhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))



















variable {alpha : Type*}





variable [MeasurableSpace alpha]



















end
end MixedPastFuture

namespace SubMarkovKernelSemigroup
namespace IsConservative





end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutCoordinates

section MixedPastFutureCutFactorization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace SubMarkovKernelSemigroup
namespace IsConservative



end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutFactorization

end MarkovProcess


