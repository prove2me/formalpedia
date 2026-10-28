-- Prove2me | Definitions.Def_OAIQ060R004
-- name    : OAIQ060R004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:54:10.814807+00:00
-- url     : https://prove2.me/theorems/5b5aba0a-020c-4a94-995e-b85eae3adc36
-- title:
--   Definitions bundle OAIQ060R004 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 100 declarations of OpenAI's Lean: 57 definitions, 1 inductive type or structure and 42 theorems. The definitions and types are `OAI.SharpRamseyFive.Marking.allWindowEncoded`, `OAI.SharpRamseyFive.Marking.allWindowExperiment`, `OAI.SharpRamseyFive.Marking.allWindowFailure`, `OAI.SharpRamseyFive.Marking.allWindowLevelLaw`, `OAI.SharpRamseyFive.Marking.allWindowPositions`, `OAI.SharpRamseyFive.Marking.arlIDE`, `OAI.SharpRamseyFive.Marking.classDomain`, `OAI.SharpRamseyFive.Marking.classPrepared`, `OAI.SharpRamseyFive.Marking.hcrIDE`, `OAI.SharpRamseyFive.Marking.highCollision`, `OAI.SharpRamseyFive.Marking.highThreeGood`, `OAI.SharpRamseyFive.Marking.orderedHighCollision`, `OAI.SharpRamseyFive.Marking.rcrIDE`, `OAI.SharpRamseyFive.Marking.smallFailureIDE`, `OAI.SharpRamseyFive.Marking.survivingEncoded`, `OAI.SharpRamseyFive.Marking.survivingExperiment`, `OAI.SharpRamseyFive.Marking.survivingLevelLaw`, `OAI.SharpRamseyFive.Marking.survivingTargetFailure`, `OAI.SharpRamseyFive.Metadata.encodeLists`, `OAI.SharpRamseyFive.Metadata.encodeTraining`, `OAI.SharpRamseyFive.ProjectiveIncidence.OriginalNodeReady`, `OAI.SharpRamseyFive.ProjectiveIncidence.guardedNodeEncoded`, `OAI.SharpRamseyFive.ProjectiveIncidence.guardedNodeLaw`, `OAI.SharpRamseyFive.ProjectiveIncidence.lowHits`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNodeEncoded`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotCapsAt`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotContextAt`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotSuccessAt`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeEncoded`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedTargetFailure`, `OAI.SharpRamseyFive.ProjectiveIncidence.variableTreeEncoded`, `OAI.SharpRamseyFive.ProjectiveIncidence.weightOnPencil`, `OAI.SharpRamseyFive.ScoreRegularity.irregular`, `OAI.SharpRamseyFive.SelectedTuple.LevelWindowSample`, `OAI.SharpRamseyFive.SelectedTuple.PolarState`, `OAI.SharpRamseyFive.SelectedTuple.PolarState.of`, `OAI.SharpRamseyFive.SelectedTuple.Prepared.mono`, `OAI.SharpRamseyFive.SelectedTuple.Prepared.reindex`, `OAI.SharpRamseyFive.SelectedTuple.Prepared.swap`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream.reindex` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `RamseyFive_Bounds_UpperSet`, `RamseyFive_Decoding_MetadataCodec`, `RamseyFive_Entropy_ClippedWeight`, `RamseyFive_Entropy_DescriptionClean`, `RamseyFive_Entropy_MarkedActualBudget`, `RamseyFive_Entropy_PreparedWindows`, `RamseyFive_Entropy_Rectangle`, `RamseyFive_Entropy_SelectedRestriction`, `RamseyFive_Entropy_WeightedLowHits`, `RamseyFive_Geometry_FiniteNode`, `RamseyFive_Geometry_GuardedNodeEncoder`, `RamseyFive_Geometry_GuardedNodeSent`, `RamseyFive_Geometry_OrderedTargetRetention`, `RamseyFive_Geometry_OrientedPivotTree`, `RamseyFive_Geometry_OrientedTreeDomains`, `RamseyFive_Geometry_ProjectiveEquiv`, `RamseyFive_Geometry_TargetCaps`, `RamseyFive_Geometry_TreeFailure`, `RamseyFive_Geometry_TreeTrims`, `RamseyFive_Iteration_HighWindowStage`, `RamseyFive_Iteration_TerminalStream`, `RamseyFive_Iteration_WindowStage`, `RamseyFive_Marking_ChooseLevel`, `RamseyFive_Marking_ClassPrepared`, `RamseyFive_Marking_ClassifiedStream`, `RamseyFive_Marking_HighChosenRound`, `RamseyFive_Marking_HighLowConflict`, `RamseyFive_Marking_MarkedStreamExtraction`, `RamseyFive_Marking_OrderedHighConflict`, `RamseyFive_Marking_ReciprocalSharpRound`, `RamseyFive_Marking_ScanChoice`, `RamseyFive_Marking_ScanRecord`, `RamseyFive_Marking_ScanRecordPresent`, `RamseyFive_Marking_SurvivingWindowCode`, `RamseyFive_Marking_TwoScan`, `RamseyFive_Marking_TwoScanContext`, `RamseyFive_Marking_WindowDeletionCount`, `RamseyFive_Marking_WindowSmallFailure`, `RamseyFive_Streams_HighSampleContradiction`, `RamseyFive_Streams_HighThreePrepared`, `RamseyFive_Streams_MiddleStream`, `RamseyFive_Streams_PreparedStream`, `RamseyFive_Trees_HistoryPrivateStream`, `RamseyFive_Trees_Windows`.
--
--   **Imports.** It imports the bundles `OAIQ060R002` and `OAIQ060R003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss`, `OAI.SharpRamseyFive.Marking.eventually_window_failure_small`, `OAI.SharpRamseyFive.Marking.exists_high_three_round`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_allWindow_cost`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_guarded_node_cost`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original`, `OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment`, `OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_ambient_tail_cases`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail`, `OAI.SharpRamseyFive.ScoreGeometry.low_original_tail`, `OAI.SharpRamseyFive.SelectedTuple.eventually_iter_produce`, `OAI.SharpRamseyFive.SelectedTuple.high_prepared_round` and `OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp`; the proofs of `OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss`, `OAI.SharpRamseyFive.Marking.eventually_window_failure_small`, `OAI.SharpRamseyFive.Marking.exists_high_three_round`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_allWindow_cost`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_guarded_node_cost`, `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original`, `OAI.SharpRamseyFive.ScoreGeometry.actual_high_radial_moment`, `OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_ambient_tail_cases`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_small_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail`, `OAI.SharpRamseyFive.ScoreGeometry.low_original_tail`, `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage`, `OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible`, `OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible`, `OAI.SharpRamseyFive.SelectedTuple.eventually_iter_produce`, `OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch`, `OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage`, `OAI.SharpRamseyFive.SelectedTuple.high_prepared_round`, `OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp` and `OAI.SharpRamseyFive.primeConstruction`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_UpperSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma nextState_mono (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b y : ℙ K (Dual K V)) : W y≤ nextState W a b y := by
  unfold nextState
  split_ifs
  · exact le_sup_right
  · exact le_rfl

lemma nextState_upper_subset (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (l : ℕ) :
    upperSet (nextState W a b) l⊆upperSet W l := by
  intro y hy
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact (Submodule.finrank_mono (nextState_mono W a b y)).trans (Finset.mem_filter.mp hy).2

lemma leaves_upper (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b y : ℙ K (Dual K V)) (l : ℕ)
    (hlevel : y∈levelSet W l) (hhit : Incident a y) (hnew : ¬b.submodule≤W y) :
    y∈upperSet W l ∧ y∉upperSet (nextState W a b) l := by
  have hl := (Finset.mem_filter.mp hlevel).2
  have hr : l<finrank K (nextState W a b y) := by
    rw [←hl,nextState,ite_eq_left hhit]
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne le_sup_right (fun h => hnew (h ▸ le_sup_left))
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.le⟩
  · exact fun hy => (not_lt_of_ge (Finset.mem_filter.mp hy).2) hr

theorem expensive_contraction (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (l : ℕ) (q : ℝ) (hq : 0<q)
    (hmax : (upperSet W l).card≤5*(levelSet W l).card)
    (hpoor : ((levelSet W l).card:ℝ)/(8*q)≤
      (((levelSet W l).filter fun y => Incident a y).card:ℝ))
    (hpop : (((levelSet W l).filter fun y => b.submodule≤W y).card:ℝ)≤
      ((levelSet W l).card:ℝ)/(16*q)) :
    ((upperSet (nextState W a b) l).card:ℝ)≤
      (1-1/(80*q))*((upperSet W l).card:ℝ) := by
  let U:=upperSet W l
  let U':=upperSet (nextState W a b) l
  let Z:=levelSet W l
  let H:=Z.filter fun y => Incident a y
  let B:=Z.filter fun y => b.submodule≤W y
  have hsub : H⊆(U\U')∪B := by
    intro y hy
    by_cases hb : y∈B
    · exact Finset.mem_union_right _ hb
    · have hyZ := (Finset.mem_filter.mp hy).1
      have hh := (Finset.mem_filter.mp hy).2
      have hn : ¬b.submodule≤W y := fun h => hb (Finset.mem_filter.mpr ⟨hyZ,h⟩)
      obtain ⟨hu,hu'⟩:=leaves_upper W a b y l hyZ hh hn
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu,hu'⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have husub : U'⊆U := nextState_upper_subset W a b l
  have hdiff : (U\U').card=U.card-U'.card := Finset.card_sdiff_of_subset husub
  have hule := Finset.card_le_card husub
  have hcount : (H.card:ℝ)≤(U.card:ℝ)-U'.card+B.card := by
    have h := hc
    rw [hdiff] at h
    exact_mod_cast h
  have hzU : (U.card:ℝ)≤5*Z.card := by exact_mod_cast hmax
  change (Z.card:ℝ)/(8*q)≤(H.card:ℝ) at hpoor
  change (B.card:ℝ)≤(Z.card:ℝ)/(16*q) at hpop
  change (U'.card:ℝ)≤(1-1/(80*q))*(U.card:ℝ)
  have hid : (Z.card:ℝ)/(8*q)=2*((Z.card:ℝ)/(16*q)) := by field_simp; ring
  have huZ : (U.card:ℝ)/(80*q)≤(Z.card:ℝ)/(16*q) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  rw [hid] at hpoor
  have heq : (1-1/(80*q))*(U.card:ℝ)=U.card-(U.card:ℝ)/(80*q) := by ring
  rw [heq]
  linarith

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_MetadataCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata

section
open Module GreedyTraining MeasurePublicTable ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]

noncomputable def encodeLists {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) : TwoListCode V h p B :=
  (fun i=>FlatAtlas.flatCode 5 hd (H i), fun i=>FlatAtlas.flatCode 5 hd (P i),
    ⟨S.card,Nat.lt_succ_of_le hB⟩,
    fun i=>⟨(S∩publicRegion (fun j=>flatPoints (H j)) i).card,
      Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_left).trans hB)⟩,
    fun i=>⟨(S∩publicRegion (fun j=>flatPoints (P j)) i).card,
      Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_left).trans hB)⟩,
    fun i=>⟨((S∩publicRegion (fun j=>flatPoints (H j)) i.1)∩
      (S∩publicRegion (fun j=>flatPoints (P j)) i.2)).card,
      Nat.lt_succ_of_le ((Finset.card_le_card (Finset.inter_subset_left.trans Finset.inter_subset_left)).trans hB)⟩)

end

open Module GreedyTraining ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)]

noncomputable def encodeTraining {h p : ℕ} (σ : ℝ) (hd : finrank K V≤5)
    (hh : h≤listCap σ) (hp : p≤listCap σ) (hj : h*p≤productCap σ)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V) (S : Finset (ℙ K V)) :
    TrainingCode V (listCap σ) (productCap σ) (Nat.card V) :=
  ⟨⟨(⟨h,Nat.lt_succ_of_le hh⟩,⟨p,Nat.lt_succ_of_le hp⟩),hj⟩,
    encodeLists hd H P S (projective_card_le_vectors S)⟩

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]

variable [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

noncomputable def weightOnPencil (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) : ℝ :=
  ∑ b, incidenceEntry a b * w b

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def irregular {d : ℕ} {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (ξ : ℝ) : Finset (ℙ K V) :=
  Finset.univ.filter fun x => ∃ j : Option (Option J),
    scale (K:=K) d S.card*Real.exp ξ < weightOnPencil (clippedWeight S C j) x

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteNode
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def OriginalNodeReady (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) : Prop :=
  δ*A₀.card≤(A₀∩UA).card ∧ δ*B₀.card≤(B₀∩UB).card ∧
    (Nat.card K:ℝ)*incidences A₀ B₀≤τ*A₀.card*B₀.card

noncomputable def guardedNodeLaw (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Fintype V := Fintype.ofFinite _
  letI : Finite (Dual K V) := Module.finite_of_finite K
  letI : Fintype (Dual K V) := Fintype.ofFinite _
  letI : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  exact if hr : OriginalNodeReady A₀ UA B₀ UB δ τ then
    let hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    let hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    let hnA := reverseLength_universal_bound σ hσ hq hd (A₀∩UA) UA hA Finset.inter_subset_right
    let hnB := reverseLength_universal_bound σ hσ hq (show finrank K (Dual K V)≤5 by simpa using hd)
      (B₀∩UB) UB hB Finset.inter_subset_right
    finiteNodeOutput pred (A₀∩UA) UA (B₀∩UB) UB (1000*(Nat.card K)^2)
      ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card) c M
  else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeEncoder
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def guardedNodeEncoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K)) :
    Option (FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Fintype V := Fintype.ofFinite _
  letI : Finite (Dual K V) := Module.finite_of_finite K
  letI : Fintype (Dual K V) := Fintype.ofFinite _
  letI : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  exact if hr : OriginalNodeReady A₀ UA B₀ UB δ τ then
    let hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    let hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    let hnA := reverseLength_universal_bound σ hσ hq hd (A₀∩UA) UA hA Finset.inter_subset_right
    let hnB := reverseLength_universal_bound σ hσ hq (show finrank K (Dual K V)≤5 by simpa using hd)
      (B₀∩UB) UB hB Finset.inter_subset_right
    finiteNodeEncoded pred (A₀∩UA) UA (B₀∩UB) UB (1000*(Nat.card K)^2)
      ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card) c M t
  else none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def orientedGuardedNodeEncoded
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K)) :
    Option (OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t) :=
  if (A₀∩UA).card≤(B₀∩UB).card then
    (guardedNodeEncoded f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1).map Sum.inl
  else
    (guardedNodeEncoded r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
      hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2).map Sum.inr

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedPivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

variable {ι : Type}

noncomputable def orientedPivotTreeEncoded
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) : OrientedPivotTreeMessage f r b ω C :=
  TreeCodec.encoded (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
    (fun i C ω=>orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd (A₀ i) C.1 (B₀ i) C.2
      (hA₀ i) (hB₀ i) c δ τ P hδ ω) b ω C
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ChooseLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K (Dual K V))]

lemma chooseLevel_sublevel (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ)
    (hr : r≤4) :
    (upperSet W (chooseLevel W r)).card≤5*(levelSet W (chooseLevel W r)).card := by
  have hm : upperSet W (chooseLevel W r)⊆upperSet W r := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2.trans (chooseLevel_le W r)⟩
  exact (Finset.card_le_card hm).trans ((chooseLevel_large W r).trans (Nat.mul_le_mul_right _ (by omega)))

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

lemma scan_rank (hdim : finrank K V=5) (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : finrank K (scanState a b q n (b n))≤4 := by
  have hle : scanState a b q n (b n)≤(a n).submodule.dualAnnihilator := by
    apply iSup₂_le
    intro i hi
    split_ifs with hab
    · exact (incident_iff_dualAnnihilator _ _).mp
        (hF i n (Finset.mem_range.mp (scanSet_subset a b q n hi)) hn hab)
    · exact bot_le
  have hr:=Submodule.finrank_mono hle
  have hd:=Subspace.finrank_add_finrank_dualAnnihilator_eq (a n).submodule
  rw [(a n).finrank_submodule,hdim] at hd
  omega

omit [FiniteDimensional K V] in
lemma scan_count (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ) :
    (scanSet a b q N).card=((Finset.range N).filter fun n =>
      Expensive (state a b (scanSet a b q n)) (a n) (b n) q).card := by
  induction N with
  | zero => simp [scanSet]
  | succ N ih =>
    have hn : N∉scanSet a b q N := fun h => (Nat.lt_irrefl N) (Finset.mem_range.mp (scanSet_subset a b q N h))
    rw [scanSet,Finset.range_add_one,Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem hn,Finset.card_insert_of_notMem (by simp),ih]
    · exact ih

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

lemma scanChoice_isSome (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (scanChoice a b q n).isSome ↔
      Expensive (scanState a b q n) (a n) (b n) q := by
  have hl : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5 :=
    (chooseLevel_le _ _).trans_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))
  simp only [scanChoice,dite_eq_left hl]
  split_ifs <;> simp_all

theorem scanSet_card_bound (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (hq : 0<q) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i)) :
    ((scanSet a b q N).card:ℝ)≤800*q*Real.log (1+Fintype.card (ℙ K (Dual K V))) := by
  let S : ℕ → Fin 5 → Finset (ℙ K (Dual K V)) :=
    fun n j => upperSet (scanState a b q n) j.val
  have hm : ∀ n<N,∀ j,S (n+1) j⊆S n j := by
    intro n _ j y hy
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact (Submodule.finrank_mono (scanState_mono a b q n y)).trans (Finset.mem_filter.mp hy).2
  have hc : ∀ n<N,∀ j,scanChoice a b q n=some j →
      (S n j).Nonempty ∧ ((S (n+1) j).card:ℝ)≤(1-1/(80*q))*(S n j).card := by
    intro n hn j hj
    have he : Expensive (scanState a b q n) (a n) (b n) q :=
      (scanChoice_isSome hdim a b q N hF hn).mp (by rw [hj]; rfl)
    have hl : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5 :=
      (chooseLevel_le _ _).trans_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))
    have hjval : j.val=chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n))) := by
      have heq : j=⟨_,hl⟩ := by
        simpa only [scanChoice,ite_eq_left he,dite_eq_left hl,Option.some.injEq] using hj.symm
      exact congrArg Fin.val heq
    let W:=scanState a b q n
    let l:=chooseLevel W (finrank K (W (b n)))
    have hnon:=chooseLevel_nonempty W (b n)
    constructor
    · obtain ⟨y,hy⟩:=hnon
      refine ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      rw [hjval]
      exact (Finset.mem_filter.mp hy).2.le
    · change ((upperSet (scanState a b q (n+1)) j.val).card:ℝ)≤
        (1-1/(80*q))*((upperSet (scanState a b q n) j.val).card:ℝ)
      rw [scanState_update a b q n he,hjval]
      exact expensive_contraction W (a n) (b n) l q hq
        (chooseLevel_sublevel W _ (scan_rank hdim a b q N hF hn)) he.2.le he.1.le
  have hb:=finite_scan_bound S (scanChoice a b q) N (1/(80*q)) (by positivity) hm hc
  have hfilter : ((Finset.range N).filter fun n => (scanChoice a b q n).isSome)=
      (Finset.range N).filter fun n => Expensive (state a b (scanSet a b q n)) (a n) (b n) q := by
    apply Finset.filter_congr
    intro n hn
    exact scanChoice_isSome hdim a b q N hF (Finset.mem_range.mp hn)
  have hzero (j : Fin 5) : S 0 j=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    change finrank K (state a b ∅ y)≤j.val
    rw [state_empty]
    simp
  rw [hfilter,←scan_count] at hb
  simp only [hzero,Finset.card_univ] at hb
  have hsum : (∑ j:Fin 5,Real.log (1+(Fintype.card (ℙ K (Dual K V)):ℝ)))=
      5*Real.log (1+(Fintype.card (ℙ K (Dual K V)):ℝ)) := by simp
  rw [hsum] at hb
  have hid : (1/(80*q))/2=1/(160*q) := by ring
  rw [hid] at hb
  have hh:=mul_le_mul_of_nonneg_right hb (show 0≤160*q by positivity)
  have hz : 160*q≠0 := by positivity
  field_simp at hh
  nlinarith

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K V)] in
lemma rankMask_val (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (rankMask a b q n).val=finrank K (scanState a b q n (b n)) :=
  Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))

variable [Finite K]

omit [Finite K] in

theorem scan_decoding (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (N : ℕ)
    (hflag : ∀ n<N,Incident (a n) (b n))
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) (hc : scanRecord a b (Nat.card K) n=none) :
    (a n,b n)∈cheapDomain (decodeState (scanRecord a b (Nat.card K)) n)
      (rankMask a b (Nat.card K) n) := by
  have he : ¬Expensive (scanState a b (Nat.card K) n) (a n) (b n) (Nat.card K) := by
    intro he
    simp only [scanRecord,ite_eq_left he] at hc
    contradiction
  rw [decode_scanRecord]
  unfold cheapDomain
  rw [rankMask_val hdim a b (Nat.card K) N hF hn,
    ite_eq_left (chooseLevel_nonempty (scanState a b (Nat.card K) n) (b n))]
  exact Finset.mem_union.mpr (cheap_mem_domains a b N hflag hF hn he)

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecordPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V α κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype α] [Fintype κ]

noncomputable local instance instDecidableEqFin_solutions_r708721_1 (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype α] [Fintype κ] in
lemma scanRecord_present (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ) :
    (∑ i : Fin N,present (scanRecord a b q i.val))=(scanSet a b q N).card := by
  rw [Fin.sum_univ_eq_sum_range (fun i => present (scanRecord a b q i)) N,scan_count]
  simp only [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : Expensive (scanState a b q i) (a i) (b i) q
  · rw [scanRecord,ite_eq_left he]
    change Expensive (state a b (scanSet a b q i)) (a i) (b i) q at he
    rw [ite_eq_left he]
    norm_num [present]
  · rw [scanRecord,ite_eq_right he]
    change ¬Expensive (state a b (scanSet a b q i)) (a i) (b i) q at he
    rw [ite_eq_right he]
    norm_num [present]

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

variable {β : Type*} [Nonempty β] {N : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.finiteMarkingDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma expensiveSet_card (f : Fin N → FlagPair K V) (q : ℝ) :
    ((expensiveSet f q).card:ℝ) =
      (scanSet (tupleFirst f) (tupleSecond f) q N).card := by
  rw [←scanRecord_present]
  change _ = ∑ i : Fin N,present (finiteRecord f q i)
  simp_rw [finiteRecord_value]
  have he (i : Fin N) : present (if i∈expensiveSet f q then some (f i) else none) =
      if i∈expensiveSet f q then (1:ℝ) else 0 := by split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp

omit [Fintype (ℙ K V)] in
theorem expensiveSet_bound (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hf : TupleConsistent f) (q : ℝ) (hq : 0<q) :
    ((expensiveSet f q).card:ℝ)≤800*q*Real.log (1+Fintype.card (ℙ K (Dual K V))) := by
  rw [expensiveSet_card]
  exact scanSet_card_bound hdim _ _ q hq N (tupleConsistent_extend hf)

variable [Finite K]

omit [Finite K] in
theorem finite_scan_decoding (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∉expensiveSet f (Nat.card K)) :
    f i∈finiteDomain (finiteRecord f (Nat.card K)) (finiteRank f (Nat.card K)) i := by
  have hr : finiteRecord f (Nat.card K) i=none := by rw [finiteRecord_value,ite_eq_right hi]
  have hh := scan_decoding hdim (tupleFirst f) (tupleSecond f) N
    (tupleIncident_extend hflag) (tupleConsistent_extend hf) i.isLt hr
  simpa only [finiteDomain,finite_decode,finiteRank,tupleFirst,tupleSecond,extendTuple_at] using hh
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
attribute [local instance] OAI.SharpRamseyFive.Marking.twoScanDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

theorem unionExpensive_bound (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hf : TupleConsistent f) (q : ℝ) (hq : 0<q) :
    ((expensiveSet f q ∪ reverseExpensive f q).card:ℝ)≤
      800*q*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))) := by
  have h₁ := expensiveSet_bound hdim f hf q hq
  have h₂ := expensiveSet_bound (K:=K) (V:=Dual K V) (by simpa using hdim)
    (reverseTuple f) (reverseTuple_consistent hf) q hq
  have hc : Fintype.card (ℙ K (Dual K (Dual K V)))=Fintype.card (ℙ K V) :=
    (Fintype.card_congr bidualPoint).symm
  rw [hc] at h₂
  have hu : ((expensiveSet f q ∪ reverseExpensive f q).card:ℝ)≤
      ((expensiveSet f q).card:ℝ)+((reverseExpensive f q).card:ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  rw [reverseExpensive_card] at hu
  nlinarith

end

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance typedScanDecEq_r708721_1 (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] {N : ℕ}

variable [Finite K]
omit [Finite K] in
lemma finite_typed_decoding (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∉expensiveSet f (Nat.card K)) :
    f i∈finiteTypedDomain (finiteRecord f (Nat.card K)) (finiteRank f (Nat.card K))
      (finitePopular f (Nat.card K)) i := by
  have hh := finite_scan_decoding hdim f hflag hf i hi
  unfold finiteDomain cheapDomain at hh
  unfold finiteTypedDomain typedDomain finitePopular
  split_ifs at hh ⊢ with hz hp
  · exact (of_decide_eq_true hp)
  · exact (Finset.mem_union.mp hh).resolve_left (by simpa using hp)
  · exact hh

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
attribute [local instance] OAI.SharpRamseyFive.Marking.concreteMarkingDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}

lemma forwardRecord_marking (f : Fin N → FlagPair K V) :
    forwardRecord (markingMessage f)=finiteRecord f (Nat.card K) := by
  funext i
  simp only [forwardRecord,markingMessage,unionMessage,unionMask,decide_eq_true_eq]
  rw [unionRecord_decode_left id (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f i,finiteRecord_value]
  rfl

variable [Finite K]

omit [Finite K] in
theorem marking_decodes (hdim : finrank K V=5) (f : Fin N → FlagPair K V)
    (hflag : TupleIncident f) (hf : TupleConsistent f) (i : Fin N)
    (hi : i∈unspecified (markingMessage f)) : f i∈markingDomain (markingMessage f) i := by
  have hi' : i∉expensiveSet f (Nat.card K) ∪ reverseExpensive f (Nat.card K) := by
    simpa only [markingMessage,unspecified_unionMessage,Finset.mem_compl] using hi
  have h₁ : i∉expensiveSet f (Nat.card K) := fun h=>hi' (Finset.mem_union_left _ h)
  have h₂ : i.rev∉expensiveSet (reverseTuple f) (Nat.card K) :=
    fun h=>hi' (Finset.mem_union_right _ ((mem_reverseExpensive f _ i).mpr h))
  apply Finset.mem_inter.mpr
  constructor
  · unfold forwardDomain
    rw [forwardRecord_marking]
    simpa only [markingMessage,unionMessage,unionMask,twoScanTypes] using
      finite_typed_decoding hdim f hflag hf i h₁
  · apply Finset.mem_map.mpr
    refine ⟨swapFlag (f i),?_,swapFlag.symm_apply_apply _⟩
    unfold backwardDomain
    rw [backwardRecord_marking]
    simpa only [markingMessage,unionMessage,
      unionMask,twoScanTypes,Fin.rev_rev,reverseTuple] using
        finite_typed_decoding (K:=K) (V:=Dual K V) (by simpa using hdim) (reverseTuple f)
          (reverseTuple_incident hflag) (reverseTuple_consistent hf) i.rev h₂

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScanContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
attribute [local instance] OAI.SharpRamseyFive.Marking.scanContextDecEq
variable {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N : ℕ}

omit [Finite K] in
theorem marking_posterior_domains (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    ∀ x,0<fiber (withMessage p markingMessage) (c,m) x→
      ∀ i∈unspecified m,x i∈markingDomain m i := by
  intro x hx i hi
  obtain ⟨hp,he⟩:=fiber_withMessage_support p markingMessage c m hm x hx
  subst m
  exact marking_decodes hdim x (hf c x hp) (hc c x hp) i hi

lemma marking_posterior_cap (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) (i : Fin N) (hi : i∈unspecified m) :
    entropy (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i))≤
      Real.log (153*(Nat.card K:ℝ)^4) := by
  apply entropy_support_cap
  have hs : support (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i)) ⊆
      markingDomain m i := by
    intro z hz
    have hzpos : 0 < map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i) z :=
      (mem_support _ _).mp hz
    obtain ⟨x,hx,rfl⟩:=map_positive (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i) z hzpos
    exact marking_posterior_domains hdim p hf hc c m hm x hx i hi
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (markingDomain_card hdim m i)

lemma marking_deficit_nonneg (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hf : ∀ c x,0<p (c,x)→TupleIncident x)
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    0≤activeDeficit (fiber (withMessage p markingMessage) (c,m)) (unspecified m)
      (Real.log (153*(Nat.card K:ℝ)^4)) := by
  have hfix := unionMessage_fixedOutside p twoScanTypes
    (fun x=>expensiveSet x (Nat.card K)) (fun x=>reverseExpensive x (Nat.card K)) c m hm
  have hh:=hfix.entropy_le_sum
  have hb : (∑ i∈unspecified m,entropy (map (fiber (withMessage p markingMessage) (c,m)) (fun x=>x i)))≤
      ((unspecified m).card:ℝ)*Real.log (153*(Nat.card K:ℝ)^4) := by
    calc
      _ ≤ ∑ i∈unspecified m,Real.log (153*(Nat.card K:ℝ)^4) :=
        Finset.sum_le_sum fun i hi=>marking_posterior_cap hdim p hf hc c m hm i hi
      _ = _ := by simp
  exact sub_nonneg.mpr (hh.trans hb)

theorem marking_expected_deficit (hdim : finrank K V=5)
    (p : Law (κ×(Fin N→FlagPair K V)))
    (hc : ∀ c x,0<p (c,x)→TupleConsistent x)
    (S : κ→Fin N→Finset (FlagPair K V)) (cap J B L : ℝ) (hcap : 1 ≤ cap)
    (hS : ∀ c i,((S c i).card:ℝ) ≤ cap)
    (hsupp : ∀ c x,0<p (c,x)→∀ i,x i∈S c i)
    (hΔ : 0≤Real.log cap-J) (hent : (N:ℝ)*J-entropy (second p)≤B)
    (hctx : entropy (first p)≤L) :
    mean (first (withMessage p markingMessage))
      (fun z=>activeDeficit (fiber (withMessage p markingMessage) z) (unspecified z.2) J)≤
      B+L+(N:ℝ)*Real.log 800+
      (800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))))*(Real.log cap-J) := by
  have hh:=union_deficit_bound p twoScanTypes (fun x=>expensiveSet x (Nat.card K))
    (fun x=>reverseExpensive x (Nat.card K)) S cap J hcap hS hsupp
  have hmean : mean (second p) (fun x=>((expensiveSet x (Nat.card K)∪reverseExpensive x (Nat.card K)).card:ℝ))≤
      800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
        Real.log (1+Fintype.card (ℙ K V))) := by
    apply (mean_mono_pos (second p) (g:=fun _=>_) _).trans_eq (mean_const _ _)
    intro x hx
    obtain ⟨c,_,hc'⟩:=Finset.sum_pos_iff_of_nonneg (fun c _=>p.nonneg (c,x)) |>.mp hx
    exact unionExpensive_bound hdim x (hc c x hc') _ (by
      exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  have hm:=mul_le_mul_of_nonneg_right hmean hΔ
  simp only [Fintype.card_fin] at hh
  exact hh.trans (by linarith)
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N l : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.markedClassFinDE
local instance markedClassPointDE_r708721_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance markedClassDualDE_r708721_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
lemma markedClassLaw_deficit (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hinc : ∀ c x,0<p (c,x)→TupleIncident x)
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (hl : l≤N) (width : ℝ) (hw : 0≤width) (a : SlotClass)
    (hE : 0<eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a)) :
    mean (first (markedClassLaw hdim p hl width hw a hE))
      (fun c=>(l:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-
        entropy (fiber (markedClassLaw hdim p hl width hw a hE) c))≤
    mean (first (withMessage p markingMessage))
      (fun c=>activeDeficit (fiber (withMessage p markingMessage) c) (unspecified c.2)
        (Real.log (153*(Nat.card K:ℝ)^4)))/
      eventMass (first (withMessage p markingMessage))
        (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) := by
  apply selectedClass_deficit hl (withMessage p markingMessage)
  · intro c hc
    exact marking_deficit_nonneg hdim p hinc hcons c.1 c.2 hc
  · intro c hc
    exact unionMessage_fixedOutside p twoScanTypes (fun x=>expensiveSet x (Nat.card K))
      (fun x=>reverseExpensive x (Nat.card K)) c.1 c.2 hc
  · intro c hc i hi
    exact marking_posterior_cap hdim p hinc hcons c.1 c.2 hc i hi
end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkedStreamExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.streamClassFinDE
local instance streamClassPointDE_r708721_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance streamClassDualDE_r708721_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
lemma classStream_consistent (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→
      TupleIncident ((classStream hdim width hw S ctx hl a hE).tuple z) ∧
      TupleConsistent ((classStream hdim width hw S ctx hl a hE).tuple z) := by
  intro z hz
  have h:=conditionOn_positive S.law _ hE z hz
  constructor
  · intro i
    exact hinc z h.2 _
  · intro i j hij
    exact hcons z h.2 _ _ ((retainedIndices hl _).strictMono hij)

def classDomain (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :=
  markingDomain c.2 (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i)

attribute [local irreducible] unspecified classPositions

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma marked_indices_properties (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V))
    (hc : c∈markedEvent hdim width hw l a) (i : Fin l) :
    selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i∈unspecified c.2 ∧
    markedCode hdim width hw c
      (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i)=a := by
  have hc' : c∈selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a := by
    simpa only [markedEvent] using hc
  exact selectedClassIndices_properties hl (fun c=>unspecified c.2)
    (markedCode hdim width hw) a c hc' i

lemma markedSelected_decodes (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (f : Fin n→FlagPair K V) (ctx : κ)
    (hinc : TupleIncident f) (hcons : TupleConsistent f)
    (hc : (ctx,markingMessage f)∈markedEvent hdim width hw l a) (i : Fin l) :
    let j:=selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a (ctx,markingMessage f) i
    f j∈markingDomain (markingMessage f) j := by
  apply marking_decodes hdim f hinc hcons
  exact (marked_indices_properties hdim width hw hl a (ctx,markingMessage f) hc i).1

lemma classStream_tuple (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) (z : Ω) (i : Fin l) :
    (classStream hdim width hw S ctx hl a hE).tuple z i=
      S.tuple z (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a
        (markedContext ctx S.tuple z) i) := rfl

lemma classStream_event (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) (z : Ω)
    (hz : 0<(classStream hdim width hw S ctx hl a hE).law z) :
    markedContext ctx S.tuple z∈markedEvent hdim width hw l a ∧ 0<S.law z := by
  obtain ⟨he,hp⟩:=conditionOn_positive S.law _ hE z hz
  exact ⟨(mem_eventPreimage _ _ _).mp he,hp⟩

lemma classStream_contains (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→∀ i,
      (classStream hdim width hw S ctx hl a hE).tuple z i∈
        classDomain hdim width hw hl a (markedContext ctx S.tuple z) i := by
  intro z hz i
  obtain ⟨hc,hp⟩:=classStream_event hdim width hw S ctx hl a hE z hz
  rw [classStream_tuple]
  exact markedSelected_decodes hdim width hw hl a (S.tuple z) (ctx z) (hinc z hp) (hcons z hp) hc i

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkedActualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.mabFinDE
local instance mabPDE_r708721_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance mabDDE_r708721_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
theorem actual_marked_deficit (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z))
    (D : κ→Fin n→Finset (FlagPair K V)) (cap B L : ℝ) (hcap : 1 ≤ cap)
    (hD : ∀c i,((D c i).card:ℝ) ≤ cap)
    (hsupp : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hΔ : 0≤Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))
    (hent : (n:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (map S.law S.tuple)≤B)
    (hctx : entropy (map S.law ctx)≤L) :
    let T:=classStream hd width hw S ctx hl a hE
    let p:=pair T.law (markedContext ctx S.tuple) T.tuple
    mean (first p) (fun c=>(l:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (fiber p c))≤
      39*(B+L+(n:ℝ)*Real.log 800+
        expensiveBound K V*(Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))) := by
  let p:=pair S.law ctx S.tuple
  have hpi : ∀c x,0<p (c,x)→TupleIncident x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hinc z hz
  have hpc : ∀c x,0<p (c,x)→TupleConsistent x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hcons z hz
  have hps : ∀c x,0<p (c,x)→∀i,x i∈D c i := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hsupp z hz
  have hb:=marking_expected_deficit hd p hpc D cap (Real.log (153*(Nat.card K:ℝ)^4))
    B L hcap hD hps hΔ (by simpa only [p,second_pair] using hent)
      (by simpa only [p,first_pair] using hctx)
  have hnon : 0 ≤ mean (first (withMessage p markingMessage)) (fun c=>
      activeDeficit (fiber (withMessage p markingMessage) c) (unspecified c.2)
        (Real.log (153*(Nat.card K:ℝ)^4))) := by
    rw [mean]
    apply Finset.sum_nonneg
    intro c hc
    by_cases hp : 0<first (withMessage p markingMessage) c
    · exact mul_nonneg hp.le (marking_deficit_nonneg hd p hpi hpc c.1 c.2 hp)
    · have hz : first (withMessage p markingMessage) c=0 := le_antisymm (le_of_not_gt hp) (Law.nonneg _ _)
      rw [hz,zero_mul]
  obtain ⟨hE',heq⟩:=classStream_joint hd width hw S ctx hl a hE
  dsimp only
  rw [heq]
  apply (markedClassLaw_deficit hd p hpi hpc hl width hw a hE').trans
  have hm' : (1:ℝ)/39≤eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hd width hw) a) := by
    simpa only [p,markedContext_law,eventMass_map_preimage,markedEvent] using hm
  apply (div_le_div_of_nonneg_right hb hE'.le).trans
  rw [div_le_iff₀ hE']
  have hn := hnon.trans hb
  have ht:=mul_le_mul_of_nonneg_left hm' hn
  dsimp only [expensiveBound]
  nlinarith
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section

lemma slotEmbedding_val {w r : ℕ} (i : Slots w r) :
    (slotEmbedding i).val=(windowCoordinates i).1.val*(4*r)+(windowCoordinates i).2.val := by
  change (windowCoordinates i).2.val+(4*r)*(windowCoordinates i).1.val=_
  ring

lemma ordered_windows {w r : ℕ} (i j : Slots w r)
    (h : (windowCoordinates i).1<(windowCoordinates j).1) :
    slotEmbedding i < slotEmbedding j := by
  simp only [Fin.lt_def,slotEmbedding_val] at h ⊢
  have hi := (windowCoordinates i).2.isLt
  have hj := (windowCoordinates j).2.isLt
  have hm : ((windowCoordinates i).1.val+1)*(4*r)≤(windowCoordinates j).1.val*(4*r) :=
    Nat.mul_le_mul_right _ h
  nlinarith

lemma middle_order {w r : ℕ} (v : Fin w) (s t : Fin (2*r)) (h : s<t) :
    slotEmbedding (Sum.inr (v,s)) < slotEmbedding (Sum.inr (v,t)) := by
  simp only [Fin.lt_def,slotEmbedding_val,windowCoordinates] at h ⊢
  omega

end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

noncomputable def orientedPivotContextAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option (PivotContext K V) :=
  contextAt (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t) b ω C j

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
noncomputable section
variable {I : Type}

local instance (priority := high) actualTargetCapsPropDecidable_r708721_1 (P : Prop) : Decidable P := Classical.propDecidable P
noncomputable def orientedPivotCapsAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option (Finset (ℙ K (Dual K V)) × Finset (ℙ K V)) :=
  observe (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t) b ω C j

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedTreeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

def variableTreeEncoded {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V ≤ 5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) : VariableTreeMessage f r t C :=
  ⟨m,orientedPivotTreeEncoded f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
    (finiteBalanced m.val) (t m) C⟩

end

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTreeFailurePropDecidable_r708721_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

noncomputable def orientedPivotSuccessAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option Unit :=
  successAt (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t) b ω C j

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrderedTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section

local instance (priority := high) orderedTargetPropDecidable_r708721_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V I Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]

def orientedTargetFailure
    (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V ≤ 5)
    (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
    (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
    (γ : Law Ω) (a : Ω → ℙ K V) (b : Ω → ℙ K (Dual K V))
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (j : Address tree) : ℝ :=
  eventMass (adaptiveLaw γ (fun _=>adaptiveLaw (originalLevelLaw μ ν)
    (fun _=>orientedPivotTreeLaw f r tree))) (Finset.univ.filter fun z=>
      ¬TargetCovered
        (orientedPivotContextAt f r σ hσ hq hd (fun i=>X i (z.2.1.1 i))
          (fun i=>Y i (z.2.1.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ tree z.2.2 (Finset.univ,Finset.univ) j)
        (orientedPivotCapsAt f r σ hσ hq hd (fun i=>X i (z.2.1.1 i))
          (fun i=>Y i (z.2.1.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ tree z.2.2 (Finset.univ,Finset.univ) j)
        (a z.1) (b z.1))

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_SurvivingWindowCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.Marking.swcProp
local instance swcBDE_r708721_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.swcIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
  {s : ℝ} (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

def survivingLevelLaw : Law (WindowLevelsData (K:=K) (V:=V) E.card) :=
  originalLevelLaw (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
def survivingEncoded (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card) :
    VariableTreeMessage f r t (Finset.univ,Finset.univ) :=
  variableTreeEncoded f r t (Finset.univ,Finset.univ)
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
    (fun i=>W.firstSupport i (z.1 i)) (fun i=>W.secondSupport i (z.2 i))
    (fun i=>W.first_nonempty i _) (fun i=>W.second_nonempty i _) c δ τ P hδ

def survivingExperiment : Law ((Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) :=
  adaptiveLaw p (fun _=>adaptiveLaw (survivingLevelLaw p u sel E hE W) (fun _=>variableTreeLaw f r w))

def survivingTargetFailure (v : Fin w) (t : Fin (2*n)) : ℝ :=
  mean (survivingExperiment f r p u sel E hE W) (fun z=>
    if z.1 (middleSlot v t)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (survivingEncoded f r p u sel E hE W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1)
      (survivorRank E v) then 1 else 0)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowProp
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowTDE
local instance allWindowBDE_r708721_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

def allWindowLevelLaw : Law (WindowLevelsData (K:=K) (V:=V) E.card) :=
  if hE : E.Nonempty then survivingLevelLaw p u sel E hE (W hE) else uniformType _

def allWindowEncoded (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card) :
    VariableTreeMessage f r t (Finset.univ,Finset.univ) :=
  if hE : E.Nonempty then
    survivingEncoded f r p u sel E hE (W hE) σ hσ hq hd c δ τ P hδ t z
  else variableTreeEmpty f r t (Finset.univ,Finset.univ)

def allWindowExperiment : Law ((Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) :=
  adaptiveLaw p (fun _=>adaptiveLaw (allWindowLevelLaw p u sel E W) (fun _=>variableTreeLaw f r w))

def allWindowFailure (v : Fin w) (t : Fin (2*n)) : ℝ :=
  mean (allWindowExperiment f r p u sel E W) (fun z=>
    if z.1 (middleSlot v t)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1)
      (survivorRank E v) then 1 else 0)

def allWindowPositions (bad : Slots w n→ℝ) (t : VariableTreeTape f r w)
    (z : (Slots w n→FlagPair K V)×WindowLevelsData (K:=K) (V:=V) E.card) :
    Finset (Fin w×Fin (2*n)) :=
  Finset.univ.filter fun i=>i.1∈E ∧ bad (Sum.inr i)=0 ∧
    z.1 (Sum.inr i)∈variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ t z.2) (survivorRank E i.1)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_MiddleStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.SelectedTuple.SelectedStream
open FiniteEntropy
open scoped Classical
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]

def reindex {N n l : ℕ} {admissible : (Fin N→α)→Prop}
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (e : Fin l↪o Fin n) :
    SelectedStream (Ω:=Ω) (β:=β) N l admissible where
  law:=S.law
  stream:=S.stream
  tuple:=fun a i=>S.tuple a (e i)
  reverse:=S.reverse
  view:=S.view
  selected:=by
    intro a ha
    apply occurrences_trans _ _ _ (S.selected a ha)
    apply sourceSequence_occurs
    exact (mem_occurrences_iff _ _).mpr ⟨e,fun _=>rfl⟩
  good:=S.good
  density:=S.density
  density_nonneg:=S.density_nonneg
  density_bound:=S.density_bound
end SharpRamseyFive.SelectedTuple.SelectedStream
namespace SharpRamseyFive.Windows
open scoped Classical

def middleEmbedding (w r : ℕ) : Fin (w*(2*r))↪o Fin (w*(4*r)) :=
  OrderEmbedding.ofStrictMono
    (fun i=>slotEmbedding (Sum.inr (finProdFinEquiv.symm i))) (by
      intro i j hij
      let a := finProdFinEquiv.symm i
      let b := finProdFinEquiv.symm j
      have hi : i.val=a.1.val*(2*r)+a.2.val := by
        calc
          _ = (finProdFinEquiv a).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i).symm
          _ = _ := by change a.2.val+(2*r)*a.1.val=_;ring
      have hj : j.val=b.1.val*(2*r)+b.2.val := by
        calc
          _ = (finProdFinEquiv b).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j).symm
          _ = _ := by change b.2.val+(2*r)*b.1.val=_;ring
      by_cases hab : a.1<b.1
      · exact ordered_windows _ _ hab
      · have hea : a.1=b.1 := by
          apply Fin.ext
          have ha:=a.2.isLt
          have hb:=b.2.isLt
          have hij' : a.1.val*(2*r)+a.2.val<b.1.val*(2*r)+b.2.val := by
            simpa only [Fin.lt_def,hi,hj] using hij
          have hle : b.1.val≤a.1.val := Nat.le_of_not_gt hab
          by_contra hn
          have hg : (b.1.val+1)*(2*r)≤a.1.val*(2*r) := by
            apply Nat.mul_le_mul_right
            omega
          nlinarith
        change slotEmbedding (Sum.inr a) < slotEmbedding (Sum.inr b)
        have hab' : a.2<b.2 := by
          have hh := hij
          simp only [Fin.lt_def,hi,hj,hea] at hh ⊢
          omega
        change slotEmbedding (Sum.inr (a.1,a.2)) < slotEmbedding (Sum.inr (b.1,b.2))
        rw [←hea]
        exact middle_order _ _ _ hab')

end SharpRamseyFive.Windows

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_HistoryPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsBDE
local instance hpsTDE_r708721_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsIDE
def windowTuple (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (a : Ω) : Slots w n→FlagPair K V := fun i=>S.tuple a (slotEmbedding i)

def actualWindowHistory (ctx : Ω→κ) (steps : ℕ) (z : WindowLiftSample Ω K V w n steps) :
    WindowHistory κ K V w n steps := ((ctx z.1,z.2.1),z.2.2)

def historyStream (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ) :
    SelectedStream (Ω:=WindowLiftSample Ω K V w n steps) (β:=FlagPair K V) N (w*(4*n)) admissible :=
  S.augment (fun a=>fiber (historyObservationLaw (first (pair S.law ctx (windowTuple S)))
    (fiber (pair S.law ctx (windowTuple S))) elig steps) (ctx a,windowTuple S a))

def historyPrivateStream (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)]
    (q : ∀h,Law (Γ h)) :
    SelectedStream (Ω:=Σz : WindowLiftSample Ω K V w n steps,Γ (actualWindowHistory ctx steps z))
      (β:=FlagPair K V) N (w*(2*n)) admissible :=
  ((historyStream S ctx elig steps).reindex (middleEmbedding w n)).augmentSigma
    (fun z=>q (actualWindowHistory ctx steps z))

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SelectedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {Ω κ α β : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
namespace SelectedStream
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.srFinDE
lemma reindex_deficit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (ctx : Ω→κ) (e : Fin l↪o Fin n) (D : κ→Fin n→Finset β) (J : ℝ)
    (hD : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hcap : ∀c,0 < map S.law ctx c→∀i,Real.log (D c i).card≤J) :
    mean (first (pair (S.reindex e).law ctx (S.reindex e).tuple))
      (fun c=>(l:ℝ)*J-entropy (fiber (pair (S.reindex e).law ctx (S.reindex e).tuple) c))≤
    mean (first (pair S.law ctx S.tuple))
      (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  have H:=selectByContext_deficit (pair S.law ctx S.tuple) (fun _=>Finset.univ)
    (fun _=>e.toEmbedding) J (fun _ _ _=>Finset.mem_univ _)
    (fun _ _=>fixedOutside_univ _) (by
      intro c hc i hi
      exact (pair_fiber_domains S.law ctx S.tuple D hD c hc).entropy_cap J
        (hcap c (by simpa only [first_pair] using hc)) i)
  rw [selected_pair] at H
  dsimp only [reindex] at *
  simp only [Fintype.card_fin,activeDeficit,Finset.card_univ,Function.comp_def] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_PreparedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

namespace Prepared
variable {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
  {ctx : Ω→κ} {J B M : ℝ}
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.psFinDE
def reindex (h : Prepared S ctx J B M) (e : Fin l↪o Fin n) :
    Prepared (S.reindex e) ctx J B M where
  domain c i:=h.domain c (e i)
  contains z hz i:=h.contains z hz (e i)
  cap c i:=h.cap c (e i)
  deficit:=(S.reindex_deficit ctx e h.domain J h.contains (fun c _=>h.cap c)).trans h.deficit
  incident z hz i:=h.incident z hz (e i)
  consistent z hz i j hij:=h.consistent z hz (e i) (e j) (e.strictMono hij)
  occupancy z hz:=occupancy_reindex _ e e.injective M (h.occupancy z hz)

def swap (h : Prepared S ctx J B M) :
    Prepared (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply) ctx J B M where
  domain c i:=swapDomain (h.domain c i.rev)
  contains z hz i:=(mem_swapDomain_iff _ _).mpr (h.contains z hz i.rev)
  cap c i:=by simpa only [swapDomain,Finset.card_map] using h.cap c i.rev
  deficit:=by rw [changeOrientation_deficit];exact h.deficit
  incident z hz:=reverseTuple_incident (h.incident z hz)
  consistent z hz:=reverseTuple_consistent (h.consistent z hz)
  occupancy z hz:=occupancy_reverse _ M (h.occupancy z hz)
end Prepared
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WeightedLowHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def lowHits (w : ℙ K V → ℝ) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun y=>weightOnHyperplane w y < 1/(4*(Nat.card K:ℝ))

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

def highThreeGood (p : Law (Fin n→FlagPair K V)) (s : ℝ)
    (i j : Fin n) (a : ℙ K V) (b : ℙ K (Dual K V)) : Prop :=
  a∈highThreeLeft (tupleMarginal p i) s ∧ b∈highThreeRight (tupleMarginal p j) s ∧ Incident a b

def highCollision (p : Law (Fin n→FlagPair K V)) (s : ℝ) (i j : Fin n) : ℝ :=
  tupleCollision p Projectivization.rep Projectivization.rep (highThreeGood p s) i j

end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DescriptionClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
def Prepared.mono {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
    {ctx : Ω→κ} {J B B' M : ℝ} (P : Prepared S ctx J B M) (hB : B≤B') :
    Prepared S ctx J B' M where
  domain:=P.domain
  contains:=P.contains
  cap:=P.cap
  deficit:=P.deficit.trans hB
  incident:=P.incident
  consistent:=P.consistent
  occupancy:=P.occupancy
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance pwIDE : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows LowConflict CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]
local instance rcrIDE : DecidableEq (Slots w n) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
  SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem card_flags : Nat.card (Flag (K := K) (V := V))=
    (∑ i∈Finset.range (finrank K V),Nat.card K^i)*
    (∑ i∈Finset.range (finrank K V-1),Nat.card K^i) := by
  let e : Flag (K := K) (V := V) ≃ (Σ a : ℙ K V,{b : ℙ K (Module.Dual K V) // Incident a b}) :=
    { toFun := fun ab => ⟨ab.val.1,⟨ab.val.2,ab.property⟩⟩
      invFun := fun ab => ⟨(ab.1,ab.2.val),ab.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp only [card_hyperplanes_through_point,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V rfl]
  simp

theorem card_flags_lower (hdim : finrank K V=5) :
    Nat.card K^7≤Nat.card (Flag (K := K) (V := V)) := by
  rw [card_flags,hdim]
  have h1 : Nat.card K^4≤∑ i∈Finset.range 5,Nat.card K^i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  have h2 : Nat.card K^3≤∑ i∈Finset.range (5-1),Nat.card K^i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  have h := Nat.mul_le_mul h1 h2
  rwa [←pow_add] at h

lemma flags_nonempty (hdim : finrank K V=5) : 0<Fintype.card (Flag (K := K) (V := V)) := by
  rw [←Nat.card_eq_fintype_card]
  exact (pow_pos (Nat.card_pos (α := K)) _).trans_le (card_flags_lower hdim)

end SharpRamseyFive.RectangleGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_HighWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hwsBDE
local instance hwsTDE_r708721_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hwsIDE
def oneMiddleEmbedding (n : ℕ) : Fin (2*n)↪o Fin (1*(4*n)) :=
  OrderEmbedding.ofStrictMono (fun t=>slotEmbedding (Sum.inr ((0:Fin 1),t)))
    (fun _ _ h=>middle_order 0 _ _ h)

variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin 1×Bool→Finset (Fin n)) (steps r' : ℕ) (s : ℝ) (h : ℕ)

def highSampleStream :=
  ((historyStream S ctx elig steps).reindex (oneMiddleEmbedding n)).augment
    (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h
      (actualWindowHistory ctx steps z))

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighSampleContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance hscBDE_r708721_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hscTDE_r708721_1 (n : ℕ) : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hscIDE (n : ℕ) : DecidableEq (Slots 1 n) := Classical.decEq _

end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hprBDE_r708721_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hprTDE_r708721_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hprIDE : DecidableEq (Slots 1 n) := Classical.decEq _

end

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassifiedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.csFinDE
local instance csPDE_r708721_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance csDDE_r708721_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] in
lemma classDomain_cap (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :
    ((classDomain hd width hw hl a c i).card:ℝ)≤153*(Nat.card K:ℝ)^4 :=
  markingDomain_card hd _ _
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] in
lemma classDomain_log_cap (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :
    Real.log (classDomain hd width hw hl a c i).card≤Real.log (153*(Nat.card K:ℝ)^4) := by
  by_cases hz : (classDomain hd width hw hl a c i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    nlinarith [sq_nonneg ((Nat.card K:ℝ)^2-1),sq_nonneg ((Nat.card K:ℝ)-1)]
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
      (classDomain_cap hd width hw hl a c i)

lemma classStream_occupancy (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a))) (M : ℝ)
    (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    let T:=classStream hd width hw S ctx hl a hE
    ∀z,0<T.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (T.tuple z i).1.rep (T.tuple z i).2.rep then (1:ℝ) else 0)≤M := by
  intro T z hz W
  have hp:=conditionOn_positive S.law
    (eventPreimage (markedContext ctx S.tuple) (markedEvent hd width hw l a)) hE z hz
  exact occupancy_reindex (S.tuple z)
    (retainedIndices hl (markedPositions hd width hw ctx S.tuple a z))
    (retainedIndices hl (markedPositions hd width hw ctx S.tuple a z)).injective
    M (hocc z hp.2) W

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_WindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsBDE
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsTDE
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsIDE
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)

abbrev windowFiber := fiber (pair S.law ctx (windowTuple S))

def levelWindowStream (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
    (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
      (u h) h.2 (survivingOriginal (E h) he) s) :=
  historyPrivateStream S ctx elig steps
    (fun h=>WindowLevelsData (K:=K) (V:=V) (E h).card)
    (fun h=>allWindowLevelLaw (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h))

variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
  (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
  (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
    (u h) h.2 (survivingOriginal (E h) he) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

abbrev LevelWindowSample := (z : WindowLiftSample Ω K V w n steps)×
  WindowLevelsData (K:=K) (V:=V) (E (actualWindowHistory ctx steps z)).card

def actualWindowEncoded (t : VariableTreeTape f r w) (z : LevelWindowSample ctx steps E) :=
  let h:=actualWindowHistory ctx steps z.1
  allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
    σ hσ hq hd c δ τ P hδ t z.2

def actualWindowPositions (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (t : VariableTreeTape f r w) (z : LevelWindowSample ctx steps E) : Finset (Fin (w*(2*n))) :=
  let h:=actualWindowHistory ctx steps z.1
  equivPositions finProdFinEquiv
    (allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
      σ hσ hq hd c δ τ P hδ (bad h) t (windowTuple S z.1.1,z.2))

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowSmallFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module FiniteEntropy ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance smallFailureIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance arlIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

attribute [local irreducible] actualWindows actualWindowSet

end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalSharpRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance rprIDE : DecidableEq (Slots w n) := Classical.decEq _

end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section
local instance rpsIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

end

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_OrderedHighConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def orderedHighCollision (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) : ℝ :=
  highCollision (orderedLaw p e) s (e i) (e j)+highCollision (orderedLaw p e) s (e j) (e i)
end
end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighChosenRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]
local instance hcrIDE : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighThreePrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance htpBDE_r708721_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance htpTDE_r708721_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance htpIDE : DecidableEq (Slots 1 n) := Classical.decEq _

end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.cpFinDE
def classPrepared (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z))
    (D : κ→Fin n→Finset (FlagPair K V)) (cap B L M : ℝ) (hcap : 1 ≤ cap)
    (hD : ∀c i,((D c i).card:ℝ) ≤ cap)
    (hsupp : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hΔ : 0≤Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))
    (hent : (n:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (map S.law S.tuple)≤B)
    (hctx : entropy (map S.law ctx)≤L)
    (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    Prepared (classStream hd width hw S ctx hl a hE) (markedContext ctx S.tuple)
      (Real.log (153*(Nat.card K:ℝ)^4))
      (39*(B+L+(n:ℝ)*Real.log 800+
        expensiveBound K V*(Real.log cap-Real.log (153*(Nat.card K:ℝ)^4)))) M where
  domain:=classDomain hd width hw hl a
  contains:=classStream_contains hd width hw S ctx hl a hE hinc hcons
  cap:=classDomain_log_cap hd width hw hl a
  deficit:=actual_marked_deficit hd width hw S ctx hl a hE hm hinc hcons D cap B L
    hcap hD hsupp hΔ hent hctx
  incident z hz:=(classStream_consistent hd width hw S ctx hl a hE hinc hcons z hz).1
  consistent z hz:=(classStream_consistent hd width hw S ctx hl a hE hinc hcons z hz).2
  occupancy:=classStream_occupancy hd width hw S ctx hl a hE M hocc
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [instance] ClassifiedPrepared.finiteSample ClassifiedPrepared.finiteContext

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_TerminalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization

noncomputable section
variable (K α : Type) [Field K] [Finite K] [Fintype α]

structure PolarState (N n : ℕ) (adm : (Fin N→α)→Prop) (d Λ Δ M : ℝ) where
  ambient : Type
  [group : AddCommGroup ambient]
  [module : Module K ambient]
  [dimension : FiniteDimensional K ambient]
  [points : Fintype (ℙ K ambient)]
  [hyperplanes : Fintype (ℙ K (Dual K ambient))]
  [bipoints : Fintype (ℙ K (Dual K (Dual K ambient)))]
  [pointNonempty : Nonempty (ℙ K ambient)]
  [planeNonempty : Nonempty (ℙ K (Dual K ambient))]
  [bipointNonempty : Nonempty (ℙ K (Dual K (Dual K ambient)))]
  dim : finrank K ambient=5
  coded : CodedStream (K:=K) (V:=ambient) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M
attribute [instance] PolarState.group PolarState.module PolarState.dimension PolarState.points
  PolarState.hyperplanes PolarState.bipoints PolarState.pointNonempty PolarState.planeNonempty
  PolarState.bipointNonempty
variable {K α}
def PolarState.of {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))]
    [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
    {N n : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M : ℝ} (hd : finrank K V=5)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M) :
    PolarState K α N n adm d Λ Δ M where
  ambient:=V
  dim:=hd
  coded:=S

end
end

open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]

lemma iid_uniform_mass (N : ℕ) (s : Fin N→α) :
    iid (uniform Fintype.card_pos) (Fin N) s=1/(Fintype.card α:ℝ)^N := by
  simp [iid,uniform]

def initialSelectedStream {N n : ℕ} (admissible : (Fin N→α)→Prop)
    (E : Finset (Fin N→α))
    (hE : 0<eventMass (iid (uniform Fintype.card_pos) (Fin N)) E)
    (hgood : ∀ s,s∈E→admissible s)
    (choose : (Fin N→α)→(Fin n↪o Fin N))
    (decode : α→β) (encode : β→α) (hinv : Function.LeftInverse encode decode) :
    SelectedStream (Ω:=Fin N→α) (β:=β) N n admissible where
  law := conditionOn (iid (uniform Fintype.card_pos) (Fin N)) E hE
  stream := id
  tuple := fun s i=>decode (s (choose s i))
  reverse := false
  view := encode
  selected := by
    intro s hs
    apply (mem_occurrences_iff _ _).mpr
    refine ⟨choose s,fun i=>?_⟩
    exact (hinv _).symm
  good := fun s hs=>hgood s (conditionOn_positive _ E hE s hs).1
  density := 1/eventMass (iid (uniform Fintype.card_pos) (Fin N)) E
  density_nonneg := by positivity
  density_bound := by
    intro s
    rw [map_id]
    have h:=conditionOn_le (iid (uniform Fintype.card_pos) (Fin N)) E hE s
    rw [iid_uniform_mass] at h
    convert h using 1 <;> first | rfl | ring

end

end SharpRamseyFive.SelectedTuple

end OAI
end


