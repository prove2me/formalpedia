-- Prove2me | Definitions.Def_OAIQ051M004
-- name    : OAIQ051M004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:32:35.070201+00:00
-- url     : https://prove2.me/theorems/311e80ef-a8e6-4e8c-965e-78e640dffb5f
-- title:
--   Definitions bundle OAIQ051M004 of the split of OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 574 declarations of OpenAI's Lean: 491 definitions, 2 inductive types or structures, 2 instances and 79 theorems. The definitions and types are `OAI.MatchingFPRAS.ExecutableSource.certificateArgsRealizer`, `OAI.MatchingFPRAS.ExecutableSource.certificateCellData`, `OAI.MatchingFPRAS.ExecutableSource.certificateCellDataRealizer`, `OAI.MatchingFPRAS.ExecutableSource.certificateMatrix`, `OAI.MatchingFPRAS.ExecutableSource.certificateMatrixRealizer`, `OAI.MatchingFPRAS.ExecutableSource.certificateSampleRealizer`, `OAI.MatchingFPRAS.ExecutableSource.currentActivityArg`, `OAI.MatchingFPRAS.ExecutableSource.currentActivityArgRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedCertificate`, `OAI.MatchingFPRAS.ExecutableSource.generatedCertificateRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedContextRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedIndexData`, `OAI.MatchingFPRAS.ExecutableSource.generatedIndexDataRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedMarkedRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedObservables`, `OAI.MatchingFPRAS.ExecutableSource.generatedObservablesRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedPreparedRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedSourceSample`, `OAI.MatchingFPRAS.ExecutableSource.generatedStageSetup`, `OAI.MatchingFPRAS.ExecutableSource.generatedStageSetupRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdate`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateArg`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateConfig`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateConfigRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateRealizer`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateSetup`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateSetupRealizer`, `OAI.MatchingFPRAS.ExecutableSource.isCentralRealizer`, `OAI.MatchingFPRAS.ExecutableSource.markPortionsRealizer`, `OAI.MatchingFPRAS.ExecutableSource.nextActivityArg`, `OAI.MatchingFPRAS.ExecutableSource.nextActivityArgRealizer`, `OAI.MatchingFPRAS.ExecutableSource.probePartRealizer`, `OAI.MatchingFPRAS.ExecutableSource.rangeFromListRealizer`, `OAI.MatchingFPRAS.ExecutableSource.realRepr`, `OAI.MatchingFPRAS.ExecutableSource.setupBags`, `OAI.MatchingFPRAS.ExecutableSource.sourceAllIndices`, `OAI.MatchingFPRAS.ExecutableSource.sourceAllIndicesRealizer`, `OAI.MatchingFPRAS.ExecutableSource.sourceBindings`, `OAI.MatchingFPRAS.ExecutableSource.sourceBindingsRealizer`, `OAI.MatchingFPRAS.ExecutableSource.sourceEdgeDataRealizer` and 453 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatchingCount, in whole or in part: `MatchingCount_Algorithm_Algorithm`, `MatchingCount_Algorithm_AlgorithmLaw`, `MatchingCount_Algorithm_EmpiricalDenom`, `MatchingCount_Algorithm_FiniteStage`, `MatchingCount_Algorithm_FiniteTrial`, `MatchingCount_Algorithm_FiniteTrialLaw`, `MatchingCount_Algorithm_Guard`, `MatchingCount_Algorithm_GuardProbability`, `MatchingCount_Algorithm_OnlineAmplification`, `MatchingCount_Algorithm_OnlineCoolingSchedule`, `MatchingCount_Algorithm_OnlineGuard`, `MatchingCount_Algorithm_OnlineHistorySize`, `MatchingCount_Algorithm_OnlineInitial`, `MatchingCount_Algorithm_OnlineInitialLaw`, `MatchingCount_Algorithm_OnlineLadderSchedule`, `MatchingCount_Algorithm_OnlineLaw`, `MatchingCount_Algorithm_OnlineMedian`, `MatchingCount_Algorithm_OnlinePowerSearch`, `MatchingCount_Algorithm_OnlineRequest`, `MatchingCount_Algorithm_OnlineSampleCount`, `MatchingCount_Algorithm_OnlineScheduleNat`, `MatchingCount_Algorithm_OnlineStage`, `MatchingCount_Algorithm_OnlineTransitionLaw`, `MatchingCount_Algorithm_OnlineTrial`, `MatchingCount_Algorithm_OnlineTrialLaw`, `MatchingCount_Algorithm_OutputLengthBound`, `MatchingCount_Algorithm_RationalCounts`, `MatchingCount_Algorithm_RationalEstimator`, `MatchingCount_Algorithm_RationalObservables`, `MatchingCount_Algorithm_RationalStart`, `MatchingCount_Algorithm_RationalUpdate`, `MatchingCount_Algorithm_RelabelWeights`, `MatchingCount_Algorithm_SortedList`, `MatchingCount_Algorithm_TreeGeneratedCertificate`, `MatchingCount_Algorithm_TreeGeneratedMarked`, `MatchingCount_Algorithm_TreeGeneratedPrepared`, `MatchingCount_Algorithm_TreeGeneratedStage`, `MatchingCount_Algorithm_TreeGeneratedUpdate`, `MatchingCount_Algorithm_TreeNumericStage`, `MatchingCount_Algorithm_TreeNumericStatistics`, `MatchingCount_Algorithm_TreeNumericStatisticsCorrect`, `MatchingCount_Algorithm_TreeNumericSummaries`, `MatchingCount_Algorithm_TreeStageStatistics`, `MatchingCount_Algorithm_TreeStageUpdateCorrect`, `MatchingCount_Algorithm_TreeStatistics`, `MatchingCount_Algorithm_TreeTierWeights`, `MatchingCount_Arithmetic_OnlineFractionParam`, `MatchingCount_Complexity_OnlineCost`, `MatchingCount_Complexity_OnlineHistoryCost`, `MatchingCount_Complexity_OnlineInitialCost`, `MatchingCount_Complexity_OnlineRequestCost`, `MatchingCount_Complexity_OnlineSampleCost`, `MatchingCount_Complexity_OnlineScheduleCost`, `MatchingCount_Complexity_OnlineStageCost`, `MatchingCount_Complexity_TreeCostMeasure`, `MatchingCount_Complexity_TreePolynomial`, `MatchingCount_Graphs_LabelOrder`, `MatchingCount_Graphs_OnlineGraphInvariant`, `MatchingCount_Graphs_RelabelMore`, `MatchingCount_Graphs_Related`, `MatchingCount_Graphs_Related2`, `MatchingCount_Graphs_TreeGeometry`, `MatchingCount_Graphs_TreeHeight`, `MatchingCount_Machines_OnlineCase`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_OnlinePhysicalProgram`, `MatchingCount_Machines_OnlineTraverse`, `MatchingCount_Machines_OnlineTree`, `MatchingCount_Machines_TreeBindings`, `MatchingCount_Machines_TreeFinite`, `MatchingCount_Machines_TreeFiniteCollections`, `MatchingCount_Machines_TreeGuideTables`, `MatchingCount_Machines_TreeMarkTable`, `MatchingCount_Machines_TreeMetadata`, `MatchingCount_Machines_TreePostRealization`, `MatchingCount_Machines_TreeScaleStateUpdate`, `MatchingCount_Machines_Wrapper`, `MatchingCount_Probability_AdaptiveLaw`, `MatchingCount_Probability_MainLaw`, `MatchingCount_Probability_Marking`, `MatchingCount_Probability_OnlineLayerLaw`, `MatchingCount_Sampling_MarkBridge`, `MatchingCount_Sampling_OnlineSample`, `MatchingCount_Sampling_Relabel`, `MatchingCount_Sampling_TreeLadder`, `MatchingCount_Sampling_TreeLadderContext`, `MatchingCount_Sampling_TreeLadderIndexed`, `MatchingCount_Sampling_TreeLadderPost`, `MatchingCount_Sampling_TreeNumericLadder`, `MatchingCount_Sampling_TreeNumericMarking`, `MatchingCount_Sampling_TreePrepareLadder`, `MatchingCount_Sampling_TreePrepared`, `MatchingCount_Sampling_TreePreparedMarked`, `MatchingCount_Sampling_TreeProbe`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_GuardBits`, `MatchingCount_Tapes_Input`, `MatchingCount_Tapes_OnlineWord`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_PackedExecution`, `MatchingCount_Tapes_PackedInverse`, `MatchingCount_Tapes_Parse`, `MatchingCount_Tapes_TreeSparseCertificate`, `MatchingCount_Tapes_TreeSparseStage`.
--
--   **Imports.** It imports the published bundle `Def_MatchingFPRAS`; the bundles `OAIQ051M002` and `OAIQ051M003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedCertificate`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedContext`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedPrepared`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedTier`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdate`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_sourceMarks`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_sourceReweights`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.sampleLaw_budget`, `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound`, `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success`, `OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean`, `OAI.MatchingFPRAS.NumericLadder.polynomial_pair`, `OAI.MatchingFPRAS.NumericLadder.polynomial_refresh`, `OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany`, `OAI.MatchingFPRAS.NumericMarking.sample_source`, `OAI.MatchingFPRAS.OnlineGuard.checked_mean`, `OAI.MatchingFPRAS.OnlineGuard.trial_bound`, `OAI.MatchingFPRAS.OnlineGuard.work_checked`, `OAI.MatchingFPRAS.OnlineInitial.work_initializeInput`, `OAI.MatchingFPRAS.OnlineSchedule.bound_precision`, `OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest`, `OAI.MatchingFPRAS.OnlineStage.source_mean`, `OAI.MatchingFPRAS.OnlineTrial.sweep_bound`, `OAI.MatchingFPRAS.OnlineTrial.work_body` and `OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw`; the proofs of `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedCertificate`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedContext`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedPrepared`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedTier`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdate`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_sourceMarks`, `OAI.MatchingFPRAS.ExecutableSource.polynomial_sourceReweights`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.sampleLaw_budget`, `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound`, `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success`, `OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean`, `OAI.MatchingFPRAS.NumericLadder.polynomial_pair`, `OAI.MatchingFPRAS.NumericLadder.polynomial_refresh`, `OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany`, `OAI.MatchingFPRAS.NumericMarking.sample_source`, `OAI.MatchingFPRAS.OnlineGuard.checked_mean`, `OAI.MatchingFPRAS.OnlineGuard.trial_bound`, `OAI.MatchingFPRAS.OnlineGuard.work_checked`, `OAI.MatchingFPRAS.OnlineInitial.work_initializeInput`, `OAI.MatchingFPRAS.OnlineSchedule.bound_precision`, `OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest`, `OAI.MatchingFPRAS.OnlineStage.source_mean`, `OAI.MatchingFPRAS.OnlineTrial.sweep_bound`, `OAI.MatchingFPRAS.OnlineTrial.work_body`, `OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw` and `OAI.MatchingFPRAS.thm_main`.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatchingCount at commit adc7f12

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M002
import Definitions.Def_OAIQ051M003

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Hierarchy

variable {V : Type*} [Fintype V]

variable (B : V → V → ℝ)

variable (hsym : ∀ a b, B a b = B b a)

variable (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)

omit [Fintype V] in
lemma mem_class_iff {H : ℕ} (k : Fin (H+1)) (x y : V) :
    Mem B hsym htri (labelAt B hsym htri k x) y ↔ Related B (2^k.val) y x :=
  Quotient.eq

omit [Fintype V] in
lemma exists_mem {H : ℕ} (l : Label B hsym htri H) : ∃ x, Mem B hsym htri l x :=
  Quotient.exists_rep l.2

omit [Fintype V] in
lemma eq_of_level_of_mem {H : ℕ} (a b : Label B hsym htri H) (hlev : a.1=b.1)
    {x : V} (ha : Mem B hsym htri a x) (hb : Mem B hsym htri b x) : a=b := by
  cases a with
  | mk k a =>
    cases b with
    | mk j b =>
      dsimp at hlev
      subst j
      exact congrArg (Sigma.mk k) (ha.symm.trans hb)

omit [Fintype V] in
lemma related_of_mem {H : ℕ} (l : Label B hsym htri H) {x y : V}
    (hx : Mem B hsym htri l x) (hy : Mem B hsym htri l y) : Related B (2^l.1.val) x y :=
  Quotient.exact (hx.trans hy.symm)

omit [Fintype V] in
lemma mem_of_related {H : ℕ} (l : Label B hsym htri H) {x y : V}
    (hx : Mem B hsym htri l x) (hxy : Related B (2^l.1.val) y x) : Mem B hsym htri l y :=
  (Quotient.sound hxy).trans hx

def Parent {H : ℕ} (a b : Label B hsym htri H) : Prop :=
  a.1.val+1=b.1.val ∧ ∃ x, Mem B hsym htri a x ∧ Mem B hsym htri b x

def tree {H : ℕ} : SimpleGraph (Label B hsym htri H) where
  Adj a b := Parent B hsym htri a b ∨ Parent B hsym htri b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a h; rcases h with h|h <;> have := h.1 <;> omega⟩

omit [Fintype V] in
lemma parent_mem {H : ℕ} {a b : Label B hsym htri H} (h : Parent B hsym htri a b)
    {x : V} (hx : Mem B hsym htri b x) : Mem B hsym htri a x := by
  obtain ⟨hlev,y,hy,hby⟩ := h
  have hpow : (2:ℝ)^a.1.val ≤ 2^b.1.val := pow_le_pow_right₀ (by norm_num) (by omega)
  exact mem_of_related B hsym htri a hy
    (related_mono B hpow (related_of_mem B hsym htri b hx hby))

omit [Fintype V] in
lemma parent_unique {H : ℕ} {a b c : Label B hsym htri H}
    (ha : Parent B hsym htri a c) (hb : Parent B hsym htri b c) : a=b := by
  obtain ⟨x,hx⟩ := exists_mem B hsym htri c
  apply eq_of_level_of_mem B hsym htri a b _
    (parent_mem B hsym htri ha hx) (parent_mem B hsym htri hb hx)
  apply Fin.ext
  have := ha.1
  have := hb.1
  omega

omit [Fintype V] in
theorem tree_acyclic (H : ℕ) : (tree B hsym htri (H := H)).IsAcyclic := by
  apply acyclic_of_unique_lower _ (fun l => l.1.val)
  · intro a b hab
    rcases hab with h | h <;> have := h.1 <;> omega
  · intro a b c hab hac hb hc
    have hp : Parent B hsym htri b a := by
      rcases hab with h | h
      · have := h.1; omega
      · exact h
    have hq : Parent B hsym htri c a := by
      rcases hac with h | h
      · have := h.1; omega
      · exact h
    exact parent_unique B hsym htri hp hq

variable (hfloor : ∀ a b, 1 ≤ B a b)

omit [Fintype V] in
lemma common_vertex_adjacent {H : ℕ} (a b : Label B hsym htri H) {x : V}
    (ha : Mem B hsym htri a x) (hb : Mem B hsym htri b x)
    (hab : a.1.val ≤ b.1.val+1) (hba : b.1.val ≤ a.1.val+1) :
    a=b ∨ (tree B hsym htri).Adj a b := by
  rcases lt_trichotomy a.1.val b.1.val with h | h | h
  · exact Or.inr (Or.inl ⟨by omega,x,ha,hb⟩)
  · exact Or.inl (eq_of_level_of_mem B hsym htri a b (Fin.ext h) ha hb)
  · exact Or.inr (Or.inr ⟨by omega,x,hb,ha⟩)

variable {E : Type*} [Fintype E] (left right : E → V) (H : ℕ)

omit [Fintype V] [Fintype E] in
include hfloor in
lemma incident_mem_label (e : E) {x : V} (hx : Incident left right e x) :
    Mem B hsym htri (edgeLabel B hsym htri left right H e) x := by
  rcases hx with rfl | rfl
  · rfl
  · apply (mem_class_iff B hsym htri _ _ _).mpr
    exact Or.inr (by rw [hsym]; exact dyadic_lower H _ (hfloor _ _))

omit [Fintype V] in
include hfloor in
lemma membership_mem {x : V} {l : Label B hsym htri H}
    (hl : l ∈ memberships B hsym htri left right H x) : Mem B hsym htri l x := by
  obtain ⟨e,he,rfl⟩ := (mem_memberships B hsym htri left right H x l).mp hl
  exact incident_mem_label B hsym htri hfloor left right H e he

variable (hupper : ∀ e, B (left e) (right e) < (2:ℝ)^(H+1))

variable (hnear : ∀ x e f, Incident left right e x → Incident left right f x →
  B (left e) (right e) ≤ 2*B (left f) (right f))

omit [Fintype V] in
include hfloor hupper hnear in

theorem memberships_tree_bags (x : V) (a b : Label B hsym htri H)
    (ha : a ∈ memberships B hsym htri left right H x)
    (hb : b ∈ memberships B hsym htri left right H x) :
    a=b ∨ (tree B hsym htri).Adj a b := by
  exact common_vertex_adjacent B hsym htri a b
    (membership_mem B hsym htri hfloor left right H ha)
    (membership_mem B hsym htri hfloor left right H hb)
    (memberships_level_near B hsym htri hfloor left right H hupper hnear ha hb)
    (memberships_level_near B hsym htri hfloor left right H hupper hnear hb ha)

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def PolynomialBound {f : A → B} (F : Realizer f) (p : Polynomial ℕ) : Prop :=
  ∀ a,F.cost a+weight (f a)≤p.eval (weight a)
def PolynomialTime {f : A → B} (F : Realizer f) : Prop := ∃ p,PolynomialBound F p

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

variable [LinearOrder A]

def finsetImage [LinearOrder B] {f : A → B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (Finset.image f) :=
  (composition (composition finsetList (map F)) (listFinset E R)).congr (by intro s; ext a; simp)

def finsetFilter {p : A → Bool} (P : Realizer p) : Realizer (fun s : Finset A=>s.filter fun a=>p a) :=
  (filter P).recode (fun s=>s.sort (·≤·)) _ (fun _=>rfl) (fun s=>by
    change encode ((s.sort (·≤·)).filter p)=encode ((s.filter fun a=>p a).sort (·≤·))
    rw [sort_filter])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def flatMapPoly {f : A → List B} (F : Realizer f) : Realizer (List.flatMap f) :=
  (composition (map F) flatten).congr (by intro as; rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineScheduleNat
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type} [Codec A]
def Realizer.addNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a+g a) := composition (pair F G) add
def Realizer.mulNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a*g a) := composition (pair F G) multiply

def fixedPower : (k : ℕ)→Realizer (fun n : ℕ=>n^k)
  | 0 => (constant 1).congr (by intro n; simp)
  | k+1 => ((fixedPower k).mulNat identity).congr (by intro n; simp [pow_succ])
def clogTwo : Realizer (Nat.clog 2) :=
  (composition predecessor bitSize).congr (fun n=>(clog_two_size_pred n).symm)
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Transport

def lRealizer : Realizer (fun x : ℕ×ℕ=>ladderL x.1 x.2) :=
  (composition (((constant (10^4)).mulNat first).mulNat second) (fixedPower 100)).congr (fun _=>rfl)
def qRealizer : Realizer (fun x : ℕ×ℕ=>ladderQ x.1 x.2) :=
  ((constant 32).mulNat lRealizer).congr (fun _=>rfl)

def mRealizer : Realizer (fun x : (ℕ×ℕ)×ℕ=>ladderM x.1.1 x.1.2 x.2) :=
  ((second.mulNat (composition (composition first qRealizer) (fixedPower 2))).addNat
    (composition first qRealizer)).congr (fun _=>rfl)
def lambdaRealizer : Realizer (fun x : (ℕ×ℕ)×(ℕ×ℕ)=>ladderLambda x.1.1 x.1.2 x.2.1 x.2.2) :=
  (((((constant 10).mulNat first.fst).mulNat (composition first qRealizer)).mulNat
    (second.snd.addNat (constant 1))).mulNat
    ((second.fst.addNat (composition ((first.fst.mulNat first.snd).addNat (constant 2)) clogTwo)).addNat (constant 1))).congr
      (fun _=>rfl)

def scansRealizer : Realizer (fun x : ScanInput=>discreteLadderSteps x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) :=
  ((((constant 20).mulNat (composition first.fst lRealizer)).mulNat
    (composition (pair first.fst first.snd.snd) mRealizer)).mulNat
    (((composition first lambdaRealizer).addNat (composition second clogTwo)).addNat (constant 1))).congr
      (fun _=>rfl)

end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineTree
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing MachineCost PhysicalStream OnlineStack TreeData TreeMachine TreeFunction TreeTyped

def initial (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨some default,none,encodeEnv (env x .nil s)⟩
def final (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨none,none,encodeEnv (env x .nil s)⟩
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → Experiment B) where
  program : OnlineProc.Proc (K Reg)
  cost : A → ℕ
  correct : ∀ a s,∃ q : Experiment B,
    Executes program.code program.coin (fun b=>final program (encode b) s)
      (initial program (encode a) s) q ∧
    (∀ g : B → ℚ,q.mean g=(f a).mean g) ∧ q.cost ≤ cost a
variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def deterministic {f : A → B} (F : TreeTyped.Realizer f) : Realizer (fun a=>.done (f a)) where
  program := OnlineProc.deterministic F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨n,hn,he⟩:=F.correct a s
    obtain ⟨p,hp,hm,hc⟩:=Executes.of_run F.program.code n _ _ _ he
    refine ⟨p.map (fun _=>f a),?_,?_,?_⟩
    · exact hp.bind (fun _=>.done (f a)) _ (fun _=>.done (f a))
    · intro g
      rw [Experiment.mean_map,hm]; rfl
    · rw [Experiment.cost_map]
      exact hc.trans hn

noncomputable def composition {f : A → Experiment B} {g : B → Experiment C}
    (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a).bind g) where
  program := OnlineProc.seq F.program G.program
  cost := fun a=>F.cost a+(f a).worst G.cost
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    choose q hq hqm hqc using fun b=>G.correct b s
    have hp':=hp.relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inl (some (Sum.inr default)) (fun _=>rfl) (fun _=>rfl)
    have hq' b := (hq b).relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inr none (fun _=>rfl) (fun _=>rfl)
    refine ⟨p.bind q,hp'.bind q _ hq',?_,?_⟩
    · intro h
      simp_rw [Experiment.mean_bind,hqm]
      exact hm _
    · apply (Experiment.cost_bind_le_of_all p q ((f a).worst G.cost) ?_).trans (Nat.add_le_add_right hc _)
      exact (Experiment.all_of_mean_eq hm _ (Experiment.all_worst (f a) G.cost)).mono
        (fun b hb=>(hqc b).trans hb)

def Realizer.congr {f g : A → Experiment B} (F : Realizer f)
    (h : ∀ a w,(f a).mean w=(g a).mean w) : Realizer g where
  program := F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨q,hq,hm,hc⟩:=F.correct a s
    exact ⟨q,hq,fun w=>(hm w).trans (h a w),hc⟩

noncomputable def choose {f g : A → Experiment B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>.read (fun b=>if b then g a else f a)) where
  program := chooseProgram F.program G.program
  cost := fun a=>1+max (F.cost a) (G.cost a)
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    obtain ⟨q,hq,hqm,hqc⟩:=G.correct a s
    have hp':=hp.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inl u)) none (fun _=>rfl) (fun _=>rfl)
    have hq':=hq.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inr u)) none (fun _=>rfl) (fun _=>rfl)
    refine ⟨.read (fun b=>if b then q else p),?_,?_,?_⟩
    · apply Executes.read _ _ _ _ _ rfl
      intro b
      cases b
      · exact hp'
      · exact hq'
    · intro h
      simp only [Experiment.mean,Bool.false_eq_true,↓reduceIte,hm,hqm]
    · simp only [Experiment.cost,Bool.false_eq_true,↓reduceIte]
      omega

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineFold
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]

namespace Fold
open OnlineControl
open TreeTyped.Fold (Point)

noncomputable def cost (f : A×B → Experiment B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+
      (f (a,b)).worst (cost f t as)

lemma runs {f : A×B → Experiment B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun b=>env (encode b) .nil s) (Option.some Point.loop)
      (env (encode (as,b)) .nil s) q ∧
      (∀ g : B → ℚ,q.mean g=(foldM f as b).mean g) ∧ q.cost ≤ cost f F.cost as b := by
  induction as generalizing b with
  | nil =>
    have hh := OnlineControl.halt (code F.program) (fun b=>env (encode b) .nil s) Point.halt rfl b
    have hc := OnlineControl.nilBranch (code F.program) (fun b=>env (encode b) .nil s)
      Point.check Point.halt Point.splitHead 1 rfl _ rfl _ hh
    obtain ⟨q,hq,hm,hcost⟩:=deterministicCall (code F.program) (fun b=>env (encode b) .nil s)
      Point.loop Point.check (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 .nil (encode b) .nil s) _ hc
    refine ⟨q,hq,?_,?_⟩
    · intro g; simpa only [Experiment.mean,foldM] using hm g
    · simpa only [cost,size_nil,Experiment.cost] using hcost
  | cons a as ih =>
    choose q hq hm hcost using ih
    let out := fun b : B=>env (encode b) .nil s
    let M := code F.program
    let sr := TreeFunction.size (encode as)
    let sa := TreeFunction.size (encode a)
    have hreb v := deterministicCall M out Point.rebuild Point.loop
      (TreeFunction.cons 1 0 (by decide)) rfl _ _ _
      (cons10 (encode v) (encode as) s) (q v) (hq v)
    choose qr hr hmr hcr using hreb
    have hpop v := deterministicCall M out Point.popTail Point.rebuild
      (TreeFunction.split 1 2 (by decide)) rfl _ _ _
      (split12 (encode v) .nil (encode as) s) (qr v) (hr v)
    choose qp hp hmp hcp using hpop
    obtain ⟨r,hrf,hrm,hrc⟩:=F.correct (a,b) (.cons (encode as) s)
    have hbody := call M out Point.body Point.popTail F.program rfl
      (env (encode (a,b)) .nil (.cons (encode as) s))
      (fun v=>env (encode v) .nil (.cons (encode as) s)) r hrf qp hp
    have h4 := TreeTyped.Fold.pushArgs (encode a) (encode b) (encode as) s
    obtain ⟨p4,hp4,hm4,hc4⟩:=deterministicCall M out Point.pushArgs Point.body
      (TreeFunction.cons 3 0 (by decide)) rfl _ _ _ h4 _ hbody
    have h5 := TreeTyped.Fold.pushTail (encode a) (encode b) (encode as) s
    obtain ⟨p5,hp5,hm5,hc5⟩:=deterministicCall M out Point.pushTail Point.pushArgs
      (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ h5 _ hp4
    have h6 := TreeTyped.Fold.splitHeads (encode a) (encode b) (encode as) s
    obtain ⟨p6,hp6,hm6,hc6⟩:=deterministicCall M out Point.splitHead Point.pushTail
      (TreeFunction.split 3 1 (by decide)) rfl _ _ _ h6 _ hp5
    have hc := OnlineControl.consBranch M out Point.check Point.halt Point.splitHead
      1 rfl (env (encode b) (encode (a::as)) s) (encode a) (encode as) rfl p6 hp6
    obtain ⟨p7,hp7,hm7,hc7⟩:=deterministicCall M out Point.loop Point.check
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 (encode (a::as)) (encode b) .nil s) _ hc
    refine ⟨p7,hp7,?_,?_⟩
    · intro g
      rw [hm7,Experiment.mean,hm6,hm5,hm4,Experiment.mean,Experiment.mean_bind]
      simp_rw [hmp,hmr,hm]
      simpa only [foldM,Experiment.mean_bind] using hrm (fun v=>(foldM f as v).mean g)
    · have hcq : ∀ v,(qp v).cost ≤ 4*sr+10+cost f F.cost as v := by
        intro v
        have hr':=(hcr v)
        have hp':=(hcp v)
        have ht:=hcost v
        simp only [size_nil] at hp'
        dsimp [sr] at *
        omega
      have ha : r.All (fun v=>(qp v).cost ≤ 4*sr+10+(f (a,b)).worst (cost f F.cost as)) := by
        apply (Experiment.all_of_mean_eq hrm _ (Experiment.all_worst (f (a,b)) (cost f F.cost as))).mono
        intro v hv
        exact (hcq v).trans (Nat.add_le_add_left hv _)
      have hbind:=Experiment.cost_bind_le_of_all r qp _ ha
      simp only [Experiment.cost,size_nil,encode_list_cons,size_cons] at hc4 hc7
      simp only [cost]
      dsimp [sr,sa] at *
      omega
end Fold

noncomputable def fold {f : A×B → Experiment B} (F : Realizer f) :
    Realizer (fun ab : List A×B=>foldM f ab.1 ab.2) where
  program := OnlineControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Fold.runs F ab.1 ab.2 s
    exact ⟨q,hq,hm,hc⟩
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineFrame
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
namespace Second
open OnlineControl

lemma runs {f : B → Experiment C} (F : Realizer f) (a : A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun ac : A×C=>env (encode ac) .nil s) (Option.some Point.split)
      (env (encode (a,b)) .nil s) q ∧
      (∀ g : A×C → ℚ,q.mean g=(f b).mean (fun c=>g (a,c))) ∧
      q.cost ≤ F.cost b+8*TreeFunction.size (encode a)+22 := by
  let M:=code F.program
  let out:=fun ac : A×C=>env (encode ac) .nil s
  have hend c:=OnlineControl.halt M out Point.halt rfl (a,c)
  have hcons c:=deterministicCall M out Point.cons Point.halt
    (TreeFunction.cons 1 0 (by decide)) rfl _ _ _ (cons10 (encode c) (encode a) s) _ (hend c)
  choose pc hc hmc hcc using hcons
  have hpop c:=deterministicCall M out Point.pop Point.cons
    (TreeFunction.split 1 2 (by decide)) rfl _ _ _ (split12 (encode c) .nil (encode a) s) _ (hc c)
  choose pp hp hmp hcp using hpop
  obtain ⟨r,hr,hmr,hcr⟩:=F.correct b (.cons (encode a) s)
  have hbody:=call M out Point.body Point.pop F.program rfl
    (env (encode b) .nil (.cons (encode a) s)) (fun c=>env (encode c) .nil (.cons (encode a) s))
    r hr pp hp
  obtain ⟨p2,hp2,hm2,hc2⟩:=deterministicCall M out Point.save Point.body
    (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ (cons12 (encode b) (encode a) s) _ hbody
  obtain ⟨p1,hp1,hm1,hc1⟩:=deterministicCall M out Point.split Point.save
    (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode a) (encode b) .nil s) _ hp2
  refine ⟨p1,hp1,?_,?_⟩
  · intro g
    rw [hm1,hm2,Experiment.mean,Experiment.mean_bind]
    simp_rw [hmp,hmc,Experiment.mean]
    exact hmr _
  · have hb : ∀ c,(pp c).cost ≤ 4*TreeFunction.size (encode a)+11 := by
      intro c
      have h1:=hcc c
      have h2:=hcp c
      simp only [Experiment.cost,size_nil] at h1 h2
      omega
    have hbind:=Experiment.cost_bind_le r pp _ hb
    simp only [Experiment.cost,size_nil] at hc1 hc2
    omega
end Second

noncomputable def mapSecond {f : B → Experiment C} (F : Realizer f) :
    Realizer (fun ab : A×B=>(f ab.2).map (Prod.mk ab.1)) where
  program := OnlineControl.compile (Second.code F.program)
  cost := fun ab=>F.cost ab.2+8*TreeFunction.size (encode ab.1)+22
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Second.runs F ab.1 ab.2 s
    exact ⟨q,hq,fun g=>by rw [Experiment.mean_map]; exact hm g,hc⟩

noncomputable def pair {f : A → Experiment B} {g : A → Experiment C}
    (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>(f a).bind (fun b=>(g a).map (Prod.mk b))) :=
  (composition (deterministic (TreeTyped.pair (TreeTyped.identity (A:=A)) TreeTyped.identity))
    (composition (mapSecond F)
      (composition (deterministic (TreeTyped.pair (TreeTyped.second (A:=A) (B:=B)) TreeTyped.first))
        (mapSecond G)))).congr (by
      intro a h
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,id_eq])
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineTraverse
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open PhysicalStream TreeTyped

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

noncomputable def collectStepRealizer {f : A → Experiment B} (F : Realizer f) :
    Realizer (collectStep f) :=
  (composition (pair (composition (deterministic TreeTyped.first) F)
    (deterministic TreeTyped.second)) (deterministic TreeTyped.listCons)).congr (by
      intro x h; simp only [Experiment.mean_bind,Experiment.mean_map,Experiment.mean,collectStep])
omit [Codec A] [Codec B] in
lemma mean_fold_collect (f : A → Experiment B) (as : List A) (bs : List B) (h : List B → ℚ) :
    (foldM (collectStep f) as bs).mean h=(traverseM f as).mean (fun cs=>h (cs.reverse++bs)) := by
  induction as generalizing bs with
  | nil => simp only [foldM,traverseM,Experiment.mean,List.reverse_nil,List.nil_append]
  | cons a as ih =>
    simp only [foldM,traverseM,collectStep,Experiment.mean_bind,Experiment.mean_map,ih]
    congr 1; funext b
    congr 1; funext cs
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
noncomputable def traverse {f : A → Experiment B} (F : Realizer f) : Realizer (traverseM f) :=
  (composition (composition (deterministic (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List B))))
    (fold (collectStepRealizer F))) (deterministic TreeTyped.reverse)).congr (by
      intro as h
      simp only [Experiment.mean_bind,Experiment.mean]
      rw [mean_fold_collect]
      simp only [List.append_nil,List.reverse_reverse,id_eq])
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_OnlineWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

noncomputable def stepRealizer : OnlineTree.Realizer step :=
  (OnlineTree.choose
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant false) TreeTyped.second) TreeTyped.listCons))
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant true) TreeTyped.second) TreeTyped.listCons))).congr
    (by intro x f; rfl)

noncomputable def listRealizer : OnlineTree.Realizer (fun as : List ℕ=>prepend as.length []) :=
  (OnlineTree.composition
    (OnlineTree.deterministic (TreeTyped.pair (TreeTyped.identity (A:=List ℕ)) (TreeTyped.constant ([] : List Bool))))
    (OnlineTree.fold stepRealizer)).congr (by
      intro as f
      change (OnlineTree.foldM step as []).mean f=(prepend as.length []).mean f
      rw [fold_step])

noncomputable def naturalRealizer : OnlineTree.Realizer (fun n : ℕ=>prepend n []) :=
  (OnlineTree.composition (OnlineTree.deterministic TreeTyped.range) listRealizer).congr
    (by intro n f; simp only [Experiment.mean_bind,Experiment.mean,List.length_range])

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

def parent {H : ℕ} (l : Label B H) : Option (Label B H) :=
  if h : 0<l.1.val then some (labelAt B hsym htri ⟨l.1.val-1,by omega⟩ l.2.val) else none

lemma parent_rank {H : ℕ} {l p : Label B H} (h : parent B hsym htri l=some p) : p.1.val<l.1.val := by
  unfold parent at h
  split_ifs at h with hl
  · cases h
    simp only [labelAt]
    omega

def componentEquiv (k : ℕ) :
    Hierarchy.Component (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) ((2:ℝ)^k) ≃
      NumberedComponent B ((2:ℚ)^k) where
  toFun := Quotient.lift (classOf B hsym htri ((2:ℚ)^k)) (by
    intro x y h
    apply Subtype.ext
    apply (root_eq_iff B hsym htri _ x y).mpr
    apply (cast_related B ((2:ℚ)^k) x y).mpr
    change Hierarchy.Related (fun x y=>(B x y:ℝ)) ((2:ℝ)^k) x y at h
    simpa only [Rat.cast_pow,Rat.cast_ofNat] using h)
  invFun x := Quotient.mk _ x.val
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      apply Quotient.sound
      change Hierarchy.Related (fun x y=>(B x y:ℝ)) ((2:ℝ)^k) (root B ((2:ℚ)^k) x) x
      have h := (cast_related B ((2:ℚ)^k) _ _).mp
        (related_symm B hsym ((2:ℚ)^k) (related_root B ((2:ℚ)^k) x))
      simpa only [Rat.cast_pow,Rat.cast_ofNat] using h
  right_inv := by intro x; apply Subtype.ext; exact x.property

def labelEquiv (H : ℕ) :
    Hierarchy.Label (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) H ≃ Label B H :=
  Equiv.sigmaCongrRight (fun k=>componentEquiv B hsym htri k.val)

lemma componentEquiv_mk (k : ℕ) (x : V) :
    componentEquiv B hsym htri k (Quotient.mk _ x)=classOf B hsym htri ((2:ℚ)^k) x := by
  rfl

lemma labelEquiv_at {H : ℕ} (k : Fin (H+1)) (x : V) :
    labelEquiv B hsym htri H (Hierarchy.labelAt _ _ _ k x)=labelAt B hsym htri k x := by
  simp [labelEquiv,Hierarchy.labelAt,labelAt,componentEquiv_mk]

lemma member_labelAt {H : ℕ} (k : Fin (H+1)) (x y : V) :
    member B (labelAt B hsym htri k x) y ↔ related B ((2:ℚ)^k.val) y x := by
  exact root_eq_iff B hsym htri _ y x

lemma member_equiv {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) (x : V) :
    member B (labelEquiv B hsym htri H l) x ↔
      Hierarchy.Mem (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) l x := by
  obtain ⟨k,l⟩:=l
  induction l using Quotient.inductionOn with | h y =>
    change member B (labelEquiv B hsym htri H (Hierarchy.labelAt _ _ _ k y)) x ↔ _
    rw [labelEquiv_at,member_labelAt]
    change related B ((2:ℚ)^k.val) x y ↔ Hierarchy.Mem _ _ _ (Hierarchy.labelAt _ _ _ k y) x
    rw [Hierarchy.mem_class_iff]
    simpa only [Rat.cast_pow,Rat.cast_ofNat] using cast_related B ((2:ℚ)^k.val) x y

lemma parent_iff {H : ℕ} (l p : Label B H) : parent B hsym htri l=some p ↔
    p.1.val+1=l.1.val ∧ member B p l.2.val := by
  obtain ⟨k,l⟩:=l
  obtain ⟨j,p⟩:=p
  unfold parent
  split_ifs with hl
  · change 0<k.val at hl
    constructor
    · intro h
      have he := Option.some.inj h
      have hk := congrArg (fun l : Label B H => l.1.val) he
      constructor
      · change j.val+1=k.val
        change k.val-1=j.val at hk
        omega
      · rw [←he]
        rfl
    · rintro ⟨hp,hm⟩
      change j.val+1=k.val at hp
      have hj : j=(⟨k.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ : Fin (H+1)) := by
        apply Fin.ext
        change j.val=k.val-1
        omega
      cases hj
      congr 1
      apply congrArg (Sigma.mk _)
      exact Subtype.ext hm
  · constructor
    · intro h; cases h
    · rintro ⟨hp,_⟩
      change j.val+1=k.val at hp
      change ¬0<k.val at hl
      omega

lemma parent_equiv_iff {H : ℕ}
    (l p : Hierarchy.Label (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) H) :
    parent B hsym htri (labelEquiv B hsym htri H l)=some (labelEquiv B hsym htri H p) ↔
      Hierarchy.Parent (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) p l := by
  rw [parent_iff]
  change (p.1.val+1=l.1.val ∧ _) ↔ _
  let v := (labelEquiv B hsym htri H l).2.val
  have hl : Hierarchy.Mem _ (symmetric B hsym) (triangular B htri) l v :=
    (member_equiv B hsym htri l v).mp (member_self B _)
  constructor
  · rintro ⟨hp,hm⟩
    exact ⟨hp,v,(member_equiv B hsym htri p v).mp hm,hl⟩
  · intro h
    exact ⟨h.1,(member_equiv B hsym htri p v).mpr (Hierarchy.parent_mem _ _ _ h hl)⟩

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

omit [Fintype E] [DecidableEq E] in
lemma edgeLabel_equiv [Fintype E] [DecidableEq E] (H : ℕ) (e : E) :
    labelEquiv B hsym htri H (Hierarchy.edgeLabel (fun x y=>(B x y:ℝ))
      (symmetric B hsym) (triangular B htri) left right H e)=edgeLabel B hsym htri left right H e := by
  unfold Hierarchy.edgeLabel edgeLabel
  rw [←level_cast]
  exact labelEquiv_at B hsym htri _ _

omit [DecidableEq E] in
lemma mem_bags [DecidableEq E] (H : ℕ) (x : V) (l : Label B H) :
    l∈bags B hsym htri left right H x ↔
      ∃ e,(x=left e ∨ x=right e) ∧ edgeLabel B hsym htri left right H e=l := by
  simp [bags]

lemma bags_equiv (H : ℕ) (x : V) :
    (Hierarchy.memberships (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri)
      left right H x).image (labelEquiv B hsym htri H)=bags B hsym htri left right H x := by
  classical
  ext l
  simp only [mem_image,mem_bags,Hierarchy.mem_memberships,Hierarchy.Incident]
  constructor
  · rintro ⟨a,⟨e,he,hea⟩,hal⟩
    refine ⟨e,he,?_⟩
    rw [←edgeLabel_equiv,hea,hal]
  · rintro ⟨e,he,hel⟩
    refine ⟨_,⟨e,he,rfl⟩,?_⟩
    rwa [edgeLabel_equiv]

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

def bags (w : V → V → ℚ) (K : ℕ) : SourceVertex V K → Finset (Label w K) :=
  NumberedHierarchy.bags (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K)

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ) (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

attribute [local instance] labelOrder

noncomputable def abstractTree (H : ℕ) : SimpleGraph (Label B H) :=
  (Hierarchy.tree (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri)).comap
    (labelEquiv B hsym htri H).symm

lemma abstractTree_acyclic (H : ℕ) : (abstractTree B hsym htri H).IsAcyclic := by
  exact SimpleGraph.IsAcyclic.of_comap (labelEquiv B hsym htri H).symm.toEmbedding
    (Hierarchy.tree_acyclic _ _ _ _)

lemma abstractTree_adj (H : ℕ) (a b : Label B H) :
    (abstractTree B hsym htri H).Adj a b ↔
      parent B hsym htri b=some a ∨ parent B hsym htri a=some b := by
  change (Hierarchy.Parent _ _ _ ((labelEquiv B hsym htri H).symm a) ((labelEquiv B hsym htri H).symm b) ∨
    Hierarchy.Parent _ _ _ ((labelEquiv B hsym htri H).symm b) ((labelEquiv B hsym htri H).symm a)) ↔ _
  have ha:=parent_equiv_iff B hsym htri ((labelEquiv B hsym htri H).symm b) ((labelEquiv B hsym htri H).symm a)
  have hb:=parent_equiv_iff B hsym htri ((labelEquiv B hsym htri H).symm a) ((labelEquiv B hsym htri H).symm b)
  simpa only [Equiv.apply_symm_apply] using or_congr ha.symm hb.symm

def tree (H : ℕ) : SimpleGraph (Label B H) where
  Adj a b := parent B hsym htri b=some a ∨ parent B hsym htri a=some b
  symm := ⟨fun _ _ h=>Or.symm h⟩
  loopless := ⟨by intro a h; rcases h with h|h <;> exact (Nat.lt_irrefl _ (parent_rank B hsym htri h))⟩

instance treeDec (H : ℕ) : DecidableRel (tree B hsym htri H).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (parent B hsym htri b=some a ∨ parent B hsym htri a=some b))

lemma tree_adj (H : ℕ) (a b : Label B H) :
    (tree B hsym htri H).Adj a b ↔
      parent B hsym htri b=some a ∨ parent B hsym htri a=some b := Iff.rfl

lemma tree_eq (H : ℕ) : tree B hsym htri H=abstractTree B hsym htri H := by
  ext a b
  exact (abstractTree_adj B hsym htri H a b).symm

lemma tree_acyclic (H : ℕ) : (tree B hsym htri H).IsAcyclic := by
  rw [tree_eq]
  exact abstractTree_acyclic B hsym htri H

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

lemma bags_nonempty (H : ℕ) (hx : ∀ x,∃ e,x=left e ∨ x=right e) (x : V) :
    (bags B hsym htri left right H x).Nonempty := by
  obtain ⟨e,he⟩:=hx x
  exact ⟨_,(mem_bags _ _ _ _ _ _ _ _).mpr ⟨e,he,rfl⟩⟩

lemma bags_adjacent (H : ℕ) (hfloor : ∀ x y,1≤B x y)
    (hmax : ∀ e,B (left e) (right e)<(2:ℚ)^(H+1))
    (hnear : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      B (left e) (right e)≤2*B (left f) (right f)) :
    ∀ x a,a∈bags B hsym htri left right H x → ∀ b∈bags B hsym htri left right H x,
      a=b ∨ (tree B hsym htri H).Adj a b := by
  intro x a ha b hb
  rw [←bags_equiv] at ha hb
  obtain ⟨a',ha',rfl⟩:=mem_image.mp ha
  obtain ⟨b',hb',rfl⟩:=mem_image.mp hb
  have hf : ∀ x y,1≤(B x y:ℝ) := by intro x y; exact_mod_cast hfloor x y
  have hm : ∀ e,(B (left e) (right e):ℝ)<(2:ℝ)^(H+1) := by
    intro e; exact_mod_cast hmax e
  have hn : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      (B (left e) (right e):ℝ)≤2*(B (left f) (right f):ℝ) := by
    intro x e f he hf; exact_mod_cast hnear x e f he hf
  have h:=Hierarchy.memberships_tree_bags (fun x y=>(B x y:ℝ)) (symmetric B hsym)
    (triangular B htri) hf left right H hm hn x a' b' ha' hb'
  rcases h with h|h
  · exact Or.inl (congrArg _ h)
  · exact Or.inr (by simpa only [tree_eq,abstractTree,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using h)

lemma bags_ranked (H : ℕ) (hfloor : ∀ x y,1≤B x y)
    (hmax : ∀ e,B (left e) (right e)<(2:ℚ)^(H+1))
    (hnear : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      B (left e) (right e)≤2*B (left f) (right f)) :
    RankedBags (bags B hsym htri left right H) (fun l=>l.1.val) (parent B hsym htri) := by
  intro x a ha b hb hab
  rcases bags_adjacent B hsym htri left right H hfloor hmax hnear x a ha b hb with h|h
  · exact (hab h).elim
  · rcases (tree_adj B hsym htri H a b).mp h with h|h
    · exact Or.inl ⟨parent_rank B hsym htri h,h⟩
    · exact Or.inr ⟨parent_rank B hsym htri h,h⟩

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

def parent (w : V → V → ℚ) (K : ℕ) : Label w K → Option (Label w K) :=
  NumberedHierarchy.parent (realB w K) (realB_symm w K) (realB_tri w K)

def tree (w : V → V → ℚ) (K : ℕ) : SimpleGraph (Label w K) :=
  NumberedHierarchy.tree (realB w K) (realB_symm w K) (realB_tri w K) (levels w K)

lemma tree_acyclic (w : V → V → ℚ) (K : ℕ) : (tree w K).IsAcyclic :=
  NumberedHierarchy.tree_acyclic _ _ _ _

lemma parent_rank (w : V → V → ℚ) (K : ℕ) (l p : Label w K)
    (h : parent w K l=some p) : p.1.val<l.1.val :=
  NumberedHierarchy.parent_rank _ _ _ h

lemma bags_adjacent (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    ∀ x a,a∈bags w K x → ∀ b∈bags w K x,a=b ∨ (tree w K).Adj a b :=
  NumberedHierarchy.bags_adjacent _ _ _ _ _ _ (realB_floor w K) (realB_upper w K h) (realB_near w K h)

lemma bags_ranked (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    UnitRefresh.RankedBags (bags w K) (fun l=>l.1.val) (parent w K) :=
  NumberedHierarchy.bags_ranked _ _ _ _ _ _ (realB_floor w K) (realB_upper w K h) (realB_near w K h)

lemma bags_nonempty (w : V → V → ℚ) (K : ℕ) (x : SourceVertex V K) :
    (bags w K x).Nonempty :=
  NumberedHierarchy.bags_nonempty _ _ _ _ _ _ (incident_exists K) x

def realLabel (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : Label w K :=
  NumberedHierarchy.edgeLabel (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K) e

def coloredReal (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : BagEdge (bags w K) :=
  ⟨⟨(edge source target (4*(2*K+2)) e.1 e.2,realLabel w K e),real_not_diag K e⟩,by
    intro x hx
    apply (NumberedHierarchy.mem_bags _ _ _ (realLeft K) (realRight K) (levels w K) x _).mpr
    refine ⟨e,?_,rfl⟩
    simpa [ColoredEdge.Incident,realLeft,realRight,edge] using hx⟩

lemma coloredReal_injective (w : V → V → ℚ) (K : ℕ) : Function.Injective (coloredReal w K) := by
  intro e f h
  apply edge_injective source target (4*(2*K+2)) (by omega)
  exact congrArg (fun q : BagEdge (bags w K)=>q.val.val.1) h

def realPortion (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  ∑ q : SourceRealEdge V K,if coloredReal w K q=e then pathActivity w K q.1 q.2 else 0

lemma realPortion_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (bags w K)) : 0 ≤ realPortion w K e := by
  apply sum_nonneg
  intro q _
  split_ifs
  · exact (pathActivity_pos w hw K q.1 q.2).le
  · exact le_rfl

def bagWeight (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  realPortion w K e+bagHeight w K e.color/D

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_r8c2707_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
def sampler (w : V → V → ℚ) (K D T m : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (s : Slot T (ladderQ (Fintype.card (SourceVertex V K)) D) → BagPM (bags w K)) :=
  finiteLadder (bags_adjacent w K h) (tree_acyclic w K) (fun l=>l.1.val) (parent w K)
    (bags_ranked w K h) (bags_nonempty w K) (parent_rank w K) D K T m hq (bagWeight w K D) M η s

noncomputable local instance instFintypeBagPMSourceVertexLabelBags (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_1_r8c2707_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance instFintypeBagPMSourceVertexLabelBags_1 (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

def topSampler (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :=
  fun bits => sampler w K D (endpoint (Fintype.card (SourceVertex V K)) D K hN) m h hq M η
    (fun _=>M) bits (topSlot _ _ hq)

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqLabelOfFintype
noncomputable def labelsEquiv (w : V → V → ℚ) (K : ℕ) :
    SourceLabel (fun x y=>(w x y:ℝ)) K ≃ Label w K :=
  (labelCast (sourceRealB_comm _ _) (sourceRealB_tri _ _)
    (NumberedHierarchy.symmetric (realB w K) (realB_symm w K))
    (NumberedHierarchy.triangular (realB w K) (realB_tri w K))
    (by funext x y;exact (realB_cast w K x y).symm) (levels_eq w K).symm).trans
      (NumberedHierarchy.labelEquiv (realB w K) (realB_symm w K) (realB_tri w K) (levels w K))

lemma source_bags_equiv (w : V → V → ℚ) (K : ℕ) (x : SourceVertex V K) :
    (sourceBags (fun a b=>(w a b:ℝ)) K x).image (labelsEquiv w K)=bags w K x := by
  change image ((NumberedHierarchy.labelEquiv _ _ _ _) ∘ _ ) _=_
  rw [←image_image,sourceBags,labelCast_bags]
  exact NumberedHierarchy.bags_equiv (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K) x

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RelabelMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

lemma labelsEquiv_edgeLabel (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    labelsEquiv w K (Hierarchy.edgeLabel (sourceRealB (fun x y=>(w x y:ℝ)) K)
      (sourceRealB_comm _ _) (sourceRealB_tri _ _) (realLeft K) (realRight K)
      (sourceLevels (fun x y=>(w x y:ℝ)) K) q)=realLabel w K q := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,labelCast_edgeLabel,NumberedHierarchy.edgeLabel_equiv,realLabel]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RelabelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open MatchingFPRAS Transport Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal
noncomputable def sourceEdgeEquiv (w : V → V → ℚ) (K : ℕ) :
    BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K) ≃ BagEdge (bags w K) :=
  relabelEdgeEquiv (labelsEquiv w K) (source_bags_equiv w K)
lemma sourceEdgeEquiv_real (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceEdgeEquiv w K (sourceColoredReal (fun x y=>(w x y:ℝ)) K q)=coloredReal w K q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact labelsEquiv_edgeLabel w K q
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_r8c2707_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma Parameters.K_pos (p : Parameters G) : 0<p.K := p.schedule.1

omit [Nontrivial (Fin G.n)] in
lemma Parameters.epsilon_real_pos (p : Parameters G) : (0:ℝ)<p.epsilon := by exact_mod_cast p.epsilon_pos

omit [Nontrivial (Fin G.n)] in
lemma Parameters.epsilon_real_lt_one (p : Parameters G) : (p.epsilon:ℝ)<1 := by exact_mod_cast p.epsilon_lt_one

noncomputable def Parameters.D (p : Parameters G) : ℕ := sourceD (V:=Fin G.n) p.K

def Parameters.N (p : Parameters G) : ℕ := Fintype.card (SourceVertex (Fin G.n) p.K)

omit [Nontrivial (Fin G.n)] in
lemma Parameters.N_pos (p : Parameters G) : 0<p.N := by
  have h := sourceVertex_card_ge (V:=Fin G.n) p.K
  simp only [Fintype.card_fin] at h
  exact lt_of_lt_of_le (by have := p.hn; omega) h

lemma Parameters.D_pos (p : Parameters G) : 0<p.D := sourceD_one _

noncomputable def Parameters.T (p : Parameters G) : ℕ := ladderTier p.N p.D p.K p.N_pos

noncomputable def Parameters.q (p : Parameters G) : ℕ := ladderQ p.N p.D

lemma Parameters.q_pos (p : Parameters G) : 0<p.q := by
  unfold Parameters.q ladderQ ladderL
  have hn := p.N_pos
  have hd := p.D_pos
  positivity

noncomputable def Parameters.sigma (p : Parameters G) : ℝ := RealStage.sigma p.D p.K p.epsilon

noncomputable def Parameters.S (p : Parameters G) : ℕ := stageSampleCount G.n p.D p.K p.epsilon

noncomputable def Parameters.initialData (p : Parameters G) : StageData G.n p.K p.K :=
  stageData G p.hn p.even p.K p.K_pos p.epsilon p.epsilon_real_pos p.epsilon_real_lt_one 0
    (Nat.zero_le _) (initialScaleState G p.hn) (initial_balanced G p.hn p.even)

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Marking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_2_r8c2707_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance instFintypeBagPMSourceVertexLabelBags_2 (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

def centralEdge (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) : BagEdge (bags w K) :=
  coloredReal w K (e,⟨2*(2*K+2),by omega⟩)
def probePortion (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  if ∃ q,centralEdge w K q=e then 1/(D:ℚ) else 0
def portions (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : Fin 3 → ℚ :=
  ![realPortion w K e,bagHeight w K e.color/D-probePortion w K D e,probePortion w K D e]
lemma portions_sum (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) :
    ∑ i,portions w K D e i=bagWeight w K D e := by
  simp [portions,Fin.sum_univ_succ,bagWeight]
lemma portions_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ)
    (e : BagEdge (bags w K)) (i : Fin 3) : 0≤portions w K D e i := by
  fin_cases i
  · exact realPortion_nonneg w hw K e
  · change 0≤bagHeight w K e.color/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (by dsimp [bagHeight]; positivity) (Nat.cast_nonneg D)
  · change 0≤probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity
lemma bagWeight_pos (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) : 0<bagWeight w K D e := by
  apply add_pos_of_nonneg_of_pos (realPortion_nonneg w hw K e)
  exact div_pos (by dsimp [bagHeight]; positivity) (by exact_mod_cast hD)

def markingTable (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) : WeightedOptions (Fin 3) where
  size:=3
  out:=id
  mass i:=portions w K D e i/bagWeight w K D e
  nonneg i:=div_nonneg (portions_nonneg w hw K D e i) (bagWeight_pos w hw K D hD e).le
  total:=by rw [←sum_div,portions_sum,div_self (bagWeight_pos w hw K D hD e).ne']

abbrev Marked (w : V → V → ℚ) (K : ℕ) := TableMarking.Marked (I:=Fin 3) (BagEdge.Incident (bags:=bags w K))
noncomputable local instance sourceMarkedFintype (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable def markedLaw (w : V → V → ℚ) (K D : ℕ) : Marked w K → ℝ :=
  sigmaLift (gibbs (fun e=>(bagWeight w K D e:ℝ)))
    (fun M=>product (fun e : M.val=>fun i=>(portions w K D e.val i/bagWeight w K D e.val:ℚ)))

def markedSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :=
  TableMarking.draw BagEdge.Incident (topSampler w K D m hN h hq M η)
    (markingTable w hw K D hD)
    (bitPrecision (6*Fintype.card (BagEdge (bags w K))) η)

noncomputable local instance sourceMarkingBitsFintype {A : Type*} [Fintype A]
    (w : V → V → ℚ) (K k : ℕ) :
    Fintype (A × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _

noncomputable def markedSamplerLaw (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    Marked w K → ℝ := imageLaw (markedSampler w hw K D m hD hN h hq M η)

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_r8c2707_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable def sourceMarkedEquiv (w : V → V → ℚ) (K : ℕ) :
    SourceMarked (fun x y=>(w x y:ℝ)) K ≃ Marked w K :=
  markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_2
def bagReweight (w w₁ : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  1+∑ q : SourceRealEdge V K,if coloredReal w K q=e then rawReweight w w₁ K q-1 else 0
lemma bagReweight_on (w w₁ : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    bagReweight w w₁ K (coloredReal w K q)=rawReweight w w₁ K q := by
  simp only [bagReweight,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]
  ring
lemma bagReweight_off (w w₁ : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : bagReweight w w₁ K e=1 := by
  have hz : (∑ q : SourceRealEdge V K,if coloredReal w K q=e then rawReweight w w₁ K q-1 else 0)=0 := by
    apply sum_eq_zero
    intro q _
    exact ite_eq_right (fun h=>he ⟨q,h⟩)
  rw [bagReweight,hz,add_zero]
lemma bagReweight_cast (w w₁ : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (bagReweight w w₁ K (sourceEdgeEquiv w K e):ℝ)=
      Enlargement.bagReweight (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,bagReweight_on]
    exact (rawReweight_cast w w₁ K q).trans (Enlargement.bagReweight_on _ _ K q).symm
  · rw [bagReweight_off w w₁ K _ ?_]
    · unfold Enlargement.bagReweight
      change ¬∃ q,sourceRealEmbedding (fun x y=>(w x y:ℝ)) K q=e at he
      rw [dite_eq_right he]
      norm_cast
    · rintro ⟨q,hq⟩
      apply he
      refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
      rwa [sourceEdgeEquiv_real]

def observableA (w : V → V → ℚ) (K : ℕ) (a : Marked w K) : ℚ :=
  if a.2=(fun _=>0) then 1 else 0

def observableD (w w₁ : V → V → ℚ) (K : ℕ) (a : Marked w K) : ℚ :=
  if a.2=(fun _=>0) then ∏ e ∈ a.1.val,bagReweight w w₁ K e else 0

def observableProbe (w w₁ : V → V → ℚ) (K : ℕ) (e₀ : LogicalEdge V) (a : Marked w K) : ℚ :=
  if {centralEdge w K e₀}⊆a.1.val ∧
      a.2=(fun e=>if e.val∈({centralEdge w K e₀}:Finset _) then 2 else 0)
    then ∏ e ∈ a.1.val \ {centralEdge w K e₀},bagReweight w w₁ K e else 0
end MatchingFPRAS.RationalSource
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_3
lemma sourceEdgeEquiv_incidence (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (x : SourceVertex V K) :
    (sourceEdgeEquiv w K e).Incident x ↔ e.Incident x := Iff.rfl
lemma sourceMarkedEquiv_zero (w : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (sourceMarkedEquiv w K a).2=(fun _=>0) ↔ a.2=(fun _=>0) :=
  markedEquiv_zero (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
lemma observableA_cast (w : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableA w K (sourceMarkedEquiv w K a):ℝ)=Enlargement.observableA (fun x y=>(w x y:ℝ)) K a := by
  simp only [observableA,Enlargement.observableA,sourceMarkedEquiv_zero]
  split_ifs <;> norm_cast
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_3
lemma observableD_cast (w w₁ : V → V → ℚ) (K : ℕ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableD w w₁ K (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableD (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K a := by
  simp only [observableD,Enlargement.observableD,sourceMarkedEquiv_zero]
  split_ifs
  · push_cast
    change matchingWeight (fun e=>(bagReweight w w₁ K e:ℝ))
      (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1)=_
    rw [matchingWeight_pmEquiv (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    unfold matchingWeight
    apply prod_congr rfl
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeCostMeasure
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def WorkBound {f : A → B} (F : Realizer f) (measure : A → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a,F.cost a+weight (f a)≤p.eval (measure a)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

variable {n m : ℕ}
def realRepr (e : LogicalEdge (Fin n)×Fin (m+1)) : RawReal := (logicalRepr e.1,e.2.val)
def vertexRepr : Vertex (Fin n) (LogicalEdge (Fin n)) m→RawVertex
  | .inl v => .inl v.val
  | .inr (e,i) => .inr (logicalRepr e,i.val)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

def inputStacks {A : Type} [Codec A] (a : A) : Stack (K Reg) :=
  encodeEnv (env (TreeTyped.encode a) .nil .nil)

noncomputable def packed {A : Type} [Codec A] (a : A) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (inputStacks a) (weight a)
end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder ExecutableMarking ExecutableOptions TreeTyped.Numbered UnitRefresh

def tableRealizer : Realizer table := getDFast []
def assignRealizer : Realizer assign := ExecutableMarking.assignRealizer tableRealizer natEqual

variable {E : Type} [Fintype E] [LinearOrder E]
noncomputable def tableRep (f : E→WeightedOptions (Fin 3)) : Tables :=
  List.ofFn (fun i=>ExecutableOptions.repr Fin.val (f (orderedEnum E i)))
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericLadder
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder

def rowRealizer : Realizer row := composition (pair first.fst.fst.fst.snd second) (getDFast [])
def guideRealizer : Realizer guide := composition
  (pair (composition (pair first.snd second.fst) (getDFast [])) second.snd) membership
def pairContextRealizer : Realizer pairContext := pair first.fst.fst.fst.fst
  (pair (composition (pair first second.fst) rowRealizer) (composition (pair first second.snd) rowRealizer))
def pairRealizer : Realizer pairDraw := (composition
  (pair (pair (pair (composition first pairContextRealizer) first.fst.fst.fst.snd) second.fst)
    second.snd.fst) ExecutablePair.drawRealizer).congr (fun _=>rfl)
def refreshRealizer : Realizer refresh := composition
  (pair first.fst.fst.snd second.snd) ExecutableRefresh.refreshRealizer
def executeRealizer : Realizer execute :=
  fold (runStepRealizer guideRealizer pairRealizer refreshRealizer natEqual leNat natEqual)
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderContext
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered UnitRefresh ExecutablePair

variable {I E V : Type} [Fintype I] [LinearOrder I] [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def contextRep (ends : E→Sym2 V) (w : I→E→ℚ) (guides : I→Finset I) (refresh : RefreshSetup) : Context :=
  let eps := List.ofFn (fun e=>endpointRep (ends (orderedEnum E e)))
  let rows := List.ofFn (fun i=>List.ofFn (fun e=>TreeFraction.repr (w (orderedEnum I i) (orderedEnum E e))))
  let univ := (Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset E))
  let gs := List.ofFn (fun i=>(Numbered.set (guides (orderedEnum I i))).sort (·≤·))
  ((((eps,rows),univ),refresh),gs)
attribute [local instance] Transport.Sparse.pmOrder
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderIndexed
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder

attribute [local instance] Transport.prodOrder Transport.sumOrder
variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]

def typedGuide (x : Context×(I×I)) : Bool := guide (x.1,(index x.2.1,index x.2.2))
def typedPair (x : LocalPairInput Context I (Finset ℕ) Bits) : Finset ℕ×Finset ℕ :=
  pairDraw ((x.1.1,(index x.1.2.1,index x.1.2.2)),x.2)
def typedRefresh (x : LocalRefreshInput Context I Bits) : Finset ℕ := refresh ((x.1.1,index x.1.2),x.2)
def typedGuideRealizer : Realizer (typedGuide (I:=I)) := guideRealizer.recode
  (fun x : Context×(I×I)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedPairRealizer : Realizer (typedPair (I:=I)) := pairRealizer.recode
  (fun x : LocalPairInput Context I (Finset ℕ) Bits=>((x.1.1,(index x.1.2.1,index x.1.2.2)),x.2)) _ (fun _=>rfl) (fun _=>rfl)
def typedRefreshRealizer : Realizer (typedRefresh (I:=I)) := refreshRealizer.recode
  (fun x : LocalRefreshInput Context I Bits=>((x.1.1,index x.1.2),x.2)) _ (fun _=>rfl) (fun _=>rfl)
abbrev TypedInput (I : Type) := List (List Bool×Bits)×(RunSetup Context I ℕ×StateTable I (Finset ℕ))
def typedExecute (x : TypedInput I) : RunSetup Context I ℕ×StateTable I (Finset ℕ) :=
  x.1.foldl (fun z b=>runStep typedGuide typedPair typedRefresh (b,z)) x.2
def typedExecuteRealizer : Realizer (typedExecute (I:=I)) :=
  fold (runStepRealizer typedGuideRealizer typedPairRealizer typedRefreshRealizer Numbered.equal Numbered.lessEqual natEqual)
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder TreePost Turing

variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
def numericSetup (x : RunSetup Context I ℕ) : RunSetup Context ℕ ℕ :=
  ((x.1.1,(Numbered.set x.1.2.1,Numbered.set x.1.2.2)),(x.2.1.map index,x.2.2))
def numericInput (x : TypedInput I) : Input := (x.1,(numericSetup x.2.1,numericState x.2.2))
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder UnitRefresh Transport Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)
variable {T q : ℕ} [Inhabited (Slot T q)]

def sourceContext (w : BagEdge bags→ℚ) (a : ExecutableDP.Bags) : Context :=
  contextRep (fun e : BagEdge bags=>e.val.val.1) (rationalSlotWeight (T:=T) (q:=q) w) guides
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeTierWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
def slotCountRealizer : Realizer slotCount := (composition
  (pair (composition (composition first.snd listLength) successor)
    (composition second.fst listLength)) multiply).congr (fun _=>rfl)
def slotsRealizer : Realizer slots := composition slotCountRealizer range
def weightRowRealizer : Realizer weightRow := (composition
  (pair (pair first.fst (composition (pair second (composition first.snd.fst listLength)) quotient)) first.snd.snd)
  (mapWith slotWeightRealizer)).congr (fun _=>rfl)
def weightRowsRealizer : Realizer weightRows := composition (pair identity slotsRealizer) (mapWith weightRowRealizer)
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeGuideTables
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

def slotUniverseRealizer : Realizer slotUniverse := composition slotsRealizer (listFinset natEqual leNat)
def guideTestRealizer : Realizer guideTest := by
  let q : Realizer (fun x : (TierData×ℕ)×ℕ=>x.1.1.2.1.length) := composition first.fst.snd.fst listLength
  let r : Realizer (fun x : (TierData×ℕ)×ℕ=>x.1.2/x.1.1.2.1.length) := composition (pair first.snd q) quotient
  exact (composition (pair (composition (pair r (composition first.fst.fst.snd listLength)) less)
    (composition (pair (composition (pair second q) quotient) (composition r successor)) natEqual)) boolAnd).congr
    (by intro x; simp [guideTest])
def guideSetRealizer : Realizer guideSet := composition (pair identity (composition first slotUniverseRealizer))
  (finsetFilterWith guideTestRealizer)
def guideRowsRealizer : Realizer guideRows := composition (pair identity slotsRealizer)
  (mapWith (composition guideSetRealizer finsetList))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepareLadder
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

def prepareContextRealizer : Realizer prepareContext := (pair
  (pair (pair (pair first.snd.fst (composition first.fst weightRowsRealizer)) first.snd.snd) second)
  (composition first.fst guideRowsRealizer)).congr (fun _=>rfl)
def baseTestRealizer : Realizer baseTest := (composition
  (pair (composition (pair second (composition first.snd.fst listLength)) quotient)
    (composition first.fst.snd listLength)) natEqual).congr (fun _=>rfl)
def baseSetRealizer : Realizer baseSet := composition (pair identity slotUniverseRealizer)
  (finsetFilterWith baseTestRealizer)
def prepareSetupRealizer : Realizer prepareSetup := (pair
  (pair prepareContextRealizer (pair (composition first.fst slotUniverseRealizer)
    (composition first.fst baseSetRealizer)))
  (pair (composition first.fst slotsRealizer) first.snd.snd.snd)).congr (fun _=>rfl)
def prepareStateRealizer : Realizer prepareState := (pair (composition first prepareSetupRealizer)
  (composition (pair second (composition first.fst.fst slotsRealizer)) (mapWith (pair second first)))).congr (fun _=>rfl)
def preparedRunRealizer : Realizer preparedRun := composition (pair first (composition second prepareStateRealizer)) executeRealizer
def preparedTopRealizer : Realizer preparedTop := (composition
  (pair (composition (composition preparedRunRealizer second) identity) (constant 0)) (lookupRealizer ∅ natEqual)).congr (fun _=>rfl)
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepared
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
def sourcePrepared (rank : L→ℕ) (parent : L→Option L) (w : BagEdge bags→ℚ)
    (a : ExecutableDP.Bags) (ft fq : List Bool) : Prepared :=
  ((((Fintype.card V,ft),(fq,List.ofFn (fun e=>TreeFraction.repr (w (orderedEnum _ e))))),
    (List.ofFn (fun e=>ExecutablePair.endpointRep (orderedEnum (BagEdge bags) e).val.val.1),
      (Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset (BagEdge bags))))),
    (ExecutableRefresh.storedCatalog (a,List.range (Fintype.card L)),
      ((a,ExecutableDP.parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedMarked
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

def sampleRealizer : Realizer sample := (composition (pair (pair first.snd second.snd)
  (composition (pair second.fst first.fst) preparedTopRealizer)) assignRealizer).congr (fun _=>rfl)

def sampleMany (x : SampleContext×List SampleBits) : List (ExecutableMarking.Marks ℕ) :=
  x.2.map (fun b=>sample (x.1,b))
def sampleManyRealizer : Realizer sampleMany := mapWith sampleRealizer

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_OnlineSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open PhysicalStream TreeTyped

variable {A : Type} [Codec A]
def repeatInputRealizer : TreeTyped.Realizer (fun x : ℕ×A=>List.replicate x.1 x.2) :=
  (TreeTyped.composition (TreeTyped.pair TreeTyped.second (TreeTyped.composition TreeTyped.first TreeTyped.range))
    (TreeTyped.mapWith TreeTyped.first)).congr (by intro x; simp)

noncomputable def wordsRealizer : OnlineTree.Realizer words :=
  (OnlineTree.composition (OnlineTree.deterministic (TreeTyped.composition
    (TreeTyped.pair TreeTyped.second TreeTyped.first) repeatInputRealizer))
    (OnlineTree.traverse OnlineWord.naturalRealizer)).congr (by intro x h; rfl)

noncomputable def localRealizer : OnlineTree.Realizer localWords :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) OnlineWord.naturalRealizer)
    wordsRealizer

noncomputable def scanRealizer : OnlineTree.Realizer scan :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) OnlineWord.naturalRealizer)
    localRealizer

noncomputable def scansRealizer : OnlineTree.Realizer scans :=
  (OnlineTree.composition (OnlineTree.deterministic (TreeTyped.composition
    (TreeTyped.pair TreeTyped.second TreeTyped.first) repeatInputRealizer))
    (OnlineTree.traverse scanRealizer)).congr (by intro x h; rfl)

noncomputable def markWordRealizer : OnlineTree.Realizer markWord :=
  OnlineTree.mapSecond OnlineWord.naturalRealizer

def markRequestsRealizer : TreeTyped.Realizer markRequests :=
  (TreeTyped.mapWith (TreeTyped.pair TreeTyped.second TreeTyped.first)).congr (fun _=>rfl)
noncomputable def marksRealizer : OnlineTree.Realizer marks :=
  OnlineTree.composition (OnlineTree.deterministic markRequestsRealizer) (OnlineTree.traverse markWordRealizer)

noncomputable def sampleRealizer : OnlineTree.Realizer sample :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) scansRealizer)
    (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) marksRealizer)
noncomputable def manyRealizer : OnlineTree.Realizer many :=
  OnlineTree.composition (OnlineTree.deterministic repeatInputRealizer) (OnlineTree.traverse sampleRealizer)
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalStart
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Enlargement Subdivision RealGeometry Switching

variable {n : ℕ}
variable [Nontrivial (Fin n)]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

def startMatching (w : Fin n → Fin n → ℚ) (K : ℕ) (he : Even n) : BagPM (bags w K) :=
  ⟨(startSet K he).map ⟨coloredReal w K,coloredReal_injective w K⟩,by
    exact (matching_map_iff
      (fun (q : SourceRealEdge (Fin n) K) x=>x∈edge source target (4*(2*K+2)) q.1 q.2)
      BagEdge.Incident ⟨coloredReal w K,coloredReal_injective w K⟩
      (fun _ _=>Iff.rfl) (startSet K he) univ).mpr (startSet_matching K he)⟩
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

def setupBags (x : BagBuildInput) : ExecutableDP.Bags :=
  buildBags (x.1,hierarchyFuel (x.1.1.1,x.2))

attribute [local instance] NumberedHierarchy.labelOrder
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMetadata
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceParents (x : BagBuildInput) : ExecutableDP.Parents := parents (setupHierarchy x).1
def sourceParentsRealizer : Realizer sourceParents := composition setupHierarchyRealizer.fst parentsRealizer
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def rangeFromListRealizer {A : Type} [Codec A] : Realizer (rangeFromList (A:=A)) :=
  composition (composition listLength range) (listFinset natEqual leNat)
def sourceEdgeDataRealizer : Realizer sourceEdgeData := (pair
  (composition sourceTablesRealizer.fst (map first))
  (pair (composition sourceVerticesRealizer rangeFromListRealizer)
    (composition sourceTablesRealizer.fst rangeFromListRealizer))).congr (fun _=>rfl)
def generatedPreparedRealizer : Realizer generatedPrepared := (pair
  (pair generatedTierRealizer (composition first.fst sourceEdgeDataRealizer))
  (composition first.fst sourceTablesRealizer)).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeProbe
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def isCentralRealizer : Realizer isCentral := (composition
  (pair second (composition first centralKeysRealizer))
  (contains (pairEqual (pairEqual natEqual natEqual) natEqual))).congr (by
    intro x; apply Bool.eq_iff_iff.mpr; simp [isCentral])
def probePartRealizer : Realizer probePart := (choose
  (composition (pair first.fst second) isCentralRealizer)
  (composition (pair (constant (1,1)) (pair first.snd (constant 1))) divRealizer)
  (constant (0,1))).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMarkTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry ExecutableOptions

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def markPortionsRealizer : Realizer markPortions := (pair
  (composition (pair first.fst second) realPartRealizer)
  (pair (composition (pair phantomPartRealizer probePartRealizer) subRealizer) probePartRealizer)).congr (fun _=>rfl)
def threeOptionsRealizer : Realizer threeOptions := (composition
  (pair (pair (constant 0) first)
    (composition (pair (pair (constant 1) second.fst)
      (composition (pair (constant 2) second.snd) listSingleton)) listCons)) listCons).congr (fun _=>rfl)
def sourceMarkRowRealizer : Realizer sourceMarkRow := (composition
  (pair sourceBagWeightRealizer (composition markPortionsRealizer threeOptionsRealizer))
  (mapWith (pair second.fst (composition (pair second.snd first) divRealizer)))).congr (fun _=>rfl)
def sourceMarksRealizer : Realizer sourceMarks := rowsWith sourceMarkRowRealizer
  (composition (first (A:=BagBuildInput) (B:=ℕ)) sourceTablesRealizer).fst

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedMarked
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def generatedContextRealizer : Realizer generatedContext := (pair
  (pair generatedPreparedRealizer (composition first.fst exactStartRealizer))
  (composition first sourceMarksRealizer)).congr (fun _=>rfl)
def generatedMarkedRealizer : Realizer generatedMarked := (composition
  (pair (composition first generatedContextRealizer) second) sampleRealizer).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageStatistics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableStatistics
open TreeTyped TreeFraction ExecutableMarking ExecutableEstimator

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

def averageA (xs : List (Marks E)) : Fraction := mean (xs.map observableA)
def averageARealizer : Realizer (averageA (E:=E)) := composition (map observableARealizer) meanRealizer

def averageD (q : C×E→Fraction) (x : C×List (Marks E)) : Fraction :=
  mean (x.2.map fun s=>observableD q (x.1,s))
def averageDRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (averageD q) :=
  (composition (mapWith (observableDRealizer Q)) meanRealizer).congr (fun _=>rfl)

def averageProbe (q : C×E→Fraction) (x : (C×E)×List (Marks E)) : Fraction :=
  mean (x.2.map fun s=>observableProbe q (x.1.1,(x.1.2,s)))
def averageProbeRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (averageProbe q) :=
  (composition (mapWith (composition (pair first.fst (pair first.snd second))
      (observableProbeRealizer Q Eq))) meanRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableStatistics

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatistics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

variable {E : Type} [Fintype E] [LinearOrder E]
def reweight (x : Reweights×ℕ) : Fraction := ExecutableLadder.lookup (1,1) x
def reweightRealizer : Realizer reweight := ExecutableLadder.lookupRealizer (1,1) natEqual
abbrev Inputs := (Reweights×(ℕ×List ℕ))×List (Marks ℕ)
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatisticsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics ExecutableLadder UnitRefresh

variable {E : Type} [Fintype E] [LinearOrder E]

noncomputable def reweightsRep (r : E→ℚ) : Reweights :=
  (List.ofFn (orderedEnum E)).map (fun e=>(index e,TreeFraction.repr (r e)))

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

  ExecutableLadder UnitRefresh NumericLadder Replica.Ladder Transport
abbrev StageInput := ((Reweights×(ℕ×List ℕ))×SampleContext)×List SampleBits

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport

variable {V : Type*} [LinearOrder V]

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelFinNCastReal_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
def sourceD (K : ℕ) : ℕ :=
  100*Fintype.card (SourceVertex (Fin G.n) K)^2*(100000000*(G.n+1)^4)

def ScaleState.matrix (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) :
    Fin G.n → Fin G.n → ℚ :=
  estimateMatrix (sourceD (G:=G) K)
    (sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)
    (fun e=>sampleAverage (RationalSource.observableProbe s.activity s.nextActivity K e) x)
lemma ScaleState.matrix_bounds (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) (a b : Fin G.n) :
    Counting.alpha ≤ s.matrix x a b ∧ s.matrix x a b≤3 := estimateMatrix_bounds _ _ _ _ _
lemma ScaleState.matrix_symm (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) (a b : Fin G.n) :
    s.matrix x a b=s.matrix x b a := estimateMatrix_symm _ _ _ _ _
def ScaleState.updateVector (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) : Fin G.n → ℚ :=
  Counting.scalingTrace hn (s.matrix x) G.n
lemma ScaleState.updateVector_bounds (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) (i : Fin G.n) :
    0 < s.updateVector hn x i ∧ s.updateVector hn x i≤2 := by
  have h:=(Counting.scalingTrace_invariant hn (s.matrix x) (s.matrix_symm x)
    (fun a b _=>s.matrix_bounds x a b) G.n).1
  exact ⟨h.pos i,h.upper i⟩
def ScaleState.update (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) : ScaleState G (j+1) where
  scale i:=s.scale i*s.updateVector hn x i
  positive i:=mul_pos (s.positive i) (s.updateVector_bounds hn x i).1
  upper i:=by
    rw [pow_succ]
    exact mul_le_mul (s.upper i) (s.updateVector_bounds hn x i).2 (s.updateVector_bounds hn x i).1.le (by positivity)

def ScaleState.ratioEstimate (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) : ℚ :=
  Counting.ratioEstimate (sampleAverage (RationalSource.observableA s.activity K) x)
    (sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)

lemma average_A (w : Fin G.n → Fin G.n → ℚ) (K : ℕ)
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableA w K) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableA (fun a b=>(w a b:ℝ)) K) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableA_cast]
lemma average_D (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ)
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableD w w₁ K) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableD_cast]
lemma ScaleState.ratioEstimate_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ)=
      RealStage.ratioEstimate
        (Enlargement.sampleAverage (Enlargement.observableA (fun a b=>(s.activity a b:ℝ)) K) x)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x) := by
  simp only [ScaleState.ratioEstimate,Counting.ratioEstimate_cast,average_A,average_D]
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericSummaries
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder ExecutableEstimator

def rawProbe (x : (Reweights×List (ExecutableMarking.Marks ℕ))×ℕ) : ℕ×Fraction :=
  (x.2,averageProbe reweight ((x.1.1,x.2),x.1.2))
def rawProbeRealizer : Realizer rawProbe := (pair second
  (composition (pair (pair first.fst second) first.snd) (averageProbeRealizer reweightRealizer natEqual))).congr (fun _=>rfl)

def summaries (x : Inputs) : Summaries :=
  ((ratio (averageA x.2,averageD reweight (x.1.1,x.2)),averageD reweight (x.1.1,x.2)),
   x.1.2.2.map (fun e=>rawProbe ((x.1.1,x.2),e)))
def summariesRealizer : Realizer summaries :=
  (pair (pair (composition (pair (composition second averageARealizer)
      (composition (pair first.fst second) (averageDRealizer reweightRealizer))) ratioRealizer)
    (composition (pair first.fst second) (averageDRealizer reweightRealizer)))
    (composition (pair (pair first.fst second) first.snd.snd) (mapWith rawProbeRealizer))).congr (fun _=>rfl)
def logicalProbesRealizer : Realizer logicalProbes := (composition (pair second first)
  (mapWith (pair second.fst (composition (pair first second.snd) (lookupRealizer (0,1) natEqual))))).congr (fun _=>rfl)
def finishUpdate (x : UpdateConfig×Summaries) : Fraction×ExecutableScaling.Vector :=
  (x.2.1.1,ExecutableAdaptive.updateVector
    (ExecutableAdaptive.estimateMatrix (((x.1.1.1,x.2.1.2),logicalProbes (x.1.2.1,x.2.2)),x.1.1.2),x.1.2.2))
def finishUpdateRealizer : Realizer finishUpdate := (pair second.fst.fst
  (composition (pair (composition (pair (pair (pair first.fst.fst second.fst.snd)
    (composition (pair first.snd.fst second.snd) logicalProbesRealizer)) first.fst.snd)
      ExecutableAdaptive.estimateMatrixRealizer) first.snd.snd) ExecutableAdaptive.updateVectorRealizer)).congr (fun _=>rfl)

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStatistics
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {E : Type} [DecidableEq E]

variable {V : Type} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

variable (w w₁ : V→V→ℚ) (K : ℕ) {S : ℕ}
    (x : Fin S→RationalSource.Marked w K)

noncomputable local instance instDecidableEqSourceLabelCastReal_r8c2707_1 (w : V→V→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_r8c2707_1 (w : V→V→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable def sourceSamples : List (ExecutableMarking.Marks ℕ) :=
  List.ofFn (fun i=>numericMarks (x i).1.val (selectedMarks (x i).1.val (x i).2))
noncomputable def sourceKeys : List (BagEdge (RationalSource.bags w K)) :=
  List.ofFn (UnitRefresh.orderedEnum _)
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def sourceAllIndices (x : BagBuildInput) : List ℕ :=
  (sourceTables x).1.map (fun key=>tableIndex (x,key))
def sourceAllIndicesRealizer : Realizer sourceAllIndices := rowsWith tableIndexRealizer sourceTablesRealizer.fst
def generatedObservables (x : GeneratedStageData) : Reweights×(ℕ×List ℕ) :=
  (sourceReweights (x.1.1.1,x.2),(x.1.1.2,sourceAllIndices x.1.1.1))

def generatedIndexData (x : GeneratedStageData) : ℕ×List ℕ :=
  (x.1.1.2,sourceAllIndices x.1.1.1)
def generatedIndexDataRealizer : Realizer generatedIndexData := (pair
  (first (A:=GeneratedInput) (B:=Matrix)).fst.snd
  (composition (first (A:=GeneratedInput) (B:=Matrix)).fst.fst sourceAllIndicesRealizer)).congr (fun _=>rfl)

def generatedObservablesRealizer : Realizer generatedObservables :=
  (TreeTyped.pair generatedReweightsRealizer generatedIndexDataRealizer).congr (fun _=>rfl)

def generatedStageSetup (x : GeneratedStageData) : (Reweights×(ℕ×List ℕ))×SampleContext :=
  (generatedObservables x,generatedContext x.1)
def generatedStageSetupRealizer : Realizer generatedStageSetup := (pair generatedObservablesRealizer
  (composition first generatedContextRealizer)).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageUpdateCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource

abbrev AdaptiveInput := UpdateConfig×StageInput
def stageUpdate (x : AdaptiveInput) : Fraction×Vector :=
  finishUpdate (x.1,summaries (x.2.1.1,sampleMany (x.2.1.2,x.2.2)))
def stageUpdateRealizer : Realizer stageUpdate := (composition
  (pair first (composition (pair second.fst.fst
    (composition (pair second.fst.snd second.snd) sampleManyRealizer)) summariesRealizer)) finishUpdateRealizer).congr (fun _=>rfl)
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeScaleStateUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelFinNCastReal_r8c2707_2 (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_r8c2707_1 (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable def sourceUpdateConfig (s : FiniteTrial.ScaleState G j) (K : ℕ) : UpdateConfig :=
  ((FiniteTrial.sourceD (G:=G) K,List.range G.n),
    ((List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin G.n)))).map
      (fun e=>(logicalRepr e,index (RationalSource.centralEdge s.activity K e))),vectorRep s.scale))
noncomputable def sourceStatisticsInput (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (x : Fin S→RationalSource.Marked s.activity K) : Inputs :=
  ((reweightsRep (RationalSource.bagReweight s.activity s.nextActivity K),
    (FiniteTrial.sourceD (G:=G) K,(sourceKeys s.activity K).map index)),sourceSamples s.activity K x)

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBindings
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def sourceBindings (x : BagBuildInput) : Bindings :=
  (logicalEdges x.1.2).map (fun e=>centralBinding (x,e))
def sourceBindingsRealizer : Realizer sourceBindings := (rowsWith centralBindingRealizer
  (composition (first (A:=BuildInput) (B:=List Bool)).snd logicalEdgesRealizer)).congr (fun _=>rfl)
def generatedUpdateConfig (x : GeneratedUpdateConfig) : UpdateConfig :=
  ((x.1.2,x.1.1.1.2),(sourceBindings x.1.1,x.2))
def generatedUpdateConfigRealizer : Realizer generatedUpdateConfig := (pair
  (pair first.snd first.fst.fst.snd)
  (pair (composition first.fst sourceBindingsRealizer) second)).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedUpdate
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def generatedUpdateArg : Realizer (fun x : GeneratedUpdateData=>(x.1.1.1,x.2)) :=
  (TreeTyped.pair (first (A:=GeneratedStageData) (B:=Vector)).fst.fst second).congr (fun _=>rfl)

def generatedUpdateSetup (x : GeneratedUpdateData) : UpdateConfig×((Reweights×(ℕ×List ℕ))×SampleContext) :=
  (generatedUpdateConfig (x.1.1.1,x.2),generatedStageSetup x.1)
def generatedUpdateSetupRealizer : Realizer generatedUpdateSetup := (TreeTyped.pair
  (composition generatedUpdateArg generatedUpdateConfigRealizer)
  (composition (first (A:=GeneratedStageData) (B:=Vector)) generatedStageSetupRealizer)).congr (fun _=>rfl)

def updateWith {A : Type} [Codec A]
    {f : A→UpdateConfig×((Reweights×(ℕ×List ℕ))×SampleContext)} (F : Realizer f) :
    Realizer (fun x : A×List SampleBits=>stageUpdate ((f x.1).1,((f x.1).2,x.2))) :=
  (composition (TreeTyped.pair (composition (first (A:=A) (B:=List SampleBits)) F) second)
    ((composition (TreeTyped.pair first.fst (TreeTyped.pair first.snd second)) stageUpdateRealizer))).congr (fun _=>rfl)

def generatedUpdate (x : GeneratedUpdateInput) : Fraction×Vector :=
  stageUpdate ((generatedUpdateSetup x.1).1,((generatedUpdateSetup x.1).2,x.2))
def generatedUpdateRealizer : Realizer generatedUpdate := updateWith generatedUpdateSetupRealizer

variable {n : ℕ} [Nontrivial (Fin n)]
noncomputable def generatedSourceSample (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) : RationalSource.Marked w K :=
  TableMarking.reveal (BagEdge.Incident (bags:=RationalSource.bags w K))
    (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
      (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
      (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
      (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
      (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
      (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length))))
    (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def currentActivityArg (x : SparseStageData) : ActivityData := (x.1.1,x.2)
def currentActivityArgRealizer : Realizer currentActivityArg :=
  (TreeTyped.pair (first (A:=(GraphData×List Bool)×StageControls) (B:=Vector)).fst second).congr (fun _=>rfl)
def sparseCurrentMatrix (x : SparseStageData) : Matrix := stageMatrix (currentActivityArg x)
def sparseCurrentMatrixRealizer : Realizer sparseCurrentMatrix :=
  (composition currentActivityArgRealizer stageMatrixRealizer).congr (fun _=>rfl)

def nextActivityArg (x : SparseStageData) : ActivityData := ((x.1.1.1,false::x.1.1.2),x.2)
def nextActivityArgRealizer : Realizer nextActivityArg := (TreeTyped.pair
  (TreeTyped.pair first.fst.fst (composition (TreeTyped.pair (constant false) first.fst.snd) listCons)) second).congr (fun _=>rfl)

def sparseNextMatrix (x : SparseStageData) : Matrix := stageMatrix (nextActivityArg x)
def sparseNextMatrixRealizer : Realizer sparseNextMatrix :=
  (composition nextActivityArgRealizer stageMatrixRealizer).congr (fun _=>rfl)

def sparseBagInput (x : SparseStageData) : BagBuildInput :=
  (((sparseCurrentMatrix x,x.1.2.1.1.1),x.1.1.1.1),x.1.2.1.1.2)
def sparseBagInputRealizer : Realizer sparseBagInput := (TreeTyped.pair
  (TreeTyped.pair (TreeTyped.pair sparseCurrentMatrixRealizer first.snd.fst.fst.fst) first.fst.fst.fst)
  first.snd.fst.fst.snd).congr (fun _=>rfl)

def sparseGeneratedInput (x : SparseStageData) : GeneratedInput :=
  ((sparseBagInput x,x.1.2.1.2),x.1.2.2)
def sparseGeneratedInputRealizer : Realizer sparseGeneratedInput := (TreeTyped.pair
  (TreeTyped.pair sparseBagInputRealizer first.snd.fst.snd) first.snd.snd).congr (fun _=>rfl)

def sparseUpdateData (x : SparseStageData) : GeneratedUpdateData :=
  ((sparseGeneratedInput x,sparseNextMatrix x),x.2)
def sparseUpdateDataRealizer : Realizer sparseUpdateData :=
  (TreeTyped.pair (TreeTyped.pair sparseGeneratedInputRealizer sparseNextMatrixRealizer) second).congr (fun _=>rfl)

def sparseStage (x : SparseStageInput) : Fraction×Vector := generatedUpdate (sparseUpdateData x.1,x.2)
def sparseStageRealizer : Realizer sparseStage := (composition
  (TreeTyped.pair (composition (first (A:=SparseStageData) (B:=List SampleBits)) sparseUpdateDataRealizer) second)
  generatedUpdateRealizer).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev Input := SparseStageData×(ℕ×OnlineSample.Request)
def execute (x : Input) : Experiment (Fraction×Vector) :=
  (OnlineSample.many x.2).map (fun bs=>sparseStage (x.1,bs))
noncomputable def executeRealizer : OnlineTree.Realizer execute :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic TreeTyped.first)
    (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) OnlineSample.manyRealizer))
    (OnlineTree.deterministic sparseStageRealizer)).congr (by
      intro x h; simp only [execute,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def data {j : ℕ} (s : FiniteTrial.ScaleState G j) (K D : ℕ) (ft fq : List Bool) : SparseStageData :=
  (((graphRep G,List.replicate j false),
    (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)

end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineRequest
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Transport ExecutableSource NumericLadder ExecutableScaling
open TreeTyped.Numbered Enlargement UnitRefresh ExecutableAdaptive
open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def lengthAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} (F : Realizer f) :
    Realizer (fun a=>(f a).length) := composition F listLength

def listIndices {A : Type} [Codec A] : Realizer (fun xs : List A=>List.range xs.length) :=
  composition listLength range

def indicesAfter {A B : Type} [Codec A] [Codec B] {f : A→List B} (F : Realizer f) :
    Realizer (fun a=>List.range (f a).length) := composition F listIndices

def scanErrorRealizer : Realizer scanError :=
  ((((constant 2).mulNat ((constant 1).addNat
    ((first.fst.snd.snd.mulNat (composition (composition first.fst.fst qRealizer) (fixedPower 2))).addNat
      (composition first.fst.fst qRealizer)))).addNat
    ((constant 4).mulNat ((((constant 8).mulNat (composition second.fst (fixedPower 2))).addNat
      ((constant 4).mulNat second.fst)).addNat (constant 3)))).addNat
    (((constant 2).mulNat (composition first.fst.fst.fst (fixedPower 2))).mulNat second.snd)).congr (fun _=>rfl)
def precisionPlanRealizer : Realizer precisionPlan :=
  (pair (pair (pair
    (composition (((composition first scansRealizer).mulNat scanErrorRealizer).mulNat first.snd) clogTwo)
    first.fst.fst.fst) (composition first scansRealizer))
    (composition (((constant 6).mulNat second.fst).mulNat first.snd) clogTwo)).congr (fun _=>rfl)

abbrev RequestInput := SparseStageData×ℕ

def sourcePrecision (x : RequestInput) : PrecisionData :=
  let b:=sparseBagInput x.1
  (((((sourceVertices b).length,x.1.1.2.1.2),(x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)),
    1000*(x.1.1.2.1.1.2.length/2)*x.2),
    ((sourceTables b).1.length,(sourceParents b).length))
def requestBagRealizer : Realizer (fun x : RequestInput=>sparseBagInput x.1) :=
  composition first sparseBagInputRealizer
def requestKRealizer : Realizer (fun x : RequestInput=>x.1.1.2.1.1.2.length/2) :=
  composition (pair (composition first.fst.snd.fst.fst.snd listLength) (constant 2)) quotient
def requestNDRealizer : Realizer (fun x : RequestInput=>((sourceVertices (sparseBagInput x.1)).length,x.1.1.2.1.2)) :=
  pair (composition (composition (g:=sourceVertices) requestBagRealizer sourceVerticesRealizer) listLength) first.fst.snd.fst.snd
def requestKTRealizer : Realizer (fun x : RequestInput=>(x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)) :=
  pair requestKRealizer (composition first.fst.snd.snd.fst listLength)
def requestMRealizer : Realizer (fun x : RequestInput=>1000*(x.1.1.2.1.1.2.length/2)*x.2) :=
  ((constant 1000).mulNat requestKRealizer).mulNat second
def requestScanRealizer : Realizer (fun x : RequestInput=>
    ((((sourceVertices (sparseBagInput x.1)).length,x.1.1.2.1.2),
      (x.1.1.2.1.1.2.length/2,x.1.1.2.2.1.length)),1000*(x.1.1.2.1.1.2.length/2)*x.2)) :=
  pair (pair requestNDRealizer requestKTRealizer) requestMRealizer
def requestTablesRealizer : Realizer (fun x : RequestInput=>sourceTables (sparseBagInput x.1)) :=
  composition (f:=fun x : RequestInput=>sparseBagInput x.1) (g:=sourceTables)
    requestBagRealizer sourceTablesRealizer
def requestCatalogRealizer : Realizer (fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) :=
  Realizer.fst (f:=fun x : RequestInput=>sourceTables (sparseBagInput x.1)) requestTablesRealizer
def requestEdgesRealizer : Realizer (fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1.length) :=
  lengthAfter (f:=fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) requestCatalogRealizer
def requestLabelsRealizer : Realizer (fun x : RequestInput=>(sourceParents (sparseBagInput x.1)).length) :=
  composition (composition (g:=sourceParents) requestBagRealizer sourceParentsRealizer) listLength
def sourcePrecisionRealizer : Realizer sourcePrecision :=
  pair requestScanRealizer (pair requestEdgesRealizer requestLabelsRealizer)

def sourceRequest (x : RequestInput) : OnlineSample.Request :=
  let plan:=precisionPlan (sourcePrecision x)
  (plan.1,(plan.2,List.range ((sourceTables (sparseBagInput x.1)).1.length)))
def requestPlanRealizer : Realizer (fun x : RequestInput=>precisionPlan (sourcePrecision x)) :=
  composition (g:=precisionPlan) sourcePrecisionRealizer precisionPlanRealizer
def requestIndicesRealizer : Realizer (fun x : RequestInput=>List.range (sourceTables (sparseBagInput x.1)).1.length) :=
  indicesAfter (f:=fun x : RequestInput=>(sourceTables (sparseBagInput x.1)).1) requestCatalogRealizer
def sourceRequestRealizer : Realizer sourceRequest :=
  pair requestPlanRealizer.fst (pair requestPlanRealizer.snd requestIndicesRealizer)

end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule

abbrev State := RequestInput×Fraction

def advance (x : SparseStageData×Vector) : SparseStageData :=
  (((x.1.1.1.1,false::x.1.1.1.2),x.1.1.2),x.2)
def advanceRealizer : TreeTyped.Realizer advance :=
  (TreeTyped.pair (TreeTyped.pair
    (TreeTyped.pair first.fst.fst.fst (composition (TreeTyped.pair (constant false) first.fst.fst.snd) listCons))
    first.fst.snd) second).congr (fun _=>rfl)

def carry (x : State×(Fraction×Vector)) : State :=
  ((advance (x.1.1.1,x.2.2),x.1.1.2),TreeFraction.mul (x.1.2,x.2.1))
def carryRealizer : TreeTyped.Realizer carry :=
  (TreeTyped.pair (TreeTyped.pair
    (composition (TreeTyped.pair first.fst.fst second.snd) advanceRealizer) first.fst.snd)
    (composition (TreeTyped.pair first.snd second.fst) mulRealizer)).congr (fun _=>rfl)

def prepare (x : RequestInput) : OnlineStage.Input :=
  (x.1,(x.2,sourceRequest x))
def prepareRealizer : TreeTyped.Realizer prepare :=
  TreeTyped.pair first (TreeTyped.pair second sourceRequestRealizer)

def step (x : State) : Experiment State :=
  (OnlineStage.execute (prepare x.1)).map (fun y=>carry (x,y))
noncomputable def stepRealizer : OnlineTree.Realizer step :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic TreeTyped.identity)
    (OnlineTree.composition (OnlineTree.deterministic (composition first prepareRealizer)) OnlineStage.executeRealizer))
    (OnlineTree.deterministic carryRealizer)).congr (by
      intro x h
      simp only [step,Experiment.mean_bind,Experiment.mean_map,Experiment.mean,Function.comp_apply,id_eq])

def body (x : Bool×State) : Experiment State := step x.2
noncomputable def bodyRealizer : OnlineTree.Realizer body :=
  (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) stepRealizer).congr (by
    intro x h; rfl)

def sweep (x : List Bool×State) : Experiment State := OnlineTree.foldM body x.1 x.2
noncomputable def sweepRealizer : OnlineTree.Realizer sweep := OnlineTree.fold bodyRealizer
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteStage
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance finiteStageSourceLabelDecidableEq_r8c2707_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.finiteStageSourceBagEdgeFintype
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_4_r8c2707_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance instFintypeBagPMSourceVertexLabelBags_4 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance instFintypeMarked_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
local instance instNonemptyProdForallFinBoolForallBagEdgeSourceVertexLabelBags (w : V → V → ℚ) (K t k : ℕ) :
    Nonempty ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := ⟨(fun _=>false,fun _ _=>false)⟩

noncomputable local instance instFintypeProdForallFinBoolForallBagEdgeSourceVertexLabelBags_r8c2707_1 (w : V → V → ℚ) (K t k : ℕ) :
    Fintype ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _
noncomputable def finiteSourceLaw (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    SourceMarked (fun x y=>(w x y:ℝ)) K → ℝ :=
  markedSamplerLaw w hw K D m hD hN h hq M η ∘ sourceMarkedEquiv w K
lemma finiteSourceLaw_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    0≤finiteSourceLaw w hw K D m hD hN h hq M η a := imageLaw_nonneg _ _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeSourceMarkedCastReal_1
lemma finiteSourceLaw_sum (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    ∑ a,finiteSourceLaw w hw K D m hD hN h hq M η a=1 := by
  unfold finiteSourceLaw
  simp only [Function.comp_apply]
  rw [(sourceMarkedEquiv w K).sum_comp]
  exact imageLaw_sum _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteTrialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance finiteTrialLawSourceLabelDecidableEq_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance finiteTrialLawSourceBagEdgeFintype (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.cap {j K : ℕ} (s : ScaleState G j) (hj : j≤K) (a b : Fin G.n) (hab : a≠b) :
    BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K := by
  have h:=s.toReal.cap hj a b hab
  rw [←s.activity_cast] at h
  have he : ((BottleneckAlgorithm.edge s.activity a b:ℚ):ℝ)=edgeActivity (fun a b=>(s.activity a b:ℝ)) a b := by
    unfold BottleneckAlgorithm.edge edgeActivity
    split_ifs <;> rfl
  rw [←he] at h
  exact_mod_cast h

noncomputable def ScaleState.runLaw (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    Law (SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K) where
  mass := RationalSource.finiteSourceLaw s.activity s.activity_pos p.K
    (Enlargement.sourceD (V:=Fin G.n) p.K) (1000*p.K*p.S)
    (sourceD_one p.K) Fintype.card_pos (s.cap hj) p.q_pos
    (RationalSource.startMatching s.activity p.K p.even) (1/(1000*p.K*p.S))
  nonneg := RationalSource.finiteSourceLaw_nonneg _ _ _ _ _ _ _ _ _ _ _
  total := RationalSource.finiteSourceLaw_sum _ _ _ _ _ _ _ _ _ _ _

noncomputable def ScaleState.sampleLaw (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    Law (Fin p.S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K) := (s.runLaw p hj).iid p.S

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport Switching

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_1_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
def ScaleState.Balanced (hn : 2≤G.n) (s : ScaleState G j) : Prop := s.toReal.Balanced hn
noncomputable def stageData (p : Trial.Parameters G) (hj : j≤p.K) (s : ScaleState G j)
    (hs : s.Balanced p.hn) : StageData G.n p.K p.K where
  hn:=p.hn
  w a b:=(s.activity a b:ℝ)
  next a b:=(s.nextActivity a b:ℝ)
  positive a b:=by exact_mod_cast s.activity_pos a b
  next_positive a b:=by exact_mod_cast s.nextActivity_pos a b
  partition_positive:=by rw [s.activity_cast]; exact s.toReal.partition_pos p.even
  lower:=by rw [s.activity_cast]; exact hs.1
  upper:=by rw [s.activity_cast]; exact hs.2
  cool_lower a b _:=by
    have h:=(s.toReal.cooling a b).1
    rw [←s.activity_cast,←s.nextActivity_cast] at h
    exact h
  cool_upper a b _:=by
    have h:=(s.toReal.cooling a b).2
    rw [←s.activity_cast,←s.nextActivity_cast] at h
    exact h
  cap:=by rw [s.activity_cast]; exact s.toReal.cap hj
  stages:=p.K_pos
  epsilon:=p.epsilon
  epsilon_positive:=p.epsilon_real_pos
  epsilon_lt_one:=p.epsilon_real_lt_one

lemma ScaleState.ratioEstimate_nonneg (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    0 ≤ s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x) := by
  have h : (0:ℝ)≤(s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ) := by
    rw [s.ratioEstimate_cast]
    unfold RealStage.ratioEstimate
    split_ifs with h
    · apply div_nonneg _ h.le
      unfold Enlargement.sampleAverage
      apply div_nonneg _ (Nat.cast_nonneg S)
      apply sum_nonneg
      intro i _
      exact (observableD_range_off (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ))
        (fun a b=>by exact_mod_cast s.activity_pos a b)
        (fun a b=>by exact_mod_cast (s.nextActivity_pos a b).le)
        (fun a b _=>by have h:=(s.toReal.cooling a b).2; rw [←s.activity_cast,←s.nextActivity_cast] at h; exact h) K (x i)).1
    · norm_num
  exact_mod_cast h
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Initializer
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_2_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_2 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
structure Layer (p : Trial.Parameters G) (j : ℕ) where
  Ω : Type
  finite : Fintype Ω
  law : @Law Ω finite
  state : Ω → ScaleState G j
  ratios : Ω → Fin j → ℚ
  ratios_nonneg : ∀ x i,0 ≤ ratios x i

attribute [instance] Layer.finite

noncomputable def Layer.good (p : Trial.Parameters G) {j : ℕ} (L : Layer p j) (x : L.Ω) : Prop :=
  (L.state x).Balanced p.hn ∧ ∀ i : Fin j,
    |(L.ratios x i:ℝ)/(partition (Trial.raw G (i.val+1)) ∅/partition (Trial.raw G i.val) ∅)-1| ≤ (p.epsilon:ℝ)/(100*p.K)

noncomputable def firstLayer (p : Trial.Parameters G) : Layer p 0 where
  Ω := PUnit
  finite := inferInstance
  law := ⟨fun _=>1,fun _=>by norm_num,by simp⟩
  state _ := initialScaleState G p.hn
  ratios _ := Fin.elim0
  ratios_nonneg _ i := Fin.elim0 i

noncomputable def Layer.append (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) : Layer p (j+1) where
  Ω := Σ x : L.Ω, Fin p.S → SourceMarked (fun a b=>((L.state x).activity a b:ℝ)) p.K
  finite := inferInstance
  law := L.law.sigma (fun x=>(L.state x).sampleLaw p hj)
  state x := (L.state x.1).update p.hn (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)
  ratios x := Fin.snoc (L.ratios x.1) ((L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2))
  ratios_nonneg x i := by
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa using (L.state x.1).ratioEstimate_nonneg x.2
    · simpa using L.ratios_nonneg x.1 i

noncomputable def layers (p : Trial.Parameters G) : (j : ℕ) → j ≤ p.K → Layer p j
  | 0, _ => firstLayer p
  | j+1, h => (layers p j (by omega)).append p (by omega)

noncomputable def output (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) : ℚ :=
  (Z (completeGraph G.n):ℚ)*∏ i,(layers p p.K le_rfl).ratios x i

def Accurate (p : Trial.Parameters G) (y : ℚ) : Prop :=
  (1-p.epsilon)*(Z G:ℚ)≤y ∧ y≤(1+p.epsilon)*(Z G:ℚ)

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
def parameters (G : GraphInput) (hn : 2≤G.n) (heven : Even G.n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    Trial.Parameters G where
  hn:=hn
  even:=heven
  K:=Counting.leastSchedule G.n hn e he he1
  epsilon:=e
  epsilon_pos:=he
  epsilon_lt_one:=he1
  schedule:=Counting.leastSchedule_spec G.n hn e he he1
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_EmpiricalDenom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
def empiricalDenom (G : GraphInput) (K : ℕ) : ℕ := (G.n+1)^Fintype.card (SourceVertex (Fin G.n) K)
end MatchingFPRAS.Trial

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def Parameters.empiricalBound (p : Parameters G) : ℕ := p.S*empiricalDenom G p.K
noncomputable def Parameters.matrixBound (p : Parameters G) : ℕ := BitArithmetic.matrixBound p.D p.empiricalBound
noncomputable def Parameters.scaleBound (p : Parameters G) (j : ℕ) : ℕ :=
  (G.n+1)*p.matrixBound^(j*(G.n+1))
end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
variable {G : GraphInput} [Nontrivial (Fin G.n)]
def sampleCount (p : Trial.Parameters G) : ℕ :=
  ⌈10*(Counting.sigma (sourceD (G:=G) p.K) p.K p.epsilon)⁻¹^2*((G.n:ℚ)+p.K+1)⌉₊
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Transport Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
lemma edge_card_polynomial (w : V → V → ℚ) (K : ℕ) :
    Fintype.card (BagEdge (bags w K)) ≤ edgePolynomial (Fintype.card (SourceVertex V K)) K := by
  apply (bagEdge_card_le (bags w K)).trans
  unfold edgePolynomial
  exact Nat.mul_le_mul_left _ (label_card w K)
lemma scan_error_polynomial (w : V → V → ℚ) (K D T : ℕ)
    (hT : T ≤ tierPolynomial (Fintype.card (SourceVertex V K)) D K) :
    scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T
      (ladderQ (Fintype.card (SourceVertex V K)) D) ≤ scanErrorPolynomial (Fintype.card (SourceVertex V K)) D K := by
  have he:=edge_card_polynomial w K
  have hl:=label_card w K
  unfold scanErrorNumerator scanErrorPolynomial ladderM
  gcongr
open Transport Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
def samplerBitCount (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K)) (η : ℚ) : ℕ :=
  let N:=Fintype.card (SourceVertex V K)
  let T:=endpoint N D K hN
  let t:=discreteLadderSteps N D K T m
  t*scanBitCount N (bitPrecision (t*scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T (ladderQ N D)) η)+
    Fintype.card (BagEdge (bags w K))*bitPrecision (6*Fintype.card (BagEdge (bags w K))) η
lemma samplerBitCount_le (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K)) (η : ℚ) :
    samplerBitCount w K D m hN η ≤ totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊ := by
  let N:=Fintype.card (SourceVertex V K)
  let T:=endpoint N D K hN
  let t:=discreteLadderSteps N D K T m
  let R:=scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T (ladderQ N D)
  have hT : T ≤ tierPolynomial N D K := endpoint_le_polynomial N D K hN
  have ht : t ≤ stepsPolynomial N D K m := discreteSteps_le_polynomial N D K T m hT
  have hR : R ≤ scanErrorPolynomial N D K := scan_error_polynomial w K D T hT
  have hE:=edge_card_polynomial w K
  have hk : bitPrecision (t*R) η ≤ stepsPolynomial N D K m*scanErrorPolynomial N D K*⌈η⁻¹⌉₊ :=
    (bitPrecision_le _ _).trans (by gcongr)
  have hm : bitPrecision (6*Fintype.card (BagEdge (bags w K))) η ≤ 6*edgePolynomial N K*⌈η⁻¹⌉₊ :=
    (bitPrecision_le _ _).trans (by gcongr)
  change t*scanBitCount N (bitPrecision (t*R) η)+Fintype.card (BagEdge (bags w K))*bitPrecision (6*Fintype.card (BagEdge (bags w K))) η ≤ _
  dsimp only [totalBitsPolynomial,scanBitCount]
  gcongr
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.RationalSource
open Transport Enlargement Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelCastReal_4_r8c2707_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_4
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_5_r8c2707_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance instFintypeBagPMSourceVertexLabelBags_5 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance instFintypeMarked_2 (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable local instance instFintypeProdForallFinBoolForallBagEdgeSourceVertexLabelBags_1 (w : V → V → ℚ) (K t k : ℕ) :
    Fintype ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _
noncomputable def bitSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    (Fin (samplerBitCount w K D m hN η) → Bool) → SourceMarked (fun x y=>(w x y:ℝ)) K :=
  (sourceMarkedEquiv w K).symm ∘ markedSampler w hw K D m hD hN h hq M η ∘
    markedBitsEquiv (BagEdge (bags w K)) _ _
noncomputable def fixedSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    (Fin (totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊) → Bool) →
      SourceMarked (fun x y=>(w x y:ℝ)) K :=
  padSampler (samplerBitCount_le w K D m hN η) (bitSampler w hw K D m hD hN h hq M η)
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_4_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_4 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_3 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
noncomputable def oneBits (p : Trial.Parameters G) : ℕ :=
  totalBitsPolynomial p.N p.D p.K (1000*p.K*p.S) ⌈(1/(1000*p.K*p.S):ℚ)⁻¹⌉₊
noncomputable def ScaleState.drawOne (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (Fin (oneBits p) → Bool) → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K :=
  RationalSource.fixedSampler s.activity s.activity_pos p.K
    (Enlargement.sourceD (V:=Fin G.n) p.K) (1000*p.K*p.S)
    (sourceD_one p.K) Fintype.card_pos (s.cap hj) p.q_pos
    (RationalSource.startMatching s.activity p.K p.even) (1/(1000*p.K*p.S))
noncomputable def stageBits (p : Trial.Parameters G) : ℕ := p.S*oneBits p
noncomputable def ScaleState.drawStage (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (Fin (stageBits p) → Bool) → Fin p.S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K :=
  (fun b i=>s.drawOne p hj (b i)) ∘ matrixBitsEquiv p.S (oneBits p)

open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_5_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable def Layer.drawAppend (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K)
    (L : Layer p j) {a : ℕ} (f : (Fin a → Bool) → L.Ω) :
    (Fin (a+stageBits p) → Bool) → (L.append p hj).Ω :=
  fun b =>
    let c : (Fin a → Bool) × (Fin (stageBits p) → Bool) := pairBitsEquiv a (stageBits p) b
    (⟨f c.1,(L.state (f c.1)).drawStage p hj c.2⟩ :
      Σ x : L.Ω, Fin p.S → SourceMarked (fun v w=>((L.state x).activity v w:ℝ)) p.K)
noncomputable def drawLayer (p : Trial.Parameters G) : (j : ℕ) → (hj : j≤p.K) →
    (Fin (j*stageBits p) → Bool) → (layers p j hj).Ω
  | 0,_ => fun _=>PUnit.unit
  | j+1,hj => (layers p j (by omega)).drawAppend p (by omega) (drawLayer p j (by omega)) ∘ successorBitsEquiv j (stageBits p)
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Guard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial
open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} {j K : ℕ} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_2_r8c2707_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable def ScaleState.certificateActivity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => GraphBridge.rawActivity G 0 a b * s.scale a * s.scale b

open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable local instance instDecidableEqSourceLabelFinN_3_r8c2707_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelSourceBags_3 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_GuardProbability
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_6_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_6 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_5 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

def ScaleState.certificateActivity {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b => (if (min a b,max a b) ∈ G.edges then 1 else 0) * s.scale a * s.scale b

noncomputable def ScaleState.certificate {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) : ℚ :=
  RationalSource.observableD s.activity s.certificateActivity K (RationalSource.sourceMarkedEquiv s.activity K a)

end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_7_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_7 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_6 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

abbrev GuardSamples (p : Trial.Parameters G) (s : ScaleState G p.K) :=
  Fin 16 → SourceMarked (fun x y => (s.activity x y : ℝ)) p.K
noncomputable def guardPass (p : Trial.Parameters G) (s : ScaleState G p.K) (x : GuardSamples p s) : Prop :=
  ∃ i, 0 < s.certificate p.K (x i)
noncomputable def guardLaw (p : Trial.Parameters G) (s : ScaleState G p.K) : Law (GuardSamples p s) :=
  (s.runLaw p le_rfl).iid 16

abbrev GuardedTrial (p : Trial.Parameters G) :=
  Σ x : (layers p p.K le_rfl).Ω, GuardSamples p ((layers p p.K le_rfl).state x)
noncomputable def guardedLaw (p : Trial.Parameters G) : Law (GuardedTrial p) :=
  (layers p p.K le_rfl).law.sigma (fun x => guardLaw p ((layers p p.K le_rfl).state x))
noncomputable def guardedOutput (p : Trial.Parameters G) (x : GuardedTrial p) : ℚ :=
  if guardPass p ((layers p p.K le_rfl).state x.1) x.2 then output p x.1 else 0

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedCertificate
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableMarking ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def generatedCertificate (x : GeneratedCertificateInput) : Fraction :=
  ExecutableMarking.observableD reweight (generatedReweights x.1,generatedMarked (x.1.1,x.2))
def certificateSampleRealizer : Realizer certificateSample :=
  (composition certificateSampleArgRealizer generatedMarkedRealizer).congr (fun _=>rfl)
def certificateArgsRealizer : Realizer certificateArgs :=
  (TreeTyped.pair certificateReweightsRealizer certificateSampleRealizer).congr (fun _=>rfl)
def generatedCertificateRealizer : Realizer generatedCertificate :=
  (composition (f:=certificateArgs) (g:=ExecutableMarking.observableD reweight)
    certificateArgsRealizer (observableDRealizer reweightRealizer)).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseCertificate
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def certificateCellData (x : CertificateMatrixInput) : CellData := ((x.1.2,(0,1)),x.2)
def certificateCellDataRealizer : Realizer certificateCellData :=
  (TreeTyped.pair (TreeTyped.pair first.snd (constant (0,1))) second).congr (fun _=>rfl)

def certificateMatrix (x : CertificateMatrixInput) : Matrix :=
  x.1.1.map (fun i=>stageRow ((certificateCellData x,x.1.1),i))
def certificateMatrixRealizer : Realizer certificateMatrix :=
  (composition (TreeTyped.pair (TreeTyped.pair certificateCellDataRealizer first.fst) first.fst)
    (mapWith stageRowRealizer)).congr (fun _=>rfl)

def sparseCertificateMatrixArg (x : SparseStageData) : CertificateMatrixInput := (x.1.1.1,x.2)
def sparseCertificateMatrixArgRealizer : Realizer sparseCertificateMatrixArg :=
  (TreeTyped.pair first.fst.fst second).congr (fun _=>rfl)

def sparseCertificateData (x : SparseStageData) : GeneratedStageData :=
  (sparseGeneratedInput x,certificateMatrix (sparseCertificateMatrixArg x))
def sparseCertificateDataRealizer : Realizer sparseCertificateData := (TreeTyped.pair
  sparseGeneratedInputRealizer (composition sparseCertificateMatrixArgRealizer certificateMatrixRealizer)).congr (fun _=>rfl)

def sparseCertificate (x : SparseStageData×SampleBits) : Fraction := generatedCertificate (sparseCertificateData x.1,x.2)
def sparseCertificateRealizer : Realizer sparseCertificate := (composition
  (TreeTyped.pair (composition first sparseCertificateDataRealizer) second) generatedCertificateRealizer).congr (fun _=>rfl)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineGuard
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource NumericMarking OnlineSchedule

def positive (q : Fraction) : Bool := TreeFraction.less ((0,1),q)
def positiveRealizer : TreeTyped.Realizer positive :=
  composition (pair (constant (0,1)) identity) lessRealizer

def accept (x : SparseStageData×List SampleBits) : Bool :=
  x.2.any (fun b=>positive (sparseCertificate (x.1,b)))
def acceptRealizer : TreeTyped.Realizer accept :=
  (composition (mapWith (composition sparseCertificateRealizer positiveRealizer)) any).congr (by
    intro x; simp only [accept,Function.comp_def,List.any_map,Function.id_def])

def test (x : RequestInput) : Experiment Bool :=
  (OnlineSample.many (16,sourceRequest x)).map (fun bs=>accept (x.1,bs))
noncomputable def testRealizer : OnlineTree.Realizer test :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic first)
    (OnlineTree.composition (OnlineTree.deterministic (pair (constant 16) sourceRequestRealizer)) OnlineSample.manyRealizer))
    (OnlineTree.deterministic acceptRealizer)).congr (by
      intro x h; simp only [test,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

def finishRealizer : TreeTyped.Realizer finish :=
  (choose second first (constant (0,1))).congr (fun _=>rfl)

def checked (x : OnlineTrial.State) : Experiment Fraction :=
  (test x.1).map (fun b=>finish (x.2,b))
noncomputable def checkedRealizer : OnlineTree.Realizer checked :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic second)
    (OnlineTree.composition (OnlineTree.deterministic first) testRealizer))
    (OnlineTree.deterministic finishRealizer)).congr (by
      intro x h; simp only [checked,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

def trial (x : List Bool×OnlineTrial.State) : Experiment Fraction :=
  (OnlineTrial.sweep x).bind checked
noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  OnlineTree.composition OnlineTrial.sweepRealizer checkedRealizer
end MatchingFPRAS.OnlineGuard

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
abbrev edgeCount := Fintype.card (BagEdge (RationalSource.bags w K))
abbrev choiceWidth (η : ℚ) := bitPrecision (scansCount (n:=n) K D m *
  scanErrorNumerator (SourceVertex (Fin n) K) (RationalSource.Label w K) (RationalSource.bags w K)
    (tierCount (n:=n) K D) (copies (n:=n) K D)) η
abbrev markWidth (η : ℚ) := bitPrecision (6*edgeCount w K) η
abbrev Raw (η : ℚ) := OnlineSample.Random (vertexCount (n:=n) K) (choiceWidth w K D m η)
  (scansCount (n:=n) K D m) (edgeCount w K) (markWidth w K η)

def rawEquiv (η : ℚ) :
    ((Fin (scansCount (n:=n) K D m*scanBitCount (vertexCount (n:=n) K) (choiceWidth w K D m η))→Bool) ×
      (BagEdge (RationalSource.bags w K)→Fin (markWidth w K η)→Bool)) ≃ Raw w K D m η :=
  Equiv.prodCongr (runBitsEquiv (SourceVertex (Fin n) K) (choiceWidth w K D m η) (scansCount (n:=n) K D m))
    (Equiv.arrowCongr (orderedEnum (BagEdge (RationalSource.bags w K))).symm (Equiv.refl _))
noncomputable def rawDraw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) : Raw w K D m η→RationalSource.Marked w K :=
  RationalSource.markedSampler w hw K D m hD Fintype.card_pos hu hq
    (RationalSource.startMatching w K he) η ∘ (rawEquiv w K D m η).symm

noncomputable def core (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K) (he : Even n)
    (T q : ℕ) (hq : 0<q) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) : RationalSource.Marked w K :=
  TableMarking.reveal (BagEdge.Incident (bags:=RationalSource.bags w K))
    (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
      (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
      (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
      (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
      (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
      (topSlot T q hq))
    (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e))
end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTransitionLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
noncomputable local instance instFintypeBagPMSourceVertexFinLabelBags_1 : Fintype (BagPM (RationalSource.bags w K)) := Fintype.ofFinite _
noncomputable local instance instFintypeMarkedFin_1 : Fintype (RationalSource.Marked w K) := Fintype.ofFinite _
noncomputable def realRawDraw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) :
    Raw w K D m η→SourceMarked (fun a b=>(w a b:ℝ)) K :=
  (RationalSource.sourceMarkedEquiv w K).symm ∘ rawDraw w K D m hw hD hu hq he η

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable abbrev denominator (p : Trial.Parameters G) := 1000*p.K*p.S
noncomputable def fixedRequest {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) : OnlineSample.Request :=
  (((choiceWidth s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p) (1/denominator p),p.N),
      scansCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p)),
    (markWidth s.activity p.K (1/denominator p),
      List.ofFn (fun i=>index (orderedEnum (BagEdge (RationalSource.bags s.activity p.K)) i))))
noncomputable def fixedData {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) : SparseStageData :=
  data s p.K (FiniteTrial.sourceD (G:=G) p.K)
    (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
    (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
noncomputable def transition {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) :
    Experiment (Fraction×Vector) := execute (fixedData p s,(p.S,fixedRequest p s))

end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def product {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) : ℚ :=
  (Z (completeGraph G.n):ℚ)*∏ i,L.ratios x i

end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTrialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def represent {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) : State :=
  ((fixedData p (L.state x),p.S),repr (product p L x))
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_GuardBits
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive Amplification Finset
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_8_r8c2707_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexFinNSourceLabelCastRealSourceBags_8 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedFinNCastReal_7 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

noncomputable def guardBits (p : Trial.Parameters G) : ℕ := 16*oneBits p
noncomputable def ScaleState.drawGuard (p : Trial.Parameters G) (s : ScaleState G p.K) :
    (Fin (guardBits p) → Bool) → GuardSamples p s :=
  (fun b i=>s.drawOne p le_rfl (b i)) ∘ matrixBitsEquiv 16 (oneBits p)

noncomputable def guardedBits (p : Trial.Parameters G) : ℕ := p.K*stageBits p+guardBits p
noncomputable def drawGuarded (p : Trial.Parameters G) :
    (Fin (guardedBits p) → Bool) → GuardedTrial p :=
  fun b =>
    let c := pairBitsEquiv (p.K*stageBits p) (guardBits p) b
    let x := drawLayer p p.K le_rfl c.1
    ⟨x,((layers p p.K le_rfl).state x).drawGuard p c.2⟩
noncomputable def guardedBitOutput (p : Trial.Parameters G) : (Fin (guardedBits p) → Bool) → ℚ :=
  guardedOutput p ∘ drawGuarded p

noncomputable def guardedAmplifiedBits (p : Trial.Parameters G) (δ : ℚ) : ℕ :=
  (2*halfRepetitions δ+1)*guardedBits p
noncomputable def drawGuardedTrials (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (guardedAmplifiedBits p δ) → Bool) → Fin (2*halfRepetitions δ+1) → GuardedTrial p :=
  (fun bits i=>drawGuarded p (bits i)) ∘ matrixBitsEquiv (2*halfRepetitions δ+1) (guardedBits p)
noncomputable def guardedAmplifiedOutput (p : Trial.Parameters G) (δ : ℚ)
    (x : Fin (2*halfRepetitions δ+1) → GuardedTrial p) : ℚ := median (fun i=>guardedOutput p (x i))
noncomputable def guardedAmplifiedBitOutput (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (guardedAmplifiedBits p δ) → Bool) → ℚ := guardedAmplifiedOutput p δ ∘ drawGuardedTrials p δ

noncomputable def guardedAccurateBits (p : Trial.Parameters G) (δ : ℚ) : Finset (Fin (guardedAmplifiedBits p δ) → Bool) :=
  univ.filter fun b=>Accurate p (guardedAmplifiedBitOutput p δ b)

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineMedian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineMedian
open TreeTyped TreeFraction

def compareRealizer : TreeTyped.Realizer (fun x : Fraction×Fraction=>decide (relation x.1 x.2)) :=
  (composition (composition (pair second first) lessRealizer) boolNot).congr (by
    intro x
    change (!(decide (x.2.1*x.1.2<x.1.1*x.2.2)))=decide (x.1.1*x.2.2≤x.2.1*x.1.2)
    simp only [←decide_not,not_lt])
def sortedRealizer : TreeTyped.Realizer sorted := insertionSort relation compareRealizer
def medianRealizer : TreeTyped.Realizer median :=
  composition (pair sortedRealizer (composition (pair listLength (constant 2)) quotient)) (getDFast (0,1))
end MatchingFPRAS.OnlineMedian

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineAmplification
open PhysicalStream TreeTyped

abbrev TrialInput := List Bool×OnlineTrial.State

def trials (x : ℕ×TrialInput) : Experiment (List TreeFraction.Fraction) :=
  OnlineTree.traverseM OnlineGuard.trial (List.replicate x.1 x.2)
noncomputable def trialsRealizer : OnlineTree.Realizer trials :=
  OnlineTree.composition (OnlineTree.deterministic OnlineSample.repeatInputRealizer)
    (OnlineTree.traverse OnlineGuard.trialRealizer)
def run (x : ℕ×TrialInput) : Experiment TreeFraction.Fraction := (trials x).map OnlineMedian.median
noncomputable def runRealizer : OnlineTree.Realizer run :=
  (OnlineTree.composition trialsRealizer (OnlineTree.deterministic OnlineMedian.medianRealizer)).congr (by
    intro x h; simp only [run,Experiment.mean_map,Experiment.mean_bind,Experiment.mean])

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def initial (p : Trial.Parameters G) : TrialInput :=
  (List.replicate p.K false,OnlineTrial.represent p (FiniteTrial.firstLayer p) PUnit.unit)
end MatchingFPRAS.OnlineAmplification

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlinePowerSearch
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

def powerCandidate (x : PowerSearchInput×ℕ) : Bool :=
  !(TreeFraction.less (fuelPower (x.1.1.1,x.1.2.take x.2),x.1.1.2))
def powerCandidateRealizer : Realizer powerCandidate :=
  (composition (composition (pair
    (composition (pair first.fst.fst (composition (pair first.snd second) takeFast)) fuelPowerRealizer)
    first.fst.snd) lessRealizer) boolNot).congr (fun _=>rfl)

def findPower (x : PowerSearchInput) : ℕ :=
  listMin ((List.range (x.2.length+1)).filter (fun i=>powerCandidate (x,i)),x.2.length)
def findPowerRealizer : Realizer findPower := by
  let B : Realizer (fun x : PowerSearchInput=>x.2.length) := composition second listLength
  let R := composition (composition B successor) range
  let F := composition (pair identity R) (filterWith powerCandidateRealizer)
  exact (composition (pair F B) listMinRealizer).congr (fun _=>rfl)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_OnlineFractionParam
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def natCeilRealizer : Realizer natCeil :=
  (composition (pair (composition (composition (pair first second) TreeTyped.add) predecessor) second) quotient).congr (fun _=>rfl)
def inverseRealizer : Realizer inverse := composition (pair second first) normalizeRealizer
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

def rootCandidateRealizer : Realizer rootCandidate :=
  (composition (pair first.fst (composition (composition second successor) (fixedPower 2))) TreeTyped.less).congr (fun _=>rfl)
def findRootRealizer : Realizer findRoot := by
  let B : Realizer (fun x : RootInput=>x.2.length) := composition second listLength
  let R := composition (composition B successor) range
  let F := composition (pair identity R) (filterWith rootCandidateRealizer)
  exact (composition (pair F B) listMinRealizer).congr (fun _=>rfl)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineCoolingSchedule
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

def fuelRealizer : Realizer (fun n : ℕ=>List.replicate n false) :=
  (composition range (map (constant false))).congr (by intro n; simp)
def scheduleBoundRealizer : Realizer scheduleBound :=
  (first.mulNat ((first.mulNat first).addNat
    ((constant 32).mulNat (composition (composition second inverseRealizer) natCeilRealizer)))).congr (fun _=>rfl)
def coolingPowerPlanRealizer : Realizer coolingPowerPlan :=
  (pair (composition (pair (constant (1,1))
    (composition (pair (constant (1,1)) (pair first.fst (constant 1))) divRealizer)) addRealizer)
    (composition (pair (composition (pair (constant (32,1))
      (composition (pair (pair first.fst (constant 1)) second) fuelPowerRealizer)) mulRealizer)
      first.snd) divRealizer)).congr (fun _=>rfl)
def coolingSearchInputRealizer : Realizer coolingSearchInput :=
  pair (composition (pair identity (composition (composition (pair first (constant 2)) quotient) fuelRealizer))
    coolingPowerPlanRealizer) (composition scheduleBoundRealizer fuelRealizer)
def coolingSchedule (x : CoolingInput) : ℕ := findPower (coolingSearchInput x)
def coolingScheduleRealizer : Realizer coolingSchedule := composition coolingSearchInputRealizer findPowerRealizer

def coolingMeasure (x : CoolingInput) : ℕ := x.1+natCeil (inverse x.2)+weight x
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineLadderSchedule
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial ExecutableSource Transport Enlargement

def vertexNumber (x : ℕ×ℕ) : ℕ :=
  (vertices (List.range x.1,List.replicate (2*x.2+2) false)).length
def vertexNumberRealizer : Realizer vertexNumber :=
  composition (composition (pair (composition first range)
    (composition (((constant 2).mulNat second).addNat (constant 2)) fuelRealizer)) verticesRealizer) listLength
def distortionRealizer : Realizer distortion :=
  (((constant 100).mulNat (composition second (fixedPower 2))).mulNat
    ((constant 100000000).mulNat (composition (composition first successor) (fixedPower 4)))).congr (fun _=>rfl)

def tierBoundRealizer : Realizer (fun x : LadderInput=>tierBound x.1.1 x.1.2 x.2) :=
  ((composition first.fst (fixedPower 2)).mulNat
    (((composition first.snd clogTwo).addNat ((constant 2).mulNat second)).addNat (constant 2))).congr (fun _=>rfl)

def ladderPowerPlan (x : (ℕ×ℕ)×List Bool) : Fraction×Fraction :=
  (TreeFraction.add ((1,1),TreeFraction.div ((1,1),(x.1.1^2,1))),
    TreeFraction.maximum ((x.1.2,1),TreeFraction.mul ((3,1),fuelPower ((4,1),x.2))))
def ladderPowerPlanRealizer : Realizer ladderPowerPlan :=
  (pair (composition (pair (constant (1,1))
    (composition (pair (constant (1,1)) (pair (composition first.fst (fixedPower 2)) (constant 1))) divRealizer)) addRealizer)
    (composition (pair (pair first.snd (constant 1))
      (composition (pair (constant (3,1)) (composition (pair (constant (4,1)) second) fuelPowerRealizer)) mulRealizer)) maximumRealizer)).congr (fun _=>rfl)

def ladderSearchInput (x : LadderInput) : PowerSearchInput :=
  (ladderPowerPlan (x.1,List.replicate x.2 false),List.replicate (tierBound x.1.1 x.1.2 x.2) false)
def ladderSearchInputRealizer : Realizer ladderSearchInput :=
  pair (composition (pair first (composition second fuelRealizer)) ladderPowerPlanRealizer)
    (composition tierBoundRealizer fuelRealizer)
def ladderSchedule (x : LadderInput) : ℕ := findPower (ladderSearchInput x)
def ladderScheduleRealizer : Realizer ladderSchedule := composition ladderSearchInputRealizer findPowerRealizer
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineSampleCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

def sigma (x : SigmaInput) : Fraction :=
  TreeFraction.minimum
    (TreeFraction.div ((1,100000),(100*x.1.1,1)),TreeFraction.div (x.2,(1000*x.1.2,1)))
def sigmaRealizer : Realizer sigma :=
  (composition (pair
    (composition (pair (constant (1,100000)) (pair ((constant 100).mulNat first.fst) (constant 1))) divRealizer)
    (composition (pair second (pair ((constant 1000).mulNat first.snd) (constant 1))) divRealizer)) minimumRealizer).congr (fun _=>rfl)

def invSigma (x : SampleCountInput) : Fraction := inverse (sigma x.2)
def reciprocalSigma : Realizer invSigma :=
  composition (f:=sigma ∘ Prod.snd) (g:=inverse)
    (composition (f:=Prod.snd) (g:=sigma) second sigmaRealizer) inverseRealizer

def fracProduct {A : Type} [Codec A] {f g : A→Fraction} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x=>TreeFraction.mul (f x,g x)) := composition (f:=fun x=>(f x,g x)) (g:=TreeFraction.mul) (pair F G) mulRealizer

def sampleFactorFn (x : SampleCountInput) : Fraction := TreeFraction.mul ((10,1),TreeFraction.mul (invSigma x,invSigma x))
def sampleFactor : Realizer sampleFactorFn := fracProduct (constant (10,1)) (fracProduct reciprocalSigma reciprocalSigma)
def sampleSum : Realizer sampleSumFn :=
  pair ((first.addNat second.fst.snd).addNat (constant 1)) (constant 1)

def sampleProduct (x : SampleCountInput) : Fraction := TreeFraction.mul (sampleFactorFn x,sampleSumFn x)
def sampleProductRealizer : Realizer sampleProduct := fracProduct sampleFactor sampleSum

def sampleCount (x : SampleCountInput) : ℕ := natCeil (sampleProduct x)
def sampleCountRealizer : Realizer sampleCount :=
  composition (f:=sampleProduct) (g:=natCeil) sampleProductRealizer natCeilRealizer

variable {G : GraphInput} [Nontrivial (Fin G.n)]
def repetitionsRealizer : Realizer repetitions :=
  (((constant 10).mulNat ((composition (composition inverseRealizer natCeilRealizer) clogTwo).addNat (constant 1))).addNat (constant 1)).congr (fun _=>rfl)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule

def seedK (x : Seed) : Seed×ℕ := (x,coolingSchedule (x.1.1.length,x.2.1))
def seedKRealizer : Realizer seedK :=
  (pair identity (composition (g:=coolingSchedule) (pair (composition first.fst listLength) second.fst) coolingScheduleRealizer)).congr (fun _=>rfl)
def seedN (x : Seed×ℕ) : (Seed×ℕ)×ℕ := (x,vertexNumber (x.1.1.1.length,x.2))
def seedNRealizer : Realizer seedN :=
  (pair identity (composition (g:=vertexNumber) (pair (composition first.fst.fst listLength) second) vertexNumberRealizer)).congr (fun _=>rfl)
def seedDRealizer : Realizer seedD :=
  pair first (pair second (composition (pair (composition first.fst.fst.fst listLength) second) distortionRealizer))
def config (x : Seed) : Config := seedD (seedN (seedK x))
def configRealizer : Realizer config := composition (composition seedKRealizer seedNRealizer) seedDRealizer

def rootRealizer : Realizer root :=
  composition (pair (composition (pair identity (constant 1)) subtract) (composition identity fuelRealizer)) findRootRealizer
def initialScaleRealizer : Realizer initialScale :=
  composition (pair (constant (1,1)) (pair rootRealizer (constant 1))) divRealizer
def scaleVectorRealizer : Realizer scaleVector :=
  (composition (pair (composition listLength initialScaleRealizer) identity)
    (mapWith (pair second first))).congr (fun _=>rfl)

def nRealizer : Realizer (fun x : Config=>x.1.1.1.1.length) := composition first.fst.fst.fst listLength

def count (x : Config) : ℕ := sampleCount (x.1.1.1.1.length,((x.2.2,x.1.2),x.1.1.2.1))
def countRealizer : Realizer count :=
  composition (pair nRealizer (pair (pair second.snd first.snd) first.fst.snd.fst)) sampleCountRealizer

def data (x : Config) : SparseStageData :=
  (((x.1.1.1,[]),(((List.replicate (2*x.1.2+2) false,List.replicate (2*x.1.2) false),x.2.2),
    (List.replicate (ladderSchedule (x.2,x.1.2)) false,List.replicate (Transport.ladderQ x.2.1 x.2.2) false))),
    scaleVector x.1.1.1.1)
def dataRealizer : Realizer data :=
  (pair (pair (pair first.fst.fst (constant []))
    (pair (pair (pair (composition (g:=fun n=>List.replicate n false) (((constant 2).mulNat first.snd).addNat (constant 2)) fuelRealizer)
      (composition ((constant 2).mulNat first.snd) fuelRealizer)) second.snd)
      (pair (composition (composition (pair second first.snd) ladderScheduleRealizer) fuelRealizer)
        (composition (composition second qRealizer) fuelRealizer))))
    (composition first.fst.fst.fst scaleVectorRealizer)).congr (fun _=>rfl)

def trialInput (x : Config) : OnlineAmplification.TrialInput :=
  (List.replicate x.1.2 false,((data x,count x),(UnitRefresh.pairingCount x.1.1.1.1.length,1)))
def trialInputRealizer : Realizer trialInput :=
  pair (composition first.snd fuelRealizer)
    (pair (pair dataRealizer countRealizer) (pair (composition nRealizer pairingNumber) (constant 1)))
def runInput (x : Config) : ℕ×OnlineAmplification.TrialInput :=
  (repetitions x.1.1.2.2,trialInput x)
def runInputRealizer : Realizer runInput :=
  (pair (composition (g:=repetitions) first.fst.snd.snd repetitionsRealizer) trialInputRealizer).congr (fun _=>rfl)

def initializeInput (x : Seed) : ℕ×OnlineAmplification.TrialInput := runInput (config x)
def initializeInputRealizer : Realizer initializeInput := composition configRealizer runInputRealizer
end MatchingFPRAS.OnlineInitial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineInitialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule
open Transport Enlargement

variable {G : GraphInput} [Nontrivial (Fin G.n)]
variable (hn : 2≤G.n) (heven : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1)
noncomputable def sourceSeed : Seed := (graphRep G,(TreeFraction.repr ε,TreeFraction.repr δ))
end MatchingFPRAS.OnlineInitial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_OnlineGraphInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGraph
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource
open PhysicalStream OnlineSchedule

variable (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es)
def data (x : SparseStageData) : SparseStageData :=
  (((graph f x.1.1.1,x.1.1.2),x.1.2),x.2)
def request (x : RequestInput) : RequestInput := (data f x.1,x.2)
def state (x : OnlineTrial.State) : OnlineTrial.State := (request f x.1,x.2)
end MatchingFPRAS.OnlineGraph

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineCase
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]
namespace Case
open OnlineControl

lemma runs {f g : A→Experiment B} (F : Realizer f) (G : Realizer g) (b : Bool) (a : A) (s : Data) :
    ∃ q,At (code F.program G.program) (fun y=>env (encode y) .nil s) (Option.some Point.split)
      (env (encode (b,a)) .nil s) q ∧
      (∀ h : B→ℚ,q.mean h=(if b then f a else g a).mean h) ∧
      q.cost≤(if b then F.cost a else G.cost a)+30 := by
  let M:=code F.program G.program
  let out:=fun y : B=>env (encode y) .nil s
  have hend y:=OnlineControl.halt M out Point.halt rfl y
  cases b with
  | false =>
    obtain ⟨r,hr,hm,hc⟩:=G.correct a s
    have hb:=call M out Point.no Point.halt G.program rfl (env (encode a) .nil s)
      (fun y=>env (encode y) .nil s) r hr (fun y=>.delay 1 (.done y)) hend
    obtain ⟨q,hq,hqm,hqc⟩:=deterministicCall M out Point.noClear Point.no
      (TreeFunction.clear 1) rfl _ _ _ (clear1 (encode a) (encode false) s) _ hb
    have ht:=nilBranch M out Point.test Point.noClear Point.yesClear 1 rfl _ rfl _ hq
    obtain ⟨v,hv,hvm,hvc⟩:=deterministicCall M out Point.split Point.test
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode false) (encode a) .nil s) _ ht
    refine ⟨v,hv,?_,?_⟩
    · intro h
      rw [hvm,Experiment.mean,hqm,Experiment.mean,Experiment.mean_bind]
      exact hm h
    · have hh:=Experiment.cost_bind_le r (fun y=>.delay 1 (.done y)) 1 (fun _=>by rfl)
      simp only [Experiment.cost] at hqc hvc
      change v.cost≤G.cost a+30
      change q.cost≤1+2+1+(1+(r.bind (fun y=>.delay 1 (.done y))).cost) at hqc
      change v.cost≤1+2*1+4+1+(1+q.cost) at hvc
      omega
  | true =>
    obtain ⟨r,hr,hm,hc⟩:=F.correct a s
    have hb:=call M out Point.yes Point.halt F.program rfl (env (encode a) .nil s)
      (fun y=>env (encode y) .nil s) r hr (fun y=>.delay 1 (.done y)) hend
    obtain ⟨q,hq,hqm,hqc⟩:=deterministicCall M out Point.yesClear Point.yes
      (TreeFunction.clear 1) rfl _ _ _ (clear1 (encode a) (encode true) s) _ hb
    have ht:=consBranch M out Point.test Point.noClear Point.yesClear 1 rfl _ .nil .nil rfl _ hq
    obtain ⟨v,hv,hvm,hvc⟩:=deterministicCall M out Point.split Point.test
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode true) (encode a) .nil s) _ ht
    refine ⟨v,hv,?_,?_⟩
    · intro h
      rw [hvm,Experiment.mean,hqm,Experiment.mean,Experiment.mean_bind]
      exact hm h
    · have hh:=Experiment.cost_bind_le r (fun y=>.delay 1 (.done y)) 1 (fun _=>by rfl)
      simp only [Experiment.cost] at hqc hvc
      change v.cost≤F.cost a+30
      change q.cost≤3+2+1+(1+(r.bind (fun y=>.delay 1 (.done y))).cost) at hqc
      change v.cost≤1+2*3+4+1+(1+q.cost) at hvc
      omega
end Case
noncomputable def caseBool {f g : A→Experiment B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x : Bool×A=>if x.1 then f x.2 else g x.2) where
  program := OnlineControl.compile (Case.code F.program G.program)
  cost := fun x=>(if x.1 then F.cost x.2 else G.cost x.2)+30
  correct := fun x s=>Case.runs F G x.1 x.2 s
noncomputable def conditional {p : A→Bool} {f g : A→Experiment B} (P : TreeTyped.Realizer p)
    (F : Realizer f) (G : Realizer g) : Realizer (fun a=>if p a then f a else g a) :=
  (composition (deterministic (TreeTyped.pair P TreeTyped.identity)) (caseBool F G)).congr (fun _ _=>rfl)
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B A' B' : Type} [Codec A] [Codec B] [Codec A'] [Codec B']
def Realizer.reencode {f : A→B} (F : Realizer f) (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a) (hg : ∀ a,encode (g a)=encode (f (i a))) : Realizer g where
  program := F.program
  cost a := F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi a,←hg a] at h
    exact h
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

instance instCodecSymbol : Codec Symbol := ⟨fun a=>TreeTyped.encode (parts a)⟩
lemma encode_parts (a : Symbol) : TreeTyped.encode (parts a)=TreeTyped.encode a := rfl
lemma weight_false_list (n : ℕ) : weight (List.replicate n false)=2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,weight_cons,ih]; change 1+1+(2*n+1)=_; omega
lemma weight_symbol (a : Symbol) : weight a=17 := by
  change weight (parts a)=17
  simp only [parts,weight_prod,weight_false_list]
  have ha:=a.isLt
  omega

def valRealizer : Realizer (Fin.val : Symbol→ℕ) :=
  (composition first listLength).reencode parts Fin.val encode_parts (fun a=>by simp [parts])
def fromBitRealizer : Realizer fromBit := choose identity (constant 2) (constant 1)
def natWordRealizer : Realizer natWord :=
  (composition (pair (composition toBits (map fromBitRealizer)) (constant [3])) append).congr (fun _=>rfl)
def ratWordRealizer : Realizer ratWord :=
  (composition (pair (constant 4) (composition (pair (composition first natWordRealizer)
    (composition second natWordRealizer)) append)) listCons).congr (fun _=>rfl)
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Parse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

def eqSymbol (a : Symbol) : Realizer (fun b : Symbol=>decide (b=a)) :=
  (composition (pair valRealizer (constant a.val)) natEqual).congr
    (fun b=>by simp only [Function.comp_apply,Fin.ext_iff])

def numStepRealizer : Realizer numStep :=
  (choose (composition first (eqSymbol 3))
    (composition (pair (constant 0) second) listCons)
    (choose (composition first (eqSymbol 1))
      (composition (pair ((constant 2).mulNat (composition second (head 0))) (composition second tail)) listCons)
      (choose (composition first (eqSymbol 2))
        (composition (pair (((constant 2).mulNat (composition second (head 0))).addNat (constant 1)) (composition second tail)) listCons)
        second))).congr (fun x=>by simp only [Function.comp_apply,decide_eq_true_eq,numStep])
def parseRealizer : Realizer parse :=
  (composition (pair reverse (constant [])) (fold numStepRealizer)).congr (fun as=>by
    simp only [Function.comp_apply,List.foldl_reverse,parse])
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Input
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped TreeFunction Polynomial LiteralParse

def pairStepRealizer : Realizer pairStep :=
  (choose second.fst.fst
    (pair (constant (false,0)) (composition (pair (pair first second.fst.snd) second.snd) listCons))
    (pair (pair (constant true) first) second.snd)).congr (by
      intro x;simp only [Function.comp_apply,pairStep])
def pairsRealizer : Realizer pairs :=
  (composition
    (composition (pair identity (constant (((false,0),[]) : PairState))) (fold pairStepRealizer)) second).congr (fun _=>rfl)
def ratTailRealizer : Realizer ratTail :=
  pair (pair (composition (composition (composition tail tail) tail) (head 0))
    (composition (composition tail tail) (head 0)))
    (pair (composition tail (head 0)) (head 0))
def reversedTailRealizer : Realizer (fun ns : List ℕ=>ns.tail.tail.reverse) :=
  composition (composition tail tail) reverse
def fromNumbersRealizer : Realizer fromNumbers :=
  (pair (head 0) (pair
    (composition (composition (composition (composition (composition reversedTailRealizer tail) tail) tail) tail) pairsRealizer)
    (composition reversedTailRealizer ratTailRealizer))).congr (fun _=>rfl)
def parseInputRealizer : Realizer parseInput := composition LiteralParse.parseRealizer fromNumbersRealizer
end MatchingFPRAS.LiteralInput

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

def emptyRealizer : Realizer empty := composition (pair first (constant 0)) natEqual
def invalidRealizer : Realizer invalid :=
  (choose (composition first ExecutableSource.evenTest)
    (composition (pair first second.fst) ExecutableInput.tooSparseRealizer) (constant true)).congr (by
      intro x
      unfold invalid
      cases h : decide (x.1%2=0) <;> simp only [Function.comp_apply,h,Bool.not_true,Bool.not_false,Bool.false_or,Bool.true_or,Bool.false_eq_true,ite_false,ite_true])
def materializeRealizer : Realizer materialize :=
  pair (pair (composition first range) second.fst) second.snd

def compute (x : Parsed) : Experiment Fraction :=
  OnlineAmplification.run (OnlineInitial.initializeInput (materialize x))
noncomputable def computeRealizer : OnlineTree.Realizer compute :=
  (OnlineTree.composition (OnlineTree.deterministic
    (composition materializeRealizer OnlineInitial.initializeInputRealizer)) OnlineAmplification.runRealizer).congr (fun _ _=>rfl)

def count (x : Parsed) : Experiment Fraction :=
  if empty x then .done (1,1) else if invalid x then .done (0,1) else compute x
noncomputable def countRealizer : OnlineTree.Realizer count :=
  (OnlineTree.conditional emptyRealizer (OnlineTree.deterministic (constant (1,1)))
    (OnlineTree.conditional invalidRealizer (OnlineTree.deterministic (constant (0,1))) computeRealizer)).congr (fun _ _=>rfl)

def algorithm (as : List Symbol) : Experiment (List Symbol) :=
  (count (parseInput as)).map LiteralCodec.ratWord
noncomputable def algorithmRealizer : OnlineTree.Realizer algorithm :=
  (OnlineTree.composition (OnlineTree.composition (OnlineTree.deterministic parseInputRealizer) countRealizer)
    (OnlineTree.deterministic LiteralCodec.ratWordRealizer)).congr (by
      intro as h;simp only [algorithm,Experiment.mean_bind,Experiment.mean,Experiment.mean_map])

noncomputable def reorder (G : GraphInput) (es : OnlineGraph.Edges) : OnlineGraph.Edges :=
  if es=(ExecutableAdaptive.graphRep G).2 then edgeNumbers G else es
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def WorkBound {f : A→Experiment B} (F : Realizer f) (measure : A→ℕ) : Prop :=
  ∃ p : Polynomial ℕ,∀ a,F.cost a+(f a).worst weight≤p.eval (measure a)
abbrev PolynomialTime {f : A→Experiment B} (F : Realizer f) : Prop := WorkBound F weight
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineSampleCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]

def mass (m : A→ℕ) (as : List A) : ℕ := weight as+(as.map m).sum

def repeatMeasure (m : A→ℕ) (x : ℕ×A) : ℕ := x.1+weight x+m x.2

def pairMeasure (x : ℕ×ℕ) : ℕ := x.1+x.2+weight x

def scansMeasure (x : (ℕ×ℕ)×ℕ) : ℕ := pairMeasure x.1+x.2+weight x

def markMeasure (x : ℕ×ℕ) : ℕ := x.2+weight x

def marksMeasure (x : ℕ×List ℕ) : ℕ := x.1+weight x

def requestMeasure (x : Request) : ℕ := scansMeasure x.1+marksMeasure x.2+weight x
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineRequestCost
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial NumericBounds Transport ExecutableSource

def requestSize (x : RequestInput) : ℕ := x.1.1.2.1.2+x.2+TreeTyped.weight x
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineStageCost
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSample

def inputSize (x : Input) : ℕ := repeatMeasure requestMeasure x.2+weight x
end MatchingFPRAS.OnlineStage

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

def stateSize (x : State) : ℕ := requestSize x.1+weight x
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineHistorySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped TreeFraction PhysicalStream ExecutableSource ExecutableScaling
open BitArithmetic Polynomial OnlineStage OnlineSchedule OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def sizeNorm (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData) : ℕ :=
  G.n+p.K+p.N+p.D+p.S+p.T+p.q+weight g+(Z (completeGraph G.n)+1).size
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineHistoryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def initial (f : Edges→Edges) (p : Trial.Parameters G) : List Bool×State :=
  (List.replicate p.K false,state f (represent p (FiniteTrial.firstLayer p) PUnit.unit))
def History (f : Edges→Edges) (p : Trial.Parameters G) (k : ℕ) (s : State) : Prop :=
  ∃ (j : ℕ) (hj : j≤p.K) (x : (FiniteTrial.layers p j hj).Ω),j+k=p.K ∧
    s=state f (represent p (FiniteTrial.layers p j hj) x)

open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AlgorithmLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

def Proper (G : GraphInput) (as : List Symbol) : Prop :=
  ∃ q : ℚ,0≤q ∧ as=encodeRat q ∧ (Z G=0→q=0)
def AccurateWord (G : GraphInput) (ε : ℚ) (as : List Symbol) : Prop :=
  ∃ q : ℚ,as=encodeRat q ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ)
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineScheduleCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial NumericBounds ExecutableSource Transport

def vertexMeasure (x : ℕ×ℕ) : ℕ := x.1+x.2+TreeTyped.weight x

def ladderMeasure (x : LadderInput) : ℕ := x.1.1+x.1.2+x.2+TreeTyped.weight x
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineInitialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction OnlineSchedule Polynomial NumericBounds

def configNumeric (x : Config) : ℕ := x.1.1.1.1.length+x.1.2+x.2.1+x.2.2+
  ladderSchedule (x.2,x.1.2)+Transport.ladderQ x.2.1 x.2.2
def configSize (x : Config) : ℕ := configNumeric x+weight x
def seedSize (x : Seed) : ℕ := x.1.1.length+natCeil (inverse x.2.1)+configNumeric (config x)+weight x

def seedNSize (x : Seed×ℕ) : ℕ := x.1.1.1.length+x.2+weight x
end MatchingFPRAS.OnlineInitial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

noncomputable def physicalProgram {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) : Program where
  State := OnlineStack.Q (K Reg) (fun _=>Bool) F.program.Label RegisterProc.Store
  table := liftBool (OnlineStack.table F.program.code F.program.coin)
  states := OnlineStack.states F.program.code
  supported := liftBool_supported _ _ (OnlineStack.table_supported F.program.code F.program.coin)
  entry := OnlineStack.initialState
  entry_mem := OnlineStack.initialState_mem F.program.code

noncomputable def physicalCost {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) : ℕ :=
  F.cost a*OnlineStack.Executes.factor F.program.code (weight a) (F.cost a)

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

def symbolBits (a : Symbol) : List Bool := (TreeData.encode (TreeTyped.encode a)).reverse++[true]
lemma symbolBits_length (a : Symbol) : (symbolBits a).length=18 := by
  simp only [symbolBits,List.length_append,List.length_reverse,List.length_singleton]
  change weight a+1=18
  rw [LiteralCodec.weight_symbol]
noncomputable def chunk (a : Symbol) : List Symbol := (symbolBits a).flatMap (fun b=>block (letter b))
lemma chunk_length (a : Symbol) : (chunk a).length=18*width := by
  exact (flatMap_uniform_length (symbolBits a) (fun b=>block (letter b)) width
    (fun b=>block_length (letter b))).trans (congrArg (fun n=>n*width) (symbolBits_length a))

end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PackedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

noncomputable def chunkFn (a : Symbol) : LiteralBlockMap.Block (18*width) :=
  fun i=>(chunk a)[i.val]'(by rw [chunk_length];exact i.isLt)
noncomputable def unchunk (b : LiteralBlockMap.Block (18*width)) : List Symbol :=
  [Function.invFun chunk (List.ofFn b)]
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PackedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

noncomputable def packCode := LiteralBlockMap.code 1 (fun b=>chunk (b 0)) header
noncomputable def unpackCode := LiteralBlockMap.code (18*width) unchunk []
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_Wrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped

noncomputable def pack : Program := Program.ofTM1 packCode .start (fun _=>0)
noncomputable def unpack : Program := Program.ofTM1 unpackCode .start (fun _=>0)
noncomputable def post : Program := erase.seq unpack
noncomputable def packTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget 1 (18*width) n 0)*MachineCost.programCost packCode
noncomputable def unpackTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget (18*width) 1 n 0)*MachineCost.programCost unpackCode
noncomputable def postTime (n : ℕ) : ℕ := eraseTime+unpackTime n

noncomputable def wrap {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f) : Program :=
  (pack.seq (OnlineTree.physicalProgram F)).seq post
noncomputable def wrapTime {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f)
    (as : List Symbol) : ℕ := packTime as.length+OnlineTree.physicalCost F as+postTime ((f as).worst List.length)
noncomputable def mainProgram : Program := wrap LiteralAlgorithm.algorithmRealizer
end MatchingFPRAS.LiteralPhysical

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_MainLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralAlgorithm
open scoped Classical

def ProperTape (G : GraphInput) (T : Tape Symbol) : Prop :=
  ∃ q : ℚ,0≤q ∧ T.right₀=ListBlank.mk (encodeRat q) ∧ (Z G=0→q=0)
def AccurateTape (G : GraphInput) (ε : ℚ) (T : Tape Symbol) : Prop :=
  ∃ q : ℚ,T.right₀=ListBlank.mk (encodeRat q) ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ)
end MatchingFPRAS.LiteralPhysical

end OAI
end


