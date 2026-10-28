-- Prove2me | Definitions.Def_OAIQ051M003
-- name    : OAIQ051M003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:16:45.858298+00:00
-- url     : https://prove2.me/theorems/f5e6ce9b-1e15-423a-b515-c0dbd530d7ad
-- title:
--   Definitions bundle OAIQ051M003 of the split of OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 732 declarations of OpenAI's Lean: 374 definitions, 11 inductive types or structures, 15 instances and 332 theorems. The definitions and types are `OAI.MatchingFPRAS.ExecutableSource.logicalRepr`, `OAI.MatchingFPRAS.ExecutableUnit.resultRep`, `OAI.MatchingFPRAS.FiniteTrial.estimateMatrix`, `OAI.MatchingFPRAS.FiniteTrial.probeMatrix`, `OAI.MatchingFPRAS.FixedAlphabetCompiler.word`, `OAI.MatchingFPRAS.GraphBridge.perfectEquiv`, `OAI.MatchingFPRAS.Initializer.fillFixed`, `OAI.MatchingFPRAS.Initializer.holesPairingEquiv`, `OAI.MatchingFPRAS.Initializer.restrictHoles`, `OAI.MatchingFPRAS.LiteralAlgorithm.empty`, `OAI.MatchingFPRAS.LiteralAlgorithm.invalid`, `OAI.MatchingFPRAS.LiteralAlgorithm.materialize`, `OAI.MatchingFPRAS.LiteralCodec.ratWord`, `OAI.MatchingFPRAS.LiteralInput.Parsed`, `OAI.MatchingFPRAS.LiteralInput.fromNumbers`, `OAI.MatchingFPRAS.LiteralInput.parseInput`, `OAI.MatchingFPRAS.LiteralInput.ratTail`, `OAI.MatchingFPRAS.LiteralPacked.Row`, `OAI.MatchingFPRAS.LiteralPacked.baseRow`, `OAI.MatchingFPRAS.LiteralPacked.bitRow`, `OAI.MatchingFPRAS.LiteralPacked.block`, `OAI.MatchingFPRAS.LiteralPacked.bottom`, `OAI.MatchingFPRAS.LiteralPacked.header`, `OAI.MatchingFPRAS.LiteralPacked.letter`, `OAI.MatchingFPRAS.LiteralPacked.width`, `OAI.MatchingFPRAS.LiteralPhysical.erase`, `OAI.MatchingFPRAS.LiteralPhysical.eraseTime`, `OAI.MatchingFPRAS.LiteralTape.Exec`, `OAI.MatchingFPRAS.LiteralTape.states`, `OAI.MatchingFPRAS.LiteralTape.table`, `OAI.MatchingFPRAS.Marking.completionEquiv`, `OAI.MatchingFPRAS.Marking.conditional`, `OAI.MatchingFPRAS.NumericLadder.instDecidableEqBagPM`, `OAI.MatchingFPRAS.NumericMarking.Summaries`, `OAI.MatchingFPRAS.NumericMarking.UpdateConfig`, `OAI.MatchingFPRAS.NumericMarking.logicalProbes`, `OAI.MatchingFPRAS.OnlineControl.At`, `OAI.MatchingFPRAS.OnlineControl.Instr`, `OAI.MatchingFPRAS.OnlineControl.Label`, `OAI.MatchingFPRAS.OnlineControl.cfg` and 345 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatchingCount, in whole or in part: `MatchingCount_Algorithm_AffineWeights`, `MatchingCount_Algorithm_Algorithm`, `MatchingCount_Algorithm_FiniteStage`, `MatchingCount_Algorithm_OnlineCoolingSchedule`, `MatchingCount_Algorithm_OnlineGuard`, `MatchingCount_Algorithm_OnlineGuardLaw`, `MatchingCount_Algorithm_OnlineInitial`, `MatchingCount_Algorithm_OnlineLaw`, `MatchingCount_Algorithm_OnlineMedian`, `MatchingCount_Algorithm_OnlinePowerSearch`, `MatchingCount_Algorithm_OnlineSampleCount`, `MatchingCount_Algorithm_OnlineTransitionLaw`, `MatchingCount_Algorithm_OutputLengthBound`, `MatchingCount_Algorithm_RationalEstimator`, `MatchingCount_Algorithm_RationalObservables`, `MatchingCount_Algorithm_RationalStart`, `MatchingCount_Algorithm_RelabelWeights`, `MatchingCount_Algorithm_TreeNumericSummaries`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Arithmetic_OnlineFractionParam`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Complexity_TreeFractionCosts`, `MatchingCount_Graphs_Admissible`, `MatchingCount_Graphs_ColoredEdge`, `MatchingCount_Graphs_Cycle`, `MatchingCount_Graphs_Edge`, `MatchingCount_Graphs_Edge2`, `MatchingCount_Graphs_EdgeLow`, `MatchingCount_Graphs_EnlargementRun`, `MatchingCount_Graphs_Evolve`, `MatchingCount_Graphs_FillHoles`, `MatchingCount_Graphs_Height`, `MatchingCount_Graphs_HoleBlocks`, `MatchingCount_Graphs_Incident`, `MatchingCount_Graphs_IndexedCycle`, `MatchingCount_Graphs_LabelCycle`, `MatchingCount_Graphs_LabelOrder`, `MatchingCount_Graphs_Marked`, `MatchingCount_Graphs_MatchingMap`, `MatchingCount_Graphs_OnlineGraphInvariant`, `MatchingCount_Graphs_PM`, `MatchingCount_Graphs_Profile`, `MatchingCount_Graphs_RatWeight`, `MatchingCount_Graphs_RelabelMore`, `MatchingCount_Graphs_Related`, `MatchingCount_Graphs_Related2`, `MatchingCount_Graphs_RemainingBags`, `MatchingCount_Graphs_SafeSwitch`, `MatchingCount_Graphs_SafeTrace`, `MatchingCount_Graphs_Sets`, `MatchingCount_Graphs_SumLiftMate`, `MatchingCount_Graphs_TreeCycleTable`, `MatchingCount_Graphs_TreeGeometry`, `MatchingCount_Graphs_TreeMatchingCheck`, `MatchingCount_Machines_OnlineBounds`, `MatchingCount_Machines_OnlineCase`, `MatchingCount_Machines_OnlineControl`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_OnlineTree`, `MatchingCount_Machines_PhysicalPost`, `MatchingCount_Machines_PhysicalProcess`, `MatchingCount_Machines_PhysicalProgram`, `MatchingCount_Machines_PhysicalRestriction`, `MatchingCount_Machines_PhysicalSequential`, `MatchingCount_Machines_TreeCertify`, `MatchingCount_Machines_TreePairProposal`, `MatchingCount_Machines_TreePostRealization`, `MatchingCount_Machines_Wrapper`, `MatchingCount_Probability_LocalVariance`, `MatchingCount_Probability_Tv`, `MatchingCount_Probability_Variance`, `MatchingCount_Sampling_AssignmentEquiv`, `MatchingCount_Sampling_Certify`, `MatchingCount_Sampling_ChosenChord`, `MatchingCount_Sampling_Component`, `MatchingCount_Sampling_ComponentOrder`, `MatchingCount_Sampling_Components`, `MatchingCount_Sampling_Corner`, `MatchingCount_Sampling_DiscreteLadderSteps`, `MatchingCount_Sampling_EndpointPair`, `MatchingCount_Sampling_Endpoints`, `MatchingCount_Sampling_IntervalPattern`, `MatchingCount_Sampling_LadderL`, `MatchingCount_Sampling_MarkBridge`, `MatchingCount_Sampling_PM`, `MatchingCount_Sampling_Plan`, `MatchingCount_Sampling_RankOrder`, `MatchingCount_Sampling_Relabel`, `MatchingCount_Sampling_RelabelMarking`, `MatchingCount_Sampling_RelationDestinations`, `MatchingCount_Sampling_Sewn`, `MatchingCount_Sampling_Span`, `MatchingCount_Sampling_Sym2Order`, `MatchingCount_Sampling_TableMarking`, `MatchingCount_Sampling_Through`, `MatchingCount_Sampling_TierClamp`, `MatchingCount_Sampling_TreeLadder`, `MatchingCount_Sampling_TreeUnitAssemble`, `MatchingCount_Sampling_Underlying`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_FixedAlphabetCompiler`, `MatchingCount_Tapes_Input`, `MatchingCount_Tapes_Online`, `MatchingCount_Tapes_OnlineComposition`, `MatchingCount_Tapes_OnlineStackCompiler`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_Physical`, `MatchingCount_Tapes_PhysicalAlphabet`, `MatchingCount_Tapes_StackWords`, `MatchingCount_Tapes_TapeTools`.
--
--   **Imports.** It imports the published bundle `Def_MatchingFPRAS`; the bundles `OAIQ051M000` and `OAIQ051M001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ051M004`.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatchingCount at commit adc7f12

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M000
import Definitions.Def_OAIQ051M001

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

theorem withEdge_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    HasHoles (withEdge m a b) (S \ {a, b}) := by
  classical
  intro v
  rw [withEdge_apply m a b v ((hm a).mpr ha) ((hm b).mpr hb)]
  by_cases hva : v = a
  · subst v
    simp [hab, Ne.symm hab]
  by_cases hvb : v = b
  · subst v
    simp [hab, Ne.symm hab]
  simp [hva, hvb, hm v]

theorem rowMax_attained [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a : V) :
    ∃ b, b ≠ a ∧ holeRatio w {a,b} = rowMax hcard w a := by
  unfold rowMax
  obtain ⟨b,hb,he⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ.erase a).Nonempty by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      omega) (fun b => holeRatio w {a,b})
  exact ⟨b,(Finset.mem_erase.mp hb).1,he.symm⟩

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AffineWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

noncomputable def holeAugmentation [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : ℝ := bottleneck w a b / holeScale V

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_FixedAlphabetCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedAlphabetCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Fintype Γ] [Inhabited Λ]
  [Inhabited σ] [Fintype σ]
variable {w : ℕ} (enc : Γ → List.Vector Bool w) (dec : List.Vector Bool w → Γ)
  (enc0 : enc default = List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
def word (input : List Γ) : List Symbol := (bitsWord enc input).map BoolPostCompiler.up
end MatchingFPRAS.FixedAlphabetCompiler

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_StackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing MachineCost

variable {K : Type*} {Γ : K → Type*}
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]
variable [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Fintype σ]
variable {w : ℕ} (enc : TM2to1.Γ' K Γ → List.Vector Bool w)
  (dec : List.Vector Bool w → TM2to1.Γ' K Γ)
  (enc0 : enc default=List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a)
  (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM2.Supports M S)
def encoded (S₀ : ∀ k,List (Γ k)) (H : ℕ) : List Symbol :=
  FixedAlphabetCompiler.word enc (word S₀ H)
end MatchingFPRAS.StackWords

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ColoredEdge
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V L : Type*}

namespace ColoredEdge

variable (e : ColoredEdge V L)

lemma exists_incident : ∃ v, e.Incident v := by
  change ∃ v, v ∈ e.val.1
  exact Sym2.inductionOn e.val.1 fun a b => ⟨a, by simp⟩

end ColoredEdge

namespace BagEdge

variable {bags : V → Finset L}

lemma exists_incident (e : BagEdge bags) : ∃ v, e.Incident v := e.val.exists_incident

end BagEdge

variable {E : Type*} [DecidableEq V] [DecidableEq E] (inc : E → V → Prop)

namespace MatchingOn

variable {inc} {M P Q : Finset E} {U W : Finset V}

omit [DecidableEq V] [DecidableEq E] in
lemma unique (hM : MatchingOn inc M U) {v : V} (hv : v ∈ U)
    {e f : E} (he : e ∈ M) (hev : inc e v) (hf : f ∈ M) (hfv : inc f v) : e = f := by
  obtain ⟨g, _, hg⟩ := hM.2 v hv
  exact (hg e ⟨he, hev⟩).trans (hg f ⟨hf, hfv⟩).symm

omit [DecidableEq V] [DecidableEq E] in
lemma edge_mem_of_incident (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hsub : P ⊆ M) {e : E} (he : e ∈ M) {v : V} (hv : v ∈ W) (hev : inc e v) : e ∈ P := by
  obtain ⟨f, ⟨hf, hfv⟩, _⟩ := hP.2 v hv
  have eq : e = f := hM.unique (hM.1 e he v hev) he hev (hsub hf) hfv
  exact eq ▸ hf

omit [DecidableEq V] [DecidableEq E] in
lemma disjoint_edges (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hinc : ∀ e, ∃ v, inc e v) (hdis : Disjoint U W) : Disjoint M P := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨v, hv⟩ := hinc e
  exact Finset.disjoint_left.mp hdis (hM.1 e he v hv) (hP.1 e hf v hv)

lemma union (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hdis : Disjoint U W) : MatchingOn inc (M ∪ P) (U ∪ W) := by
  refine ⟨?_, ?_⟩
  · intro e he v hev
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (hM.1 e he v hev)
    · exact Finset.mem_union_right _ (hP.1 e he v hev)
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨e, ⟨he, hev⟩, hu⟩ := hM.2 v hv
      refine ⟨e, ⟨Finset.mem_union_left _ he, hev⟩, ?_⟩
      intro f hf
      rcases Finset.mem_union.mp hf.1 with hfM | hfP
      · exact hu f ⟨hfM, hf.2⟩
      · exact False.elim (Finset.disjoint_left.mp hdis hv (hP.1 f hfP v hf.2))
    · obtain ⟨e, ⟨he, hev⟩, hu⟩ := hP.2 v hv
      refine ⟨e, ⟨Finset.mem_union_right _ he, hev⟩, ?_⟩
      intro f hf
      rcases Finset.mem_union.mp hf.1 with hfM | hfP
      · exact False.elim (Finset.disjoint_left.mp hdis (hM.1 f hfM v hf.2) hv)
      · exact hu f ⟨hfP, hf.2⟩

lemma sdiff (hM : MatchingOn inc M U) (hP : MatchingOn inc P W) (hsub : P ⊆ M) :
    MatchingOn inc (M \ P) (U \ W) := by
  refine ⟨?_, ?_⟩
  · intro e he v hev
    obtain ⟨heM, heP⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨hM.1 e heM v hev, ?_⟩
    intro hv
    exact heP (hM.edge_mem_of_incident hP hsub heM hv hev)
  · intro v hv
    obtain ⟨hvU, hvW⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := hM.2 v hvU
    have heP : e ∉ P := fun hp => hvW (hP.1 e hp v hev)
    refine ⟨e, ⟨Finset.mem_sdiff.mpr ⟨he, heP⟩, hev⟩, ?_⟩
    intro f hf
    exact hu f ⟨(Finset.mem_sdiff.mp hf.1).1, hf.2⟩

lemma replace (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hQ : MatchingOn inc Q W) (hsub : P ⊆ M) (hWU : W ⊆ U) :
    MatchingOn inc ((M \ P) ∪ Q) U := by
  have h := (hM.sdiff hP hsub).union hQ Finset.sdiff_disjoint
  simpa only [Finset.sdiff_union_of_subset hWU] using h

lemma context_disjoint (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hQ : MatchingOn inc Q W) (hsub : P ⊆ M)
    (hinc : ∀ e, ∃ v, inc e v) : Disjoint (M \ P) Q :=
  (hM.sdiff hP hsub).disjoint_edges hQ hinc Finset.sdiff_disjoint

end MatchingOn

lemma pattern_interchange {M N P Q : Finset E} {U W : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hP : MatchingOn inc P W) (hQ : MatchingOn inc Q W)
    (hPM : P ⊆ M) (hQN : Q ⊆ N) (hWU : W ⊆ U)
    (hinc : ∀ e, ∃ v, inc e v) :
    MatchingOn inc ((M \ P) ∪ Q) U ∧
    MatchingOn inc ((N \ Q) ∪ P) U ∧
    ((M \ P) ∪ Q).val + ((N \ Q) ∪ P).val = M.val + N.val := by
  refine ⟨hM.replace hP hQ hPM hWU, hN.replace hQ hP hQN hWU, ?_⟩
  rw [union_val_add (hM.context_disjoint hP hQ hPM hinc),
    union_val_add (hN.context_disjoint hQ hP hQN hinc)]
  calc
    _ = ((M \ P).val + P.val) + ((N \ Q).val + Q.val) := by ac_rfl
    _ = _ := by rw [sdiff_val_add hPM, sdiff_val_add hQN]

lemma pathPattern_matching (vertices : ℕ → V) (edges : ℕ → E) (lo hi : ℕ)
    (hlohi : lo < hi) (hodd : (hi - lo) % 2 = 1)
    (hinj : Set.InjOn vertices (Set.Icc lo hi))
    (hedges : ∀ i, lo ≤ i → i < hi →
      ∀ v, inc (edges i) v ↔ v = vertices i ∨ v = vertices (i + 1)) :
    MatchingOn inc (pathPattern edges lo hi) ((Finset.Icc lo hi).image vertices) := by
  classical
  refine ⟨?_, ?_⟩
  · intro e he v hv
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hirange, hiParity⟩ := Finset.mem_filter.mp hi'
    obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hirange
    rcases (hedges i hil hih v).mp hv with rfl | rfl
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hil, by omega⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  · intro v hv
    obtain ⟨k, hkrange, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hkl, hkh⟩ := Finset.mem_Icc.mp hkrange
    have hex : ∃ i, lo ≤ i ∧ i < hi ∧ i % 2 = lo % 2 ∧ (k = i ∨ k = i + 1) := by
      by_cases hk : k % 2 = lo % 2
      · exact ⟨k, hkl, by omega, hk, Or.inl rfl⟩
      · exact ⟨k - 1, by omega, by omega, by omega, Or.inr (by omega)⟩
    obtain ⟨i, hil, hih, hip, hki⟩ := hex
    have hem : edges i ∈ pathPattern edges lo hi :=
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hil, hih⟩, hip⟩, rfl⟩
    have hev : inc (edges i) (vertices k) := by
      apply (hedges i hil hih _).mpr
      exact hki.imp (congrArg vertices) (congrArg vertices)
    refine ⟨edges i, ⟨hem, hev⟩, ?_⟩
    intro f hf
    obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hf.1
    obtain ⟨hjrange, hjp⟩ := Finset.mem_filter.mp hj'
    obtain ⟨hjl, hjh⟩ := Finset.mem_Ico.mp hjrange
    have hkj : k = j ∨ k = j + 1 := by
      rcases (hedges j hjl hjh _).mp hf.2 with h | h
      · exact Or.inl (hinj ⟨hkl, hkh⟩ ⟨hjl, by omega⟩ h)
      · exact Or.inr (hinj ⟨hkl, hkh⟩ ⟨by omega, by omega⟩ h)
    have hji : j = i := by omega
    exact congrArg edges hji

omit [DecidableEq E] in
lemma singleton_matching (e : E) (a b : V)
    (he : ∀ v, inc e v ↔ v = a ∨ v = b) : MatchingOn inc {e} {a, b} := by
  classical
  refine ⟨?_, ?_⟩
  · intro f hf v hv
    have hf' : f = e := Finset.mem_singleton.mp hf
    subst f
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (he v).mp hv
  · intro v hv
    refine ⟨e, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · apply (he v).mpr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
    · intro f hf
      exact Finset.mem_singleton.mp hf.1

omit [DecidableEq V] [DecidableEq E] in
lemma empty_matching : MatchingOn inc ∅ ∅ := by simp [MatchingOn]

lemma repairedThrough_matching (vertices : ℕ → V) (edges : ℕ → E) (lo hi : ℕ)
    (hlong : lo + 3 ≤ hi) (hodd : (hi - lo) % 2 = 1)
    (hinj : Set.InjOn vertices (Set.Icc lo hi))
    (hedges : ∀ i, lo ≤ i → i < hi →
      ∀ v, inc (edges i) v ↔ v = vertices i ∨ v = vertices (i + 1))
    (repair : E)
    (hrepair : ∀ v, inc repair v ↔ v = vertices (lo + 1) ∨ v = vertices (hi - 1)) :
    MatchingOn inc (pathPattern edges (lo + 2) (hi - 2) ∪ {repair})
      ((Finset.Icc (lo + 1) (hi - 1)).image vertices) := by
  have hT : MatchingOn inc (pathPattern edges (lo + 2) (hi - 2))
      ((Finset.Icc (lo + 2) (hi - 2)).image vertices) := by
    by_cases h : lo + 2 < hi - 2
    · apply pathPattern_matching inc vertices edges (lo + 2) (hi - 2) h
      · omega
      · intro i hi' j hj' heq
        simp only [Set.mem_Icc] at hi' hj'
        exact hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
      · intro i hi' hi'' v
        exact hedges i (by omega) (by omega) v
    · have hl : hi - 2 < lo + 2 := by omega
      have he : Finset.Ico (lo + 2) (hi - 2) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      have he' : Finset.Icc (lo + 2) (hi - 2) = ∅ := Finset.Icc_eq_empty_of_lt hl
      simpa [pathPattern, he, he'] using (empty_matching (V := V) (E := E) inc)
  have hc := singleton_matching inc repair (vertices (lo + 1)) (vertices (hi - 1)) hrepair
  have hd : Disjoint ((Finset.Icc (lo + 2) (hi - 2)).image vertices)
      {vertices (lo + 1), vertices (hi - 1)} := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hv
    have hir := Finset.mem_Icc.mp hi'
    rcases Finset.mem_insert.mp hw with h | h
    · have heq := hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h
      omega
    · have heq := hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (Finset.mem_singleton.mp h)
      omega
  have hs : ((Finset.Icc (lo + 2) (hi - 2)).image vertices) ∪
      {vertices (lo + 1), vertices (hi - 1)} =
      (Finset.Icc (lo + 1) (hi - 1)).image vertices := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨i, hi', rfl⟩ | h | h)
      · exact ⟨i, ⟨by omega, by omega⟩, rfl⟩
      · exact ⟨lo + 1, ⟨le_rfl, by omega⟩, h.symm⟩
      · exact ⟨hi - 1, ⟨by omega, le_rfl⟩, h.symm⟩
    · rintro ⟨i, hi', rfl⟩
      by_cases hl : i = lo + 1
      · exact Or.inr (Or.inl (congrArg vertices hl))
      by_cases hh : i = hi - 1
      · exact Or.inr (Or.inr (congrArg vertices hh))
      exact Or.inl ⟨i, ⟨by omega, by omega⟩, rfl⟩
  simpa only [hs] using hT.union hc hd

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Span
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V L : Type*} [DecidableEq V]
variable {E : Type*} [DecidableEq E] (inc : E → V → Prop)
namespace OddPath

variable {inc}

variable (p : OddPath inc)

lemma through_matching : MatchingOn inc p.through p.span := by
  apply pathPattern_matching inc p.vertex p.edge 0 p.length p.positive
  · simpa using p.odd
  · exact p.simple
  · intro i _ hi v
    exact p.incidence i hi v

lemma interior_matching : MatchingOn inc p.interior p.inside := by
  by_cases h : p.length = 1
  · simpa [interior, inside, h, pathPattern] using
      (empty_matching (V := V) (E := E) inc)
  · have hpos := p.positive
    have hodd := p.odd
    apply pathPattern_matching inc p.vertex p.edge 1 (p.length - 1)
    · omega
    · omega
    · intro i hi j hj heq
      simp only [Set.mem_Icc] at hi hj
      exact p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
    · intro i hi hj v
      exact p.incidence i (by omega) v

lemma closed_matching (chord : E)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length) :
    MatchingOn inc (p.closed chord) p.span := by
  have hm := p.interior_matching.union (singleton_matching inc chord _ _ hc)
    p.inside_disjoint_ends
  change MatchingOn inc (p.closed chord) (p.inside ∪ p.ends) at hm
  rwa [p.inside_union_ends] at hm

lemma repaired_matching (repair : E)
    (hr : p.length ≠ 1 → ∀ v,
      inc repair v ↔ v = p.vertex 1 ∨ v = p.vertex (p.length - 1)) :
    MatchingOn inc (p.repaired repair) p.inside := by
  by_cases h : p.length = 1
  · simpa [repaired, inside, h] using (empty_matching (V := V) (E := E) inc)
  · have hpos := p.positive
    have hodd := p.odd
    simp only [repaired, ite_eq_right h]
    simpa only [Nat.zero_add, inside] using repairedThrough_matching inc p.vertex p.edge 0
      p.length (by omega) (by simpa using p.odd) p.simple
      (fun i _ hi v => p.incidence i hi v) repair (hr h)

lemma closed_val (chord : E)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length)
    (hinc : ∀ e, ∃ v, inc e v) :
    (p.closed chord).val = p.interior.val + {chord} := by
  apply union_val_add
  exact p.interior_matching.disjoint_edges (singleton_matching inc chord _ _ hc)
    hinc p.inside_disjoint_ends

omit [DecidableEq V] in
lemma repair_conservation (repair : E)
    (hr : p.length ≠ 1 → ∀ v,
      inc repair v ↔ v = p.vertex 1 ∨ v = p.vertex (p.length - 1))
    (_hinc : ∀ e, ∃ v, inc e v) :
    (p.repaired repair).val + p.boundary.val = p.through.val + p.repairAdded repair := by
  by_cases h : p.length = 1
  · have ht : p.through = {p.edge 0} := by simp [through, pathPattern, h, Finset.filter_singleton]
    simp only [repaired, boundary, repairAdded, ite_eq_left h, ht, Finset.empty_val,
      zero_add, add_zero]
  · have hpos := p.positive
    have hodd := p.odd
    have hlen : 3 ≤ p.length := by omega
    let trim := pathPattern p.edge 2 (p.length - 2)
    have ht : p.through = trim ∪ p.boundary := by
      simpa only [through, trim, Nat.zero_add, boundary, ite_eq_right h] using
        pathPattern_boundary p.edge 0 p.length hlen (by simpa using hodd)
    have hbdis : Disjoint trim p.boundary := by
      apply Finset.disjoint_left.mpr
      intro e he hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hi
      simp only [boundary, ite_eq_right h, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hh | hh
      · have hh' := p.edge_injective ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
      · have hh' := p.edge_injective ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
    have hrdis : Disjoint trim {repair} := by
      apply Finset.disjoint_left.mpr
      intro e he hr'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hi
      have heq := Finset.mem_singleton.mp hr'
      have hiinc : inc repair (p.vertex i) := by
        rw [← heq]
        exact (p.incidence i (by omega) _).mpr (Or.inl rfl)
      rcases (hr h _).mp hiinc with hh | hh
      · have hh' := p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
      · have hh' := p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
    rw [ht, union_val_add hbdis]
    simp only [repaired, ite_eq_right h, repairAdded]
    rw [union_val_add hrdis]
    simp only [Finset.singleton_val]
    ac_rfl

end OddPath

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Corner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V L : Type*} [DecidableEq V]
variable {E : Type*} [DecidableEq E] (inc : E → V → Prop)
namespace CellPaths

variable {inc} (c : CellPaths inc)

lemma matching_even_full (M : Fin 4 → Finset E)
    (h0 : MatchingOn inc (M 0) (c.side 0).span)
    (h2 : MatchingOn inc (M 2) (c.side 2).span)
    (h1 : MatchingOn inc (M 1) (c.side 1).inside)
    (h3 : MatchingOn inc (M 3) (c.side 3).inside) :
    MatchingOn inc (assemble M) c.vertices := by
  have h02 := h0.union h2 c.opposite_span_even
  have h13 := h1.union h3 (c.interiors_disjoint (by decide : (1 : Fin 4) ≠ 3))
  have hd : Disjoint ((c.side 0).span ∪ (c.side 2).span)
      ((c.side 1).inside ∪ (c.side 3).inside) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨(c.inside_disjoint_span 1 0 (by decide)).symm,
      (c.inside_disjoint_span 1 2 (by decide)).symm⟩,
      ⟨(c.inside_disjoint_span 3 0 (by decide)).symm,
      (c.inside_disjoint_span 3 2 (by decide)).symm⟩⟩
  simpa only [c.even_blocks_union, assemble] using h02.union h13 hd

lemma matching_odd_full (M : Fin 4 → Finset E)
    (h0 : MatchingOn inc (M 0) (c.side 0).inside)
    (h2 : MatchingOn inc (M 2) (c.side 2).inside)
    (h1 : MatchingOn inc (M 1) (c.side 1).span)
    (h3 : MatchingOn inc (M 3) (c.side 3).span) :
    MatchingOn inc (assemble M) c.vertices := by
  have h02 := h0.union h2 (c.interiors_disjoint (by decide : (0 : Fin 4) ≠ 2))
  have h13 := h1.union h3 c.opposite_span_odd
  have hd : Disjoint ((c.side 0).inside ∪ (c.side 2).inside)
      ((c.side 1).span ∪ (c.side 3).span) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨c.inside_disjoint_span 0 1 (by decide), c.inside_disjoint_span 2 1 (by decide)⟩,
      ⟨c.inside_disjoint_span 0 3 (by decide), c.inside_disjoint_span 2 3 (by decide)⟩⟩
  have hs : ((c.side 0).inside ∪ (c.side 2).inside) ∪
      ((c.side 1).span ∪ (c.side 3).span) = c.vertices :=
    (Finset.union_comm _ _).trans c.odd_blocks_union
  simpa only [hs, assemble] using h02.union h13 hd

omit [DecidableEq E] in
lemma blocks_disjoint (b : Bool) : Pairwise fun i j => Disjoint (c.blocks b i) (c.blocks b j) := by
  intro i j hij
  by_cases hi : sideBit i = b <;> by_cases hj : sideBit j = b
  · simp only [blocks, ite_eq_left hi, ite_eq_left hj]
    exact c.same_bit_spans i j hij (hi.trans hj.symm)
  · simp only [blocks, ite_eq_left hi, ite_eq_right hj]
    exact (c.inside_disjoint_span j i hij.symm).symm
  · simp only [blocks, ite_eq_right hi, ite_eq_left hj]
    exact c.inside_disjoint_span i j hij
  · simp only [blocks, ite_eq_right hi, ite_eq_right hj]
    exact c.interiors_disjoint hij

lemma assembled_matching (b : Bool) (M : Fin 4 → Finset E)
    (hM : ∀ i, MatchingOn inc (M i) (c.blocks b i)) :
    MatchingOn inc (assemble M) c.vertices := by
  cases b
  · apply c.matching_odd_full M <;> first
      | simpa [blocks, sideBit] using hM 0
      | simpa [blocks, sideBit] using hM 1
      | simpa [blocks, sideBit] using hM 2
      | simpa [blocks, sideBit] using hM 3
  · apply c.matching_even_full M <;> first
      | simpa [blocks, sideBit] using hM 0
      | simpa [blocks, sideBit] using hM 1
      | simpa [blocks, sideBit] using hM 2
      | simpa [blocks, sideBit] using hM 3

lemma assemble_val (b : Bool) (M : Fin 4 → Finset E)
    (hM : ∀ i, MatchingOn inc (M i) (c.blocks b i)) (hinc : ∀ e, ∃ v, inc e v) :
    (assemble M).val = ∑ i, (M i).val := by
  have hd (i j : Fin 4) (hij : i ≠ j) : Disjoint (M i) (M j) :=
    (hM i).disjoint_edges (hM j) hinc (c.blocks_disjoint b hij)
  have hu : Disjoint (M 0 ∪ M 2) (M 1 ∪ M 3) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨hd 0 1 (by decide), hd 2 1 (by decide)⟩,
      ⟨hd 0 3 (by decide), hd 2 3 (by decide)⟩⟩
  rw [assemble, union_val_add hu, union_val_add (hd 0 2 (by decide)),
    union_val_add (hd 1 3 (by decide))]
  rw [Fin.sum_univ_four]
  ac_rfl

omit [DecidableEq E] in
lemma pieces_matching (b : Bool) (full inner : Fin 4 → Finset E)
    (hf : ∀ i, sideBit i = b → MatchingOn inc (full i) (c.side i).span)
    (hi : ∀ i, sideBit i ≠ b → MatchingOn inc (inner i) (c.side i).inside) :
    ∀ i, MatchingOn inc (pieces b full inner i) (c.blocks b i) := by
  intro i
  by_cases h : sideBit i = b
  · simpa only [pieces, blocks, ite_eq_left h] using hf i h
  · simpa only [pieces, blocks, ite_eq_right h] using hi i h

lemma orientation_pieces_matching (b : Bool) :
    ∀ i, MatchingOn inc (c.orientationPieces b i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).through_matching)
    (fun i _ => (c.side i).interior_matching)

lemma switch_pieces_matching (b : Bool) :
    ∀ i, MatchingOn inc (c.switchPieces b i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).closed_matching _ (c.chord_incidence i))
    (fun i _ => (c.side i).interior_matching)

lemma repair_pieces_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    ∀ i, MatchingOn inc (c.repairPieces b repair i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).through_matching)
    (fun i hi => (c.side i).repaired_matching _ (hr i hi))

lemma guide_pieces_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    ∀ i, MatchingOn inc (c.guidePieces b repair i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).closed_matching _ (c.chord_incidence i))
    (fun i hi => (c.side i).repaired_matching _ (hr i hi))

lemma orientation_matching (b : Bool) : MatchingOn inc (c.orientation b) c.vertices :=
  c.assembled_matching b _ (c.orientation_pieces_matching b)

lemma switched_matching (b : Bool) : MatchingOn inc (c.switched b) c.vertices :=
  c.assembled_matching b _ (c.switch_pieces_matching b)

lemma repaired_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    MatchingOn inc (c.repaired b repair) c.vertices :=
  c.assembled_matching b _ (c.repair_pieces_matching b repair hr)

lemma guide_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    MatchingOn inc (c.guide b repair) c.vertices :=
  c.assembled_matching b _ (c.guide_pieces_matching b repair hr)

lemma closed_subset_guide (b : Bool) (repair : Fin 4 → E) (i : Fin 4) (hi : sideBit i = b) :
    (c.side i).closed (c.chord i) ⊆ c.guide b repair := by
  have h := component_subset_assemble (c.guidePieces b repair) i
  simpa only [guidePieces, pieces, ite_eq_left hi, guide] using h

lemma orientation_val (b : Bool) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation b).val = ∑ i, (c.orientationPieces b i).val :=
  c.assemble_val b _ (c.orientation_pieces_matching b) hinc

lemma switched_val (b : Bool) (hinc : ∀ e, ∃ v, inc e v) :
    (c.switched b).val = ∑ i, (c.switchPieces b i).val :=
  c.assemble_val b _ (c.switch_pieces_matching b) hinc

lemma repaired_val (r : Bool) (repair : Fin 4 → E) (hr : c.Repairs r repair)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.repaired r repair).val = ∑ i, (c.repairPieces r repair i).val :=
  c.assemble_val r _ (c.repair_pieces_matching r repair hr) hinc

lemma guide_val (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.guide b repair).val = ∑ i, (c.guidePieces b repair i).val :=
  c.assemble_val b _ (c.guide_pieces_matching b repair hr) hinc

lemma switch_piece_val (b : Bool) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.switchPieces b i).val = (c.side i).interior.val +
      (if sideBit i = b then {c.chord i} else 0) := by
  by_cases h : sideBit i = b
  · simp only [switchPieces, pieces, ite_eq_left h]
    exact (c.side i).closed_val _ (c.chord_incidence i) hinc
  · simp [switchPieces, pieces, h]

lemma repair_piece_conservation (r : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs r repair) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.repairPieces r repair i).val +
        (if sideBit i = r then 0 else (c.side i).boundary.val) =
      (c.side i).through.val +
        (if sideBit i = r then 0 else (c.side i).repairAdded (repair i)) := by
  by_cases h : sideBit i = r
  · simp [repairPieces, pieces, h]
  · simp only [repairPieces, pieces, ite_eq_right h]
    exact (c.side i).repair_conservation _ (hr i h) hinc

lemma switch_conservation (b r : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs r repair) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation true).val + (c.orientation false).val + c.additions b r repair =
      (c.switched b).val + (c.repaired r repair).val + c.drops r := by
  rw [c.orientation_val true hinc, c.orientation_val false hinc,
    c.switched_val b hinc, c.repaired_val r repair hr hinc]
  simp only [additions, drops, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [c.two_orientation_pieces i, c.switch_piece_val b i hinc]
  have h := c.repair_piece_conservation r repair hr i hinc
  calc
    _ = (c.side i).interior.val + (if sideBit i = b then {c.chord i} else 0) +
        ((c.side i).through.val +
          (if sideBit i = r then 0 else (c.side i).repairAdded (repair i))) := by ac_rfl
    _ = _ := by rw [← h]; ac_rfl

lemma guide_piece_conservation (b : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs b repair) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientationPieces b i).val + (c.guidePieces b repair i).val +
        (if sideBit i = b then 0 else (c.side i).boundary.val) =
      (c.side i).through.val + (c.side i).interior.val +
        (if sideBit i = b then {c.chord i} else 0) +
        (if sideBit i = b then 0 else (c.side i).repairAdded (repair i)) := by
  by_cases h : sideBit i = b
  · simp only [orientationPieces, guidePieces, pieces, ite_eq_left h, add_zero]
    rw [(c.side i).closed_val _ (c.chord_incidence i) hinc]
    ac_rfl
  · simp only [orientationPieces, guidePieces, pieces, ite_eq_right h, add_zero]
    have hh := (c.side i).repair_conservation _ (hr i h) hinc
    calc
      _ = (c.side i).interior.val +
          ((c.side i).repaired (repair i)).val + (c.side i).boundary.val := rfl
      _ = _ := by rw [add_assoc, hh]; ac_rfl

lemma guide_conservation (b : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs b repair) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation true).val + (c.orientation false).val + c.additions b b repair =
      (c.orientation b).val + (c.guide b repair).val + c.drops b := by
  rw [c.orientation_val true hinc, c.orientation_val false hinc,
    c.orientation_val b hinc, c.guide_val b repair hr hinc]
  simp only [additions, drops, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [c.two_orientation_pieces i]
  have h := c.guide_piece_conservation b repair hr i hinc
  simpa only [add_assoc] using h.symm

lemma through_subset_orientation (b : Bool) (i : Fin 4) (hi : sideBit i = b) :
    (c.side i).through ⊆ c.orientation b := by
  have h := component_subset_assemble (c.orientationPieces b) i
  simpa only [orientationPieces, pieces, ite_eq_left hi, orientation] using h

lemma context_one_properties (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (Y : Fin 4) (hY : sideBit Y = b) (hinc : ∀ e, ∃ v, inc e v) :
    MatchingOn inc (c.contextOne b Y) c.vertices ∧
    MatchingOn inc (c.guideOne b repair Y) c.vertices ∧
    (c.contextOne b Y).val + (c.guideOne b repair Y).val =
      (c.orientation b).val + (c.guide b repair).val := by
  exact pattern_interchange inc (c.orientation_matching b) (c.guide_matching b repair hr)
    (c.side Y).through_matching ((c.side Y).closed_matching _ (c.chord_incidence Y))
    (c.through_subset_orientation b Y hY) (c.closed_subset_guide b repair Y hY)
    (c.span_subset_vertices Y) hinc

lemma closed_subset_guide_one (b : Bool) (repair : Fin 4 → E) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hXY : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.side X).closed (c.chord X) ⊆ c.guideOne b repair Y := by
  have hdis := ((c.side X).closed_matching _ (c.chord_incidence X)).disjoint_edges
    ((c.side Y).closed_matching _ (c.chord_incidence Y)) hinc
    (c.same_bit_spans X Y hXY (hX.trans hY.symm))
  intro e he
  exact Finset.mem_union_left _ <| Finset.mem_sdiff.mpr
    ⟨c.closed_subset_guide b repair X hX he, fun hh => Finset.disjoint_left.mp hdis he hh⟩

end CellPaths

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_IndexedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

section

variable [Fintype V] [DecidableEq E]

lemma adjacent_mem_complement {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) (hi : i < c.size) :
    c.edgeAt (i+1) ∈ M ↔ c.edgeAt i ∉ M := by
  have hein := (c.edgeAt_incidence i (c.vertexAt (i+1))).mpr (Or.inr rfl)
  have hfin := (c.edgeAt_incidence (i+1) (c.vertexAt (i+1))).mpr (Or.inl rfl)
  constructor
  · intro hf he
    exact c.consecutive_ne i hi (hM.unique (Finset.mem_univ _) he hein hf hfin)
  · intro he
    have heN := (Finset.mem_union.mp (hU i)).resolve_left he
    rcases Finset.mem_union.mp (hU (i+1)) with hf | hf
    · exact hf
    · exact False.elim (c.consecutive_ne i hi (hN.unique (Finset.mem_univ _) heN hein hf hfin))

lemma cycle_edge_mem_complement {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) :
    c.edgeAt i ∈ N ↔ c.edgeAt i ∉ M := by
  have hm : i % c.size < c.size := Nat.mod_lt i (by have := c.four_le; omega)
  have heq := c.edgeAt_mod i
  have h := c.adjacent_mem_complement hM hN hU (i % c.size) hm
  have hn := c.adjacent_mem_complement hN hM
    (fun j => by rw [Finset.union_comm]; exact hU j) (i % c.size) hm
  constructor
  · intro hiN hiM
    have hjM : c.edgeAt (i % c.size + 1) ∉ M := fun hj => (h.mp hj) (heq.symm ▸ hiM)
    have hjN : c.edgeAt (i % c.size + 1) ∉ N := fun hj => (hn.mp hj) (heq.symm ▸ hiN)
    exact (Finset.mem_union.mp (hU _)).elim hjM hjN
  · intro hiM
    exact (Finset.mem_union.mp (hU i)).resolve_left hiM

lemma cycle_edge_mem_parity {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) :
    c.edgeAt i ∈ M ↔ if i % 2 = 0 then c.edgeAt 0 ∈ M else c.edgeAt 0 ∉ M := by
  have hb : ∀ j, j < c.size →
      (c.edgeAt j ∈ M ↔ if j % 2 = 0 then c.edgeAt 0 ∈ M else c.edgeAt 0 ∉ M) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        rw [c.adjacent_mem_complement hM hN hU j (by omega), ih (by omega)]
        split_ifs <;> first | omega | tauto
  have hh := hb (i % c.size) (Nat.mod_lt i (by have := c.four_le; omega))
  have hdiv : 2 ∣ c.size := Nat.dvd_of_mod_eq_zero c.even
  have hmod : (i % c.size) % 2 = i % 2 := Nat.mod_mod_of_dvd i hdiv
  simpa only [c.edgeAt_mod, hmod] using hh

end

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Sets
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E L : Type*}

namespace BagEdge

variable {bags : V → Finset L}

def color (e : BagEdge bags) : L := e.val.color

lemma color_mem (e : BagEdge bags) {v : V} (hv : e.Incident v) : e.color ∈ bags v :=
  e.property v hv

def ofEndpoints (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) : BagEdge bags :=
  ⟨⟨(s(v,w),l), by simpa using hvw⟩, by
    intro u hu
    change u ∈ s(v,w) at hu
    change l ∈ bags u
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hlv
    · exact hlw⟩

lemma ofEndpoints_incidence (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) (u : V) :
    (ofEndpoints v w hvw l hlv hlw).Incident u ↔ u = v ∨ u = w :=
  Sym2.mem_iff

lemma ofEndpoints_color (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) :
    (ofEndpoints v w hvw l hlv hlw).color = l := rfl

end BagEdge

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelCycle
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E L : Type*}
namespace IndexedCycle

variable {bags : V → Finset L}

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

lemma current_color_mem (i : ℤ) : (c.edgeAtZ i).color ∈ bags (c.vertexAtZ i) :=
  BagEdge.color_mem _ ((c.edgeAtZ_incidence i _).mpr (Or.inl rfl))

lemma previous_color_mem (i : ℤ) : (c.edgeAtZ (i-1)).color ∈ bags (c.vertexAtZ i) := by
  apply BagEdge.color_mem
  apply (c.edgeAtZ_incidence (i-1) _).mpr
  right
  congr 1
  omega

def labelCycle : MatchingFPRAS.Cells.CycleData G c.size where
  labels i := (c.edgeAtZ i).color
  periodic i := by rw [c.edgeAtZ_periodic]
  adjacent i := hbags (c.vertexAtZ i) _ (c.previous_color_mem i) _ (c.current_color_mem i)

variable [DecidableEq L]

lemma labelCycle_sets_subset (i : ℤ) : (c.labelCycle hbags).sets i ⊆ bags (c.vertexAtZ i) := by
  intro l hl
  simp only [MatchingFPRAS.Cells.CycleData.sets, labelCycle,
    Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact c.previous_color_mem i
  · exact c.current_color_mem i

lemma labelSets_periodic (i : ℤ) :
    (c.labelCycle hbags).sets (i+c.size) = (c.labelCycle hbags).sets i := by
  have h : i + (c.size : ℤ) - 1 = (i-1) + c.size := by ring
  simp only [MatchingFPRAS.Cells.CycleData.sets, labelCycle, h, c.edgeAtZ_periodic]

lemma edge_color_fixed (i : ℕ) :
    (c.edgeAt i).color ∈ (c.labelCycle hbags).sets i ∧
    (c.edgeAt i).color ∈ (c.labelCycle hbags).sets (i+1) := by
  have h : (c.edgeAtZ (i : ℤ)).color ∈ (c.labelCycle hbags).sets (i : ℤ) ∧
      (c.edgeAtZ (i : ℤ)).color ∈ (c.labelCycle hbags).sets ((i : ℤ)+1) := by
    simp [MatchingFPRAS.Cells.CycleData.sets, labelCycle]
  simpa only [c.edgeAtZ_nat] using h

noncomputable def chord (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) : BagEdge bags := by
  classical
  exact if hshort : y = x+1 then c.edgeAt x
    else if hwrap : x = 0 ∧ y+1 = c.size then c.edgeAt y
    else
      let l := ha.choose
      BagEdge.ofEndpoints (c.vertexAt x) (c.vertexAt y)
        (fun h => by
          have := (c.vertexAt_eq_iff (a := 0) (by have := c.four_le; omega)
            ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).mp h
          omega) l
        (by simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags x ha.choose_spec.1)
        (by simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags y ha.choose_spec.2)

lemma chord_incidence (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (v : V) :
    (c.chord hbags x y hxy hy ha).Incident v ↔ v = c.vertexAt x ∨ v = c.vertexAt y := by
  classical
  dsimp only [chord]
  split_ifs with hshort hwrap
  · simpa [hshort] using c.edgeAt_incidence x v
  · rw [c.edgeAt_incidence]
    have he : c.vertexAt (y+1) = c.vertexAt x := by
      rw [hwrap.2, hwrap.1]
      simpa using c.vertexAt_periodic 0
    rw [he]
    tauto
  · exact BagEdge.ofEndpoints_incidence _ _ _ _ _ _ _

lemma chord_color_fixed (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) :
    (c.chord hbags x y hxy hy ha).color ∈ (c.labelCycle hbags).sets x ∧
    (c.chord hbags x y hxy hy ha).color ∈ (c.labelCycle hbags).sets y := by
  classical
  dsimp only [chord]
  split_ifs with hs hw
  · simpa only [hs, Nat.cast_add, Nat.cast_one] using c.edge_color_fixed hbags x
  · have hb := c.edge_color_fixed hbags y
    refine ⟨?_, hb.1⟩
    have he : (y : ℤ)+1 = (0 : ℤ)+c.size := by omega
    rw [he, c.labelSets_periodic hbags] at hb
    simpa only [hw.1, Nat.cast_zero] using hb.2
  · exact ha.choose_spec

def cellCorners {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : c.Corners where
  a₀ := x
  a₁ := p
  a₂ := q
  a₃ := y
  lt₀ := hc.first_pos
  lt₁ := hc.middle_pos
  lt₂ := hc.third_pos
  lt₃ := hy
  odd₀ := hc.odd_first
  odd₁ := hc.odd_middle
  odd₂ := hc.odd_third
  odd₃ := by
    have he : c.size + x - y = c.size - (y-x) := by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega
    rw [he]
    exact hc.odd_exterior

noncomputable def cellChords {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : Fin 4 → BagEdge bags :=
  ![c.chord hbags x p hc.first_pos (by have := hc.middle_pos; have := hc.third_pos; omega) hc.first,
    c.chord hbags p q hc.middle_pos (by have := hc.third_pos; omega) hc.middle,
    c.chord hbags q y hc.third_pos hy hc.third,
    c.chord hbags x y (by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega)
      hy (by obtain ⟨l, hly, hlx⟩ := hc.exterior; exact ⟨l,hlx,hly⟩)]

lemma cellChords_incidence {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (v : V) :
    (c.cellChords hbags hc hy i).Incident v ↔
      v = ((c.cellCorners hbags hc hy).side i).vertex 0 ∨
      v = ((c.cellCorners hbags hc hy).side i).vertex
        ((c.cellCorners hbags hc hy).side i).length := by
  simp only [Corners.side_first, Corners.side_last]
  have hper : c.vertexAt (c.size+x) = c.vertexAt x := by
    simpa only [Nat.add_comm] using c.vertexAt_periodic x
  fin_cases i <;> simp [cellChords, chord_incidence, cellCorners, Corners.start,
    Corners.stop, hper, or_comm]

noncomputable def pathsOfCell [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : CellPaths (BagEdge.Incident (bags := bags)) :=
  (c.cellCorners hbags hc hy).cellPaths (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy)

def sideGood (k : c.Corners) (i : Fin 4) : Prop :=
  k.length i = 1 ∨ ∃ l, l ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    l ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1)

lemma cell_sideGood {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    c.sideGood hbags (c.cellCorners hbags hc hy) i ↔
      ![(c.labelCycle hbags).Good x p, (c.labelCycle hbags).Good p q,
        (c.labelCycle hbags).Good q y, (c.labelCycle hbags).ExteriorGood x y] i := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  have cast_sub (a : ℕ) (ha : 1 ≤ a) : ((a-1 : ℕ) : ℤ) = (a : ℤ)-1 := by omega
  have he : ((c.size : ℤ)+(x : ℤ))-1 = ((x : ℤ)-1) + c.size := by ring
  fin_cases i <;> simp only [sideGood, cellCorners, Corners.length, Corners.start,
    Corners.stop]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub p (by omega), Nat.cast_add, Nat.cast_one, show p-x=1 ↔ p=x+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub q (by omega), Nat.cast_add, Nat.cast_one, show q-p=1 ↔ q=p+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub y (by omega), Nat.cast_add, Nat.cast_one, show y-q=1 ↔ y=q+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.ExteriorGood, Nat.cast_add, he,
      c.labelSets_periodic hbags, show c.size+x-y=1 ↔ y+1=x+c.size by omega]

noncomputable def leafRepair (k : c.Corners) (i : Fin 4) : BagEdge bags := by
  classical
  exact if hg : c.sideGood hbags k i ∧ k.length i ≠ 1 then
    let hl := hg.1.resolve_left hg.2
    BagEdge.ofEndpoints ((k.side i).vertex 1) ((k.side i).vertex ((k.side i).length-1))
      (by
        have hp := (k.side i).positive
        have ho := (k.side i).odd
        have hn : (k.side i).length ≠ 1 := hg.2
        intro he
        have hh := (k.side i).simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
        omega)
      hl.choose
      (by
        have hm := c.labelCycle_sets_subset hbags (k.start i+1) hl.choose_spec.1
        have hv : c.vertexAtZ ((k.start i : ℤ)+1) = (k.side i).vertex 1 := by
          simpa only [Corners.side_vertex, Nat.cast_add, Nat.cast_one] using c.vertexAtZ_nat (k.start i+1)
        exact (congrArg (fun v => hl.choose ∈ bags v) hv).mp hm)
      (by
        have hm := c.labelCycle_sets_subset hbags ((k.stop i : ℤ)-1) hl.choose_spec.2
        have hb := k.bounds i
        have he : ((k.stop i : ℤ)-1) = ((k.start i + ((k.side i).length-1) : ℕ) : ℤ) := by
          rw [Corners.side_length]
          dsimp [Corners.length]
          omega
        have hv : c.vertexAtZ ((k.stop i : ℤ)-1) = (k.side i).vertex ((k.side i).length-1) := by
          rw [he, c.vertexAtZ_nat]
          rfl
        exact (congrArg (fun v => hl.choose ∈ bags v) hv).mp hm)
  else c.edgeAt (k.start i)

lemma leafRepair_incidence (k : c.Corners) (i : Fin 4)
    (hg : c.sideGood hbags k i) (hl : k.length i ≠ 1) (v : V) :
    (c.leafRepair hbags k i).Incident v ↔
      v = (k.side i).vertex 1 ∨ v = (k.side i).vertex ((k.side i).length-1) := by
  simp only [leafRepair, dite_eq_left (And.intro hg hl), BagEdge.ofEndpoints_incidence]

lemma leafRepair_color_fixed (k : c.Corners) (i : Fin 4)
    (hg : c.sideGood hbags k i) (hl : k.length i ≠ 1) :
    (c.leafRepair hbags k i).color ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    (c.leafRepair hbags k i).color ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1) := by
  simp only [leafRepair, dite_eq_left (And.intro hg hl), BagEdge.ofEndpoints_color]
  exact (hg.resolve_left hl).choose_spec

lemma cell_has_good_pair {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) :
    ∃ b : Bool, ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i := by
  rcases hc.some_good with ⟨hf,ht⟩ | ⟨hm,he⟩
  · refine ⟨false, ?_⟩
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]
  · refine ⟨true, ?_⟩
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]

lemma cell_actual_repairs [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b : Bool)
    (hg : ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i) :
    (c.pathsOfCell hbags hc hy).Repairs b
      (c.leafRepair hbags (c.cellCorners hbags hc hy)) := by
  intro i hi hl v
  exact c.leafRepair_incidence hbags _ i (hg i hi) hl v

lemma cell_long_opposite_good {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b : Bool)
    (hl : ∀ i : Fin 4, CellPaths.sideBit i = b →
      (c.cellCorners hbags hc hy).length i ≠ 1) :
    ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  cases b
  · have h₁ := hl 1 (by decide)
    have h₃ := hl 3 (by decide)
    simp only [Corners.length, Corners.start, Corners.stop, cellCorners] at h₁ h₃
    have hg := hc.middle_exterior_long (by dsimp at h₁; omega) (by dsimp at h₃; omega)
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]
  · have h₀ := hl 0 (by decide)
    have h₂ := hl 2 (by decide)
    simp only [Corners.length, Corners.start, Corners.stop, cellCorners] at h₀ h₂
    have hg := hc.outer_long (by dsimp at h₀; omega) (by dsimp at h₂; omega)
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]

lemma cellChords_fixed {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    (c.cellChords hbags hc hy i).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).start i) ∧
    (c.cellChords hbags hc hy i).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).stop i) := by
  fin_cases i
  · exact c.chord_color_fixed hbags x p hc.first_pos
      (by have := hc.middle_pos; have := hc.third_pos; omega) hc.first
  · exact c.chord_color_fixed hbags p q hc.middle_pos
      (by have := hc.third_pos; omega) hc.middle
  · exact c.chord_color_fixed hbags q y hc.third_pos hy hc.third
  · have hb := c.chord_color_fixed hbags x y
      (by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega) hy
      (by obtain ⟨l,hly,hlx⟩ := hc.exterior; exact ⟨l,hlx,hly⟩)
    change _ ∈ (c.labelCycle hbags).sets y ∧ _ ∈ (c.labelCycle hbags).sets (c.size+x)
    rw [add_comm, c.labelSets_periodic hbags]
    exact ⟨hb.2,hb.1⟩

lemma cellChords_previous_fixed {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    (c.cellChords hbags hc hy (i+1)).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).stop i) := by
  have h := (c.cellChords_fixed hbags hc hy (i+1)).1
  fin_cases i
  · exact h
  · exact h
  · exact h
  · change _ ∈ (c.labelCycle hbags).sets (c.size+x)
    rw [add_comm, c.labelSets_periodic hbags]
    exact h

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

include hheight hstep in
lemma fixed_height_ratio (i : ℤ) {a b : L}
    (ha : a ∈ (c.labelCycle hbags).sets i) (hb : b ∈ (c.labelCycle hbags).sets i) :
    height a ≤ 2 * height b := by
  rcases (c.labelCycle hbags).sets_clique i a ha b hb with rfl | hab
  · linarith [hheight a]
  · exact hstep a b hab

include hheight hstep in
lemma cellChords_height_ratio {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i j : Fin 4) :
    height (c.cellChords hbags hc hy i).color ≤ 4 * height (c.cellChords hbags hc hy j).color := by
  have hn (i : Fin 4) :
      height (c.cellChords hbags hc hy i).color ≤ 2 * height (c.cellChords hbags hc hy (i+1)).color ∧
      height (c.cellChords hbags hc hy (i+1)).color ≤ 2 * height (c.cellChords hbags hc hy i).color := by
    exact ⟨c.fixed_height_ratio hbags height hheight hstep _
      (c.cellChords_fixed hbags hc hy i).2 (c.cellChords_previous_fixed hbags hc hy i),
      c.fixed_height_ratio hbags height hheight hstep _
      (c.cellChords_previous_fixed hbags hc hy i) (c.cellChords_fixed hbags hc hy i).2⟩
  have h₀ := hn 0
  have h₁ := hn 1
  have h₂ := hn 2
  have h₃ := hn 3
  change height (c.cellChords hbags hc hy 0).color ≤ 2 * height (c.cellChords hbags hc hy 1).color ∧
    height (c.cellChords hbags hc hy 1).color ≤ 2 * height (c.cellChords hbags hc hy 0).color at h₀
  change height (c.cellChords hbags hc hy 1).color ≤ 2 * height (c.cellChords hbags hc hy 2).color ∧
    height (c.cellChords hbags hc hy 2).color ≤ 2 * height (c.cellChords hbags hc hy 1).color at h₁
  change height (c.cellChords hbags hc hy 2).color ≤ 2 * height (c.cellChords hbags hc hy 3).color ∧
    height (c.cellChords hbags hc hy 3).color ≤ 2 * height (c.cellChords hbags hc hy 2).color at h₂
  change height (c.cellChords hbags hc hy 3).color ≤ 2 * height (c.cellChords hbags hc hy 0).color ∧
    height (c.cellChords hbags hc hy 0).color ≤ 2 * height (c.cellChords hbags hc hy 3).color at h₃
  have hp₀ := hheight (c.cellChords hbags hc hy 0).color
  have hp₁ := hheight (c.cellChords hbags hc hy 1).color
  have hp₂ := hheight (c.cellChords hbags hc hy 2).color
  have hp₃ := hheight (c.cellChords hbags hc hy 3).color
  rcases h₀ with ⟨h₀,h₀'⟩
  rcases h₁ with ⟨h₁,h₁'⟩
  rcases h₂ with ⟨h₂,h₂'⟩
  rcases h₃ with ⟨h₃,h₃'⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;> linarith

def LocalEdge {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (e : BagEdge bags) : Prop :=
  ∃ i : Fin 4, e = c.cellChords hbags hc hy i ∨
    e = ((c.cellCorners hbags hc hy).side i).edge 0 ∨
    e = ((c.cellCorners hbags hc hy).side i).edge
        (((c.cellCorners hbags hc hy).side i).length-1) ∨
    (c.sideGood hbags (c.cellCorners hbags hc hy) i ∧
      (c.cellCorners hbags hc hy).length i ≠ 1 ∧
      e = c.leafRepair hbags (c.cellCorners hbags hc hy) i)

lemma side_boundaries_fixed (k : c.Corners) (i : Fin 4) :
    ((k.side i).edge 0).color ∈ (c.labelCycle hbags).sets (k.start i) ∧
    ((k.side i).edge 0).color ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    ((k.side i).edge ((k.side i).length-1)).color ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1) ∧
    ((k.side i).edge ((k.side i).length-1)).color ∈ (c.labelCycle hbags).sets (k.stop i) := by
  have hb := k.bounds i
  have he : k.start i + (k.length i-1) = k.stop i-1 := by dsimp [Corners.length]; omega
  change (c.edgeAt (k.start i+0)).color ∈ _ ∧ (c.edgeAt (k.start i+0)).color ∈ _ ∧
    (c.edgeAt (k.start i + (k.length i-1))).color ∈ _ ∧
    (c.edgeAt (k.start i + (k.length i-1))).color ∈ _
  rw [Nat.add_zero, he]
  have hs := c.edge_color_fixed hbags (k.start i)
  have ht := c.edge_color_fixed hbags (k.stop i-1)
  have hcast : ((k.stop i-1 : ℕ) : ℤ) = (k.stop i : ℤ)-1 := by omega
  have hcast' : ((k.stop i-1 : ℕ) : ℤ)+1 = (k.stop i : ℤ) := by omega
  exact ⟨hs.1, hs.2, by simpa only [hcast] using ht.1, by simpa only [hcast'] using ht.2⟩

include hheight hstep in
lemma localEdge_height_ratio {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) {e : BagEdge bags} (he : c.LocalEdge hbags hc hy e) :
    ∃ i : Fin 4,
      height e.color ≤ 4 * height (c.cellChords hbags hc hy i).color ∧
      height (c.cellChords hbags hc hy i).color ≤ 4 * height e.color := by
  obtain ⟨i,he⟩ := he
  refine ⟨i,?_⟩
  have hh := hheight e.color
  have hch := hheight (c.cellChords hbags hc hy i).color
  have hbc := c.side_boundaries_fixed hbags (c.cellCorners hbags hc hy) i
  have hc' := c.cellChords_fixed hbags hc hy i
  rcases he with rfl | rfl | rfl | ⟨hg,hl,rfl⟩
  · constructor <;> linarith
  · have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hbc.1 hc'.1
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hc'.1 hbc.1
    constructor <;> linarith
  · have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hbc.2.2.2 hc'.2
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hc'.2 hbc.2.2.2
    constructor <;> linarith
  · have hrc := c.leafRepair_color_fixed hbags _ i hg hl
    have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hrc.1 hbc.2.1
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hbc.2.1 hrc.1
    have h₃ := c.fixed_height_ratio hbags height hheight hstep _ hbc.1 hc'.1
    have h₄ := c.fixed_height_ratio hbags height hheight hstep _ hc'.1 hbc.1
    constructor <;> linarith

include hheight hstep in

theorem cell_comparability {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    {e f : BagEdge bags} (he : c.LocalEdge hbags hc hy e) (hf : c.LocalEdge hbags hc hy f) :
    w e ≤ (1000 * D) * w f := by
  obtain ⟨i,hei,hie⟩ := c.localEdge_height_ratio hbags height hheight hstep hc hy he
  obtain ⟨j,hfj,hjf⟩ := c.localEdge_height_ratio hbags height hheight hstep hc hy hf
  have hij := c.cellChords_height_ratio hbags height hheight hstep hc hy i j
  have hh : height e.color ≤ 64 * height f.color := by linarith
  have hDpos : 0 < D := by linarith
  have hfpos : 0 < w f := lt_of_lt_of_le (div_pos (hheight f.color) hDpos) (hw f).1
  have hlo : height f.color ≤ w f * D := (div_le_iff₀ hDpos).mp (hw f).1
  have h192 : w e ≤ 192 * D * w f := by nlinarith [(hw e).2]
  nlinarith [mul_pos hDpos hfpos]

include hheight hstep in
lemma cell_clamp_comparability {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 ≤ lo)
    {e f : BagEdge bags} (he : c.LocalEdge hbags hc hy e) (hf : c.LocalEdge hbags hc hy f) :
    max lo (min hi (w e)) ≤ (1000 * D) * max lo (min hi (w f)) :=
  common_clamp_ratio hlo (by linarith) (c.cell_comparability hbags height hheight hstep hc hy D hD w hw he hf)

lemma drops_local [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (r : Bool) {e : BagEdge bags}
    (he : e ∈ (c.pathsOfCell hbags hc hy).drops r) : c.LocalEdge hbags hc hy e := by
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
  by_cases h : CellPaths.sideBit i = r
  · simp only [ite_eq_left h, Multiset.notMem_zero] at hi
  · simp only [ite_eq_right h, Finset.mem_val] at hi
    refine ⟨i, Or.inr ?_⟩
    change e ∈ ((c.cellCorners hbags hc hy).side i).boundary at hi
    by_cases hl : ((c.cellCorners hbags hc hy).side i).length = 1
    · simp only [OddPath.boundary, ite_eq_left hl, Finset.mem_singleton] at hi
      exact Or.inl hi
    · simp only [OddPath.boundary, ite_eq_right hl, Finset.mem_insert, Finset.mem_singleton] at hi
      exact hi.imp_right Or.inl

lemma additions_local [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b r : Bool)
    (hg : ∀ i, CellPaths.sideBit i ≠ r → c.sideGood hbags (c.cellCorners hbags hc hy) i)
    {e : BagEdge bags} (he : e ∈ (c.pathsOfCell hbags hc hy).additions b r
      (c.leafRepair hbags (c.cellCorners hbags hc hy))) : c.LocalEdge hbags hc hy e := by
  rcases Multiset.mem_add.mp he with he | he
  · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
    by_cases h : CellPaths.sideBit i = b
    · simp only [ite_eq_left h, Multiset.mem_singleton] at hi
      exact ⟨i, Or.inl hi⟩
    · simp only [ite_eq_right h, Multiset.notMem_zero] at hi
  · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
    by_cases h : CellPaths.sideBit i = r
    · simp only [ite_eq_left h, Multiset.notMem_zero] at hi
    · simp only [ite_eq_right h] at hi
      change e ∈ ((c.cellCorners hbags hc hy).side i).repairAdded (c.leafRepair hbags (c.cellCorners hbags hc hy) i) at hi
      by_cases hl : ((c.cellCorners hbags hc hy).side i).length = 1
      · simp only [OddPath.repairAdded, ite_eq_left hl, Multiset.notMem_zero] at hi
      · simp only [OddPath.repairAdded, ite_eq_right hl, Multiset.mem_singleton] at hi
        exact ⟨i, Or.inr (Or.inr (Or.inr ⟨hg i h, hl, hi⟩))⟩

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_PM
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideOverlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq E]

variable (inc : E → V → Prop)

abbrev PM := {M : Finset E // MatchingOn inc M Finset.univ}

@[ext] structure RawDemand where
  first : PM inc
  second : PM inc
  anchor : E
  corners : Fin 4 → V
  flags : Fin 64

structure DemandEncoding (d : RawDemand inc) where
  first : PM inc
  second : PM inc
  added : Multiset E
  dropped : Multiset E
  added_card : added.card ≤ 4
  dropped_card : dropped.card ≤ 4
  conservation : d.first.val.val + d.second.val.val + added =
    first.val.val + second.val.val + dropped
  outside : ∀ e ∈ d.first.val ∪ d.second.val,
    ¬ (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e →
    (e ∈ d.first.val ↔ e ∈ first.val)

namespace DemandEncoding

variable {inc}

def code {d : RawDemand inc} (a : DemandEncoding inc d) :=
  (a.first, a.second, d.anchor, d.corners, d.flags,
   decide (d.anchor ∈ d.first.val), a.added, a.dropped)

noncomputable def tag {d : RawDemand inc} (a : DemandEncoding inc d) : DemandTag (V := V) (E := E) :=
  (d.anchor, d.corners, d.flags, decide (d.anchor ∈ d.first.val),
   padOccurrences a.added, padOccurrences a.dropped)

noncomputable def finiteCode {d : RawDemand inc} (a : DemandEncoding inc d) :=
  (a.first, a.second, a.tag)

end DemandEncoding

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

structure EmbeddedCell (d : RawDemand inc) where
  cell : CellPaths inc
  orientation : Bool
  first_pattern : cell.orientation orientation ⊆ d.first.val
  second_pattern : cell.orientation (!orientation) ⊆ d.second.val
  reach : ∀ e ∈ cell.orientation true ∪ cell.orientation false,
    (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e

namespace EmbeddedCell

variable {inc} {d : RawDemand inc} (c : EmbeddedCell inc d)

variable (hinc : ∀ e, ∃ v, inc e v)

def outsideFirst : Finset E := d.first.val \ c.cell.orientation c.orientation

def outsideSecond : Finset E := d.second.val \ c.cell.orientation (!c.orientation)

lemma outsideFirst_matching : MatchingOn inc c.outsideFirst (Finset.univ \ c.cell.vertices) :=
  d.first.property.sdiff (c.cell.orientation_matching c.orientation) c.first_pattern

lemma outsideSecond_matching : MatchingOn inc c.outsideSecond (Finset.univ \ c.cell.vertices) :=
  d.second.property.sdiff (c.cell.orientation_matching (!c.orientation)) c.second_pattern

lemma context_vertices_disjoint : Disjoint (Finset.univ \ c.cell.vertices) c.cell.vertices :=
  Finset.sdiff_disjoint

def attachFirst (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) : PM inc :=
  ⟨c.outsideFirst ∪ p, by
    have h := c.outsideFirst_matching.union hp c.context_vertices_disjoint
    simpa only [Finset.sdiff_union_of_subset (Finset.subset_univ _)] using h⟩

def attachSecond (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) : PM inc :=
  ⟨c.outsideSecond ∪ p, by
    have h := c.outsideSecond_matching.union hp c.context_vertices_disjoint
    simpa only [Finset.sdiff_union_of_subset (Finset.subset_univ _)] using h⟩

include hinc in
lemma attachFirst_val (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) :
    (c.attachFirst p hp).val.val = c.outsideFirst.val + p.val :=
  union_val_add (c.outsideFirst_matching.disjoint_edges hp hinc c.context_vertices_disjoint)

include hinc in
lemma attachSecond_val (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) :
    (c.attachSecond p hp).val.val = c.outsideSecond.val + p.val :=
  union_val_add (c.outsideSecond_matching.disjoint_edges hp hinc c.context_vertices_disjoint)

include hinc in
lemma source_first_val : d.first.val.val =
    c.outsideFirst.val + (c.cell.orientation c.orientation).val := by
  have h := c.attachFirst_val hinc _ (c.cell.orientation_matching c.orientation)
  have he : (c.attachFirst _ (c.cell.orientation_matching c.orientation)).val = d.first.val := by
    exact Finset.sdiff_union_of_subset c.first_pattern
  rwa [he] at h

include hinc in
lemma source_second_val : d.second.val.val =
    c.outsideSecond.val + (c.cell.orientation (!c.orientation)).val := by
  have h := c.attachSecond_val hinc _ (c.cell.orientation_matching (!c.orientation))
  have he : (c.attachSecond _ (c.cell.orientation_matching (!c.orientation))).val = d.second.val := by
    exact Finset.sdiff_union_of_subset c.second_pattern
  rwa [he] at h

include hinc in
lemma attach_outside (p : Finset E) (hp : MatchingOn inc p c.cell.vertices)
    (e : E) (he : e ∈ d.first.val ∪ d.second.val)
    (hn : ¬ (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e) :
    e ∈ d.first.val ↔ e ∈ (c.attachFirst p hp).val := by
  have hnot (b : Bool) : e ∉ c.cell.orientation b := by
    intro hm
    apply hn
    apply c.reach e
    cases b
    · exact Finset.mem_union_right _ hm
    · exact Finset.mem_union_left _ hm
  have hnp : e ∉ p := by
    intro hm
    obtain ⟨v,hv⟩ := hinc e
    have hvc := hp.1 e hm v hv
    rcases Finset.mem_union.mp he with he | he
    · exact hnot _ (d.first.property.edge_mem_of_incident
        (c.cell.orientation_matching c.orientation) c.first_pattern he hvc hv)
    · exact hnot _ (d.second.property.edge_mem_of_incident
        (c.cell.orientation_matching (!c.orientation)) c.second_pattern he hvc hv)
  change e ∈ d.first.val ↔ e ∈ c.outsideFirst ∪ p
  simp only [outsideFirst, Finset.mem_union, Finset.mem_sdiff, hnot, hnp, not_false_eq_true,
    and_true, or_false]

def encode (p q : Finset E) (hp : MatchingOn inc p c.cell.vertices)
    (hq : MatchingOn inc q c.cell.vertices) (add drop : Multiset E)
    (ha : add.card ≤ 4) (hd : drop.card ≤ 4)
    (hcons : (c.cell.orientation true).val + (c.cell.orientation false).val + add =
      p.val + q.val + drop) : DemandEncoding inc d where
  first := c.attachFirst p hp
  second := c.attachSecond q hq
  added := add
  dropped := drop
  added_card := ha
  dropped_card := hd
  conservation := by
    rw [c.source_first_val hinc, c.source_second_val hinc,
      c.attachFirst_val hinc p hp, c.attachSecond_val hinc q hq]
    have ho : (c.cell.orientation c.orientation).val +
        (c.cell.orientation (!c.orientation)).val =
        (c.cell.orientation true).val + (c.cell.orientation false).val := by
      cases c.orientation <;> simp only [Bool.not_false, Bool.not_true]
      ac_rfl
    calc
      _ = c.outsideFirst.val + c.outsideSecond.val +
          ((c.cell.orientation c.orientation).val + (c.cell.orientation (!c.orientation)).val + add) := by ac_rfl
      _ = c.outsideFirst.val + c.outsideSecond.val + (p.val + q.val + drop) := by rw [ho,hcons]
      _ = _ := by ac_rfl
  outside := c.attach_outside hinc p hp

def switchEncoding (b r : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs r repair) :
    DemandEncoding inc d :=
  c.encode hinc (c.cell.switched b) (c.cell.repaired r repair)
    (c.cell.switched_matching b) (c.cell.repaired_matching r repair hr)
    (c.cell.additions b r repair) (c.cell.drops r)
    (by rw [← (c.cell.modification_cards b r repair).1]; exact (c.cell.modification_cards b r repair).2)
    (c.cell.modification_cards b r repair).2
    (c.cell.switch_conservation b r repair hr hinc)

def errorZeroEncoding (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair) :
    DemandEncoding inc d :=
  c.encode hinc (c.cell.orientation b) (c.cell.guide b repair)
    (c.cell.orientation_matching b) (c.cell.guide_matching b repair hr)
    (c.cell.additions b b repair) (c.cell.drops b)
    (by rw [← (c.cell.modification_cards b b repair).1]; exact (c.cell.modification_cards b b repair).2)
    (c.cell.modification_cards b b repair).2
    (c.cell.guide_conservation b repair hr hinc)

def errorOneEncoding (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (Y : Fin 4) (hY : CellPaths.sideBit Y = b) : DemandEncoding inc d :=
  c.encode hinc (c.cell.contextOne b Y) (c.cell.guideOne b repair Y)
    (c.cell.context_one_properties b repair hr Y hY hinc).1
    (c.cell.context_one_properties b repair hr Y hY hinc).2.1
    (c.cell.additions b b repair) (c.cell.drops b)
    (by rw [← (c.cell.modification_cards b b repair).1]; exact (c.cell.modification_cards b b repair).2)
    (c.cell.modification_cards b b repair).2 (by
      rw [(c.cell.context_one_properties b repair hr Y hY hinc).2.2]
      exact c.cell.guide_conservation b repair hr hinc)

lemma zero_guide_contains (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (X : Fin 4) (hX : CellPaths.sideBit X = b) :
    (c.cell.side X).closed (c.cell.chord X) ⊆
      (c.errorZeroEncoding hinc b repair hr).second.val := by
  intro e he
  exact Finset.mem_union_right _ (c.cell.closed_subset_guide b repair X hX he)

lemma one_guide_contains (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (X Y : Fin 4) (hX : CellPaths.sideBit X = b) (hY : CellPaths.sideBit Y = b)
    (hne : X ≠ Y) :
    (c.cell.side X).closed (c.cell.chord X) ⊆
      (c.errorOneEncoding hinc b repair hr Y hY).second.val := by
  intro e he
  exact Finset.mem_union_right _ (c.cell.closed_subset_guide_one b repair X Y hX hY hne hinc he)

end EmbeddedCell

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle.Corners

variable {c : IndexedCycle inc} (k : c.Corners)

def rawDemand (M N : PM inc) (flags : Fin 64) : RawDemand inc :=
  ⟨M, N, c.edgeAt 0, (fun i => c.vertexAt (k.start i)), flags⟩

noncomputable def embeddedPair (M N : PM inc)
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (flags : Fin 64) : EmbeddedCell inc (k.rawDemand M N flags) := by
  classical
  let a : ℕ := if c.edgeAt 0 ∈ M.val then 0 else 1
  have ha : a < 2 := by dsimp [a]; split <;> omega
  have hM : ∀ t, t % 2 = a → c.edgeAt t ∈ M.val := by
    intro t ht
    apply (c.cycle_edge_mem_parity M.property N.property hU t).mpr
    dsimp [a] at ht
    split_ifs at ht ⊢ <;> omega
  have hN : ∀ t, t % 2 = 1-a → c.edgeAt t ∈ N.val := by
    intro t ht
    apply (c.cycle_edge_mem_complement M.property N.property hU t).mpr
    rw [c.cycle_edge_mem_parity M.property N.property hU t]
    dsimp [a] at ht
    split_ifs at ht ⊢ <;> first | omega | tauto
  have hb : decide (k.a₀ % 2 = 1-a) = !decide (k.a₀ % 2 = a) := by
    by_cases h : k.a₀ % 2 = a
    · have hn : k.a₀ % 2 ≠ 1-a := by omega
      simp [h]
      omega
    · have hn : k.a₀ % 2 = 1-a := by omega
      simp [hn]
      omega
  refine ⟨k.cellPaths chord hc, decide (k.a₀ % 2 = a),
    k.cell_orientation_subset chord hc M.val a ha hM, ?_, ?_⟩
  · rw [← hb]
    exact k.cell_orientation_subset chord hc N.val (1-a) (by omega) hN
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact k.cell_orientation_reachable chord hc _ hU true e he
    · exact k.cell_orientation_reachable chord hc _ hU false e he

end IndexedCycle.Corners

end

variable {V E : Type*} [Fintype V]

variable {inc : E → V → Prop}

noncomputable def matchingWeight (w : E → ℝ) (M : PM inc) : ℝ := ∏ e ∈ M.val, w e

lemma matchingWeight_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < matchingWeight w M := Finset.prod_pos (fun e _ => hw e)

variable [Fintype E]

noncomputable def partition (w : E → ℝ) : ℝ := by
  classical
  exact ∑ M : PM inc, matchingWeight w M

lemma partition_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < partition (inc := inc) w := by
  classical
  exact Finset.sum_pos' (fun A _ => le_of_lt (matchingWeight_pos w hw A))
    ⟨M, Finset.mem_univ _, matchingWeight_pos w hw M⟩

noncomputable def gibbs (w : E → ℝ) (M : PM inc) : ℝ :=
  matchingWeight w M / partition (inc := inc) w

lemma gibbs_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < gibbs w M := div_pos (matchingWeight_pos w hw M) (partition_pos w hw M)

lemma gibbs_sum (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    ∑ A : PM inc, gibbs w A = 1 := by
  classical
  simp only [gibbs, ← Finset.sum_div]
  have hp := ne_of_gt (partition_pos w hw M)
  convert div_self hp using 1
  all_goals try with_reducible_and_instances rfl
  all_goals (try congr 1)
  all_goals (try unfold partition)
  all_goals (try congr 1)
  all_goals (try ext A)
  all_goals (try simp)

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_IntervalPattern
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable {inc : E → V → Prop}
namespace DemandEncoding

variable {d : RawDemand inc} (enc : DemandEncoding inc d)

lemma gibbs_bound (w : E → ℝ) (hw : ∀ e, 0 < w e) (A : ℝ) (hA : 1 ≤ A)
    (hcard : enc.dropped.card = enc.added.card)
    (hcompare : ∀ e ∈ enc.dropped, ∀ f ∈ enc.added, w e ≤ A * w f) :
    gibbs w d.first * gibbs w d.second ≤ A^4 * gibbs w enc.first * gibbs w enc.second := by
  have h := four_edge_weight_bound w hw A hA
    (d.first.val.val + d.second.val.val) (enc.first.val.val + enc.second.val.val)
    enc.dropped enc.added enc.conservation hcard enc.dropped_card hcompare
  simp only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] at h
  have h' : matchingWeight w d.first * matchingWeight w d.second ≤
      A^4 * (matchingWeight w enc.first * matchingWeight w enc.second) := h
  have hp : 0 ≤ partition (inc := inc) w * partition (inc := inc) w := mul_self_nonneg _
  have hh := div_le_div_of_nonneg_right h' hp
  dsimp only [gibbs]
  calc
    _ = (matchingWeight w d.first * matchingWeight w d.second) /
        (partition (inc := inc) w * partition (inc := inc) w) := div_mul_div_comm _ _ _ _
    _ ≤ A^4 * (matchingWeight w enc.first * matchingWeight w enc.second) /
        (partition (inc := inc) w * partition (inc := inc) w) := hh
    _ = _ := by
      field_simp [ne_of_gt (partition_pos w hw d.first)]

end DemandEncoding

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance instFintypeBagEdge : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

include hheight hstep

theorem actual_switch_encoding
    (M N : PM (BagEdge.Incident (bags := bags)))
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size)
    (flags : Fin 64) (b : Bool) (D : ℝ) (hD : 1 ≤ D)
    (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 < lo) (_hlohi : lo ≤ hi) :
    let k := c.cellCorners hbags hc hy
    let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
      (c.cellChords_incidence hbags hc hy) flags
    let wt := fun e => max lo (min hi (w e))
    ∃ enc : DemandEncoding BagEdge.Incident (k.rawDemand M N flags),
      enc.first.val = emb.outsideFirst ∪ (c.pathsOfCell hbags hc hy).switched b ∧
      gibbs wt M * gibbs wt N ≤
        (1000*D)^4 * gibbs wt enc.first * gibbs wt enc.second := by
  classical
  dsimp only
  let k := c.cellCorners hbags hc hy
  let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy) flags
  obtain ⟨r, hg⟩ := c.cell_has_good_pair hbags hc hy
  have hr := c.cell_actual_repairs hbags hc hy r hg
  let enc := emb.switchEncoding BagEdge.exists_incident b r (c.leafRepair hbags k) hr
  refine ⟨enc, rfl, ?_⟩
  apply enc.gibbs_bound (fun e => max lo (min hi (w e)))
    (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
  · exact ((c.pathsOfCell hbags hc hy).modification_cards b r (c.leafRepair hbags k)).1
  · intro e he f hf
    exact c.cell_clamp_comparability hbags height hheight hstep hc hy D hD w hw lo hi
      (le_of_lt hlo) (c.drops_local hbags hc hy r he)
      (c.additions_local hbags hc hy b r hg hf)

theorem actual_error_encodings
    (M N : PM (BagEdge.Incident (bags := bags)))
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size)
    (flags : Fin 64) (b : Bool) (X Y : Fin 4)
    (hX : CellPaths.sideBit X = b) (hY : CellPaths.sideBit Y = b) (hne : X ≠ Y)
    (hl : ∀ i : Fin 4, CellPaths.sideBit i = b → (c.cellCorners hbags hc hy).length i ≠ 1)
    (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 < lo) (_hlohi : lo ≤ hi) :
    let k := c.cellCorners hbags hc hy
    let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
      (c.cellChords_incidence hbags hc hy) flags
    let cp := c.pathsOfCell hbags hc hy
    let wt := fun e => max lo (min hi (w e))
    ∃ enc₀ enc₁ : DemandEncoding BagEdge.Incident (k.rawDemand M N flags),
      enc₀.first.val = emb.outsideFirst ∪ cp.orientation b ∧
      enc₁.first.val = emb.outsideFirst ∪ cp.contextOne b Y ∧
      (cp.side X).closed (cp.chord X) ⊆ enc₀.second.val ∧
      (cp.side X).closed (cp.chord X) ⊆ enc₁.second.val ∧
      gibbs wt M * gibbs wt N ≤ (1000*D)^4 * gibbs wt enc₀.first * gibbs wt enc₀.second ∧
      gibbs wt M * gibbs wt N ≤ (1000*D)^4 * gibbs wt enc₁.first * gibbs wt enc₁.second := by
  classical
  dsimp only
  let k := c.cellCorners hbags hc hy
  let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy) flags
  have hg := c.cell_long_opposite_good hbags hc hy b hl
  have hr := c.cell_actual_repairs hbags hc hy b hg
  let enc₀ := emb.errorZeroEncoding BagEdge.exists_incident b (c.leafRepair hbags k) hr
  let enc₁ := emb.errorOneEncoding BagEdge.exists_incident b (c.leafRepair hbags k) hr Y hY
  refine ⟨enc₀, enc₁, rfl, rfl,
    emb.zero_guide_contains BagEdge.exists_incident b _ hr X hX,
    emb.one_guide_contains BagEdge.exists_incident b _ hr X Y hX hY hne, ?_, ?_⟩
  all_goals
    first
    | apply enc₀.gibbs_bound (fun e => max lo (min hi (w e)))
        (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
    | apply enc₁.gibbs_bound (fun e => max lo (min hi (w e)))
        (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
    · exact ((c.pathsOfCell hbags hc hy).modification_cards b b (c.leafRepair hbags k)).1
    · intro e he f hf
      exact c.cell_clamp_comparability hbags height hheight hstep hc hy D hD w hw lo hi
        (le_of_lt hlo) (c.drops_local hbags hc hy b he)
        (c.additions_local hbags hc hy b b hg hf)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport

section

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

variable [DecidableEq E]

variable [DecidableEq V]

namespace Corners

variable {c} (k : c.Corners)

lemma cell_piece_interval (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (b : Bool) (i : Fin 4) :
    (k.cellPaths chord hc).orientationPieces b i =
      c.intervalPattern (k.start i) (k.stop i) (if b then k.a₀%2 else 1-k.a₀%2) := by
  have hs := k.parity_start i
  have hb := k.bounds i
  have he : k.start i + k.length i = k.stop i := by dsimp [length]; omega
  change (if CellPaths.sideBit i = b then (k.side i).through else (k.side i).interior) = _
  by_cases h : CellPaths.sideBit i = b
  · rw [ite_eq_left h]
    rw [show (k.side i).through = _ from c.arc_through _ _ _ _ _ _, he]
    cases b <;> simp_all
  · rw [ite_eq_right h]
    rw [show (k.side i).interior = _ from c.arc_interior _ _ _ _ _ _, he]
    cases b <;> cases hi : CellPaths.sideBit i <;> simp_all
    congr 1
    omega

lemma cell_orientation_parity (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (b : Bool) :
    (k.cellPaths chord hc).orientation b =
      c.parityPattern (if b then k.a₀%2 else 1-k.a₀%2) := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  unfold CellPaths.orientation CellPaths.assemble
  simp only [k.cell_piece_interval, start, stop, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [show c.size + k.a₀ = k.a₀ + c.size by omega]
  have h := c.rotatedPattern (x := k.a₀) (by omega) (if b then k.a₀%2 else 1-k.a₀%2)
  rw [← h]
  ext e
  simp only [Finset.mem_union, c.mem_intervalPattern]
  constructor
  · rintro ((⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩) | (⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩)) <;>
      exact ⟨i,by omega,by omega,hp,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    by_cases ha : i < k.a₁
    · exact Or.inl (Or.inl ⟨i,hi,ha,hp,he⟩)
    · by_cases hb : i < k.a₂
      · exact Or.inr (Or.inl ⟨i,by omega,hb,hp,he⟩)
      · by_cases hd : i < k.a₃
        · exact Or.inl (Or.inr ⟨i,by omega,hd,hp,he⟩)
        · exact Or.inr (Or.inr ⟨i,by omega,hj,hp,he⟩)

end Corners

end IndexedCycle

end

open scoped symmDiff

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

lemma exchange_matching [Fintype V] {M N S : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (h : ExchangeCompatible (inc := inc) M N S) :
    MatchingOn inc (exchange M N S) Finset.univ := by
  refine ⟨fun _ _ v _ => Finset.mem_univ v, ?_⟩
  intro v _
  obtain ⟨e,⟨he,hev⟩,hu⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨f,⟨hf,hfv⟩,hv⟩ := hN.2 v (Finset.mem_univ v)
  have hs := h e he f hf v hev hfv
  by_cases hse : e ∈ S
  · have hsf := hs.mp hse
    refine ⟨f, ⟨(mem_exchange M N S f).mpr (Or.inr ⟨hf,hsf⟩),hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases (mem_exchange M N S g).mp hg with ⟨hgm,hgs⟩ | ⟨hgn,_⟩
    · have heq := hu g ⟨hgm,hgv⟩
      exact (hgs (heq ▸ hse)).elim
    · exact hv g ⟨hgn,hgv⟩
  · refine ⟨e, ⟨(mem_exchange M N S e).mpr (Or.inl ⟨he,hse⟩),hev⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases (mem_exchange M N S g).mp hg with ⟨hgm,_⟩ | ⟨hgn,hgs⟩
    · exact hu g ⟨hgm,hgv⟩
    · have heq := hv g ⟨hgn,hgv⟩
      exact (hse (hs.mpr (heq ▸ hgs))).elim

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}



namespace IndexedCycle

variable (c : IndexedCycle inc)

variable [Fintype V]

lemma inter_edgeSet_parity {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) :
    M ∩ c.edgeSet = c.parityPattern (if c.edgeAt 0 ∈ M then 0 else 1) := by
  classical
  ext e
  simp only [Finset.mem_inter, c.mem_edgeSet, parityPattern, mem_intervalPattern]
  constructor
  · rintro ⟨heM,i,hi,rfl⟩
    refine ⟨i, Nat.zero_le _,hi,?_,rfl⟩
    have hp := (c.cycle_edge_mem_parity hM hN hU i).mp heM
    split_ifs at hp ⊢ <;> first | omega | tauto
  · rintro ⟨i,_,hi,hpar,rfl⟩
    refine ⟨?_, i,hi,rfl⟩
    apply (c.cycle_edge_mem_parity hM hN hU i).mpr
    split_ifs at hpar ⊢ <;> omega

end IndexedCycle

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Sewn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section
variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}
namespace IndexedCycle.Corners

variable {c : IndexedCycle inc} (k : c.Corners)

lemma embeddedPair_outside [Fintype V] (M N : PM inc) (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (flags : Fin 64) :
    (k.embeddedPair M N hU chord hc flags).outsideFirst = M.val \ c.edgeSet := by
  classical
  change M.val \ (k.cellPaths chord hc).orientation
    (decide (k.a₀ % 2 = if c.edgeAt 0 ∈ M.val then 0 else 1)) = _
  rw [k.cell_orientation_parity]
  have hp := c.inter_edgeSet_parity M.property N.property hU
  have he : (if decide (k.a₀ % 2 = if c.edgeAt 0 ∈ M.val then 0 else 1)
      then k.a₀ % 2 else 1-k.a₀ % 2) = (if c.edgeAt 0 ∈ M.val then 0 else 1) := by
    by_cases hz : c.edgeAt 0 ∈ M.val <;> simp only [hz,ite_true,ite_false]
    all_goals split_ifs <;> simp_all
  rw [he,← hp]
  ext e
  simp

end IndexedCycle.Corners

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ChosenChord
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def chosenChord (x y : ℕ) : BagEdge bags := by
  classical
  exact if h : x < y ∧ y < c.size ∧ (c.labelCycle hbags).Admissible x y then
    c.chord hbags x y h.1 h.2.1 h.2.2 else c.edgeAt 0

noncomputable def diagramGain (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x y : ℕ) : ℝ := c.signedGain R f x y (c.chosenChord hbags x y)

noncomputable def diagramTerm (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) : ℝ := by
  classical
  exact if h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size then
    (c.cellCorners hbags h.1 h.2).signedLocalTerm (c.cellChords hbags h.1 h.2)
      (c.cellChords_incidence hbags h.1 h.2) R f else 0

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport.IndexedCycle

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def diagramEnergy (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) : ℝ := by
  classical
  exact if h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size then
    let P := c.pathsOfCell hbags h.1 h.2
    (f (R ∪ P.switched true) - f (R ∪ P.switched false))^2 +
      (P.contextError R f true 2 0)^2 + (P.contextError R f false 3 1)^2
    else 0

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def subdivision (hG : G.IsAcyclic) :
    MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1) :=
  Classical.choice ((c.labelCycle hbags).quadrangulate hG c.four_le c.even)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

abbrev LongComponent (p : PM inc × PM inc) :=
  {S : Finset E // ∃ c : IndexedCycle inc, c.edgeSet = S ∧ ∀ i, c.edgeAt i ∈ p.1.val ∪ p.2.val}

namespace LongComponent

variable {p : PM inc × PM inc} (S : LongComponent p)

noncomputable instance instFintype : Fintype (LongComponent p) := Fintype.ofFinite _

noncomputable def cycle : IndexedCycle inc := S.property.choose

omit [DecidableEq V] [Fintype E] in
lemma cycle_union : ∀ i, S.cycle.edgeAt i ∈ p.1.val ∪ p.2.val := S.property.choose_spec.2

end LongComponent

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

abbrev Demand := Σ p : PM (BagEdge.Incident (bags := bags)) × PM BagEdge.Incident,
  Σ S : LongComponent p, ↥(S.cycle.subdivision hbags hG).cellSet

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Cycle
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands
variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
variable {bags : V → Finset L}
variable {G : SimpleGraph L}
variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
variable (hG : G.IsAcyclic)
namespace Demand

variable {hbags hG} (d : Demand hbags hG)

noncomputable def cycle := d.2.1.cycle

omit [Fintype L] in
lemma cell : (d.cycle.labelCycle hbags).Cell d.2.2.val.x d.2.2.val.p d.2.2.val.q d.2.2.val.y :=
  ((d.2.1.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp d.2.2.property)).2.2

omit [Fintype L] in
lemma last_lt : d.2.2.val.y < d.cycle.size := by
  have hy := ((d.2.1.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp d.2.2.property)).2.1
  have hsize := d.cycle.four_le
  change d.2.2.val.y ≤ d.cycle.size-1 at hy
  omega

noncomputable def corners : d.cycle.Corners := d.cycle.cellCorners hbags d.cell d.last_lt

noncomputable def raw (flags : Fin 64) : RawDemand (BagEdge.Incident (bags := bags)) :=
  d.corners.rawDemand d.1.1 d.1.2 flags

end Demand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_1 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

noncomputable instance instFintypeDemand : Fintype (Demand hbags hG) := Fintype.ofFinite _

namespace Demand

noncomputable def paths (d : Demand hbags hG) := d.cycle.pathsOfCell hbags d.cell d.last_lt

noncomputable def outside (d : Demand hbags hG) := d.1.1.val \ d.cycle.edgeSet

end Demand

abbrev ErrorDemand (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) :=
  {e : Bool × Demand hbags hG // ∀ i : Fin 4, CellPaths.sideBit i = e.1 →
    (e.2.paths.side i).length ≠ 1}

noncomputable instance instFintypeErrorDemand : Fintype (ErrorDemand hbags hG) := Fintype.ofFinite _

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

def bit : Bool := e.val.1

def demand : Demand hbags hG := e.val.2

def X : Fin 4 := if e.bit then 2 else 3

def Y : Fin 4 := if e.bit then 0 else 1

omit [Fintype L] in
lemma X_bit : CellPaths.sideBit e.X = e.bit := by cases hb : e.bit <;> simp [X,hb,CellPaths.sideBit]

omit [Fintype L] in
lemma Y_bit : CellPaths.sideBit e.Y = e.bit := by cases hb : e.bit <;> simp [Y,hb,CellPaths.sideBit]

omit [Fintype L] in
lemma X_ne_Y : e.X ≠ e.Y := by cases hb : e.bit <;> simp [X,Y,hb]

def flags : Fin 64 := if e.bit then 2 else 1

noncomputable def raw := e.demand.raw e.flags

end ErrorDemand

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

namespace Demand

variable (d : Demand hbags hG)

include hheight hstep hD hw hlo hlohi in
lemma exists_switch : ∃ enc : DemandEncoding BagEdge.Incident (d.raw 0),
    enc.first.val = d.outside ∪ d.paths.switched true ∧
    gibbs (fun e => max lo (min hi (w e))) d.1.1 * gibbs (fun e => max lo (min hi (w e))) d.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc.first *
        gibbs (fun e => max lo (min hi (w e))) enc.second := by
  obtain ⟨enc,he,hw⟩ := d.cycle.actual_switch_encoding hbags height hheight hstep
    d.1.1 d.1.2 d.2.1.cycle_union d.cell d.last_lt 0 true D hD w hw lo hi hlo hlohi
  refine ⟨enc,?_,hw⟩
  exact he.trans (congrArg (fun R => R ∪ d.paths.switched true)
    (d.corners.embeddedPair_outside d.1.1 d.1.2 d.2.1.cycle_union d.paths.chord d.paths.chord_incidence 0))

noncomputable def switchChoice : DemandEncoding BagEdge.Incident (d.raw 0) :=
  (d.exists_switch height hheight hstep D hD w hw lo hi hlo hlohi).choose

end Demand

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

include hheight hstep hD hw hlo hlohi in
lemma exists_errors : ∃ enc₀ enc₁ : DemandEncoding BagEdge.Incident e.raw,
    enc₀.first.val = e.demand.outside ∪ e.demand.paths.orientation e.bit ∧
    enc₁.first.val = e.demand.outside ∪ e.demand.paths.contextOne e.bit e.Y ∧
    (e.demand.paths.side e.X).closed (e.demand.paths.chord e.X) ⊆ enc₀.second.val ∧
    (e.demand.paths.side e.X).closed (e.demand.paths.chord e.X) ⊆ enc₁.second.val ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc₀.first *
        gibbs (fun e => max lo (min hi (w e))) enc₀.second ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc₁.first *
        gibbs (fun e => max lo (min hi (w e))) enc₁.second := by
  obtain ⟨enc₀,enc₁,h₀,h₁,hr⟩ := e.demand.cycle.actual_error_encodings hbags height hheight hstep
    e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union e.demand.cell e.demand.last_lt
    e.flags e.bit e.X e.Y e.X_bit e.Y_bit e.X_ne_Y e.property D hD w hw lo hi hlo hlohi
  refine ⟨enc₀,enc₁,?_,?_,hr⟩
  · exact h₀.trans (congrArg (fun R => R ∪ e.demand.paths.orientation e.bit)
      (e.demand.corners.embeddedPair_outside e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union
        e.demand.paths.chord e.demand.paths.chord_incidence e.flags))
  · exact h₁.trans (congrArg (fun R => R ∪ e.demand.paths.contextOne e.bit e.Y)
      (e.demand.corners.embeddedPair_outside e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union
        e.demand.paths.chord e.demand.paths.chord_incidence e.flags))

noncomputable def errorZero : DemandEncoding BagEdge.Incident e.raw :=
  (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose

noncomputable def errorOne : DemandEncoding BagEdge.Incident e.raw :=
  (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec.choose

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport.OddPath

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop} (p : OddPath inc) (chord : E)

variable (hlong : 3 ≤ p.length)

variable (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length)

def closedCycle : IndexedCycle inc where
  size := p.length + 1
  four_le := by omega
  even := by have := p.odd; omega
  vertex i := p.vertex i
  simple := by
    intro i j h
    exact Fin.ext (p.simple ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ h)
  edge i := if i.val < p.length then p.edge i else chord
  incidence := by
    intro i v
    by_cases hi : i.val < p.length
    · rw [ite_eq_left hi,p.incidence i hi]
      have hm : (i.val + 1) % (p.length + 1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hm]
    · have hil : i.val = p.length := by omega
      rw [ite_eq_right hi,hc]
      simp only [hil,Nat.mod_self]
      exact or_comm

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma closedCycle_edgeAt (i : ℕ) (hi : i < p.length) :
    (p.closedCycle chord hlong hc).edgeAt i = p.edge i := by
  simp only [IndexedCycle.edgeAt,IndexedCycle.index,closedCycle]
  rw [Nat.mod_eq_of_lt (by omega),ite_eq_left hi]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma closedCycle_chord :
    (p.closedCycle chord hlong hc).edgeAt p.length = chord := by
  simp [IndexedCycle.edgeAt,IndexedCycle.index,closedCycle,Nat.mod_eq_of_lt (by omega : p.length < p.length+1)]

omit [Fintype V] [DecidableEq V] in
lemma closedCycle_parity_zero :
    (p.closedCycle chord hlong hc).parityPattern 0 = p.through := by
  ext e
  simp only [IndexedCycle.parityPattern,IndexedCycle.mem_intervalPattern,through,
    pathPattern,Finset.mem_image,Finset.mem_filter,Finset.mem_Ico]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    have hil : i < p.length := by
      change i < p.length + 1 at hj
      have := p.odd
      omega
    exact ⟨i,⟨⟨by omega,hil⟩,by simpa using hp⟩,
      (p.closedCycle_edgeAt chord hlong hc i hil).symm.trans he⟩
  · rintro ⟨i,⟨hi,hp⟩,he⟩
    refine ⟨i,by omega,by change i < p.length+1; omega,?_,?_⟩
    · simpa using hp
    · exact (p.closedCycle_edgeAt chord hlong hc i hi.2).trans he

omit [Fintype V] [DecidableEq V] in
lemma closedCycle_parity_one :
    (p.closedCycle chord hlong hc).parityPattern 1 = p.closed chord := by
  ext e
  simp only [IndexedCycle.parityPattern,IndexedCycle.mem_intervalPattern,closed,
    interior,pathPattern,Finset.mem_union,Finset.mem_image,Finset.mem_filter,
    Finset.mem_Ico,Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    change i < p.length+1 at hj
    by_cases hil : i < p.length
    · left
      refine ⟨i,⟨⟨by omega,?_⟩,?_⟩, (p.closedCycle_edgeAt chord hlong hc i hil).symm.trans he⟩
      · have := p.odd; omega
      · omega
    · right
      have hie : i = p.length := by omega
      subst i
      exact he.symm.trans (p.closedCycle_chord chord hlong hc)
  · rintro (⟨i,⟨hi,hp⟩,he⟩ | he)
    · refine ⟨i,by omega,by change i < p.length+1; omega,by omega,?_⟩
      exact (p.closedCycle_edgeAt chord hlong hc i (by omega)).trans he
    · exact ⟨p.length,by omega,by change p.length < p.length+1; omega,
        p.odd,(p.closedCycle_chord chord hlong hc).trans he.symm⟩

end MatchingFPRAS.Transport.OddPath

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Through
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}
namespace PatternCode

variable (x : PatternCode inc)

noncomputable def ofPath (p : OddPath inc) (chord : E) (hlong : 3 ≤ p.length)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length) : PatternCode inc :=
  ⟨(p.through,p.closed chord),p.closedCycle chord hlong hc,
    p.closedCycle_parity_zero chord hlong hc,p.closedCycle_parity_one chord hlong hc⟩

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable instance instFintypePM : Fintype (PM inc) := Fintype.ofFinite _

noncomputable def gibbsLaw (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    MatchingFPRAS.PairEnergy.Law (PM inc) where
  weight := gibbs w
  nonneg := fun A => le_of_lt (gibbs_pos w hw A)
  total := gibbs_sum w hw M

namespace PatternCode

noncomputable def throughStates (x : PatternCode inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (fun A => x.through ⊆ A.val)

noncomputable def closedStates (x : PatternCode inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (fun A => x.closed ⊆ A.val)

def firstDerivative (f : Finset E → ℝ) (x : PatternCode inc) (A : PM inc) : ℝ :=
  f A.val - f ((A.val \ x.through) ∪ x.closed)

def secondDerivative (g : Finset E → ℝ) (x : PatternCode inc) (B : PM inc) : ℝ :=
  g ((B.val \ x.closed) ∪ x.through) - g B.val

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_2 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

omit [Fintype L] in
lemma X_long : 3 ≤ (e.demand.paths.side e.X).length := by
  have hp := (e.demand.paths.side e.X).positive
  have ho := (e.demand.paths.side e.X).odd
  have hn := e.property e.X e.X_bit
  change (e.demand.paths.side e.X).length ≠ 1 at hn
  omega

noncomputable def pattern : PatternCode (BagEdge.Incident (bags := bags)) :=
  PatternCode.ofPath (e.demand.paths.side e.X) (e.demand.paths.chord e.X) e.X_long
    (e.demand.paths.chord_incidence e.X)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

noncomputable def choice (j : Bool) : DemandEncoding BagEdge.Incident e.raw :=
  if j then e.errorOne height hheight hstep D hD w hw lo hi hlo hlohi
  else e.errorZero height hheight hstep D hD w hw lo hi hlo hlohi

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SafeSwitch
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_3 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

def SafeSwitch (w : E → ℝ) (K : ℝ) (A B : PM inc) : Prop :=
  ∃ (v : Fin 4 → V) (e : Fin 4 → E) (R : Finset E),
    Function.Injective v ∧
    (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
    A.val = R ∪ {e 0,e 2} ∧ B.val = R ∪ {e 1,e 3} ∧
    (∀ i j, w (e i) ≤ K * w (e j))

noncomputable def safeDestinations (w : E → ℝ) (K : ℝ) (A : PM inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (SafeSwitch w K A)

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_4 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

variable (d : Demand hbags hG)

noncomputable def switchState (b : Bool) : PM (BagEdge.Incident (bags := bags)) :=
  let emb := d.corners.embeddedPair d.1.1 d.1.2 d.2.1.cycle_union
    d.paths.chord d.paths.chord_incidence 0
  emb.attachFirst (d.paths.switched b) (d.paths.switched_matching b)

end Demand

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_5 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

noncomputable def cellError (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) (b : Bool) : ℝ :=
  d.paths.contextError d.outside f b (if b then 2 else 3) (if b then 0 else 1)

noncomputable def cellSwitch (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  f (d.outside ∪ d.paths.switched true)-f (d.outside ∪ d.paths.switched false)

noncomputable def cellCost (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  (d.cellSwitch f)^2+(d.cellError f true)^2+(d.cellError f false)^2

end Demand

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Underlying
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

namespace Overlay

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

omit [DecidableEq V] [DecidableEq E] in
lemma underlying_perfect [DecidableEq V] [DecidableEq E] (M : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ) :
    (SimpleGraph.toSubgraph (G := ⊤) (underlying ends hloop M) le_top).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e, ⟨he, hev⟩, heuniq⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨w, hw⟩ := exists_partner ends hev
  refine ⟨w, ⟨e, he, hw⟩, ?_⟩
  rintro u ⟨f, hf, hfu⟩
  have hfv : v ∈ ends f := by rw [hfu]; simp
  have hfe := heuniq f ⟨hf, hfv⟩
  have hsym : s(v,u) = s(v,w) := hfu.symm.trans ((congrArg ends hfe).trans hw)
  have h : u = w ∨ v = w ∧ u = v := by simpa using hsym
  exact h.elim id (fun h => h.2.trans h.1)

open scoped symmDiff

lemma discrepancy_alternating (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ) :
    (discrepancy ends hloop M N).IsAlternating (underlying ends hloop M) := by
  have h := (underlying_perfect ends hloop M hM).isAlternating_symmDiff_left
    (underlying_perfect ends hloop N hN)
  exact h

lemma unique_colored_lift (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v w : V} (hadj : (discrepancy ends hloop M N).Adj v w) :
    ∃! e, e ∈ M ∪ N ∧ ends e = s(v,w) := by
  rcases (discrepancy_adj_iff ends hloop M N v w).mp hadj with h | h
  · obtain ⟨e, he, hend⟩ := h.1
    refine ⟨e, ⟨Finset.mem_union_left N he, hend⟩, ?_⟩
    rintro f ⟨hf, hfend⟩
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨g, hg, hu⟩ := hM.2 v (Finset.mem_univ v)
      exact (hu f ⟨hf, by change v ∈ ends f; rw [hfend]; simp⟩).trans
        (hu e ⟨he, by change v ∈ ends e; rw [hend]; simp⟩).symm
    · exact (h.2 ⟨f, hf, hfend⟩).elim
  · obtain ⟨e, he, hend⟩ := h.1
    refine ⟨e, ⟨Finset.mem_union_right M he, hend⟩, ?_⟩
    rintro f ⟨hf, hfend⟩
    rcases Finset.mem_union.mp hf with hf | hf
    · exact (h.2 ⟨f, hf, hfend⟩).elim
    · obtain ⟨g, hg, hu⟩ := hN.2 v (Finset.mem_univ v)
      exact (hu f ⟨hf, by change v ∈ ends f; rw [hfend]; simp⟩).trans
        (hu e ⟨he, by change v ∈ ends e; rw [hend]; simp⟩).symm

noncomputable def cyclicEdge (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v : V} (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) (i : ℕ) : E :=
  (unique_colored_lift ends hloop M N hM hN (cyclicVertex_adj p hp i)).choose

lemma cyclicEdge_spec (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v : V} (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) (i : ℕ) :
    cyclicEdge ends hloop M N hM hN p hp i ∈ M ∪ N ∧
      ends (cyclicEdge ends hloop M N hM hN p hp i) =
        s(cyclicVertex p i, cyclicVertex p (i + 1)) :=
  (unique_colored_lift ends hloop M N hM hN (cyclicVertex_adj p hp i)).choose_spec.1

end Overlay

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.Overlay

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

variable (M N : Finset E)

variable (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)

variable (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)

noncomputable def indexedCycle {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) :
    IndexedCycle (fun e v => v ∈ ends e) where
  size := p.length
  four_le := by
    have hh := hp.three_le_length
    have he := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
    omega
  even := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
  vertex i := cyclicVertex p i.val
  simple := by
    intro i j h
    apply Fin.ext
    exact cyclicVertex_injOn p hp ⟨Nat.zero_le _, i.isLt⟩ ⟨Nat.zero_le _, j.isLt⟩ h
  edge i := cyclicEdge ends hloop M N hM hN p hp i.val
  incidence := by
    intro i w
    rw [(cyclicEdge_spec ends hloop M N hM hN p hp i.val).2]
    simp only [Sym2.mem_iff, cyclicVertex, Nat.mod_mod]

end

end MatchingFPRAS.Transport.Overlay

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ComponentOrder
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def prefixPair (p : PM inc × PM inc) (i : ℕ) : PM inc × PM inc :=
  (⟨exchange p.1.val p.2.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.1.property p.2.property (componentPrefix_compatible _ _ _)⟩,
   ⟨exchange p.2.val p.1.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.2.property p.1.property (componentPrefix_compatible _ _ _).symm⟩)

noncomputable def componentPair (p : PM inc × PM inc) (i : ℕ) : PM inc × PM inc :=
  (⟨exchange p.1.val p.2.val (componentAt (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.1.property p.2.property (componentAt_compatible _ _ _)⟩,
   ⟨exchange p.2.val p.1.val (componentAt (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.2.property p.1.property (componentAt_compatible _ _ _).symm⟩)

noncomputable def componentDifference (f : PM inc → ℝ) (p : PM inc × PM inc) (i : ℕ) : ℝ :=
  f p.1 - f (componentPair p i).1

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

def ColorChange (A B : PM (fun e v => v ∈ ends e)) : Prop :=
  ∃ e f : E, ∃ R : Finset E, ends e = ends f ∧ A.val = R ∪ {e} ∧ B.val = R ∪ {f}

noncomputable def colorDestinations (A : PM (fun e v => v ∈ ends e)) :
    Finset (PM (fun e v => v ∈ ends e)) := by
  classical
  exact Finset.univ.filter (ColorChange ends A)

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_6 : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

noncomputable def longCellCost (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  ∑ S : LongComponent p, ∑ a : ↥(S.cycle.subdivision hbags hG).cellSet,
    (show Demand hbags hG from ⟨p,S,a⟩).cellCost f

noncomputable def colorCost (A : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  ∑ B ∈ colorDestinations (fun e : BagEdge bags => e.val.val.1) A, (f A.val-f B.val)^2

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_EndpointPair
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_7 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance endpointPairBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

namespace BagEdge

noncomputable def endpointPair (e : BagEdge bags) : V × V :=
  Classical.choose (show ∃ p : V × V, e.val.val.1 = s(p.1,p.2) from
    Sym2.inductionOn e.val.val.1 (fun a b => ⟨(a,b),rfl⟩))

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma endpointPair_eq (e : BagEdge bags) : e.val.val.1 = s(e.endpointPair.1,e.endpointPair.2) :=
  Classical.choose_spec (show ∃ p : V × V, e.val.val.1 = s(p.1,p.2) from
    Sym2.inductionOn e.val.val.1 (fun a b => ⟨(a,b),rfl⟩))

noncomputable def verticesColor (e : BagEdge bags) : Σ v : V, V × ↥(bags v) :=
  ⟨e.endpointPair.1,e.endpointPair.2,⟨e.color,e.property _ (by
    change e.endpointPair.1 ∈ e.val.val.1
    rw [e.endpointPair_eq]
    simp)⟩⟩

end BagEdge

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

def TwoEdgeSwitch (A B : PM inc) : Prop :=
  ∃ (v : Fin 4 → V) (e : Fin 4 → E) (R : Finset E),
    Function.Injective v ∧
    (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
    A.val = R ∪ {e 0,e 2} ∧ B.val = R ∪ {e 1,e 3}

noncomputable def switchDestinations (A : PM inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (TwoEdgeSwitch A)

noncomputable def discrepancyComponents (A B : PM inc) : Finset (Finset E) := by
  classical
  exact (components (inc := inc) (A.val ∪ B.val)).filter (fun S => ¬ S ⊆ A.val ∩ B.val)

noncomputable def switchDirichlet (w : E → ℝ) (f : Finset E → ℝ) : ℝ :=
  ∑ A : PM inc, ∑ B ∈ switchDestinations A,
    min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 / (48 * (A.val.card.choose 2 : ℝ))

noncomputable def cycleDirichlet (w : E → ℝ) (f g : Finset E → ℝ) : ℝ :=
  ∑ A : PM inc, ∑ B : PM inc, gibbs w A * gibbs w B *
    (∑ S ∈ discrepancyComponents A B, cycleSquare f g A.val B.val S /
      (6 * ((discrepancyComponents A B).card : ℝ)))

variable (ends : E → Sym2 V)

noncomputable def colorDirichlet (w : E → ℝ) (f : Finset E → ℝ) : ℝ :=
  ∑ A : PM (fun e v => v ∈ ends e), ∑ B ∈ colorDestinations ends A,
    min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 / (12 * (A.val.card : ℝ))

noncomputable def pairDirichlet (w : E → ℝ) (f g : Finset E → ℝ) : ℝ :=
  switchDirichlet (inc := fun e v => v ∈ ends e) w f + colorDirichlet ends w f +
    cycleDirichlet (inc := fun e v => v ∈ ends e) w f g

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Variance
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_8 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬(ends e).IsDiag)

include hloop

omit [Fintype E] [DecidableEq E] in
lemma PM.twice_card (A : PM (fun e v => v ∈ ends e)) : 2*A.val.card = Fintype.card V := by
  classical
  have hv (v : V) : (∑ e ∈ A.val, if v ∈ ends e then (1:ℕ) else 0) = 1 := by
    obtain ⟨e,⟨he,hev⟩,hu⟩ := A.property.2 v (Finset.mem_univ v)
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro f hf hfe
      have : v ∉ ends f := fun hfv => hfe (hu f ⟨hf,hfv⟩)
      simp [this]
    · exact fun h => (h he).elim
  have he (e : E) : (∑ v : V, if v ∈ ends e then (1:ℕ) else 0) = 2 := by
    have hs : Finset.univ.filter (fun v => v ∈ ends e) = (ends e).toFinset := by
      ext v; simp
    rw [← Finset.sum_filter,Finset.sum_const,smul_eq_mul,mul_one,hs]
    exact Sym2.card_toFinset_of_not_isDiag _ (hloop e)
  calc
    _ = ∑ e ∈ A.val, ∑ v : V, if v ∈ ends e then (1:ℕ) else 0 := by
      simp [he,Nat.mul_comm]
    _ = ∑ v : V, ∑ e ∈ A.val, if v ∈ ends e then (1:ℕ) else 0 := by rw [Finset.sum_comm]
    _ = _ := by simp [hv]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_ArithmeticSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
omit [DecidableEq K] in
lemma mapCfg_none (f : Λ → P) (h : Option P) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨none,v,S⟩=⟨h,v,S⟩ := rfl

open Turing MachineCost

end MatchingFPRAS.StackComposition

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_FillHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

theorem mate_edge_count [Fintype V] [LinearOrder V] (q : Mate V) (S : Finset V)
    (hq : HasHoles q Sᶜ) :
    2 * (Finset.univ.filter (fun v => v < q.1 v)).card = S.card := by
  let L := Finset.univ.filter (fun v => v < q.1 v)
  let R := Finset.univ.filter (fun v => q.1 v < v)
  have himg : L.image q.1 = R := by
    ext v
    simp only [Finset.mem_image, L,R,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro hv
      exact ⟨q.1 v,by simpa using hv,mate_mate q v⟩
  have hcard : L.card = R.card := by
    rw [← himg]
    exact (Finset.card_image_of_injective L q.2.injective).symm
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hl hr
    have hl' : v < q.1 v := (Finset.mem_filter.mp hl).2
    have hr' : q.1 v < v := (Finset.mem_filter.mp hr).2
    exact (lt_asymm hl' hr')
  have hunion : L ∪ R = S := by
    ext v
    simp only [L,R,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← ne_iff_lt_or_gt]
    have h := hq v
    simp only [Finset.mem_compl] at h
    simpa only [ne_eq, eq_comm, not_not] using (not_congr h)
  have hc := Finset.card_union_of_disjoint hdis
  rw [hunion,← hcard] at hc
  change 2 * L.card = S.card
  omega

theorem pairing_exists [Fintype V] [DecidableEq V] (S : Finset V) (hS : Even S.card) :
    ∃ q : Mate V, HasHoles q Sᶜ := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hEmpty : S = ∅
    · subst S
      refine ⟨⟨id,fun _ => rfl⟩,?_⟩
      intro v
      simp
    · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hcardpos := Finset.card_pos.mpr (show S.Nonempty from ⟨a,ha⟩)
      have hcard2 : 2 ≤ S.card := by obtain ⟨k,hk⟩ := hS; omega
      have herase : (S.erase a).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem ha]
        omega
      obtain ⟨b,hb⟩ := herase
      have hba := (Finset.mem_erase.mp hb).1
      have hbS := (Finset.mem_erase.mp hb).2
      let T := S \ {a,b}
      have hTcard : T.card + 2 = S.card := by
        have h := sdiff_pair_card S a b ha hbS hba.symm
        change T.card = S.card - 2 at h
        omega
      have hTeven : Even T.card := by
        obtain ⟨k,hk⟩ := hS
        refine ⟨k-1,?_⟩
        omega
      have hTsub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.sdiff_subset,by intro he; have := congrArg Finset.card he; omega⟩
      obtain ⟨q,hq⟩ := ih T hTsub hTeven
      have haT : a ∈ Tᶜ := by simp [T]
      have hbT : b ∈ Tᶜ := by simp [T]
      refine ⟨withEdge q a b,?_⟩
      have hh := withEdge_holes q Tᶜ hq a b haT hbT hba.symm
      have he : Tᶜ \ {a,b} = Sᶜ := by
        ext v
        simp only [T,Finset.mem_sdiff,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton]
        have hsub : ({a,b} : Finset V) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        constructor
        · intro h
          tauto
        · intro hv
          constructor
          · tauto
          · intro hvp
            exact hv (hsub (by simpa using hvp))
      rwa [he] at hh

noncomputable def pairingCapacity [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (S : Finset V) (hS : Even S.card) : ℝ :=
  (matchings Sᶜ).sup' (by
    obtain ⟨q,hq⟩ := pairing_exists S hS
    exact ⟨q,(mem_matchings q Sᶜ).mpr hq⟩) (weight B)

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SumLiftMate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

section

open Finset

variable {V W : Type*}

def sumRetractMate (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) : Mate V := by
  let f : V → V := fun a => Sum.elim id (fun _ => a) (q.val (Sum.inl a))
  have hf : ∀ a, Sum.inl (f a)=q.val (Sum.inl a) := by
    intro a
    cases he : q.val (Sum.inl a) with
    | inl b => simp [f,he]
    | inr w =>
      have hh := q.property (Sum.inl a)
      rw [he,hfix] at hh
      contradiction
  refine ⟨f,?_⟩
  intro a
  apply Sum.inl_injective (β := W)
  rw [hf,hf,q.property]

end

end MatchingFPRAS.Switching

namespace MatchingFPRAS.Subdivision

open Finset

noncomputable def selectedWeight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m) : ℝ :=
  ∏ i, if b i then w i else 1

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

lemma valid_step_eq_iff {m : ℕ} {U : Finset (Fin m)} {b c : Selection m}
    (hb : Valid U b) (hc : Valid U c) (i : Fin m) :
    b i.castSucc = c i.castSucc ↔ b i.succ = c i.succ := by
  by_cases hi : i ∈ U
  · have hb' := hb i
    have hc' := hc i
    simp only [hi, ↓reduceIte] at hb' hc'
    simp [hb'.1,hb'.2,hc'.1,hc'.2]
  · have hb' : b i.succ = !(b i.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa only [hi, ↓reduceIte] using hb i
    have hc' : c i.succ = !(c i.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa only [hi, ↓reduceIte] using hc i
    rw [hb',hc']
    simp

lemma valid_eq_iff_zero {m : ℕ} {U : Finset (Fin m)} {b c : Selection m}
    (hb : Valid U b) (hc : Valid U c) (i : Fin (m+1)) :
    b i = c i ↔ b 0 = c 0 := by
  have aux (k : ℕ) (hk : k < m+1) : b ⟨k,hk⟩ = c ⟨k,hk⟩ ↔ b 0 = c 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < m := by omega
      exact ((valid_step_eq_iff hb hc ⟨k,hk'⟩).symm).trans (ih (by omega))
  exact aux i.val i.isLt

theorem broken_unique {m : ℕ} {U : Finset (Fin m)} (hU : U.Nonempty)
    {b c : Selection m} (hb : Valid U b) (hc : Valid U c) : b = c := by
  obtain ⟨j,hj⟩ := hU
  have hb' := hb j
  have hc' := hc j
  simp only [hj, ↓reduceIte] at hb' hc'
  have hzero := (valid_eq_iff_zero hb hc j.castSucc).mp (hb'.1.trans hc'.1.symm)
  funext i
  exact (valid_eq_iff_zero hb hc i).mpr hzero

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

theorem residualHoles_independent {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) {b c : E → Selection m}
    (hb : FamilyHoles u v m R₀ U b) (hc : FamilyHoles u v m R₀ U c) :
    residualHoles u v R₀ U b = residualHoles u v R₀ U c := by
  classical
  have he (e) (h : e ∈ broken U) : b e = c e :=
    broken_unique ((mem_broken U e).mp h) (hb.1 e) (hc.1 e)
  ext x
  simp only [mem_residualHoles]
  apply or_congr Iff.rfl
  apply exists_congr
  intro e
  constructor <;> rintro ⟨h,hx⟩ <;> refine ⟨h,?_⟩
  · simpa only [Uses,he e h] using hx
  · simpa only [Uses,he e h] using hx

noncomputable def extract {m : ℕ} (U : E → Finset (Fin m))
    (b : E → Selection m) (e : E) : Bool :=
  if (U e).Nonempty then false else b e 0

 theorem extract_legal {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) :
    LogicalHoles u v (residualHoles u v R₀ U b) (broken U) (extract U b) := by
  classical
  have he (e x) : extract U b e = true ∧ (u e = x ∨ v e = x) ↔
      e ∉ broken U ∧ Uses u v b e x := by
    by_cases h : (U e).Nonempty
    · simp [extract,h]
    · have hu : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [extract,h,↓reduceIte,mem_broken,not_false_eq_true,true_and]
      exact (intact_uses hm u v b e x (by simpa [hu] using hb.1 e)).symm
  refine ⟨?_,?_,?_⟩
  · intro e he'
    simp [extract,(mem_broken U e).mp he']
  · intro x hx e hxe
    rw [he] at hxe
    rcases (mem_residualHoles u v R₀ U b x).mp hx with hx | ⟨f,hf,hfx⟩
    · exact hb.2.1 x hx e hxe.2
    · have hx0 : x ∉ R₀ := by intro hx0; exact hb.2.1 x hx0 f hfx
      obtain ⟨a,ha,hu⟩ := hb.2.2 x hx0
      have hef : e = f := (hu e hxe.2).trans (hu f hfx).symm
      exact hxe.1 (hef.symm ▸ hf)
  · intro x hx
    have hx0 : x ∉ R₀ := by intro h; exact hx ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inl h))
    obtain ⟨e,he',hu⟩ := hb.2.2 x hx0
    have hn : e ∉ broken U := by
      intro h
      exact hx ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inr ⟨e,h,he'⟩))
    refine ⟨e,(he e x).mpr ⟨hn,he'⟩,?_⟩
    intro f hf
    exact hu f ((he f x).mp hf).2

noncomputable def rebuild {m : ℕ} (U : E → Finset (Fin m))
    (base : E → Selection m) (s : E → Bool) (e : E) : Selection m :=
  if (U e).Nonempty then base e else fun i => alternating (s e) i.val

omit [Fintype V] in
lemma rebuild_uses {m : ℕ} (hm : Even m) (u v : E → V)
    (U : E → Finset (Fin m)) (base : E → Selection m) (s : E → Bool) (e : E) (x : V) :
    Uses u v (rebuild U base s) e x ↔
      (e ∈ broken U ∧ Uses u v base e x) ∨
      (e ∉ broken U ∧ s e = true ∧ (u e = x ∨ v e = x)) := by
  classical
  by_cases h : (U e).Nonempty
  · simp [rebuild,h,Uses]
  · simp [rebuild,h,Uses,alternating,Nat.even_iff.mp hm,and_or_left]

 theorem rebuild_legal {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base) (s : E → Bool)
    (hs : LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s) :
    FamilyHoles u v m R₀ U (rebuild U base s) := by
  classical
  let R := residualHoles u v R₀ U base
  have hu (e x) := rebuild_uses hm u v U base s e x
  refine ⟨?_,?_,?_⟩
  · intro e
    by_cases he : (U e).Nonempty
    · simpa [rebuild,he] using hb.1 e
    · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simpa [rebuild,he,he'] using alternating_valid m (s e)
  · intro x hx e he
    have hxR : x ∈ R := (mem_residualHoles _ _ _ _ _ _).mpr (Or.inl hx)
    rcases (hu e x).mp he with ⟨_,he⟩ | ⟨_,he⟩
    · exact hb.2.1 x hx e he
    · exact hs.2.1 x hxR e he
  · intro x hx
    by_cases hxR : x ∈ R
    · obtain hx0 | ⟨e,he,hxe⟩ := (mem_residualHoles _ _ _ _ _ _).mp hxR
      · exact (hx hx0).elim
      obtain ⟨a,ha,hauniq⟩ := hb.2.2 x hx
      refine ⟨e,(hu e x).mpr (Or.inl ⟨he,hxe⟩),?_⟩
      intro f hf
      rcases (hu f x).mp hf with ⟨_,hf⟩ | ⟨_,hf⟩
      · exact (hauniq f hf).trans (hauniq e hxe).symm
      · exact (hs.2.1 x hxR f hf).elim
    · obtain ⟨e,he,heuniq⟩ := hs.2.2 x hxR
      have hen : e ∉ broken U := by
        intro he'
        have := hs.1 e he'
        simp [this] at he
      refine ⟨e,(hu e x).mpr (Or.inr ⟨hen,he⟩),?_⟩
      intro f hf
      rcases (hu f x).mp hf with ⟨hfb,hf⟩ | ⟨_,hf⟩
      · exact (hxR ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inr ⟨f,hfb,hf⟩))).elim
      · exact heuniq f hf

omit [Fintype V] [Fintype E] in
 theorem rebuild_extract [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b) :
    rebuild U base (extract U b) = b := by
  classical
  funext e i
  by_cases he : (U e).Nonempty
  · have hbe := broken_unique he (hb0.1 e) (hb.1 e)
    simp [rebuild,he,hbe]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hl := (intact_iff (b e)).mp (by simpa [he'] using hb.1 e) i
    simpa [rebuild,extract,he] using hl.symm

omit [Fintype V] [Fintype E] in
 theorem extract_rebuild [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m) (s : E → Bool)
    (hs : LogicalHoles u v R (broken U) s) :
    extract U (rebuild U base s) = s := by
  classical
  funext e
  by_cases he : (U e).Nonempty
  · have hs' := hs.1 e ((mem_broken U e).mpr he)
    simp [extract,he,hs']
  · simp [extract,rebuild,he]

noncomputable def deletionEquiv {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base) :
    {b : E → Selection m // FamilyHoles u v m R₀ U b} ≃
      {s : E → Bool // LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s} where
  toFun b := ⟨extract U b.val, by
    have h := extract_legal hm u v R₀ U b.val b.property
    rwa [residualHoles_independent u v R₀ U b.property hb] at h⟩
  invFun s := ⟨rebuild U base s.val,rebuild_legal hm u v R₀ U base hb s.val s.property⟩
  left_inv b := Subtype.ext (rebuild_extract u v R₀ U base b.val hb b.property)
  right_inv s := Subtype.ext (extract_rebuild u v _ U base s.val s.property)

noncomputable def realHolePartition (u v : E → V) (m : ℕ) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (w : E → Fin (m+1) → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  exact ∑ b : {b : E → Selection m // FamilyHoles u v m R₀ U b},
    ∏ e, selectedWeight (w e) (b.val e)

noncomputable def logicalHolePartition (u v : E → V) (R : Finset V)
    (forbidden : Finset E) (lam : E → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {s : E → Bool // LogicalHoles u v R forbidden s}
  exact ∑ s : {s : E → Bool // LogicalHoles u v R forbidden s},
    ∏ e, if s.val e then lam e else 1

noncomputable def deletionConstant {m : ℕ} (U : E → Finset (Fin m))
    (base : E → Selection m) (w : E → Fin (m+1) → ℝ) (C : E → ℝ) : ℝ :=
  ∏ e, if (U e).Nonempty then selectedWeight (w e) (base e) else C e

end Deletion

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_HoleBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision
open Finset

def HoleBlocks.flatten {m : ℕ} (d : HoleBlocks m) : List (Fin m) :=
  d.left.toList ++ d.neutral.flatMap (fun q => [q.1,q.2]) ++ d.right.toList

def HoleBlocks.Parity {m : ℕ} (d : HoleBlocks m) : Prop :=
  (∀ j ∈ d.left, j.val%2=1) ∧
  (∀ q ∈ d.neutral, q.1.val%2=0 ∧ q.2.val%2=1) ∧
  (∀ j ∈ d.right, j.val%2=0)

end MatchingFPRAS.Subdivision

end OAI
end

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
lemma related_mono {s t : ℝ} (hst : s ≤ t) {a b : V} (h : Related B t a b) :
    Related B s a b := h.imp id (fun hb => hst.trans hb)

variable (hfloor : ∀ a b, 1 ≤ B a b)

noncomputable instance labelFintype (H : ℕ) : Fintype (Label B hsym htri H) := Fintype.ofFinite _

lemma dyadic_lower (H : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ)^(dyadicLevel H x).val ≤ x := by
  classical
  exact Nat.findGreatest_spec (P := fun k => (2:ℝ)^k ≤ x) (Nat.zero_le H) (by simpa using hx)

lemma dyadic_upper_of_lt (H : ℕ) (x : ℝ) (hx : x < (2:ℝ)^(H+1)) :
    x < (2:ℝ)^((dyadicLevel H x).val+1) := by
  classical
  by_cases he : (dyadicLevel H x).val=H
  · simpa [he] using hx
  · by_contra hn
    have hle : (dyadicLevel H x).val+1 ≤ H := by have := (dyadicLevel H x).isLt; omega
    have hg := Nat.le_findGreatest (P := fun k => (2:ℝ)^k ≤ x) hle (le_of_not_gt hn)
    change (dyadicLevel H x).val+1 ≤ (dyadicLevel H x).val at hg
    omega

lemma dyadic_near_of_lt (H : ℕ) (x y : ℝ) (hxlo : 1≤x) (hyhi : y < (2:ℝ)^(H+1))
    (hxy : x≤2*y) : (dyadicLevel H x).val ≤ (dyadicLevel H y).val+1 := by
  by_contra hn
  have hpow : (2:ℝ)^((dyadicLevel H y).val+2) ≤ 2^(dyadicLevel H x).val :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hx := dyadic_lower H x hxlo
  have hy := dyadic_upper_of_lt H y hyhi
  rw [show (dyadicLevel H y).val+2=((dyadicLevel H y).val+1)+1 by omega,pow_succ] at hpow
  linarith

variable {E : Type*} [Fintype E] (left right : E → V) (H : ℕ)

variable (hupper : ∀ e, B (left e) (right e) < (2:ℝ)^(H+1))

variable (hnear : ∀ x e f, Incident left right e x → Incident left right f x →
  B (left e) (right e) ≤ 2*B (left f) (right f))

omit [Fintype V] in
include hfloor hupper hnear in
lemma memberships_level_near {x : V} {a b : Label B hsym htri H}
    (ha : a ∈ memberships B hsym htri left right H x)
    (hb : b ∈ memberships B hsym htri left right H x) : a.1.val ≤ b.1.val+1 := by
  obtain ⟨e,he,rfl⟩ := (mem_memberships B hsym htri left right H x a).mp ha
  obtain ⟨f,hf,rfl⟩ := (mem_memberships B hsym htri left right H x b).mp hb
  exact dyadic_near_of_lt H _ _ (hfloor _ _) (hupper f) (hnear x e f he hf)

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

noncomputable instance partialFintype : Fintype (Partial inc) := Fintype.ofFinite _

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma submatching {M Q : Finset E} {U : Finset V} (hM : MatchingOn inc M U) (hQ : Q⊆M) :
    MatchingOn inc Q (support inc Q) := by
  refine ⟨?_,?_⟩
  · intro e he v hv; exact (mem_support inc Q v).mpr ⟨e,he,hv⟩
  · intro v hv
    obtain ⟨e,he,hev⟩ := (mem_support inc Q v).mp hv
    refine ⟨e,⟨he,hev⟩,?_⟩
    intro f hf
    exact hM.unique (hM.1 e (hQ he) v hev) (hQ hf.1) hf.2 (hQ he) hev

omit [Fintype E] [DecidableEq E] in
lemma support_sdiff_disjoint (Q : Finset E) : Disjoint (support inc Q) (univ \ support inc Q) := by
  exact Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp hy).2 hx)

noncomputable def expansionEquiv (hinc : ∀ e, ∃ v, inc e v) :
    (Σ M : Matchings inc univ, {Q : Finset E // Q⊆M.val}) ≃
      Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val) where
  toFun a := ⟨⟨a.2.val,submatching inc a.1.property a.2.property⟩,
    ⟨a.1.val \ a.2.val,a.1.property.sdiff
      (submatching inc a.1.property a.2.property) a.2.property⟩⟩
  invFun a := ⟨⟨a.1.val ∪ a.2.val,by
      have h := a.1.property.union a.2.property (support_sdiff_disjoint inc a.1.val)
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)] at h
      exact h⟩,⟨a.1.val,Finset.subset_union_left⟩⟩
  left_inv a := by
    rcases a with ⟨M,Q,hQ⟩
    have h : Q ∪ (M.val \ Q)=M.val := Finset.union_sdiff_of_subset hQ
    apply Sigma.ext (Subtype.ext h)
    change HEq (⟨Q,Finset.subset_union_left⟩ : {R : Finset E // R ⊆ Q ∪ (M.val \ Q)})
      (⟨Q,hQ⟩ : {R : Finset E // R ⊆ M.val})
    exact (Subtype.heq_iff_coe_eq (fun R => by rw [h])).mpr rfl
  right_inv a := by
    rcases a with ⟨Q,M⟩
    have hd : Disjoint Q.val M.val := Q.property.disjoint_edges M.property hinc
      (support_sdiff_disjoint inc Q.val)
    change (⟨Q,⟨(Q.val ∪ M.val) \ Q.val,_⟩⟩ :
      Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val)) = ⟨Q,M⟩
    apply congrArg (fun R : Matchings inc (univ \ support inc Q.val) =>
      (⟨Q,R⟩ : Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val)))
    exact Subtype.ext (Finset.union_sdiff_cancel_left hd)

end

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

noncomputable def emptyPartial : Partial inc := ⟨∅,by simp [MatchingOn]⟩

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

lemma asMate_holes : HasHoles (asMate R s hs) R := by
  intro x
  change mateFun R s hs x=x ↔ x ∈ R
  by_cases hx : x ∈ R
  · simp [hx,mateFun_hole R s hs x hx]
  · simp only [hx,iff_false]
    change mateFun R s hs x ≠ x
    rw [mateFun_selected R s hs _ (chosen_spec R s hs x hx).1 x (chosen_spec R s hs x hx).2]
    exact other_ne _ x (chosen_spec R s hs x hx).2

variable {R s hs}

lemma asMate_select (m : Mate V) (hm : HasHoles m R) :
    asMate R (select m) (select_holes m hm)=m := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ R
  · exact (mateFun_hole R _ _ x hx).trans ((hm x).mpr hx).symm
  · let h := select_holes m hm
    let e := chosen R (select m) h x hx
    have he := chosen_spec R (select m) h x hx
    exact (mateFun_selected R _ h e he.1 x he.2).trans
      (select_mate_other m e he.1 x he.2).symm

noncomputable def matchingEquiv (R : Finset V) :
    {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s} ≃
    {m : Mate V // HasHoles m R} where
  toFun s := ⟨asMate R s.val s.property,asMate_holes R s.val s.property⟩
  invFun m := ⟨select m.val,select_holes m.val m.property⟩
  left_inv _selection := Subtype.ext select_asMate
  right_inv m := Subtype.ext (asMate_select m.val m.property)

end MatchingFPRAS.Representation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Switching

variable {V E : Type*} [Fintype V] [LinearOrder V]

variable (edge : E → Sym2 V) (hnd : ∀ e, ¬(edge e).IsDiag)

local notation "inc" => (fun (e : E) (x : V) => x ∈ edge e)

variable (Q : Partial (fun (e : E) (x : V) => x ∈ edge e))

noncomputable def pickedEdge (x : V) (hx : x ∈ support inc Q.val) : E :=
  Classical.choose (Q.property.2 x hx)

omit [LinearOrder V] in
lemma pickedEdge_spec (x : V) (hx : x ∈ support inc Q.val) :
    pickedEdge edge Q x hx ∈ Q.val ∧ x ∈ edge (pickedEdge edge Q x hx) :=
  (Classical.choose_spec (Q.property.2 x hx)).1

omit [LinearOrder V] in
lemma pickedEdge_unique (x : V) (hx : x ∈ support inc Q.val) (e : E)
    (he : e∈Q.val) (hxe : x ∈ edge e) : e=pickedEdge edge Q x hx :=
  (Classical.choose_spec (Q.property.2 x hx)).2 e ⟨he,hxe⟩

noncomputable def partialMateFun (x : V) : V :=
  if hx : x∈support inc Q.val then Sym2.Mem.other (pickedEdge_spec edge Q x hx).2 else x

lemma partialMateFun_out (x : V) (hx : x∉support inc Q.val) : partialMateFun edge Q x=x := by
  simp [partialMateFun,hx]

include hnd in
lemma partialMateFun_ne (x : V) (hx : x∈support inc Q.val) : partialMateFun edge Q x≠x := by
  simp only [partialMateFun,dite_eq_left hx]
  exact Sym2.other_ne (hnd _) _

lemma partialMateFun_pair (x : V) (hx : x∈support inc Q.val) :
    s(x,partialMateFun edge Q x)=edge (pickedEdge edge Q x hx) := by
  simp only [partialMateFun,dite_eq_left hx]
  exact Sym2.other_spec _

lemma partialMateFun_incident (e : E) (he : e∈Q.val) (x : V) (hx : x∈edge e) :
    s(x,partialMateFun edge Q x)=edge e := by
  have hxQ := (mem_support inc Q.val x).mpr ⟨e,he,hx⟩
  rw [partialMateFun_pair edge Q x hxQ,←pickedEdge_unique edge Q x hxQ e he hx]

include hnd in
lemma partialMateFun_involutive : Function.Involutive (partialMateFun edge Q) := by
  intro x
  by_cases hx : x∈support inc Q.val
  · have h₁ := partialMateFun_pair edge Q x hx
    have hi : partialMateFun edge Q x ∈ edge (pickedEdge edge Q x hx) := by rw [←h₁]; simp
    have h₂ := partialMateFun_incident edge Q (pickedEdge edge Q x hx)
      (pickedEdge_spec edge Q x hx).1 _ hi
    rcases Sym2.eq_iff.mp (h₂.trans h₁.symm) with h | h
    · exact False.elim (partialMateFun_ne edge hnd Q x hx h.1)
    · exact h.2
  · rw [partialMateFun_out edge Q x hx,partialMateFun_out edge Q x hx]

noncomputable def partialMate : Mate V := ⟨partialMateFun edge Q,partialMateFun_involutive edge hnd Q⟩

lemma partialMate_holes : HasHoles (partialMate edge hnd Q) (support inc Q.val)ᶜ := by
  intro x
  change partialMateFun edge Q x=x ↔ _
  rw [Finset.mem_compl]
  constructor
  · intro h hx; exact partialMateFun_ne edge hnd Q x hx h
  · exact partialMateFun_out edge Q x

lemma partialMate_low (e : E) (he : e∈Q.val) :
    partialMateFun edge Q (edgeLow (edge e))=edgeHigh (edge e) := by
  have h := partialMateFun_incident edge Q e he _ (edgeLow_mem _)
  exact Sym2.congr_right.mp (h.trans (edge_low_high (edge e)).symm)

lemma partial_low_mem (e : E) (he : e∈Q.val) :
    edgeLow (edge e) ∈ univ.filter (fun x => x < (partialMate edge hnd Q).val x) := by
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change edgeLow (edge e) < partialMateFun edge Q (edgeLow (edge e))
  rw [partialMate_low edge Q e he]
  exact edgeLow_lt_high _ (hnd e)

lemma partial_low_injective (e : E) (he : e∈Q.val) (f : E) (hf : f∈Q.val)
    (h : edgeLow (edge e)=edgeLow (edge f)) : e=f := by
  have hx := edgeLow_mem (edge e)
  exact Q.property.unique (Q.property.1 e he _ hx) he hx hf (h.symm ▸ edgeLow_mem (edge f))

lemma partial_low_surjective (x : V)
    (hx : x ∈ univ.filter (fun x => x < (partialMate edge hnd Q).val x)) :
    ∃ e, ∃ _ : e∈Q.val, edgeLow (edge e)=x := by
  have hx' : x < partialMateFun edge Q x := (Finset.mem_filter.mp hx).2
  have hcov : x∈support inc Q.val := by
    by_contra hn
    rw [partialMateFun_out edge Q x hn] at hx'
    exact lt_irrefl _ hx'
  refine ⟨pickedEdge edge Q x hcov,(pickedEdge_spec edge Q x hcov).1,?_⟩
  rw [←partialMateFun_pair edge Q x hcov,edgeLow_mk,min_eq_left hx'.le]

include hnd in
lemma partial_card : (support inc Q.val).card=2*Q.val.card := by
  have hcard := Finset.card_bij (fun e _ => edgeLow (edge e))
    (partial_low_mem edge hnd Q) (partial_low_injective edge Q)
    (partial_low_surjective edge hnd Q)
  have hmate := mate_edge_count (partialMate edge hnd Q) (support inc Q.val)
    (partialMate_holes edge hnd Q)
  omega

include hnd in
lemma partial_even : Even (support inc Q.val).card := by
  rw [partial_card edge hnd Q]
  exact even_two_mul _

end

section

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

noncomputable local instance edgeLowCardinalityBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

noncomputable def bagEdgeSigmaEquiv : BagEdge bags ≃
    Σ s : {s : Sym2 V // ¬s.IsDiag}, {l : L // ∀ x, x∈s.val → l∈bags x} where
  toFun e := ⟨⟨e.val.val.1,e.val.property⟩,⟨e.val.val.2,e.property⟩⟩
  invFun a := ⟨⟨(a.1.val,a.2.val),a.1.property⟩,a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

open Finset MatchingFPRAS.Switching

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

noncomputable local instance edgeLowInflationBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

end MatchingFPRAS.Transport

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma edge_incident_internal (q : E × Fin (m+1)) (e : E) (i : Fin m) :
    Sum.inr (e,i) ∈ edge u v m q.1 q.2 ↔ q=(e,i.castSucc) ∨ q=(e,i.succ) := by
  simp only [edge,Sym2.mem_iff,eq_comm (a := Sum.inr _) ]
  rw [atVertex_eq_inr_iff,atVertex_eq_inr_iff]
  simp only [Fin.val_castSucc,Fin.val_succ,Prod.ext_iff]
  constructor
  · rintro (⟨h,h'⟩|⟨h,h'⟩)
    · exact Or.inr ⟨h,Fin.ext h'⟩
    · exact Or.inl ⟨h,Fin.ext (show q.2.val=i.val by omega)⟩
  · rintro (⟨h,h'⟩|⟨h,h'⟩)
    · exact Or.inr ⟨h,by have := congrArg Fin.val h'; simpa using this⟩
    · exact Or.inl ⟨h,by have := congrArg Fin.val h'; simpa using this⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma edge_incident_terminal (q : E × Fin (m+1)) (x : V) :
    Sum.inl x ∈ edge u v m q.1 q.2 ↔
      (q.2=0 ∧ u q.1=x) ∨ (q.2=Fin.last m ∧ v q.1=x) := by
  simp only [edge,Sym2.mem_iff,eq_comm (a := Sum.inl _)]
  rw [first_vertex_terminal,second_vertex_terminal]
  simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last]

noncomputable def selectedSet (b : E → Selection m) : Finset (E × Fin (m+1)) := by
  classical
  exact univ.filter fun q => b q.1 q.2=true

omit [DecidableEq E] in
@[simp] lemma mem_selectedSet (b : E → Selection m) (q : E × Fin (m+1)) :
    q∈selectedSet m b ↔ b q.1 q.2=true := by
  simp [selectedSet]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma internal_unique_iff (b : E → Selection m) (e : E) (i : Fin m) :
    (∃! q, q∈selectedSet m b ∧ Sum.inr (e,i)∈edge u v m q.1 q.2) ↔
      b e i.castSucc ≠ b e i.succ := by
  simp only [mem_selectedSet,edge_incident_internal]
  have hne : i.castSucc≠i.succ := by intro h; have := congrArg Fin.val h; simp at this
  cases h₁ : b e i.castSucc <;> cases h₂ : b e i.succ <;> simp only [ne_eq,Bool.false_eq_true,
    not_false_eq_true,Bool.true_eq_false,not_true_eq_false,iff_false,iff_true]
  · rintro ⟨q,hq,_⟩; rcases hq.2 with rfl|rfl <;> simp_all
  · refine ⟨(e,i.succ),⟨h₂,Or.inr rfl⟩,?_⟩
    rintro ⟨f,j⟩ ⟨hs,hq⟩
    rcases hq with hq|hq
    · cases hq; simp_all
    · exact hq
  · refine ⟨(e,i.castSucc),⟨h₁,Or.inl rfl⟩,?_⟩
    rintro ⟨f,j⟩ ⟨hs,hq⟩
    rcases hq with hq|hq
    · exact hq
    · cases hq; simp_all
  · rintro ⟨q,hq,hu⟩
    have h := (hu (e,i.castSucc) ⟨h₁,Or.inl rfl⟩).trans (hu (e,i.succ) ⟨h₂,Or.inr rfl⟩).symm
    exact hne (congrArg Prod.snd h)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma terminal_selected_iff (b : E → Selection m) (q : E × Fin (m+1)) (x : V) :
    q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2 ↔
    (q.2=0 ∧ b q.1 0=true ∧ u q.1=x) ∨
      (q.2=Fin.last m ∧ b q.1 (Fin.last m)=true ∧ v q.1=x) := by
  rw [mem_selectedSet,edge_incident_terminal]
  constructor
  · rintro ⟨hs, (⟨h₀,hu⟩|⟨hm,hv⟩)⟩
    · exact Or.inl ⟨h₀,h₀ ▸ hs,hu⟩
    · exact Or.inr ⟨hm,hm ▸ hs,hv⟩
  · rintro (⟨h₀,hs,hu⟩|⟨hm,hs,hv⟩)
    · exact ⟨h₀ ▸ hs,Or.inl ⟨h₀,hu⟩⟩
    · exact ⟨hm ▸ hs,Or.inr ⟨hm,hv⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma terminal_unique_iff (huv : ∀ e,u e≠v e) (b : E → Selection m) (x : V) :
    (∃! q, q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2) ↔
    (∃! e, Uses u v b e x) := by
  constructor
  · rintro ⟨q,hq,hunique⟩
    rw [terminal_selected_iff] at hq
    have huse : Uses u v b q.1 x := by rcases hq with h|h; exact Or.inl h.2; exact Or.inr h.2
    refine ⟨q.1,huse,?_⟩
    intro f hf
    rcases hf with hf|hf
    · exact congrArg Prod.fst (hunique (f,0) ((terminal_selected_iff _ _ _ _ _ _).mpr (Or.inl ⟨rfl,hf⟩)))
    · exact congrArg Prod.fst (hunique (f,Fin.last m) ((terminal_selected_iff _ _ _ _ _ _).mpr (Or.inr ⟨rfl,hf⟩)))
  · rintro ⟨e,he,hu⟩
    have uniq (i : Fin (m+1)) (hi : (e,i)∈selectedSet m b ∧ Sum.inl x∈edge u v m e i)
        (q : E × Fin (m+1)) (hq : q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2) : q=(e,i) := by
      rw [terminal_selected_iff] at hi hq
      have hf : q.1=e := hu q.1 (by rcases hq with h|h; exact Or.inl h.2; exact Or.inr h.2)
      apply Prod.ext hf
      rcases hi with hi|hi <;> rcases hq with hq|hq
      · exact hq.1.trans hi.1.symm
      · exact False.elim (huv e (hi.2.2.trans (hf ▸ hq.2.2).symm))
      · exact False.elim (huv e ((hf ▸ hq.2.2).trans hi.2.2.symm))
      · exact hq.1.trans hi.1.symm
    rcases he with he|he
    · have hi := (terminal_selected_iff u v m b (e,0) x).mpr (Or.inl ⟨rfl,he⟩)
      exact ⟨(e,0),hi,uniq 0 hi⟩
    · have hi := (terminal_selected_iff u v m b (e,Fin.last m) x).mpr (Or.inr ⟨rfl,he⟩)
      exact ⟨(e,Fin.last m),hi,uniq _ hi⟩

omit [DecidableEq V] [DecidableEq E] in
theorem family_iff_matching (huv : ∀ e,u e≠v e) (R : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) :
    FamilyHoles u v m R U b ↔
    MatchingOn (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (selectedSet m b) (survivors m R U) := by
  constructor
  · intro hb
    constructor
    · intro q hq x hx
      cases x with
      | inl x =>
        rw [mem_survivors_terminal]
        intro hr
        have huse : Uses u v b q.1 x := by
          rcases (terminal_selected_iff u v m b q x).mp ⟨hq,hx⟩ with h|h
          · exact Or.inl h.2
          · exact Or.inr h.2
        exact hb.2.1 x hr q.1 huse
      | inr ei =>
        rcases ei with ⟨e,i⟩
        rw [mem_survivors_internal]
        intro hi
        have hd := hb.1 e i
        simp only [hi,ite_eq_left] at hd
        rcases (edge_incident_internal u v m q e i).mp hx with rfl|rfl
        · have h := (mem_selectedSet m b _).mp hq; simp_all
        · have h := (mem_selectedSet m b _).mp hq; simp_all
    · intro x hx
      cases x with
      | inl x => exact (terminal_unique_iff u v m huv b x).mpr (hb.2.2 x ((mem_survivors_terminal m R U x).mp hx))
      | inr ei =>
        rcases ei with ⟨e,i⟩
        apply (internal_unique_iff u v m b e i).mpr
        simpa only [Valid,ite_eq_right ((mem_survivors_internal m R U e i).mp hx)] using hb.1 e i
  · intro hM
    refine ⟨?_,?_,?_⟩
    · intro e i
      split_ifs with hi
      · constructor
        · cases h : b e i.castSucc
          · rfl
          · have hx := hM.1 (e,i.castSucc) ((mem_selectedSet m b _).mpr h) (Sum.inr (e,i))
              ((edge_incident_internal u v m _ e i).mpr (Or.inl rfl))
            exact False.elim (((mem_survivors_internal m R U e i).mp hx) hi)
        · cases h : b e i.succ
          · rfl
          · have hx := hM.1 (e,i.succ) ((mem_selectedSet m b _).mpr h) (Sum.inr (e,i))
              ((edge_incident_internal u v m _ e i).mpr (Or.inr rfl))
            exact False.elim (((mem_survivors_internal m R U e i).mp hx) hi)
      · exact (internal_unique_iff u v m b e i).mp (hM.2 (Sum.inr (e,i)) ((mem_survivors_internal m R U e i).mpr hi))
    · intro x hx e he
      have hq : ∃ q, q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2 := by
        rcases he with he|he
        · exact ⟨(e,0),(terminal_selected_iff u v m b _ x).mpr (Or.inl ⟨rfl,he⟩)⟩
        · exact ⟨(e,Fin.last m),(terminal_selected_iff u v m b _ x).mpr (Or.inr ⟨rfl,he⟩)⟩
      obtain ⟨q,hq,hqx⟩ := hq
      exact ((mem_survivors_terminal m R U x).mp (hM.1 q hq _ hqx)) hx
    · intro x hx
      exact (terminal_unique_iff u v m huv b x).mp (hM.2 (Sum.inl x) ((mem_survivors_terminal m R U x).mpr hx))

noncomputable def selectionEquiv : (E → Selection m) ≃ Finset (E × Fin (m+1)) where
  toFun := selectedSet m
  invFun S e i := decide ((e,i)∈S)
  left_inv b := by
    funext e i
    simp [mem_selectedSet]
  right_inv S := by
    ext ⟨e,i⟩
    simp

noncomputable def realMatchingEquiv (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m)) :
    {b : E → Selection m // FamilyHoles u v m R U b} ≃
    Matchings (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (survivors m R U) :=
  (selectionEquiv (E := E) m).subtypeEquiv (family_iff_matching u v m huv R U)

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_MatchingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

include hinc in
omit [Fintype V] [Fintype E] [Fintype F] [DecidableEq V] [DecidableEq E] [DecidableEq F] in
lemma matching_map_iff [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F] (S : Finset E) (U : Finset V) :
    MatchingOn inc' (S.map f) U ↔ MatchingOn inc S U := by
  constructor
  · intro hM
    refine ⟨fun e he x hx => hM.1 (f e) (Finset.mem_map.mpr ⟨e,he,rfl⟩) x ((hinc e x).mpr hx),?_⟩
    intro x hx
    obtain ⟨q,⟨hq,hqx⟩,hu⟩ := hM.2 x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
    refine ⟨e,⟨he,(hinc e x).mp hqx⟩,?_⟩
    intro e' he'
    apply f.injective
    exact hu (f e') ⟨Finset.mem_map.mpr ⟨e',he'.1,rfl⟩,(hinc e' x).mpr he'.2⟩
  · intro hM
    constructor
    · intro q hq x hx
      obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
      exact hM.1 e he x ((hinc e x).mp hx)
    · intro x hx
      obtain ⟨e,⟨he,hex⟩,hu⟩ := hM.2 x hx
      refine ⟨f e,⟨Finset.mem_map.mpr ⟨e,he,rfl⟩,(hinc e x).mpr hex⟩,?_⟩
      intro q hq
      obtain ⟨e',he',rfl⟩ := Finset.mem_map.mp hq.1
      exact congrArg f (hu e' ⟨he',(hinc e' x).mp hq.2⟩)

noncomputable def matchingMap (U : Finset V) (M : Matchings inc U) : Matchings inc' U :=
  ⟨M.val.map f,(matching_map_iff inc inc' f hinc M.val U).mpr M.property⟩

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TierClamp
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def cycleMove (p : PM inc × PM inc) (S : Finset E) : PM inc × PM inc := by
  classical
  exact if h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val) then
    (⟨exchange p.1.val p.2.val S, exchange_matching p.1.property p.2.property
        (component_exchange_compatible h)⟩,
     ⟨exchange p.2.val p.1.val S, exchange_matching p.2.property p.1.property
        (component_exchange_compatible h).symm⟩) else p

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_val (p : PM inc × PM inc) (S : Finset E)
    (h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)) :
    (cycleMove p S).1.val = exchange p.1.val p.2.val S ∧
    (cycleMove p S).2.val = exchange p.2.val p.1.val S := by
  classical
  simp only [cycleMove,dite_eq_left h,Subtype.coe_mk,and_self]

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_union (p : PM inc × PM inc) (S : Finset E) :
    (cycleMove p S).1.val ∪ (cycleMove p S).2.val = p.1.val ∪ p.2.val := by
  classical
  unfold cycleMove
  split_ifs with h
  · exact exchange_union _ _ _
  · rfl

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_inter (p : PM inc × PM inc) (S : Finset E) :
    (cycleMove p S).1.val ∩ (cycleMove p S).2.val = p.1.val ∩ p.2.val := by
  classical
  unfold cycleMove
  split_ifs with h
  · exact exchange_inter _ _ _
  · rfl

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_discrepancy (p : PM inc × PM inc) (S : Finset E) :
    discrepancyComponents (cycleMove p S).1 (cycleMove p S).2 = discrepancyComponents p.1 p.2 := by
  classical
  unfold discrepancyComponents
  rw [cycleMove_union,cycleMove_inter]

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_involution (p : PM inc × PM inc) (S : Finset E) :
    cycleMove (cycleMove p S) S = p := by
  classical
  by_cases h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)
  · have h' : S ∈ components (inc := inc) ((cycleMove p S).1.val ∪ (cycleMove p S).2.val) := by
      rwa [cycleMove_union]
    apply Prod.ext <;> apply Subtype.ext
    · rw [(cycleMove_val _ _ h').1,(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2]
      exact exchange_involution _ _ _
    · rw [(cycleMove_val _ _ h').2,(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2]
      exact exchange_involution _ _ _
  · simp only [cycleMove,dite_eq_right h]

noncomputable def cycleTerm (p q : PM inc × PM inc) (S : Finset E) : ℝ := by
  classical
  exact if S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q then
    ((discrepancyComponents p.1 p.2).card : ℝ)⁻¹ else 0

noncomputable def cycleProposal (p q : PM inc × PM inc) : ℝ := by
  classical
  exact if (discrepancyComponents p.1 p.2).Nonempty then ∑ S, cycleTerm p q S
    else if p = q then 1 else 0

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_symmetric (p q : PM inc × PM inc) (S : Finset E) :
    cycleTerm p q S = cycleTerm q p S := by
  classical
  have he : (S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q) ↔
      (S ∈ discrepancyComponents q.1 q.2 ∧ cycleMove q S = p) := by
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨by rwa [cycleMove_discrepancy],cycleMove_involution _ _⟩
    · rintro ⟨h,rfl⟩
      exact ⟨by rwa [cycleMove_discrepancy],cycleMove_involution _ _⟩
  unfold cycleTerm
  by_cases h : S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q
  · rw [ite_eq_left h,ite_eq_left (he.mp h),← h.2,cycleMove_discrepancy]
  · rw [ite_eq_right h,ite_eq_right (mt he.mpr h)]

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_nonneg (p q : PM inc × PM inc) (S : Finset E) : 0 ≤ cycleTerm p q S := by
  classical
  unfold cycleTerm
  split_ifs <;> positivity

omit [DecidableEq V] in
lemma cycleTerm_sum (p : PM inc × PM inc) (S : Finset E) :
    (∑ q, cycleTerm p q S) = if S ∈ discrepancyComponents p.1 p.2 then
      ((discrepancyComponents p.1 p.2).card : ℝ)⁻¹ else 0 := by
  classical
  by_cases h : S ∈ discrepancyComponents p.1 p.2
  · simp only [cycleTerm,h,true_and]
    simp
  · simp [cycleTerm,h]

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_zero (p q : PM inc × PM inc) (h : ¬(discrepancyComponents p.1 p.2).Nonempty)
    (S : Finset E) : cycleTerm p q S = 0 := by
  classical
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  simp [cycleTerm,he]

omit [DecidableEq V] in
lemma cycleProposal_nonneg (p q : PM inc × PM inc) : 0 ≤ cycleProposal p q := by
  classical
  unfold cycleProposal
  split_ifs
  · exact Finset.sum_nonneg (fun S _ => cycleTerm_nonneg p q S)
  · norm_num
  · norm_num

omit [DecidableEq V] in
lemma cycleProposal_row (p : PM inc × PM inc) : (∑ q, cycleProposal p q) = 1 := by
  classical
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h]
    rw [Finset.sum_comm]
    simp_rw [cycleTerm_sum]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (Finset.card_pos.mpr h))
  · simp [cycleProposal,h]

omit [DecidableEq V] in
lemma cycleProposal_symmetric (p q : PM inc × PM inc) : cycleProposal p q = cycleProposal q p := by
  classical
  by_cases hp : (discrepancyComponents p.1 p.2).Nonempty <;>
    by_cases hq : (discrepancyComponents q.1 q.2).Nonempty
  · simp only [cycleProposal,ite_eq_left hp,ite_eq_left hq,cycleTerm_symmetric p q]
  · have hpq : p ≠ q := by rintro rfl; exact hq hp
    simp only [cycleProposal,ite_eq_left hp,ite_eq_right hq,ite_eq_right (Ne.symm hpq)]
    apply Finset.sum_eq_zero; intro S _
    rw [cycleTerm_symmetric,cycleTerm_zero _ _ hq]
  · exact (by
      have hpq : q ≠ p := by rintro rfl; exact hp hq
      simp only [cycleProposal,ite_eq_right hp,ite_eq_left hq,ite_eq_right (Ne.symm hpq)]
      symm; apply Finset.sum_eq_zero; intro S _
      rw [cycleTerm_symmetric,cycleTerm_zero _ _ hp])
  · simp only [cycleProposal,ite_eq_right hp,ite_eq_right hq,eq_comm]

end

section

open Finset

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance tierClampBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

namespace BagEdge

noncomputable def parallels (e : BagEdge bags) : Finset (BagEdge bags) := by
  classical
  exact Finset.univ.filter (fun f => f.val.val.1 = e.val.val.1)

omit [DecidableEq L] in
lemma parallels_card_le (hb : ∀ v, (bags v).card ≤ 2) (e : BagEdge bags) :
    (parallels e).card ≤ 2 := by
  classical
  obtain ⟨v,hv⟩ := e.exists_incident
  let colorMap : ↥(parallels e) → ↥(bags v) := fun f => ⟨f.val.color, by
    apply f.val.color_mem
    change v ∈ f.val.val.val.1
    rw [(Finset.mem_filter.mp f.property).2]
    exact hv⟩
  have hinj : Function.Injective colorMap := by
    intro f g h
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp f.property).2.trans (Finset.mem_filter.mp g.property).2.symm
    · exact congrArg Subtype.val h
  have hc : (parallels e).card ≤ (bags v).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective colorMap hinj
  exact hc.trans (hb v)

end BagEdge

end

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.symm {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    ColorChange ends B A := by
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  exact ⟨f,e,R,hef.symm,hB,hA⟩

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.edit {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    ∃ e ∈ A.val, ∃ f, ends f = ends e ∧ B.val = insert f (A.val.erase e) := by
  classical
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  have he : e ∈ A.val := by rw [hA]; simp
  refine ⟨e,he,f,hef.symm,?_⟩
  by_cases h : e = f
  · subst f
    rw [Finset.insert_erase he]
    exact hB.trans hA.symm
  · obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := Sym2.inductionOn (ends e) (fun u v => ⟨u,by simp⟩)
    have hr : e ∉ R := by
      intro hr
      exact h (B.property.unique (Finset.mem_univ v) (by rw [hB]; simp [hr]) hv
        (by rw [hB]; simp) (hef ▸ hv))
    rw [hA,hB]
    ext a
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,Finset.mem_erase]
    by_cases ha : a = e
    · subst a; simp [hr,h]
    · tauto

lemma colorDestinations_card_bound
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (colorDestinations ends A).card ≤ 2*A.val.card := by
  classical
  let options (e : E) : Finset (Finset E) :=
    (Finset.univ.filter (fun f => ends f = ends e)).image (fun f => insert f (A.val.erase e))
  have hsub : (colorDestinations ends A).image Subtype.val ⊆ A.val.biUnion options := by
    intro B hB
    obtain ⟨C,hC,hCB⟩ := Finset.mem_image.mp hB
    rw [← hCB]
    obtain ⟨e,he,f,hf,hval⟩ := ColorChange.edit ends ((Finset.mem_filter.mp hC).2)
    apply Finset.mem_biUnion.mpr
    exact ⟨e,he,Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,hval.symm⟩⟩
  have hi : (colorDestinations ends A).card = ((colorDestinations ends A).image Subtype.val).card := by
    symm; exact Finset.card_image_of_injective _ Subtype.val_injective
  calc
    _ = _ := hi
    _ ≤ (A.val.biUnion options).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ A.val, (options e).card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ A.val, 2 := Finset.sum_le_sum (fun e _ => (Finset.card_image_le).trans (hpar e))
    _ = _ := by simp [Nat.mul_comm]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelationDestinations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma relationProposal_row (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) :
    (∑ b, relationProposal R d a b) = 1 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  have hh : (∑ b ∈ Finset.univ.erase a, relationProposal R d a b) =
      ∑ b, relationOff R d a b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),relationOff_self,add_zero]
    apply Finset.sum_congr rfl; intro b hb
    simp only [relationProposal,ite_eq_right (Finset.ne_of_mem_erase hb).symm]
  rw [hh]
  simp only [relationProposal,ite_true]
  ring

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def colorProposal (A B : PM (fun e v => v ∈ ends e)) : ℝ :=
  relationProposal (ColorChange ends) (Fintype.card V) A B

omit [DecidableEq V] in
lemma colorProposal_row (A : PM (fun e v => v ∈ ends e)) : (∑ B, colorProposal ends A B) = 1 :=
  relationProposal_row _ _ _

omit [DecidableEq V] in
lemma colorProposal_symmetric (A B : PM (fun e v => v ∈ ends e)) :
    colorProposal ends A B = colorProposal ends B A :=
  relationProposal_symmetric _ _ (fun _ _ => ⟨ColorChange.symm ends,ColorChange.symm ends⟩) A B

lemma colorProposal_nonneg (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) : 0 ≤ colorProposal ends A B := by
  classical
  apply relationProposal_nonneg
  intro C
  calc
    _ ≤ (colorDestinations ends C).card := Finset.card_le_card (by
      intro D hD; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hD).2).2⟩)
    _ ≤ 2*C.val.card := colorDestinations_card_bound ends hpar C
    _ = _ := C.twice_card ends hloop

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.symm {A B : PM inc} (h : TwoEdgeSwitch A B) : TwoEdgeSwitch B A := by
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  refine ⟨(fun i => v (i+1)),(fun i => e (i+1)),R,?_,?_,?_,?_⟩
  · exact hv.comp (fun _ _ h => add_right_cancel h)
  · intro i x
    simpa only [add_assoc] using he (i+1) x
  · simpa using hB
  · simpa [Finset.pair_comm] using hA

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.normal_form {A B : PM inc} (h : TwoEdgeSwitch A B) :
    ∃ (v : Fin 4 → V) (e : Fin 4 → E), Function.Injective v ∧
      (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
      e 0 ≠ e 2 ∧ {e 0,e 2} ⊆ A.val ∧
      B.val = (A.val \ {e 0,e 2}) ∪ {e 1,e 3} := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  have hne (i j : Fin 4) (hij : i ≠ j) (hij' : i ≠ j+1) : e i ≠ e j := by
    intro h
    have hi := (he i (v i)).mpr (Or.inl rfl)
    rw [h] at hi
    rcases (he j (v i)).mp hi with h | h
    · exact hij (hv h)
    · exact hij' (hv h)
  have h01 : e 0 ≠ e 1 := hne 0 1 (by decide) (by decide)
  have h23 : e 2 ≠ e 3 := hne 2 3 (by decide) (by decide)
  have h02 : e 0 ≠ e 2 := hne 0 2 (by decide) (by decide)
  have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
  have hb1 : e 1 ∈ B.val := by rw [hB]; simp
  have hb3 : e 3 ∈ B.val := by rw [hB]; simp
  have hr0 : e 0 ∉ R := by
    intro hr
    exact h01 (B.property.unique (Finset.mem_univ (v 1)) (hRB hr)
      ((he 0 (v 1)).mpr (Or.inr rfl)) hb1 ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr2 : e 2 ∉ R := by
    intro hr
    exact h23 (B.property.unique (Finset.mem_univ (v 3)) (hRB hr)
      ((he 2 (v 3)).mpr (Or.inr rfl)) hb3 ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hR : A.val \ {e 0,e 2} = R := by
    rw [hA]
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · tauto
    · intro ha
      exact ⟨Or.inl ha,by rintro (rfl|rfl) <;> contradiction⟩
  exact ⟨v,e,hv,he,h02,by rw [hA]; exact Finset.subset_union_right,by rw [hR]; exact hB⟩

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

lemma switch_mem_options {A B : PM (fun e v => v ∈ ends e)} (h : TwoEdgeSwitch A B) :
    ∃ I ∈ A.val.powersetCard 2, B.val ∈ switchOptions ends A.val I := by
  classical
  obtain ⟨v,e,hv,he,h02,hsub,hB⟩ := h.normal_form
  let I : Finset E := {e 0,e 2}
  have hI : I.card = 2 := by simp [I,h02]
  refine ⟨I,Finset.mem_powersetCard.mpr ⟨hsub,hI⟩,?_⟩
  have hend (i : Fin 4) : ends (e i) = s(v i,v (i+1)) :=
    inc_eq_ends ends (e i) (v i) (v (i+1))
      (fun h => (by omega : i ≠ i+1) (hv h)) (he i)
  unfold switchOptions
  rw [dite_eq_left hI]
  dsimp only
  obtain ⟨hne,hr⟩ := pairRep_spec I hI
  have h1 : (pairRep I hI).1 = e 0 ∨ (pairRep I hI).1 = e 2 := by
    have : (pairRep I hI).1 ∈ I := by
      exact (congrArg (fun S : Finset E => (pairRep I hI).1 ∈ S) hr).mpr (by simp)
    simpa [I] using this
  have h2 : (pairRep I hI).2 = e 0 ∨ (pairRep I hI).2 = e 2 := by
    have : (pairRep I hI).2 ∈ I := by
      exact (congrArg (fun S : Finset E => (pairRep I hI).2 ∈ S) hr).mpr (by simp)
    simpa [I] using this
  rw [hB]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact False.elim (hne (h1.trans h2.symm))
  · rw [h1,h2]
    exact mem_pairOptions_of_endpoints ends (A.val\I) (e 0) (e 2) (e 1) (e 3)
      (v 0) (v 1) (v 2) (v 3) (hend 0) (hend 2) (hend 1) (hend 3)
  · rw [h1,h2,Finset.pair_comm (e 1) (e 3)]
    exact mem_pairOptions_of_endpoints ends (A.val\I) (e 2) (e 0) (e 3) (e 1)
      (v 2) (v 3) (v 0) (v 1) (hend 2) (hend 0) (hend 3) (hend 1)
  · exact False.elim (hne (h1.trans h2.symm))

lemma switchDestinations_card_bound
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) :
    (switchDestinations A).card ≤ 8 * A.val.card.choose 2 := by
  classical
  have hsub : (switchDestinations A).image Subtype.val ⊆
      (A.val.powersetCard 2).biUnion (switchOptions ends A.val) := by
    intro B hB
    obtain ⟨C,hC,hCB⟩ := Finset.mem_image.mp hB
    rw [← hCB]
    obtain ⟨I,hI,hB⟩ := switch_mem_options ends ((Finset.mem_filter.mp hC).2)
    exact Finset.mem_biUnion.mpr ⟨I,hI,hB⟩
  calc
    _ = ((switchDestinations A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((A.val.powersetCard 2).biUnion (switchOptions ends A.val)).card := Finset.card_le_card hsub
    _ ≤ ∑ I ∈ A.val.powersetCard 2, (switchOptions ends A.val I).card := Finset.card_biUnion_le
    _ ≤ ∑ I ∈ A.val.powersetCard 2, 8 :=
      Finset.sum_le_sum fun I _ => switchOptions_card_le ends hpar A.val I
    _ = _ := by simp [Nat.mul_comm]

end

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def switchProposal (A B : PM (fun e v => v ∈ ends e)) : ℝ :=
  relationProposal TwoEdgeSwitch (8*(Fintype.card V/2).choose 2) A B

omit [DecidableEq V] in
lemma switchProposal_row (A : PM (fun e v => v ∈ ends e)) : (∑ B, switchProposal ends A B) = 1 :=
  relationProposal_row _ _ _

omit [DecidableEq V] in
lemma switchProposal_symmetric (A B : PM (fun e v => v ∈ ends e)) :
    switchProposal ends A B = switchProposal ends B A :=
  relationProposal_symmetric _ _ (fun _ _ => ⟨TwoEdgeSwitch.symm,TwoEdgeSwitch.symm⟩) A B

lemma switchProposal_nonneg (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) : 0 ≤ switchProposal ends A B := by
  classical
  apply relationProposal_nonneg
  intro C
  have hn : Fintype.card V/2 = C.val.card := by have := C.twice_card ends hloop; omega
  calc
    _ ≤ (switchDestinations C).card := Finset.card_le_card (by
      intro D hD; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hD).2).2⟩)
    _ ≤ 8*C.val.card.choose 2 := switchDestinations_card_bound ends hpar C
    _ = _ := by rw [hn]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_LocalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma metropolisCapacity_symmetric (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : metropolisCapacity P π a b = metropolisCapacity P π b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [metropolisCapacity,ite_eq_right h,ite_eq_right (Ne.symm h)]
    exact offCapacity_symmetric P π a b

lemma metropolisCapacity_row (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a : Ω) : (∑ b, metropolisCapacity P π a b) = π a := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  have he : (∑ b ∈ Finset.univ.erase a, metropolisCapacity P π a b) =
      ∑ b ∈ Finset.univ.erase a, offCapacity P π a b := by
    apply Finset.sum_congr rfl; intro b hb
    rw [metropolisCapacity,ite_eq_right (Finset.ne_of_mem_erase hb).symm]
  rw [he]
  simp only [metropolisCapacity,ite_true]
  ring

lemma metropolisCapacity_col (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (b : Ω) : (∑ a, metropolisCapacity P π a b) = π b := by
  simp_rw [metropolisCapacity_symmetric P π]
  exact metropolisCapacity_row P π b

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def pairProposalRaw (a b : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) : ℝ :=
  (firstLift (switchProposal ends) a b + firstLift (colorProposal ends) a b + cycleProposal a b)/3

noncomputable def pairProposal (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2) :
    SymmetricProposal (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) where
  q := pairProposalRaw ends
  nonneg a b := by
    unfold pairProposalRaw firstLift
    have hs := switchProposal_nonneg ends hloop hpar a.1 b.1
    have hc := colorProposal_nonneg ends hloop hpar a.1 b.1
    have hy := cycleProposal_nonneg a b
    split_ifs <;> positivity
  row a := by
    unfold pairProposalRaw
    rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_add_distrib,
      firstLift_row _ (switchProposal_row ends),firstLift_row _ (colorProposal_row ends),cycleProposal_row]
    norm_num
  symmetric a b := by
    unfold pairProposalRaw
    rw [firstLift_symmetric _ (switchProposal_symmetric ends),
      firstLift_symmetric _ (colorProposal_symmetric ends),cycleProposal_symmetric a b]

noncomputable def pairLaw (w z : E → ℝ) (a : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) : ℝ :=
  gibbs w a.1*gibbs z a.2

end

open Finset MatchingFPRAS.Replica

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePairProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

noncomputable def treePairProposal : SymmetricProposal (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) :=
  pairProposal (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
    (fun e => BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e)

noncomputable def treePairLaw (w z : BagEdge bags → ℝ)
    (a : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) : ℝ := gibbs w a.1*gibbs z a.2

noncomputable def treePairEnergy (w z : BagEdge bags → ℝ)
    (f : (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) → ℝ) : ℝ := by
  classical
  exact localEnergy (metropolisCapacity (treePairProposal hbags hG) (treePairLaw w z)) f

end

section

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_1 : Fintype (BagEdge bags) := Fintype.ofFinite _

end

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance instFintypeBagEdge_2 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_3 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable def slotWeight {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q) (e : BagEdge bags) : ℝ :=
  tierClamp (tierBase V) (tier x) (w e)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_pos {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q) (e : BagEdge bags) :
    0 < slotWeight w x e := tierClamp_pos (tierBase_pos V) _ _

noncomputable def slotLaw {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (A : PM (BagEdge.Incident (bags := bags))) : ℝ := gibbs (slotWeight w x) A

omit [DecidableEq V] [DecidableEq J] in
lemma slotLaw_pos {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (A : PM (BagEdge.Incident (bags := bags))) : 0 < slotLaw w x A := gibbs_pos _ (slotWeight_pos w x) A

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

noncomputable def treeLadderCapacity {T q : ℕ} (w : BagEdge bags → ℝ) (x y : Slot T q) :
    PairCapacity (slotLaw w) x y := by
  classical
  let π : (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) → ℝ :=
    fun a => slotLaw w x a.1*slotLaw w y a.2
  exact {
    q := metropolisCapacity (treePairProposal hbags hG) π
    nonneg := metropolisCapacity_nonneg _ _ (fun a => mul_nonneg (slotLaw_pos w x a.1).le (slotLaw_pos w y a.2).le)
    row := metropolisCapacity_row _ _
    col := metropolisCapacity_col _ _ }

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_4 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Evolve
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_5 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance instDecidableEqPMBagEdgeIncident : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

noncomputable def ladderLaw (w : BagEdge bags → ℝ) (T q : ℕ) :
    (Slot T q → PM (BagEdge.Incident (bags := bags))) → ℝ := density (slotLaw w)

noncomputable def ladderFlow
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (w : BagEdge bags → ℝ) (T q : ℕ) :
    (Slot T q → PM (BagEdge.Incident (bags := bags))) →
      (Slot T q → PM (BagEdge.Incident (bags := bags))) → ℝ :=
  scanFlow (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w)

noncomputable local instance instFintypeBagEdge_6 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance instDecidableEqPMBagEdgeIncident_1 : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def chosenEdge (A : PM inc) (v : V) : E :=
  Classical.choose (A.property.2 v (mem_univ v))

end

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_7 : Fintype (BagEdge bags) := Fintype.ofFinite _

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_8 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_LadderL
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance instFintypeBagEdge_10 : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance instDecidableEqPMBagEdgeIncident_2 : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

def probeWord (p : ℕ) : Selection (4*p) :=
  fun i => if i.val=2*p then false else alternating true i.val

@[simp] lemma probeWord_first (p : ℕ) (hp : 1≤p) : probeWord p 0=true := by
  simp [probeWord,show 0≠2*p by omega]

@[simp] lemma probeWord_last (p : ℕ) (hp : 1≤p) : probeWord p (Fin.last (4*p))=true := by
  simp [probeWord,show 4*p≠2*p by omega,alternating,Nat.mul_mod]


variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (p : ℕ) (hp : 1≤p) (e₀ : E)

def insertProbe (s : E → Bool) (e : E) : Selection (4*p) :=
  if e=e₀ then probeWord p else fun i => alternating (s e) i.val


end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

noncomputable def completionEquiv (hinc : ∀ e,∃ x,inc e x) (Q : Partial inc) :
    {M : Matchings inc univ // Q.val⊆M.val} ≃ Matchings inc (univ \ support inc Q.val) where
  toFun M := ⟨M.val.val \ Q.val,M.val.property.sdiff Q.property M.property⟩
  invFun M := ⟨⟨Q.val∪M.val,by
    have h := Q.property.union M.property (support_sdiff_disjoint inc Q.val)
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)] at h
    exact h⟩,Finset.subset_union_left⟩
  left_inv M := by
    apply Subtype.ext
    exact Subtype.ext (Finset.union_sdiff_of_subset M.property)
  right_inv M := by
    have hd := Q.property.disjoint_edges M.property hinc (support_sdiff_disjoint inc Q.val)
    exact Subtype.ext (Finset.union_sdiff_cancel_left hd)

noncomputable def conditional (part : E → I → ℝ) (M : Matchings inc univ)
    (m : ↥M.val → I) : ℝ := ∏ e : M.val,part e.val (m e)/collapse part e.val

end MatchingFPRAS.Marking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Tv
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

noncomputable local instance instFintypeBagEdge_11 : Fintype (BagEdge bags) := Fintype.ofFinite _

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EnlargementRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

variable {α β : Type*}

variable [DecidableEq α]

def Pairing.insert (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) : Pairing α where
  mate x := if hx : x=a then b else if hy : x=b then a else (p.mate ⟨x,hx,hy⟩).val
  involutive x := by
    by_cases hx : x=a
    · subst x; simp [hab]
    by_cases hy : x=b
    · subst x; simp [hab]
    simp only [dite_eq_right hx,dite_eq_right hy]
    rw [dite_eq_right (p.mate ⟨x,hx,hy⟩).property.1,dite_eq_right (p.mate ⟨x,hx,hy⟩).property.2]
    exact congrArg Subtype.val (p.involutive ⟨x,hx,hy⟩)
  no_fixed x := by
    by_cases hx : x=a
    · subst x; simpa using hab
    by_cases hy : x=b
    · subst x; simpa [hx] using hab.symm
    simp only [dite_eq_right hx,dite_eq_right hy]
    intro h
    exact p.no_fixed ⟨x,hx,hy⟩ (Subtype.ext h)

@[simp] lemma Pairing.insert_at (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) : (p.insert a b hab).mate a=b := by
  simp [Pairing.insert]

@[simp] lemma Pairing.insert_other (a b : α) (hab : b≠a)
    (p : Pairing {x : α // x≠a ∧ x≠b}) (x : {x : α // x≠a ∧ x≠b}) :
    (p.insert a b hab).mate x=(p.mate x).val := by
  simp [Pairing.insert,x.property.1,x.property.2]

noncomputable def Pairing.split (a : α) :
    Pairing α ≃ Σ b : {x : α // x≠a}, Pairing {x : α // x≠a ∧ x≠b.val} where
  toFun p := ⟨⟨p.mate a,p.no_fixed a⟩,p.remove a⟩
  invFun q := q.2.insert a q.1.val q.1.property
  left_inv p := by
    ext x
    by_cases hx : x=a
    · subst x; simp
    by_cases hy : x=p.mate a
    · subst x
      simp [Pairing.insert,p.no_fixed a,p.involutive a]
    · simp [Pairing.insert,hx,hy,Pairing.remove]
  right_inv q := by
    rcases q with ⟨⟨b,hb⟩,p⟩
    apply Sigma.ext (Subtype.ext (by simp))
    apply Pairing.subtype_hext
    · intro x; simp only [Pairing.insert_at]
    · intro x y hxy
      change (p.insert a b hb).mate x = (p.mate y).val
      rw [hxy]
      exact Pairing.insert_other a b hb p y

universe u

theorem pairing_card_aux (n : ℕ) : ∀ (α : Type u) [Fintype α],
    Fintype.card α=n → Fintype.card (Pairing α)=pairingCount n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α inst hcard
    classical
    by_cases hn : n=0
    · have hzero : Fintype.card α=0 := hcard.trans hn
      let : IsEmpty α := Fintype.card_eq_zero_iff.mp hzero
      let p : Pairing α := ⟨id,fun x => rfl,fun x => isEmptyElim x⟩
      let : Unique (Pairing α) := ⟨⟨p⟩,fun q => by ext x; exact isEmptyElim x⟩
      simp [hn]
    · have hnpos : 0<n := Nat.pos_of_ne_zero hn
      have hα : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let a : α := Classical.choice hα
      have hm : n-2<n := Nat.sub_lt hnpos (by omega)
      have he (b : {x : α // x≠a}) :
          Fintype.card (Pairing {x : α // x≠a ∧ x≠b.val})=pairingCount (n-2) := by
        apply ih (n-2) hm
        rw [card_except_two a b.val b.property,hcard]
      calc
        _ = Fintype.card (Σ b : {x : α // x≠a}, Pairing {x : α // x≠a ∧ x≠b.val}) :=
          Fintype.card_congr (Pairing.split a)
        _ = ∑ b : {x : α // x≠a}, Fintype.card (Pairing {x : α // x≠a ∧ x≠b.val}) :=
          Fintype.card_sigma
        _ = ∑ _b : {x : α // x≠a}, pairingCount (n-2) := Finset.sum_congr rfl (fun b _ => he b)
        _ = (n-1)*pairingCount (n-2) := by
          simp [Fintype.card_subtype_compl,hcard]
        _ = pairingCount n := (pairingCount_pos_recurrence hnpos).symm

omit [DecidableEq α] in
theorem pairing_card [Fintype α] : Fintype.card (Pairing α)=pairingCount (Fintype.card α) :=
  pairing_card_aux (Fintype.card α) α rfl

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Initializer

open Finset MatchingFPRAS.Switching MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

noncomputable def restrictHoles (R : Finset V) (m : {m : Mate V // HasHoles m R}) :
    Pairing {x : V // x∉R} where
  mate x := ⟨m.val.val x.val,fun h => x.property ((mate_mem_holes_iff m.val R m.property x.val).mp h)⟩
  involutive x := Subtype.ext (m.val.property x.val)
  no_fixed x h := x.property ((m.property x.val).mp (congrArg Subtype.val h))

noncomputable def fillFixed (R : Finset V) (p : Pairing {x : V // x∉R}) : Mate V := by
  classical
  refine ⟨fun x => if hx : x∉R then (p.mate ⟨x,hx⟩).val else x,?_⟩
  intro x
  by_cases hx : x∉R
  · simp only [dite_eq_left hx]
    rw [dite_eq_left (p.mate ⟨x,hx⟩).property]
    exact congrArg Subtype.val (p.involutive ⟨x,hx⟩)
  · simp only [dite_eq_right hx]

omit [Fintype V] in
lemma fillFixed_holes (R : Finset V) (p : Pairing {x : V // x∉R}) : HasHoles (fillFixed R p) R := by
  classical
  intro x
  by_cases hx : x∉R
  · simp only [fillFixed,iff_false,hx]
    intro h
    exact p.no_fixed ⟨x,hx⟩ (Subtype.ext h)
  · simp only [fillFixed,dite_eq_right hx]
    exact iff_of_true trivial (not_not.mp hx)

noncomputable def holesPairingEquiv (R : Finset V) :
    {m : Mate V // HasHoles m R} ≃ Pairing {x : V // x∉R} where
  toFun := restrictHoles R
  invFun p := ⟨fillFixed R p,fillFixed_holes R p⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x∉R
    · change (if hy : x∉R then (restrictHoles R m).mate ⟨x,hy⟩ |>.val else x)=m.val.val x
      rw [dite_eq_left hx]
      rfl
    · change (if hy : x∉R then (restrictHoles R m).mate ⟨x,hy⟩ |>.val else x)=m.val.val x
      rw [dite_eq_right hx]
      exact ((m.property x).mpr (not_not.mp hx)).symm
  right_inv p := by
    apply Pairing.ext
    intro x
    apply Subtype.ext
    change (fillFixed R p).val x.val=(p.mate x).val
    simp only [fillFixed,dite_eq_left x.property]

lemma matchings_card (R : Finset V) :
    (matchings R).card=pairingCount (Fintype.card V-R.card) := by
  classical
  calc
    _ = Fintype.card {m : Mate V // HasHoles m R} := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext m
      simp [matchings]
    _ = Fintype.card (Pairing {x : V // x∉R}) := Fintype.card_congr (holesPairingEquiv R)
    _ = _ := by rw [pairing_card,Fintype.card_subtype_compl,Fintype.card_coe]

lemma uniform_weight (c : ℝ) (R : Finset V) (m : Mate V) (hm : HasHoles m R) :
    weight (fun _ _ => c) m=c^((Fintype.card V-R.card)/2) := by
  classical
  have hmc : HasHoles m Rᶜᶜ := by simpa using hm
  have hc := mate_edge_count m Rᶜ hmc
  rw [Finset.card_compl] at hc
  have he : (univ.filter fun v => v < m.val v).card=(Fintype.card V-R.card)/2 := by omega
  unfold weight
  rw [←Finset.prod_filter (s:=univ) (fun v : V => v < m.val v) (fun _ : V => c)]
  simp only [Finset.prod_const,he]

theorem uniform_partition (c : ℝ) (R : Finset V) :
    partition (fun _ _ : V => c) R=
      (pairingCount (Fintype.card V-R.card):ℝ)*c^((Fintype.card V-R.card)/2) := by
  unfold partition
  simp_rw [Finset.sum_congr rfl (fun m hm => uniform_weight c R m ((mem_matchings m R).mp hm))]
  simp only [Finset.sum_const,nsmul_eq_mul,matchings_card]

lemma uniform_hole_ratio (hn : 2 ≤ Fintype.card V) (he : Even (Fintype.card V))
    (c : ℝ) (hc : 0 < c) (a b : V) (hab : a≠b) :
    holeRatio (fun _ _ : V => c) {a,b}=1/((Fintype.card V-1)*c) := by
  have h2 : ({a,b} : Finset V).card=2 := by simp [hab]
  have hc2 : Fintype.card V-2+2=Fintype.card V := by omega
  have he2 : Even (Fintype.card V-2) := by obtain ⟨k,hk⟩ := he; exact ⟨k-1,by omega⟩
  have hp : (pairingCount (Fintype.card V-2):ℝ)≠0 := by
    exact_mod_cast (pairingCount_pos_of_even _ he2).ne'
  have hpow : c^((Fintype.card V-2)/2)≠0 := pow_ne_zero _ hc.ne'
  unfold holeRatio
  rw [uniform_partition,uniform_partition,h2,Finset.card_empty,Nat.sub_zero]
  have hnrec : pairingCount (Fintype.card V)=
      (Fintype.card V-1)*pairingCount (Fintype.card V-2) :=
    pairingCount_pos_recurrence (by omega)
  have hexp : Fintype.card V/2=(Fintype.card V-2)/2+1 := by omega
  rw [hnrec,hexp,pow_succ,Nat.cast_mul,Nat.cast_sub (by omega : 1≤Fintype.card V),Nat.cast_one]
  field_simp

theorem initial_balanced (hn : 2 ≤ Fintype.card V) (he : Even (Fintype.card V)) :
    let w := fun _ _ : V => ((initialScale (Fintype.card V):ℚ):ℝ)^2
    (0 < partition w ∅) ∧
    (∀ a,(1:ℝ)/4 ≤ rowMax hn w a) ∧ (∀ a,rowMax hn w a ≤ 1) := by
  dsimp only
  let n := Fintype.card V
  have hs : 0 < ((initialScale n:ℚ):ℝ) := by exact_mod_cast initialScale_pos n hn
  have hsq : 0 < ((initialScale n:ℚ):ℝ)^2 := sq_pos_of_pos hs
  have hr (a b : V) (hab : a≠b) :
      holeRatio (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) {a,b}=
        (Nat.sqrt (n-1):ℝ)^2/(n-1) := by
    rw [uniform_hole_ratio hn he _ hsq a b hab]
    unfold initialScale
    push_cast
    change 1/((n-1)*((1:ℝ)/Nat.sqrt (n-1))^2)=_
    have hp : (Nat.sqrt (n-1):ℝ)≠0 := by
      have h := initialScale_pos n hn
      simp only [initialScale,one_div,inv_pos] at h
      exact_mod_cast h.ne'
    field_simp
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < n-1 := by linarith
  refine ⟨?_,?_,?_⟩
  · rw [uniform_partition,Finset.card_empty,Nat.sub_zero]
    exact mul_pos (by exact_mod_cast pairingCount_pos_of_even n he) (pow_pos hsq _)
  · intro a
    obtain ⟨b,hba,hb⟩ := rowMax_attained hn (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) a
    rw [←hb,hr a b hba.symm]
    have hbnd := (sqrt_square_bounds n hn).1
    apply (le_div_iff₀ hden).mpr
    linarith
  · intro a
    obtain ⟨b,hba,hb⟩ := rowMax_attained hn (fun _ _ : V => ((initialScale n:ℚ):ℝ)^2) a
    rw [←hb,hr a b hba.symm]
    exact (div_le_one hden).mpr
      (sqrt_square_bounds n hn).2

end MatchingFPRAS.Initializer

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Certify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

instance decideMatching (M : Finset E) :
    Decidable (MatchingOn (fun e v => v ∈ ends e) M univ) := by
  unfold MatchingOn ExistsUnique
  infer_instance

def certify (s : Finset (Finset E)) : Finset (PM (fun e v => v ∈ ends e)) :=
  Finset.subtype (fun A => MatchingOn (fun e v => v ∈ ends e) A univ) s

@[simp] lemma mem_certify (s : Finset (Finset E)) (A : PM (fun e v => v ∈ ends e)) :
    A ∈ certify ends s ↔ A.val ∈ s := Finset.mem_subtype

def colors (A : PM (fun e v => v ∈ ends e)) : Finset (PM (fun e v => v ∈ ends e)) :=
  certify ends (colorRaw ends A.val)

@[simp] lemma mem_colors (A B : PM (fun e v => v ∈ ends e)) :
    B ∈ colors ends A ↔ ColorChange ends A B := by
  rw [colors,mem_certify,mem_colorRaw]
  constructor
  · rintro ⟨e,he,f,hf,hB⟩
    refine ⟨e,f,A.val.erase e,hf.symm,?_,?_⟩
    · simpa only [union_singleton] using (insert_erase he).symm
    · simpa only [union_singleton] using hB
  · exact ColorChange.edit ends

lemma colors_eq (A : PM (fun e v => v ∈ ends e)) :
    colors ends A = colorDestinations ends A := by
  ext B
  simp [colorDestinations]

def switches (A : PM (fun e v => v ∈ ends e)) : Finset (PM (fun e v => v ∈ ends e)) :=
  certify ends (switchRaw ends A.val)

@[simp] lemma mem_switches (A B : PM (fun e v => v ∈ ends e)) :
    B ∈ switches ends A ↔ TwoEdgeSwitch A B := by
  rw [switches,mem_certify]
  constructor
  · intro h
    obtain ⟨⟨v,e⟩,hp,hB⟩ := mem_image.mp h
    obtain ⟨hv,he,hne,hsub⟩ := (mem_filter.mp hp).2
    refine ⟨v,e,A.val \ {e 0,e 2},hv,he,?_,hB.symm⟩
    exact (sdiff_union_of_subset hsub).symm
  · intro h
    obtain ⟨v,e,hv,he,hne,hsub,hB⟩ := h.normal_form
    exact mem_image.mpr ⟨(v,e),mem_filter.mpr ⟨mem_univ _,hv,he,hne,hsub⟩,hB.symm⟩

lemma switches_eq (A : PM (fun e v => v ∈ ends e)) :
    switches ends A = switchDestinations A := by
  ext B
  simp [switchDestinations]

theorem colors_card (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (colors ends A).card ≤ 2*A.val.card := by
  rw [colors_eq]
  exact colorDestinations_card_bound ends hpar A

theorem switches_card (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (switches ends A).card ≤ 8*A.val.card.choose 2 := by
  rw [switches_eq]
  exact switchDestinations_card_bound ends hpar A

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Component
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

def component (U : Finset E) (a : E) : Finset E :=
  U ∩ ComputableReach.closure (overlayLineGraph (fun e v => v ∈ ends e) U) a

lemma component_eq (U : Finset E) (a : E) :
    component ends U a = componentEdges (inc:=fun e v => v ∈ ends e) U a := by
  ext e
  simp only [component,mem_inter,ComputableReach.mem_closure,mem_componentEdges]

def allComponents (U : Finset E) : Finset (Finset E) := U.image (component ends U)

lemma allComponents_eq (U : Finset E) :
    allComponents ends U = components (inc:=fun e v => v ∈ ends e) U := by
  simp only [allComponents,components]
  exact Finset.image_congr (fun a _ => component_eq ends U a)

def discrepancies (A B : PM (fun e v => v ∈ ends e)) : Finset (Finset E) :=
  (allComponents ends (A.val ∪ B.val)).filter (fun S => ¬S ⊆ A.val ∩ B.val)

def cycle (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e))
    (S : Finset E) : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e) :=
  if h : S ∈ allComponents ends (p.1.val ∪ p.2.val) then
    (⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property
        (component_exchange_compatible (by rwa [allComponents_eq] at h))⟩,
     ⟨exchange p.2.val p.1.val S,exchange_matching p.2.property p.1.property
        (component_exchange_compatible (by rwa [allComponents_eq] at h)).symm⟩)
  else p

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS.Transport.Sparse

open Finset WeightedOptions

variable {Ω : Type*} [Fintype Ω] [LinearOrder Ω] [DecidableEq Ω]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

attribute [local instance] OAI.MatchingFPRAS.Transport.Sparse.finsetOrder
local instance pmOrder : LinearOrder (PM (fun e v => v ∈ ends e)) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

lemma color_degree (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : ((colors ends A).erase A).card ≤ Fintype.card V :=
  (card_erase_le).trans ((colors_card ends hpar A).trans_eq (A.twice_card ends hloop))

lemma switch_degree (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) :
    ((switches ends A).erase A).card ≤ 8*(Fintype.card V/2).choose 2 := by
  have h : Fintype.card V/2=A.val.card := by have := A.twice_card ends hloop; omega
  rw [h]
  exact card_erase_le.trans (switches_card ends hpar A)

def colorTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : WeightedOptions (PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.neighbors A ((colors ends A).erase A) (Fintype.card V)
    (color_degree ends hloop hpar A)

def switchTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : WeightedOptions (PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.neighbors A ((switches ends A).erase A) (8*(Fintype.card V/2).choose 2)
    (switch_degree ends hloop hpar A)

def cycleTable (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    WeightedOptions (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :=
  if h : (discrepancies ends p.1 p.2).Nonempty then
    (WeightedOptions.uniform _ h).map (cycle ends p)
  else WeightedOptions.pure p

def pairTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    WeightedOptions (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.mix (1/3) (by norm_num) (by norm_num)
    ((switchTable ends hloop hpar p.1).map (fun x => (x,p.2)))
    (WeightedOptions.mix (1/2) (by norm_num) (by norm_num)
      ((colorTable ends hloop hpar p.1).map (fun x => (x,p.2)))
      (cycleTable ends p))

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Admissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset Replica Variation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

attribute [local instance] finsetOrder pmOrder

def rationalWeight (w : E → ℚ) (A : PM (fun e v=>v∈ends e)) : ℚ := ∏ e∈A.val,w e

omit [DecidableEq V] [Fintype E] [LinearOrder E] in
lemma rationalWeight_pos [DecidableEq V] [Fintype E] [LinearOrder E]
    (w : E → ℚ) (hw : ∀ e,0<w e) (A : PM (fun e v=>v∈ends e)) :
    0 < rationalWeight ends w A := prod_pos (fun e _=>hw e)

def rationalPairWeight (w z : E → ℚ) (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) : ℚ :=
  rationalWeight ends w a.1*rationalWeight ends z a.2

lemma rationalPairWeight_pos (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) : 0 < rationalPairWeight ends w z a :=
  mul_pos (rationalWeight_pos ends w hw a.1) (rationalWeight_pos ends z hz a.2)

def pairStepTable (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) :=
  (pairTable ends hloop hpar a).metropolisChoice (rationalPairWeight ends w z)
    (rationalPairWeight_pos ends w z hw hz) a

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS.UnitRefresh

instance instFinitePairing_1 {α : Type*} [Finite α] : Finite (Pairing α) := by
  apply Finite.of_injective Pairing.mate
  intro p q h
  cases p; cases q
  simp only [Pairing.mk.injEq] at *
  exact h

noncomputable instance instFintypePairing_1 {α : Type*} [Fintype α] : Fintype (Pairing α) := Fintype.ofFinite _

variable {α β : Type*}

variable [DecidableEq α]

universe u



open Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]



open Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]



def Pairing.sigma {L : Type*} {A : L → Type*} (p : ∀ l, Pairing (A l)) : Pairing (Sigma A) where
  mate x := ⟨x.1,(p x.1).mate x.2⟩
  involutive x := by
    cases x with
    | mk l x => exact congrArg (Sigma.mk l) ((p l).involutive x)
  no_fixed x h := by
    have he : (p x.1).mate x.2=x.2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact (p x.1).no_fixed x.2 he

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

structure ColoredPairing (bags : V → Finset L) where
  pair : Pairing V
  color : V → L
  allowed : ∀ x, color x ∈ bags x
  same_color : ∀ x, color (pair.mate x)=color x

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
@[ext] lemma ColoredPairing.ext {bags : V → Finset L} {p q : ColoredPairing bags}
    (hp : p.pair=q.pair) (hc : p.color=q.color) : p=q := by
  cases p; cases q; simp_all

instance instFiniteColoredPairing (bags : V → Finset L) : Finite (ColoredPairing bags) :=
  Finite.of_injective (fun p : ColoredPairing bags => (p.pair,p.color)) (by
    intro p q h
    exact ColoredPairing.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance instFintypeColoredPairing (bags : V → Finset L) : Fintype (ColoredPairing bags) := Fintype.ofFinite _

def ColoredPairing.fiber {bags : V → Finset L} (p : ColoredPairing bags) (l : L) :
    Pairing {x : V // p.color x=l} where
  mate x := ⟨p.pair.mate x,(p.same_color x).trans x.property⟩
  involutive x := Subtype.ext (p.pair.involutive x)
  no_fixed x h := p.pair.no_fixed x (congrArg Subtype.val h)

def ColoredPairing.glue (bags : V → Finset L) (f : Assignment bags)
    (p : ∀ l,Pairing {x : V // f.val x=l}) : ColoredPairing bags where
  pair := (Pairing.sigma p).map (Equiv.sigmaFiberEquiv f.val)
  color := f.val
  allowed := f.property
  same_color x := (p (f.val x)).mate ⟨x,rfl⟩ |>.property

def assignmentPairingEquiv (bags : V → Finset L) :
    ColoredPairing bags ≃ Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l} where
  toFun p := ⟨⟨p.color,p.allowed⟩,p.fiber⟩
  invFun q := ColoredPairing.glue bags q.1 q.2
  left_inv p := by
    apply ColoredPairing.ext
    · ext x; rfl
    · rfl
  right_inv q := by
    rcases q with ⟨f,p⟩
    change (⟨f,(ColoredPairing.glue bags f p).fiber⟩ :
      Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l}) = ⟨f,p⟩
    apply congrArg (fun q : ∀ l, Pairing {x : V // f.val x=l} =>
      (⟨f,q⟩ : Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l}))
    funext l
    ext x
    change ((p (f.val x)).mate ⟨x,rfl⟩).val = ((p l).mate x).val
    obtain ⟨x,hx⟩ := x
    dsimp at hx ⊢
    subst l
    rfl

theorem coloredPairing_card (bags : V → Finset L) :
    Fintype.card (ColoredPairing bags) =
      ∑ f : Assignment bags, ∏ l : L, pairingCount (Fintype.card {x : V // f.val x=l}) := by
  classical
  rw [Fintype.card_congr (assignmentPairingEquiv bags),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro l hl
  exact pairing_card

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Edge2
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}

def ColoredPairing.edgeAt (p : ColoredPairing bags) (x : V) : BagEdge bags :=
  ⟨⟨(s(x,p.pair.mate x),p.color x),by
    simp only [Sym2.mk_isDiag_iff]
    exact (p.pair.no_fixed x).symm⟩,by
    intro y hy
    change p.color x ∈ bags y
    rcases Sym2.mem_iff.mp hy with h | h <;> subst y
    · exact p.allowed x
    · rw [←p.same_color x]
      exact p.allowed (p.pair.mate x)⟩

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_incident (p : ColoredPairing bags) (x y : V) :
    (p.edgeAt x).Incident y ↔ y=x ∨ y=p.pair.mate x := Sym2.mem_iff

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_mate (p : ColoredPairing bags) (x : V) :
    p.edgeAt (p.pair.mate x)=p.edgeAt x := by
  apply Subtype.ext
  apply Subtype.ext
  change (s(p.pair.mate x,p.pair.mate (p.pair.mate x)),p.color (p.pair.mate x)) = _
  rw [p.pair.involutive,p.same_color,Sym2.eq_swap]
  rfl

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.edgeAt_of_incident (p : ColoredPairing bags) (x y : V)
    (h : (p.edgeAt x).Incident y) : p.edgeAt y=p.edgeAt x := by
  rcases (p.edgeAt_incident x y).mp h with rfl | rfl
  · rfl
  · exact p.edgeAt_mate x

noncomputable def ColoredPairing.toPM (p : ColoredPairing bags) : PM (BagEdge.Incident (bags := bags)) :=
  ⟨Finset.univ.image p.edgeAt,by
    constructor
    · intros; exact Finset.mem_univ _
    · intro x hx
      refine ⟨p.edgeAt x,⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
      · exact (p.edgeAt_incident x x).mpr (Or.inl rfl)
      · intro e he
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he.1
        exact (p.edgeAt_of_incident y x he.2).symm⟩

noncomputable def chosenEdge (M : PM (BagEdge.Incident (bags := bags))) (x : V) : BagEdge bags :=
  Classical.choose (M.property.2 x (Finset.mem_univ x))

omit [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma chosenEdge_spec [Fintype L] [DecidableEq V] [DecidableEq L]
    (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    chosenEdge M x ∈ M.val ∧ (chosenEdge M x).Incident x :=
  (Classical.choose_spec (M.property.2 x (Finset.mem_univ x))).1

omit [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma chosenEdge_unique [Fintype L] [DecidableEq V] [DecidableEq L]
    (M : PM (BagEdge.Incident (bags := bags))) (x : V) (e : BagEdge bags)
    (he : e ∈ M.val) (hx : e.Incident x) : e=chosenEdge M x :=
  (Classical.choose_spec (M.property.2 x (Finset.mem_univ x))).2 e ⟨he,hx⟩

noncomputable def chosenMate (M : PM (BagEdge.Incident (bags := bags))) (x : V) : V :=
  Sym2.Mem.other (chosenEdge_spec M x).2

lemma chosenMate_pair (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    s(x,chosenMate M x)=(chosenEdge M x).val.val.1 := Sym2.other_spec _

lemma chosenMate_ne (M : PM (BagEdge.Incident (bags := bags))) (x : V) : chosenMate M x ≠ x :=
  Sym2.other_ne (chosenEdge M x).val.property _

lemma chosenEdge_chosenMate (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    chosenEdge M (chosenMate M x)=chosenEdge M x := by
  symm
  apply chosenEdge_unique M _ _ (chosenEdge_spec M x).1
  exact Sym2.other_mem (chosenEdge_spec M x).2

lemma chosenMate_involutive (M : PM (BagEdge.Incident (bags := bags))) :
    Function.Involutive (chosenMate M) := by
  intro x
  have h := chosenMate_pair M (chosenMate M x)
  rw [chosenEdge_chosenMate,←chosenMate_pair M x] at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact False.elim (chosenMate_ne M x h.1)
  · exact h.2

noncomputable def fromPM (M : PM (BagEdge.Incident (bags := bags))) : ColoredPairing bags where
  pair := ⟨chosenMate M,chosenMate_involutive M,chosenMate_ne M⟩
  color x := (chosenEdge M x).val.color
  allowed x := (chosenEdge M x).property x (chosenEdge_spec M x).2
  same_color x := congrArg (fun e : BagEdge bags => e.val.color) (chosenEdge_chosenMate M x)

lemma fromPM_edgeAt (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    (fromPM M).edgeAt x=chosenEdge M x := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (chosenMate_pair M x) rfl

lemma chosenEdge_toPM (p : ColoredPairing bags) (x : V) : chosenEdge p.toPM x=p.edgeAt x := by
  symm
  apply chosenEdge_unique
  · exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · exact (p.edgeAt_incident x x).mpr (Or.inl rfl)

noncomputable def coloredPMEquiv : PM (BagEdge.Incident (bags := bags)) ≃ ColoredPairing bags where
  toFun := fromPM
  invFun := ColoredPairing.toPM
  left_inv M := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      rw [fromPM_edgeAt]
      exact (chosenEdge_spec M x).1
    · intro he
      obtain ⟨x,hx⟩ := e.exists_incident
      apply Finset.mem_image.mpr
      exact ⟨x,Finset.mem_univ _,(fromPM_edgeAt M x).trans (chosenEdge_unique M x e he hx).symm⟩
  right_inv p := by
    apply ColoredPairing.ext
    · ext x
      change chosenMate p.toPM x=p.pair.mate x
      have h := chosenMate_pair p.toPM x
      rw [chosenEdge_toPM] at h
      change s(x,chosenMate p.toPM x)=s(x,p.pair.mate x) at h
      exact Sym2.congr_right.mp h
    · funext x
      change (chosenEdge p.toPM x).val.color=p.color x
      rw [chosenEdge_toPM]
      rfl



open Finset

variable {U S W L : Type*} [Fintype U] [Fintype S] [Fintype W] [Fintype L]
  [DecidableEq U] [DecidableEq S] [DecidableEq W] [DecidableEq L]

omit [DecidableEq W] in
lemma fiberCount_leaf [DecidableEq W] (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val l = Fintype.card U+T.card := by
  rw [fiberCount_sum,fiberCount_sum]
  have hz : fiberCount f.val l=0 := fiberCount_zero _ _ (fun x h => hb x (h ▸ f.property x))
  change fiberCount (fun _ : U => l) l +
    (fiberCount (fun x : S => if x∈T then l else p) l + fiberCount f.val l)=_
  rw [fiberCount_const,ite_eq_left rfl,hz,Nat.add_zero]
  congr 1
  unfold fiberCount
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x => x∈T) (fun x => by simp [hlp.symm]))]
  exact Fintype.card_coe T

omit [DecidableEq W] in
lemma fiberCount_parent [DecidableEq W] (l p : L) (hlp : l≠p) (b : W → Finset L)
    (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val p =
      Fintype.card S-T.card+fiberCount f.val p := by
  rw [fiberCount_sum,fiberCount_sum]
  change fiberCount (fun _ : U => l) p +
    (fiberCount (fun x : S => if x∈T then l else p) p + fiberCount f.val p)=_
  rw [fiberCount_const,ite_eq_right hlp,Nat.zero_add]
  congr 1
  unfold fiberCount
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x => x∉T) (fun x => by simp [hlp]))]
  rw [Fintype.card_subtype_compl,Fintype.card_coe]

omit [DecidableEq W] in
lemma fiberCount_other [DecidableEq W] (l p a : L) (hal : a≠l) (hap : a≠p) (b : W → Finset L)
    (T : Finset S) (f : Assignment b) :
    fiberCount (leafAssignment (U := U) l p b T f).val a = fiberCount f.val a := by
  rw [fiberCount_sum,fiberCount_sum]
  change fiberCount (fun _ : U => l) a +
    (fiberCount (fun x : S => if x∈T then l else p) a + fiberCount f.val a)=_
  rw [fiberCount_const,ite_eq_right hal.symm]
  have hz : fiberCount (fun x : S => if x∈T then l else p) a=0 := by
    apply fiberCount_zero
    intro x
    split_ifs
    · exact hal.symm
    · exact hap.symm
  simp [hz]

lemma leaf_assignment_weight (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) (T : Finset S) (f : Assignment b) :
    (∏ a,w a (fiberCount (leafAssignment (U := U) l p b T f).val a)) =
      w l (Fintype.card U+T.card) * w p (Fintype.card S-T.card+fiberCount f.val p) *
        (∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a)) := by
  rw [prod_split_two l p hlp,fiberCount_leaf l p hlp b hb,fiberCount_parent l p hlp]
  congr 1
  apply prod_congr rfl
  intro a ha
  rw [fiberCount_other _ _ _ (mem_erase.mp (mem_erase.mp ha).2).1 (mem_erase.mp ha).1]

theorem leaf_elimination (l p : L) (hlp : l≠p) (b : W → Finset L)
    (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) :
    assignmentPartition (leafBags (U := U) (S := S) l p b) w =
      assignmentPartition b (leafUpdate (Fintype.card U) (Fintype.card S) l p w) := by
  classical
  unfold assignmentPartition
  calc
    _ = ∑ q : Finset S × Assignment b,
        ∏ a,w a (fiberCount (leafAssignment (U := U) l p b q.1 q.2).val a) := by
      apply Fintype.sum_equiv (leafAssignmentEquiv l p hlp b)
      intro f
      exact congrArg (fun q : Assignment (leafBags (U := U) (S := S) l p b) =>
        ∏ a,w a (fiberCount q.val a)) ((leafAssignmentEquiv l p hlp b).left_inv f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_comm]
      apply sum_congr rfl
      intro f hf
      simp_rw [leaf_assignment_weight l p hlp b hb w]
      rw [sum_finset_card (S:=S) (fun k =>
        w l (Fintype.card U+k)*w p (Fintype.card S-k+fiberCount f.val p)*
        (∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a)))]
      rw [prod_split_two l p hlp]
      have he : (∏ a∈(univ.erase l).erase p,
          leafUpdate (Fintype.card U) (Fintype.card S) l p w a (fiberCount f.val a)) =
          ∏ a∈(univ.erase l).erase p,w a (fiberCount f.val a) := by
        apply prod_congr rfl
        intro a ha
        simp only [leafUpdate,ite_eq_right (mem_erase.mp (mem_erase.mp ha).2).1,
          ite_eq_right (mem_erase.mp ha).1]
      rw [he]
      simp only [leafUpdate,ite_true,ite_eq_right hlp.symm,one_mul]
      rw [sum_mul]
      apply sum_congr rfl
      intro k hk
      ac_rfl

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_AssignmentEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {V W L : Type*} [Fintype V] [Fintype W] [Fintype L]
  [DecidableEq V] [DecidableEq W] [DecidableEq L]

theorem tree_leaf_elimination (b : V → Finset L) (l p : L) (hlp : l≠p)
    (h : LeafAt b l p) (w : L → ℕ → ℕ) :
    assignmentPartition b w =
      assignmentPartition (fun x : Outside b l => b x.val)
        (leafUpdate (Fintype.card (Private b l)) (Fintype.card (Shared b l)) l p w) := by
  classical
  rw [assignmentPartition_equiv b _ (splitLeaf b l) (splitLeaf_bags b l p h)]
  exact leaf_elimination l p hlp _ (fun x => x.property) w

lemma root_elimination {U : Type*} [Fintype U] [DecidableEq U]
    (l : L) (b : W → Finset L) (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) :
    assignmentPartition (rootBags (U:=U) l b) w =
      assignmentPartition b (rootUpdate (Fintype.card U) l w) := by
  classical
  unfold assignmentPartition
  apply Fintype.sum_equiv (rootAssignmentEquiv l b)
  intro f
  have hl : fiberCount f.val l = Fintype.card U := by
    rw [fiberCount_sum]
    have he : (fun x : U => f.val (.inl x))=(fun _ => l) := by
      funext x; simpa [rootBags] using f.property (.inl x)
    rw [he,fiberCount_const,ite_eq_left rfl]
    have hz : fiberCount (fun x : W => f.val (.inr x)) l=0 := by
      apply fiberCount_zero
      intro x hx
      exact hb x (hx ▸ f.property (.inr x))
    omega
  apply prod_congr rfl
  intro a ha
  by_cases h : a=l
  · subst a; simp [rootUpdate,hl]
  · simp only [rootUpdate,ite_eq_right h]
    congr 1
    rw [fiberCount_sum]
    have he : (fun x : U => f.val (.inl x))=(fun _ => l) := by
      funext x; simpa [rootBags] using f.property (.inl x)
    rw [he,fiberCount_const,ite_eq_right (Ne.symm h),zero_add]
    rfl

theorem tree_root_elimination (b : V → Finset L) (l : L)
    (h : ∀ x,l∈b x → b x={l}) (w : L → ℕ → ℕ) :
    assignmentPartition b w =
      assignmentPartition (fun x : Outside b l => b x.val)
        (rootUpdate (Fintype.card {x : V // l∈b x}) l w) := by
  classical
  have he (x : V) : rootBags l (fun y : Outside b l => b y.val) (splitRoot b l x)=b x := by
    unfold splitRoot
    simp only [Equiv.coe_fn_mk]
    split_ifs with hx
    · exact (h x hx).symm
    · rfl
  rw [assignmentPartition_equiv b _ (splitRoot b l) he]
  exact root_elimination l _ (fun x => x.property) w

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

theorem active_leaf_elimination (b : V → Finset L) (R : Finset V) (l p : L) (hlp : l≠p)
    (h : LeafAt (fun x : R => b x.val) l p) (w : L → ℕ → ℕ) :
    activePartition b R w = activePartition b (trim b R l)
      (leafUpdate (privateCount b R l) (sharedCount b R l) l p w) := by
  unfold activePartition
  rw [tree_leaf_elimination _ l p hlp h,active_outside]
  rw [show Fintype.card (Private (fun x : R => b x.val) l)=privateCount b R l from
    active_card_filter R (fun x => b x={l}),
    show Fintype.card (Shared (fun x : R => b x.val) l)=sharedCount b R l from
    active_card_filter R (fun x => l∈b x ∧ b x≠{l})]
  rfl

lemma active_root_elimination (b : V → Finset L) (R : Finset V) (l : L)
    (h : ∀ x : R,l∈b x.val → b x.val={l}) (w : L → ℕ → ℕ) :
    activePartition b R w = activePartition b (trim b R l)
      (rootUpdate ((R.filter fun x => l∈b x).card) l w) := by
  unfold activePartition
  rw [tree_root_elimination _ l h,active_outside,active_card_filter R (fun x => l∈b x)]
  rfl

theorem tableDP_correct (b : V → Finset L) (parent : L → Option L)
    (ls : List L) (R : Finset V) (hp : LegalPlan b parent ls R) (w : L → ℕ → ℕ) :
    activePartition b R w=∏ l,tableDP b parent ls R w l 0 := by
  induction ls generalizing R w with
  | nil =>
    have hR : R=∅ := hp
    subst R
    exact active_empty b w
  | cons l ls ih =>
    have ht : activePartition b R w =
        activePartition b (trim b R l) (advanceTable b R parent l w) := by
      cases hpar : parent l with
      | none =>
        unfold advanceTable; rw [hpar]
        exact active_root_elimination b R l (by simpa only [LegalPlan,hpar] using hp.1) w
      | some p =>
        have h := hp.1
        simp only [hpar] at h
        unfold advanceTable; rw [hpar]
        exact active_leaf_elimination b R l p h.1 h.2 w
    rw [ht]
    exact ih _ hp.2 _

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RankOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

lemma finiteDP_correct (b : V → Finset L) (parent : L → Option L) (ls : List L)
    (R : Finset V) (w z : L → ℕ → ℕ)
    (h : ∀ a r,r≤Fintype.card V*ls.length → w a r=z a r) (a : L) :
    finiteDP b parent ls R w a 0=tableDP b parent ls R z a 0 := by
  induction ls generalizing R w z with
  | nil => exact h a 0 (by simp)
  | cons l ls ih =>
    apply ih
    intro a r hr
    rw [capTable,ite_eq_left hr]
    apply advanceTable_congr b R parent l w z (Fintype.card V*ls.length)
    · intro a r hr
      apply h
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one] using hr
    · exact hr

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.subtype_hext [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]
    {bags : V → Finset L} {P Q : V → Prop}
    [DecidablePred P] [DecidablePred Q]
    (p : ColoredPairing (fun x : {x // P x} => bags x.val))
    (q : ColoredPairing (fun x : {x // Q x} => bags x.val))
    (hPQ : ∀ x,P x ↔ Q x)
    (hm : ∀ (x : {x // P x}) (y : {x // Q x}),x.val=y.val →
      (p.pair.mate x).val=(q.pair.mate y).val)
    (hc : ∀ (x : {x // P x}) (y : {x // Q x}),x.val=y.val → p.color x=q.color y) :
    HEq p q := by
  have he : P=Q := funext fun x => propext (hPQ x)
  subst Q
  apply heq_of_eq
  apply ColoredPairing.ext
  · ext x; exact hm x x rfl
  · funext x; exact hc x x rfl

def ColoredPairing.remove {bags : V → Finset L} (p : ColoredPairing bags) (a : V) :
    ColoredPairing (residualBags bags a (p.pair.mate a)) where
  pair := p.pair.remove a
  color x := p.color x.val
  allowed x := p.allowed x.val
  same_color x := p.same_color x.val

def ColoredPairing.insert {bags : V → Finset L} (a : V) (c : Partner bags a)
    (p : ColoredPairing (residualBags bags a c.val.1)) : ColoredPairing bags where
  pair := p.pair.insert a c.val.1 c.property.1
  color x := if hx : x=a ∨ x=c.val.1 then c.val.2 else p.color ⟨x,by tauto⟩
  allowed x := by
    dsimp
    split_ifs with hx
    · rcases hx with rfl|rfl
      · exact c.property.2.1
      · exact c.property.2.2
    · exact p.allowed _
  same_color x := by
    by_cases ha : x=a
    · subst x
      simp [Pairing.insert,c.property.1]
    by_cases hb : x=c.val.1
    · subst x
      simp [Pairing.insert,c.property.1]
    simp only [Pairing.insert,dite_eq_right ha,dite_eq_right hb]
    rw [dite_eq_right (by exact not_or.mpr (p.pair.mate ⟨x,ha,hb⟩).property),
      dite_eq_right (not_or.mpr ⟨ha,hb⟩)]
    exact p.same_color ⟨x,ha,hb⟩

omit [Fintype V] [Fintype L] [DecidableEq L] in
@[simp] lemma ColoredPairing.insert_color [Fintype V] [Fintype L] [DecidableEq L]
    {bags : V → Finset L} (a : V) (c : Partner bags a)
    (p : ColoredPairing (residualBags bags a c.val.1)) :
    (p.insert a c).color a=c.val.2 := by simp [ColoredPairing.insert]

omit [Fintype V] [Fintype L] [DecidableEq L] in
@[simp] lemma ColoredPairing.insert_color_residual [Fintype V] [Fintype L] [DecidableEq L]
    {bags : V → Finset L} (a : V)
    (c : Partner bags a) (p : ColoredPairing (residualBags bags a c.val.1))
    (x : withoutPair a c.val.1) :
    (p.insert a c).color x.val=p.color x := by
  simp [ColoredPairing.insert,x.property.1,x.property.2]

noncomputable def ColoredPairing.split {bags : V → Finset L} (a : V) :
    ColoredPairing bags ≃ Σ c : Partner bags a,ColoredPairing (residualBags bags a c.val.1) where
  toFun p := ⟨⟨(p.pair.mate a,p.color a),p.pair.no_fixed a,p.allowed a,
    by rw [← p.same_color a]; exact p.allowed _⟩,p.remove a⟩
  invFun q := q.2.insert a q.1
  left_inv p := by
    apply ColoredPairing.ext
    · ext x
      by_cases ha : x=a
      · subst x; simp [ColoredPairing.insert,Pairing.insert]
      by_cases hb : x=p.pair.mate a
      · subst x; simp [ColoredPairing.insert,Pairing.insert,p.pair.no_fixed,p.pair.involutive a]
      simp [ColoredPairing.insert,Pairing.insert,ColoredPairing.remove,Pairing.remove,ha,hb]
    · funext x
      by_cases ha : x=a
      · subst x; simp [ColoredPairing.insert]
      by_cases hb : x=p.pair.mate a
      · subst x; simp [ColoredPairing.insert,p.same_color]
      simp [ColoredPairing.insert,ColoredPairing.remove,ha,hb]
  right_inv q := by
    rcases q with ⟨c,p⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact Prod.ext (Pairing.insert_at a c.val.1 c.property.1 p.pair) (ColoredPairing.insert_color a c p)
    · apply ColoredPairing.subtype_hext
      · intro x; simp only [ColoredPairing.insert,Pairing.insert_at]
      · intro x y hxy
        change (p.pair.insert a c.val.1 c.property.1).mate x.val=(p.pair.mate y).val
        rw [hxy]
        exact Pairing.insert_other _ _ _ _ y
      · intro x y hxy
        change (p.insert a c).color x.val=p.color y
        rw [hxy]
        exact ColoredPairing.insert_color_residual _ _ _ y

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma read_tabulate {m B : ℕ} (f : Fin m → ℕ → ℕ) (a : Fin m) (r : ℕ) :
    read (tabulate m B f) a.val r = if r≤B then f a r else 0 := by
  unfold read tabulate List.getD
  simp only [List.getElem?_ofFn, a.isLt, dite_eq_left, Option.getD_some]
  by_cases hr : r≤B
  · have h : r<B+1 := by omega
    simp [hr,h]
  · have h : ¬r<B+1 := by omega
    simp [hr,h]

lemma read_update {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (B r : ℕ) (t : Table) :
    read (update bags R parent l B t) a.val r =
      capTable B (advanceTable bags R parent l (fun a r=>read t a.val r)) a r := by
  rw [update,read_tabulate]
  unfold capTable
  split_ifs <;> simp [entry_eq]

lemma read_run {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (ls : List (Fin m)) (R : Finset V) (t : Table) (a : Fin m) (r : ℕ) :
    read (run bags parent ls R t) a.val r =
      finiteDP bags parent ls R (fun a r=>read t a.val r) a r := by
  induction ls generalizing R t with
  | nil => rfl
  | cons l ls ih =>
    rw [run,finiteDP,ih]
    congr 2
    funext a r
    exact read_update bags R parent l a _ r t

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def val (x : Fraction) : ℚ := (x.1:ℚ)/x.2

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Plan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem computable_count_eq {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l) :
    count bags parent (plan rank)=Fintype.card (ColoredPairing bags) := by
  rw [coloredPairing_card]
  change count bags parent (plan rank)=assignmentPartition bags (fun _=>pairingCount)
  rw [←active_univ]
  rw [tableDP_correct bags parent _ _ (plan_legal bags rank parent hb hne hp)]
  unfold count
  apply prod_congr rfl
  intro a _
  rw [read_run]
  apply finiteDP_correct
  intro b r hr
  rw [plan_length] at hr
  simp [initial,read_tabulate,hr]

def branchCount {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a b : V) : ℕ :=
  count (residualBags bags a b) parent (plan rank)

lemma branchCount_eq {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a b : V) : branchCount bags rank parent a b=
      Fintype.card (ColoredPairing (residualBags bags a b)) := by
  apply computable_count_eq
  · intro x c hc d hd; exact hb x.val c hc d hd
  · intro x; exact hne x.val
  · exact hp

lemma branchCount_sum {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : V) : (∑ c : Partner bags a,branchCount bags rank parent a c.val.1)=
      count bags parent (plan rank) := by
  rw [computable_count_eq bags rank parent hb hne hp,
    Fintype.card_congr (ColoredPairing.split a),Fintype.card_sigma]
  apply sum_congr rfl
  intro c _
  exact branchCount_eq bags rank parent hb hne hp a c.val.1



open Finset MatchingFPRAS.FiniteChoice

variable {n m : ℕ}

def edgeCount (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (bc : Fin n × Fin m) : ℕ :=
  if validBranch bags a bc then branchCount bags rank parent a bc.1 else 0

lemma edgeCount_sum (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) : (∑ bc,edgeCount bags rank parent a bc)=count bags parent (plan rank) := by
  rw [←branchCount_sum bags rank parent hb hne hp a]
  change (∑ bc,if validBranch bags a bc then branchCount bags rank parent a bc.1 else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro bc; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl) _

def edgeProbability (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (i : Fin (n*m)) : ℚ :=
  edgeCount bags rank parent a (finProdFinEquiv.symm i)/count bags parent (plan rank)

lemma edgeProbability_sum (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) :
    ∑ i,edgeProbability bags rank parent a i=1 := by
  unfold edgeProbability
  rw [←Finset.sum_div,←Nat.cast_sum]
  rw [←finProdFinEquiv.sum_comp (fun i=>edgeCount bags rank parent a (finProdFinEquiv.symm i))]
  simp only [Equiv.symm_apply_apply]
  rw [edgeCount_sum bags rank parent hb hne hp a]
  exact div_self (by exact_mod_cast hz.ne')

def drawEdge (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) (k : ℕ) (bits : Fin k → Bool) :
    {c : Partner bags a // 0<branchCount bags rank parent a c.val.1} := by
  let p := edgeProbability bags rank parent a
  have hs := edgeProbability_sum bags rank parent hb hne hp a hz
  let i := chooseBits p hs k bits
  let bc := finProdFinEquiv.symm i
  have hh : 0<edgeCount bags rank parent a bc := by
    have h := chooseBits_pos p hs k bits
    change 0<(edgeCount bags rank parent a bc:ℚ)/(count bags parent (plan rank):ℚ) at h
    have := (div_pos_iff_of_pos_right (by exact_mod_cast hz : (0:ℚ) < count bags parent (plan rank))).mp h
    exact_mod_cast this
  have hv : validBranch bags a bc := by
    by_contra hv
    simp [edgeCount,hv] at hh
  exact ⟨⟨bc,hv⟩,by simpa [edgeCount,hv] using hh⟩

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {U V L : Type*} [Fintype U] [Fintype V] [Fintype L] [DecidableEq U] [DecidableEq V] [DecidableEq L]

def ColoredPairing.map (bags : V → Finset L) (e : U ≃ V)
    (p : ColoredPairing (fun x=>bags (e x))) : ColoredPairing bags where
  pair := p.pair.map e
  color x := p.color (e.symm x)
  allowed x := by simpa using p.allowed (e.symm x)
  same_color x := by simpa [Pairing.map] using p.same_color (e.symm x)

def ColoredPairing.comap (bags : V → Finset L) (e : U ≃ V)
    (p : ColoredPairing bags) : ColoredPairing (fun x=>bags (e x)) where
  pair := p.pair.map e.symm
  color x := p.color (e x)
  allowed x := p.allowed (e x)
  same_color x := by simpa [Pairing.map] using p.same_color (e x)

def ColoredPairing.equiv (bags : V → Finset L) (e : U ≃ V) :
    ColoredPairing (fun x=>bags (e x)) ≃ ColoredPairing bags where
  toFun := ColoredPairing.map bags e
  invFun := ColoredPairing.comap bags e
  left_inv p := by
    apply ColoredPairing.ext
    · ext x; simp [ColoredPairing.map,ColoredPairing.comap,Pairing.map]
    · funext x; simp [ColoredPairing.map,ColoredPairing.comap]
  right_inv p := by
    apply ColoredPairing.ext
    · ext x; simp [ColoredPairing.map,ColoredPairing.comap,Pairing.map]
    · funext x; simp [ColoredPairing.map,ColoredPairing.comap]

def removePairEquiv {n : ℕ} (a b : Fin (n+2)) (hb : b≠a) :
    Fin n ≃ withoutPair a b := by
  let e := gapEquiv a
  let b' := e.symm ⟨b,hb⟩
  let f := gapEquiv b'
  refine {
    toFun := fun i=>⟨(e (f i).val).val,(e (f i).val).property,?_⟩
    invFun := fun x=>f.symm ⟨e.symm ⟨x.val,x.property.1⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro h
    apply (f i).property
    apply e.injective
    apply Subtype.ext
    simpa [b'] using h
  · intro h
    have hh := congrArg (fun i=>(e i).val) h
    apply x.property.2
    simpa [b'] using hh
  · intro i
    apply f.injective
    simp
  · intro x
    apply Subtype.ext
    simp

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice

variable {m : ℕ}

lemma singleton_count_zero (bags : Fin 1 → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l) :
    count bags parent (plan rank)=0 := by
  rw [computable_count_eq bags rank parent hb hne hp]
  have : IsEmpty (ColoredPairing bags) := ⟨fun p=>p.pair.no_fixed 0 (Subsingleton.elim _ _)⟩
  exact Fintype.card_eq_zero

def sampleUnit (k : ℕ) : (n : ℕ) → (bags : Fin n → Finset (Fin m)) →
    (rank : Fin m → ℕ) → (parent : Fin m → Option (Fin m)) →
    (hb : RankedBags bags rank parent) → (hne : ∀ x,(bags x).Nonempty) →
    (hp : ∀ l p,parent l=some p → rank p < rank l) →
    0 < count bags parent (plan rank) → (Fin n → Fin k → Bool) → ColoredPairing bags
  | 0,bags,_,_,_,_,_,_,_ =>
    ⟨⟨fun x=>Fin.elim0 x,fun x=>Fin.elim0 x,fun x=>Fin.elim0 x⟩,
      (fun x=>Fin.elim0 x),(fun x=>Fin.elim0 x),(fun x=>Fin.elim0 x)⟩
  | 1,bags,rank,parent,hb,hne,hp,hz,_ =>
    False.elim (by rw [singleton_count_zero bags rank parent hb hne hp] at hz; omega)
  | n+2,bags,rank,parent,hb,hne,hp,hz,bits => by
    let a : Fin (n+2) := Fin.last (n+1)
    let c := drawEdge bags rank parent hb hne hp a hz k (bits a)
    let e := removePairEquiv a c.val.val.1 c.val.property.1
    let b' : Fin n → Finset (Fin m) := fun x=>bags (e x).val
    have hb' : RankedBags b' rank parent := by
      intro x l hl r hr; exact hb (e x).val l hl r hr
    have hne' : ∀ x,(b' x).Nonempty := fun x=>hne (e x).val
    have hz' : 0 < count b' parent (plan rank) := by
      rw [computable_count_eq b' rank parent hb' hne' hp]
      rw [Fintype.card_congr (ColoredPairing.equiv (residualBags bags a c.val.val.1) e)]
      rw [←branchCount_eq bags rank parent hb hne hp]
      exact c.property
    let p := sampleUnit k n b' rank parent hb' hne' hp hz'
      (fun i=>bits i.castSucc.castSucc)
    exact (ColoredPairing.map (residualBags bags a c.val.val.1) e p).insert a c.val



open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

abbrev PositivePartner (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) :=
  {c : Partner bags a // 0<branchCount bags rank parent a c.val.1}

def partnerIndex (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n)
    (c : PositivePartner bags rank parent a) : Fin (n*m) := finProdFinEquiv c.val.val

noncomputable def positiveSplitEquiv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) :
    (Σ c : PositivePartner bags rank parent a,ColoredPairing (residualBags bags a c.val.val.1)) ≃ ColoredPairing bags := by
  let e : (Σ c : PositivePartner bags rank parent a,ColoredPairing (residualBags bags a c.val.val.1)) ≃
      (Σ c : Partner bags a,ColoredPairing (residualBags bags a c.val.1)) := {
    toFun := fun s=>⟨s.1.val,s.2⟩
    invFun := fun s=>⟨⟨s.1,by
      rw [branchCount_eq bags rank parent hb hne hp]
      exact Fintype.card_pos_iff.mpr ⟨s.2⟩⟩,s.2⟩
    left_inv := fun s=>by rcases s with ⟨⟨c,hc⟩,x⟩; rfl
    right_inv := fun s=>by cases s; rfl }
  exact e.trans (ColoredPairing.split a).symm

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RemainingBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

def remainingBags (bags : Fin (n+2) → Finset (Fin m)) (a : Fin (n+2))
    (c : Partner bags a) : Fin n → Finset (Fin m) :=
  fun x=>bags (removePairEquiv a c.val.1 c.property.1 x).val

lemma remainingRanked (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (a : Fin (n+2)) (c : Partner bags a) : RankedBags (remainingBags bags a c) rank parent := by
  intro x l hl r hr
  exact hb _ l hl r hr

lemma remainingNonempty (bags : Fin (n+2) → Finset (Fin m))
    (hne : ∀ x,(bags x).Nonempty) (a : Fin (n+2)) (c : Partner bags a) :
    ∀ x,(remainingBags bags a c x).Nonempty := fun _=>hne _

lemma remainingCard (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (c : Partner bags a) :
    Fintype.card (ColoredPairing (remainingBags bags a c))=branchCount bags rank parent a c.val.1 := by
  have h := Fintype.card_congr (ColoredPairing.equiv (residualBags bags a c.val.1)
    (removePairEquiv a c.val.1 c.property.1))
  exact h.trans (branchCount_eq bags rank parent hb hne hp _ _).symm

lemma remainingPositive (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) :
    0 < count (remainingBags bags a c.val) parent (plan rank) := by
  rw [computable_count_eq _ rank parent (remainingRanked bags rank parent hb a c.val)
    (remainingNonempty bags hne a c.val) hp, remainingCard bags rank parent hb hne hp]
  exact c.property

def assembleEdge (bags : Fin (n+2) → Finset (Fin m)) (a : Fin (n+2)) (c : Partner bags a)
    (p : ColoredPairing (remainingBags bags a c)) : ColoredPairing bags :=
  (ColoredPairing.map (residualBags bags a c.val.1) (removePairEquiv a c.val.1 c.property.1) p).insert a c

def residualSampler (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) (bits : Fin n → Fin k → Bool) : ColoredPairing bags :=
  assembleEdge bags a c.val (sampleUnit k n (remainingBags bags a c.val) rank parent
    (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val) hp
    (remainingPositive bags rank parent hb hne hp a c) bits)

noncomputable def renumberedSplitEquiv (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) :
    (Σ c : PositivePartner bags rank parent a,ColoredPairing (remainingBags bags a c.val)) ≃ ColoredPairing bags :=
  (Equiv.sigmaCongrRight (fun c : PositivePartner bags rank parent a=>
    ColoredPairing.equiv (residualBags bags a c.val.val.1)
      (removePairEquiv a c.val.val.1 c.val.property.1))).trans
    (positiveSplitEquiv bags rank parent hb hne hp a)

open Finset MatchingFPRAS.Variation
open scoped Classical

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh.Computable

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}

instance edgeDec (e : BagEdge bags) (x : V) : Decidable (e.Incident x) :=
  inferInstanceAs (Decidable (x∈e.val.val.1))

def edge (M : PM (BagEdge.Incident (bags := bags))) (x : V) : BagEdge bags :=
  M.val.choose (fun e=>e.Incident x) (M.property.2 x (mem_univ x))

omit [Fintype L] [DecidableEq L] in
lemma edge_spec [DecidableEq L] (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    edge M x∈M.val ∧ (edge M x).Incident x :=
  M.val.choose_spec _ (M.property.2 x (mem_univ x))

lemma edge_eq (M : PM (BagEdge.Incident (bags := bags))) (x : V) : edge M x=chosenEdge M x :=
  chosenEdge_unique M x _ (edge_spec M x).1 (edge_spec M x).2

def mate (M : PM (BagEdge.Incident (bags := bags))) (x : V) : V :=
  Sym2.Mem.other' (edge_spec M x).2

lemma mate_eq (M : PM (BagEdge.Incident (bags := bags))) (x : V) : mate M x=chosenMate M x := by
  have hp : s(x,mate M x)=(edge M x).val.val.1 := Sym2.other_spec' (edge_spec M x).2
  apply (Sym2.congr_right (a:=x)).mp
  exact hp.trans (by rw [edge_eq,←chosenMate_pair])

def fromMatching (M : PM (BagEdge.Incident (bags := bags))) : ColoredPairing bags where
  pair := ⟨mate M,(fun x=>by simpa only [mate_eq] using chosenMate_involutive M x),
    fun x=>by simpa only [mate_eq] using chosenMate_ne M x⟩
  color x := (edge M x).val.color
  allowed x := (edge M x).property x (edge_spec M x).2
  same_color x := by
    simp only [mate_eq,edge_eq]
    exact congrArg (fun e : BagEdge bags=>e.val.color) (chosenEdge_chosenMate M x)

lemma from_eq (M : PM (BagEdge.Incident (bags := bags))) : fromMatching M=fromPM M := by
  apply ColoredPairing.ext
  · apply Pairing.ext; intro x; exact mate_eq M x
  · funext x; exact congrArg (fun e : BagEdge bags=>e.val.color) (edge_eq M x)

def toMatching (p : ColoredPairing bags) : PM (BagEdge.Incident (bags := bags)) :=
  ⟨Finset.univ.image p.edgeAt,by exact p.toPM.property⟩

omit [Fintype L] in
lemma to_eq [Fintype L] (p : ColoredPairing bags) : toMatching p=p.toPM := rfl

def pairingEquiv : PM (BagEdge.Incident (bags := bags)) ≃ ColoredPairing bags where
  toFun := fromMatching
  invFun := toMatching
  left_inv M := by
    rw [from_eq,to_eq]
    exact (coloredPMEquiv (bags:=bags)).left_inv M
  right_inv p := by
    rw [to_eq,from_eq]
    exact (coloredPMEquiv (bags:=bags)).right_inv p

end MatchingFPRAS.UnitRefresh.Computable

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Variation

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] [DecidableEq L] [DecidableEq J]

def ColoredPairing.colorEquiv (bags : V → Finset L) (e : L ≃ J) :
    ColoredPairing bags ≃ ColoredPairing (fun x=>(bags x).map e.toEmbedding) where
  toFun p := {
    pair:=p.pair
    color:=fun x=>e (p.color x)
    allowed:=fun x=>by simpa using p.allowed x
    same_color:=fun x=>congrArg e (p.same_color x) }
  invFun p := {
    pair:=p.pair
    color:=fun x=>e.symm (p.color x)
    allowed:=fun x=>by
      obtain ⟨l,hl,he⟩:=mem_map.mp (p.allowed x)
      simpa only [←he,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hl
    same_color:=fun x=>congrArg e.symm (p.same_color x) }
  left_inv p := by
    apply ColoredPairing.ext
    · rfl
    · funext x; exact e.symm_apply_apply _
  right_inv p := by
    apply ColoredPairing.ext
    · rfl
    · funext x; exact e.apply_symm_apply _

open Finset MatchingFPRAS.Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

def numberingEquiv (bags : V → Finset L) :
    ColoredPairing (numberedBags bags) ≃ ColoredPairing bags :=
  (ColoredPairing.colorEquiv (fun x=>bags (orderedEnum V x)) (orderedEnum L).symm).symm.trans
    (ColoredPairing.equiv bags (orderedEnum V))

lemma numbered_count_pos (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (M : ColoredPairing bags) :
    0<Materialized.count (numberedBags bags) (numberedParent parent)
      (Materialized.plan (numberedRank rank)) := by
  rw [Materialized.computable_count_eq _ _ _ (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)]
  exact Fintype.card_pos_iff.mpr ⟨(numberingEquiv bags).symm M⟩

def sampleNumbered (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (M : ColoredPairing bags)
    (bits : Fin (Fintype.card V) → Fin k → Bool) : ColoredPairing bags :=
  numberingEquiv bags (Materialized.sampleUnit k (Fintype.card V) (numberedBags bags)
    (numberedRank rank) (numberedParent parent) (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp M) bits)

open MatchingFPRAS.Transport

def sampleMatching (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (M : PM (BagEdge.Incident (bags:=bags)))
    (bits : Fin (Fintype.card V) → Fin k → Bool) : PM (BagEdge.Incident (bags:=bags)) :=
  (Computable.pairingEquiv (bags:=bags)).symm
    (sampleNumbered k bags rank parent hb hne hp (Computable.pairingEquiv M) bits)

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Sym2Order
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

attribute [local instance] sym2Order

attribute [local instance] bagEdgeOrder

def rationalSlotWeight {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) : ℚ :=
  max ((rationalTierBase V)^tier x)⁻¹ (min ((rationalTierBase V)^tier x) (w e))

omit [LinearOrder V] [Fintype L] [LinearOrder L] in
lemma rationalSlotWeight_cast [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) :
    (rationalSlotWeight w x e:ℝ)=slotWeight (fun e=>(w e:ℝ)) x e := by
  simp [rationalSlotWeight,slotWeight,tierClamp,rationalTierBase_cast]

lemma rationalSlotWeight_pos {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) : 0 < rationalSlotWeight w x e := by
  have h:=slotWeight_pos (fun e=>(w e:ℝ)) x e
  rw [←rationalSlotWeight_cast] at h
  exact_mod_cast h

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

attribute [local instance] UnitRefresh.Computable.allowedDec

attribute [local instance] bagEdgeFintype

abbrev BagPM (bags : V → Finset L) := PM (BagEdge.Incident (bags:=bags))

noncomputable local instance instDecidableEqBagPM_r8038f5_1 : DecidableEq (BagPM bags) := Classical.decEq _
include hbags hG in
lemma parallels_bound (e : BagEdge bags) :
    (univ.filter (fun f : BagEdge bags=>f.val.val.1=e.val.val.1)).card≤2 := by
  have h:=BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e
  unfold BagEdge.parallels at h
  have instances_eq : tierClampBagEdgeFintype (bags:=bags) =
      (inferInstance : Fintype (BagEdge bags)) := Subsingleton.elim _ _
  rw [instances_eq] at h
  exact h

def sampleLadderPair {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (k : ℕ) : (Fin k → Bool) → BagPM bags × BagPM bags :=
  (Sparse.pairStepTable (fun e : BagEdge bags=>e.val.val.1) (fun e=>e.val.property)
    (parallels_bound hbags hG)
    (rationalSlotWeight w x) (rationalSlotWeight w y)
    (rationalSlotWeight_pos w x) (rationalSlotWeight_pos w y) a).draw k

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec



open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance instDecidableEqBagPM_2 : DecidableEq (BagPM bags) := Classical.decEq _

attribute [local instance] prodOrder sumOrder

noncomputable local instance instDecidableEqBagPM_1_r8038f5_1 : DecidableEq (BagPM bags) := Classical.decEq _
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

def pairDraw {T q : ℕ} (w : BagEdge bags → ℚ) (k : ℕ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (bits : LocalBits V k) : BagPM bags × BagPM bags :=
  sampleLadderPair hbags hG w x y a k bits.1

def baseDraw (M : BagPM bags) (k : ℕ) (bits : LocalBits V k) : BagPM bags :=
  UnitRefresh.sampleMatching k bags rank parent hb hne hp M bits.2

def ladderScan {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k : ℕ)
    (s : Slot T q → BagPM bags) (bits : ScanBits V k) : Slot T q → BagPM bags :=
  sampleScan guides (base T q) (base_nonempty T q hq) (pairDraw hbags hG w k)
    (fun _=>baseDraw rank parent hb hne hp M k) k s bits

def scanErrorNumerator (V L : Type*) [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L] (bags : V → Finset L)
    (T q : ℕ) : ℕ :=
  2*(1+(T*q^2+q))+
  4*(8*(Fintype.card (BagEdge bags))^2+4*Fintype.card (BagEdge bags)+3)+
  2*(Fintype.card V)^2*Fintype.card L

def ladderRun {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) (bits : Fin n → ScanBits V k) : Slot T q → BagPM bags :=
  runSample (ladderScan hbags hG rank parent hb hne hp hq w M k) s n bits



open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance instDecidableEqBagPM_3 : DecidableEq (BagPM bags) := Classical.decEq _

attribute [local instance] prodOrder sumOrder

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

def ladderBitRun {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) (bits : Fin (n*scanBitCount (Fintype.card V) k) → Bool) :
    Slot T q → BagPM bags :=
  ladderRun hbags hG rank parent hb hne hp hq w M k n s (runBitsEquiv V k n bits)

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_DiscreteLadderSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

attribute [local instance] prodOrder sumOrder

noncomputable local instance instDecidableEqBagPM_4_r8038f5_1 : DecidableEq (BagPM bags) := Classical.decEq _
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

def finiteLadder (D K T m : ℕ) (hq : 0<ladderQ (Fintype.card V) D)
    (w : BagEdge bags → ℚ) (M : BagPM bags) (η : ℚ)
    (s : Slot T (ladderQ (Fintype.card V) D) → BagPM bags) :
    (Fin (discreteLadderSteps (Fintype.card V) D K T m * scanBitCount (Fintype.card V)
      (bitPrecision (discreteLadderSteps (Fintype.card V) D K T m *
        scanErrorNumerator V L bags T (ladderQ (Fintype.card V) D)) η)) → Bool) →
        Slot T (ladderQ (Fintype.card V) D) → BagPM bags :=
  ladderBitRun hbags hG rank parent hb hne hp hq w M
    (bitPrecision (discreteLadderSteps (Fintype.card V) D K T m *
      scanErrorNumerator V L bags T (ladderQ (Fintype.card V) D)) η)
    (discreteLadderSteps (Fintype.card V) D K T m) s

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

def tick (M : Table Γ Q) (c : Cfg Γ Q) (b : Bool) : Cfg Γ Q :=
  match c.state with
  | none => c
  | some q => match M q c.tape.head b with
    | none => ⟨none,c.tape⟩
    | some (q',a) => ⟨some q',match a with
      | .move d => c.tape.move d
      | .write s => c.tape.write s⟩

def execute (M : Table Γ Q) : ℕ → Cfg Γ Q → Stream → Cfg Γ Q
  | 0,c,_ => c
  | n+1,c,b => execute M n (tick M c (b 0)) (shift 1 b)

variable [Fintype Q] [Inhabited Q]

noncomputable def machine (M : Table Symbol Q) : RandomMachine where
  states := Fintype.card Q-1
  transition q a b := (M ((enumeration (Q:=Q)).symm q) a b).map
    (fun qa=>(enumeration qa.1,qa.2))

noncomputable def sealCfg (M : Table Symbol Q) (c : Cfg Symbol Q) : Configuration (machine M) :=
  ⟨c.state.map enumeration,c.tape⟩

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

noncomputable def restrict (M : Table Γ Q) (S : Finset Q) (_h : Supported M S) :
    Table Γ {q // q∈S} := by
  classical
  exact fun q a b=>(M q.val a b).map (fun qa=>
    ((if hm:qa.1∈S then ⟨qa.1,hm⟩ else q),qa.2))

def liftCfg (S : Finset Q) (c : Cfg Γ {q // q∈S}) : Cfg Γ Q :=
  ⟨c.state.map Subtype.val,c.tape⟩

noncomputable def restrictedMachine (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S) : RandomMachine :=
  letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  machine (restrict M S h)

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SafeTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SafeTrace
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

inductive Path (M : Λ → TM1.Stmt Γ Λ σ) (safe : Λ → Prop) :
    ℕ → TM1.Cfg Γ Λ σ → TM1.Cfg Γ Λ σ → Prop
  | refl (c) : Path M safe 0 c c
  | cons {n c d} (hc : ∀ l,c.l=some l→safe l)
      (rest : Path M safe n (advance (TM1.step M) c) d) : Path M safe (n+1) c d

end MatchingFPRAS.SafeTrace

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

inductive Implements (M : Table Γ Q) (out : α → Cfg Γ Q) :
    Cfg Γ Q → Experiment α → Prop
  | done (a) : Implements M out (out a) (.done a)
  | read (c) (f : Bool → Experiment α)
      (h : ∀ b,Implements M out (tick M c b) (f b)) : Implements M out c (.read f)
  | delay (c d) (n : ℕ) (p : Experiment α)
      (step : ∀ b : Stream,execute M n c b=d)
      (rest : Implements M out d p) : Implements M out c (.delay n p)

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PhysicalAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream BoolPostCompiler

variable {Q : Type}

def liftBool (M : Table Bool Q) : Table Symbol Q := fun q a b=>
  (M q (down a) b).map (fun qa=>(qa.1,qa.2.map up))
def upCfg (c : Cfg Bool Q) : Cfg Symbol Q := ⟨c.state,c.tape.map up⟩
lemma liftBool_supported (M : Table Bool Q) (S : Finset Q) (hS : Supported M S) :
    Supported (liftBool M) S := by
  intro q hq a b q' act he
  simp only [liftBool,Option.map_eq_some_iff] at he
  obtain ⟨⟨q'',act'⟩,h,e⟩:=he
  have hqq : q''=q':=congrArg Prod.fst e
  subst q''
  exact hS q hq (down a) b q' act' h
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_OnlineStackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream SafeTrace
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
abbrev Q (K : Type) (Γ : K → Type) (Λ σ : Type) := CoinTM1.State Bool (L2 K Γ Λ σ) σ

variable (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
noncomputable def coin2 := CoinAlphabet.coins (Γ:=Alpha K Γ) (σ:=σ) (CoinStack.coins (Γ:=Γ) (σ:=σ) coin)
noncomputable def table := CoinTM1.table (program2 M) (coin2 coin)
noncomputable def states := CoinTM1.states (program2 M) (support2 M)
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma coin2_supported [Inhabited Λ] [Inhabited σ] [Fintype σ] :
    ∀ l∈support2 M,∀ f,coin2 coin l=some f→∀ b,f b∈support2 M :=
  CoinAlphabet.coins_supported (program1 M) (support1 M) _
    (CoinStack.coins_supported M Finset.univ coin (fun _ _ _ _ _=>Finset.mem_univ _))
lemma table_supported : PhysicalPost.Supported (table M coin) (states M) :=
  CoinTM1.table_supported (program2 M) (support2 M) (supports2 M) (coin2 coin) (coin2_supported M coin)
noncomputable def cfg (c : TM2.Cfg Γ Λ σ) : PhysicalPost.Cfg Bool (Q K Γ Λ σ) :=
  CoinTM1.trCfg (TM1to1.trCfg enc enc0 (stackCfg c))

noncomputable def overhead : ℕ :=
  (AlphabetCost.supportedWrites (program1 M) (support1 M)+1)*
    SupportedCompiler.cost (program2 M) (support2 M)

noncomputable def initialState : Q K Γ Λ σ :=
  (.inl (.normal (.normal default)),default)
lemma initialState_mem : initialState (K:=K) (Γ:=Γ) (Λ:=Λ) (σ:=σ)∈states M := by
  apply CoinTM1.state_mem
  apply CoinTM1.node_entry
  apply (CoinAlphabet.normal_mem _ _ _).mpr
  exact (CoinStack.normal_mem M Finset.univ default).mpr (Finset.mem_univ default)

end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Online
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

inductive Executes (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
    (out : α → TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ → Experiment α → Prop
  | done (a) : Executes M coin out (out a) (.done a)
  | read (l v S) (f : Bool → Λ) (p : Bool → Experiment α)
      (hf : coin l=some f)
      (rest : ∀ b,Executes M coin out ⟨some (f b),v,S⟩ (p b)) :
      Executes M coin out ⟨some l,v,S⟩ (.read p)
  | step (l v S) (p : Experiment α) (safe : coin l=none)
      (rest : Executes M coin out (TM2.stepAux (M l) v S) p) :
      Executes M coin out ⟨some l,v,S⟩ (.delay 1 p)

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
lemma bind {β : Type} (h : Executes M coin out c p) (q : α → Experiment β)
    (out' : β → TM2.Cfg Γ Λ σ) (hq : ∀ a,Executes M coin out' (out a) (q a)) :
    Executes M coin out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read l v S f p hf rest ih => exact .read l v S f _ hf ih
  | step l v S p safe rest ih => exact .step l v S _ safe ih

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

noncomputable def factor (M : Λ → TM2.Stmt Γ Λ σ) (H n : ℕ) : ℕ :=
  overhead M*(1+2*accesses M*(H+n*accesses M+1))+1
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_OnlineComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream StackComposition

variable {K Λ Λ' σ α : Type} {Γ : K → Type} [DecidableEq K]
namespace Executes
lemma relabel {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
    {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
    (h : Executes M coin out c p) (N : Λ' → TM2.Stmt Γ Λ' σ)
    (co : CoinTM1.Coins Λ') (f : Λ → Λ') (halt : Option Λ')
    (hN : ∀ l,N (f l)=StackComposition.relabel f halt (M l))
    (hco : ∀ l,co (f l)=(coin l).map (fun g=>f ∘ g)) :
    Executes N co (fun a=>mapCfg f halt (out a)) (mapCfg f halt c) p := by
  induction h with
  | done a => exact .done a
  | read l v S g p hg rest ih =>
    apply Executes.read (f l) v S (f ∘ g) p
    · rw [hco,hg]; rfl
    · exact ih
  | step l v S p hs rest ih =>
    apply Executes.step (f l) v S p
    · rw [hco,hs]; rfl
    · rw [hN,StackComposition.relabel_eval]
      exact ih

lemma of_run (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ) (c : TM2.Cfg Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ p : Experiment Unit,Executes M (fun _=>none) (fun _ : Unit=>⟨none,v,S⟩) c p ∧
      (∀ f : Unit → ℚ,p.mean f=f ()) ∧ p.cost≤n := by
  induction n generalizing c with
  | zero => cases he; exact ⟨.done (),.done (),fun _=>rfl,le_rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [StackComposition.run_halted] at he
      cases he
      exact ⟨.done (),.done (),fun _=>rfl,Nat.zero_le _⟩
    | some l =>
      obtain ⟨p,hp,hm,hc⟩:=ih (TM2.stepAux (M l) v' S') he
      exact ⟨.delay 1 p,.step l v' S' p rfl hp,hm,by simpa [Experiment.cost,Nat.add_comm] using Nat.succ_le_succ hc⟩
end Executes
end MatchingFPRAS.OnlineStack

namespace MatchingFPRAS.OnlineProc
open Turing MachineCost PhysicalStream OnlineStack RegisterProc

variable {K : Type} [DecidableEq K]

structure Proc (K : Type) extends RegisterProc.Proc K where
  coin : CoinTM1.Coins Label

def deterministic (P : RegisterProc.Proc K) : Proc K := ⟨P,fun _=>none⟩
def seq (P Q : Proc K) : Proc K where
  toProc := RegisterProc.seq P.toProc Q.toProc
  coin := fun l=>match l with
    | .inl l => (P.coin l).map (fun f b=>Sum.inl (f b))
    | .inr l => (Q.coin l).map (fun f b=>Sum.inr (f b))

end MatchingFPRAS.OnlineProc

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineControl
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineControl
open TreeData TreeMachine RegisterProc Turing MachineCost PhysicalStream OnlineStack

variable {R Λ α : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : OnlineProc.Proc (K R)) (next : Λ)

def procedure : Instr R Λ → OnlineProc.Proc (K R)
  | .call P _ => P
  | _ => OnlineProc.deterministic (atom .halt)
def successor : Instr R Λ → Option Λ
  | .call _ l => some l
  | _ => none
abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance instFintypeLabel (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | .call _ _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)
def coins (M : Λ → Instr R Λ) : CoinTM1.Coins (Label M)
  | .inl _ => none
  | .inr ⟨l,u⟩ => ((procedure (M l)).coin u).map (fun g b=>.inr ⟨l,g b⟩)
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : OnlineProc.Proc (K R) :=
  { toProc := { Label := Label M, entry := ⟨.inl default⟩, code := code M }, coin := coins M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩
def At (M : Λ → Instr R Λ) (out : α → Env R) (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) (fun a=>cfg M none (out a)) (cfg M l E) p

lemma done (M : Λ → Instr R Λ) (out : α → Env R) (a : α) :
    At M out none (out a) (.done a) := .done a
lemma halt (M : Λ → Instr R Λ) (out : α → Env R) (l : Λ) (h : M l=.halt) (a : α) :
    At M out (some l) (out a) (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,cfg,Option.map_none] using done M out a
lemma nilBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (hi : E i=.nil)
    (p : Experiment α) (hp : At M out (some a) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false,
    cfg,Option.map_some] using hp
lemma consBranch (M : Λ → Instr R Λ) (out : α → Env R) (l a b : Λ) (i : R)
    (h : M l=.branch i a b) (E : Env R) (x y : Data) (hi : E i=.cons x y)
    (p : Experiment α) (hp : At M out (some b) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true,
    cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b=>⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b=>⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh := hq'.relabel (code M) (coins M) (fun u=>Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _=>rfl) (fun _=>rfl)
  apply Executes.step _ _ _ _ rfl
  have hb := hh.bind p (fun a=>cfg M none (out a)) (fun b=>by
    simpa only [At,cfg,Option.map_none,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Env R) (l next : Λ)
    (P : RegisterProc.Proc (K R)) (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _=>p)),call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit=>F)
    r hr (fun _=>p) (fun _=>hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _=>p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _=>p) p.cost (fun _=>le_rfl)
    simp only [Experiment.cost]
    omega
end MatchingFPRAS.OnlineControl

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing MachineCost PhysicalStream OnlineStack TreeData TreeMachine TreeFunction TreeTyped

abbrev StoreCfg (P : OnlineProc.Proc (K Reg)) := TM2.Cfg (fun _ : K Reg=>Bool) P.Label RegisterProc.Store
variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def chooseProgram (P Q : OnlineProc.Proc (K Reg)) : OnlineProc.Proc (K Reg) where
  toProc := {
    Label := Unit ⊕ (P.Label ⊕ Q.Label)
    entry := ⟨.inl ()⟩
    code := fun l=>match l with
      | .inl _ => .halt
      | .inr (.inl l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inl u)) none (P.code l)
      | .inr (.inr l) => StackComposition.relabel (fun u=>Sum.inr (Sum.inr u)) none (Q.code l) }
  coin := fun l=>match l with
    | .inl _ => some (fun b=>if b then .inr (.inr default) else .inr (.inl default))
    | .inr (.inl l) => (P.coin l).map (fun f b=>.inr (.inl (f b)))
    | .inr (.inr l) => (Q.coin l).map (fun f b=>.inr (.inr (f b)))

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineFold
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

def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .loop => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (OnlineProc.deterministic (TreeFunction.split 3 1 (by decide))) .pushTail
  | .pushTail => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .pushArgs
  | .pushArgs => .call (OnlineProc.deterministic (TreeFunction.cons 3 0 (by decide))) .body
  | .body => .call P .popTail
  | .popTail => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .rebuild
  | .rebuild => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .loop
  | .halt => .halt
end Fold

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineFrame
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

def code (P : OnlineProc.Proc (K Reg)) : Point → OnlineControl.Instr Reg Point
  | .split => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .save
  | .save => .call (OnlineProc.deterministic (TreeFunction.cons 1 2 (by decide))) .body
  | .body => .call P .pop
  | .pop => .call (OnlineProc.deterministic (TreeFunction.split 1 2 (by decide))) .cons
  | .cons => .call (OnlineProc.deterministic (TreeFunction.cons 1 0 (by decide))) .halt
  | .halt => .halt
end Second

end MatchingFPRAS.OnlineTree

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

lemma level_cast (H : ℕ) (x : ℚ) : level H x=Hierarchy.dyadicLevel H (x:ℝ) := by
  apply Fin.ext
  change Nat.findGreatest (fun k => (2:ℚ)^k≤x) H = Nat.findGreatest (fun k => (2:ℝ)^k≤(x:ℝ)) H
  have h : (fun k => (2:ℚ)^k≤x) = (fun k => (2:ℝ)^k≤(x:ℝ)) := by
    funext k
    apply propext
    norm_cast
  simp only [h]

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

def logicalB (w : V → V → ℚ) : V → V → ℚ :=
  BottleneckAlgorithm.close w (Fintype.card V)

omit [Nontrivial V] in
lemma logicalB_cast [Nontrivial V] (w : V → V → ℚ) (x y : V) :
    (logicalB w x y:ℝ)=bottleneck (fun x y=>(w x y:ℝ)) x y :=
  BottleneckAlgorithm.rational_close_eq w x y

def height (w : V → V → ℚ) (x : V) : ℚ :=
  (univ.erase x).sup' (row_nonempty x) (logicalB w x)

lemma height_cast (w : V → V → ℚ) (x : V) :
    (height w x:ℝ)=sourceHeight (fun x y=>(w x y:ℝ)) x := by
  unfold height sourceHeight
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x:ℚ=>(x:ℝ)) (by intro x y; exact Rat.cast_max x y)]
  apply Finset.sup'_congr _ rfl
  intro y _
  exact logicalB_cast w x y

def maxHeight (w : V → V → ℚ) : ℚ := univ.sup' univ_nonempty (height w)

lemma maxHeight_cast (w : V → V → ℚ) :
    (maxHeight w:ℝ)=maxSourceHeight (fun x y=>(w x y:ℝ)) := by
  unfold maxHeight maxSourceHeight
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x:ℚ=>(x:ℝ)) (by intro x y; exact Rat.cast_max x y)]
  apply Finset.sup'_congr _ rfl
  intro x _
  exact height_cast w x

def levels (w : V → V → ℚ) (K : ℕ) : ℕ :=
  (NumberedHierarchy.level (2*K) (maxHeight w)).val

lemma levels_eq (w : V → V → ℚ) (K : ℕ) :
    levels w K=sourceLevels (fun x y=>(w x y:ℝ)) K := by
  simp only [levels,NumberedHierarchy.level_cast,maxHeight_cast,sourceLevels]

lemma profile_cast (p : ℕ) (B Hu Hv lam : ℚ) (i : Fin (4*p+1)) :
    (profile p B Hu Hv lam i:ℝ)=profileActivity p B Hu Hv lam i := by
  rcases lt_trichotomy i.val (2*p) with h|h|h
  · rw [profile,ite_eq_left h,profile_left _ _ _ _ _ _ h]
    norm_cast
  · have he : i=⟨2*p,by omega⟩:=Fin.ext h
    rw [he]
    simp [profile]
  · rw [profile,ite_eq_right (by omega),ite_eq_right (by omega),profile_right _ _ _ _ _ _ h]
    norm_cast

def pathActivity (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) : Fin (4*(2*K+2)+1) → ℚ :=
  profile (2*K+2) (logicalB w (source e) (target e)) (height w (source e))
    (height w (target e)) (BottleneckAlgorithm.edge w (source e) (target e))

lemma pathActivity_cast (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) (i : Fin (4*(2*K+2)+1)) :
    (pathActivity w K e i:ℝ) = Enlargement.pathActivity (2*K+2)
      (fun e=>bottleneck (fun x y=>(w x y:ℝ)) (source e) (target e))
      (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (source e))
      (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (target e))
      (logicalActivity (fun x y=>(w x y:ℝ))) e i := by
  rw [pathActivity,profile_cast,logicalB_cast,height_cast,height_cast]
  congr 1
  have he : source e<target e:=e.property
  simp [BottleneckAlgorithm.edge,logicalActivity,edgeActivity,he]

def activity (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) : ℚ :=
  ∑ q : SourceRealEdge V K,
    if RealGeometry.edge source target (4*(2*K+2)) q.1 q.2=s(x,y)
      then pathActivity w K q.1 q.2 else 0

lemma activity_cast (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    (activity w K x y:ℝ)=RealGeometry.activity source target (4*(2*K+2))
      (Enlargement.pathActivity (2*K+2)
        (fun e=>bottleneck (fun x y=>(w x y:ℝ)) (source e) (target e))
        (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (source e))
        (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (target e))
        (logicalActivity (fun x y=>(w x y:ℝ)))) x y := by
  unfold activity RealGeometry.activity
  push_cast
  apply sum_congr rfl
  intro q _
  split_ifs
  · exact pathActivity_cast w K q.1 q.2
  · norm_cast

def realB (w : V → V → ℚ) (K : ℕ) : SourceVertex V K → SourceVertex V K → ℚ :=
  BottleneckAlgorithm.close (activity w K) (Fintype.card (SourceVertex V K))

lemma realB_cast (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    (realB w K x y:ℝ)=sourceRealB (fun x y=>(w x y:ℝ)) K x y := by
  rw [realB,BottleneckAlgorithm.rational_close_eq]
  unfold sourceRealB realBottleneck
  congr 2
  funext a b
  exact activity_cast w K a b

lemma realB_symm (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    realB w K x y=realB w K y x := by
  apply Rat.cast_injective (α:=ℝ)
  simp only [realB_cast,sourceRealB_comm]

lemma realB_tri (w : V → V → ℚ) (K : ℕ) (x y z : SourceVertex V K)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    min (realB w K x z) (realB w K z y) ≤ realB w K x y := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simp only [Rat.cast_min,realB_cast]
  exact sourceRealB_tri _ _ _ _ _ hxy hxz hyz

abbrev Label (w : V → V → ℚ) (K : ℕ) := NumberedHierarchy.Label (realB w K) (levels w K)

theorem label_card (w : V → V → ℚ) (K : ℕ) :
    Fintype.card (Label w K)≤(2*K+1)*Fintype.card (SourceVertex V K) := by
  calc
    _ ≤ (levels w K+1)*Fintype.card (SourceVertex V K) := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ k : Fin (levels w K+1),Fintype.card (SourceVertex V K) :=
          sum_le_sum (fun k _=>Fintype.card_subtype_le _)
        _ = _ := by simp
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      rw [levels_eq]
      exact Nat.add_le_add_right (sourceLevels_le _ _) 1

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

omit [Fintype V] [Nontrivial V] in
lemma raw_cast [Fintype V] [Nontrivial V] (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    ∀ x y,x≠y → edgeActivity (fun x y=>(w x y:ℝ)) x y≤(4:ℝ)^K := by
  intro x y hxy
  have he : ((BottleneckAlgorithm.edge w x y:ℚ):ℝ)=edgeActivity (fun x y=>(w x y:ℝ)) x y := by
    unfold BottleneckAlgorithm.edge edgeActivity
    split_ifs <;> rfl
  simpa only [he,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (h x y hxy)

lemma realB_floor (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) : 1 ≤ realB w K x y := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [Rat.cast_one,realB_cast] using sourceRealB_floor (fun x y=>(w x y:ℝ)) K x y

lemma realB_upper (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) (e : SourceRealEdge V K) :
    realB w K (realLeft K e) (realRight K e)<(2:ℚ)^(levels w K+1) := by
  apply (Rat.cast_lt (K:=ℝ)).mp
  simpa only [realB_cast,levels_eq,Rat.cast_pow,Rat.cast_ofNat] using
    (source_strength_le_max (fun x y=>(w x y:ℝ)) K (raw_cast w K h) e).trans_lt
      (maxSourceHeight_lt (fun x y=>(w x y:ℝ)) K (raw_cast w K h))

lemma realB_near (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (x : SourceVertex V K) (e f : SourceRealEdge V K)
    (he : Hierarchy.Incident (realLeft K) (realRight K) e x)
    (hf : Hierarchy.Incident (realLeft K) (realRight K) f x) :
    realB w K (realLeft K e) (realRight K e)≤2*realB w K (realLeft K f) (realRight K f) := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [realB_cast,Rat.cast_mul,Rat.cast_ofNat] using
    source_strength_incident_near (fun x y=>(w x y:ℝ)) K (raw_cast w K h) x e f he hf

omit [Fintype V] in
lemma incident_exists [Fintype V] (K : ℕ) (x : SourceVertex V K) :
    ∃ e,Hierarchy.Incident (realLeft K) (realRight K) e x := by
  cases x with
  | inl x =>
    obtain ⟨y,hy⟩ := exists_ne x
    rcases lt_or_gt_of_ne hy with h | h
    · let e : LogicalEdge V := ⟨(y,x),h⟩
      refine ⟨(e,Fin.last (4*(2*K+2))),Or.inr ?_⟩
      simp [realRight,atVertex_last,target,e]
    · let e : LogicalEdge V := ⟨(x,y),h⟩
      refine ⟨(e,0),Or.inl ?_⟩
      simp [realLeft,atVertex_zero,source,e]
  | inr q =>
    obtain ⟨e,i⟩ := q
    refine ⟨(e,i.castSucc),Or.inr ?_⟩
    change Sum.inr (e,i)=atVertex source target _ e i.castSucc.succ
    have he : i.castSucc.succ=i.succ.castSucc := Fin.ext rfl
    rw [he,atVertex_internal]

omit [Nontrivial V] in
lemma real_not_diag [Nontrivial V] (K : ℕ) (e : SourceRealEdge V K) :
    ¬(edge source target (4*(2*K+2)) e.1 e.2).IsDiag := by
  rw [edge,Sym2.mk_isDiag_iff]
  intro he
  have hi := atVertex_injective source target (4*(2*K+2)) e.1 (source_ne_target e.1) he
  have := congrArg Fin.val hi
  simp at this

lemma pathActivity_pos (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : LogicalEdge V) (i : Fin (4*(2*K+2)+1)) : 0<pathActivity w K e i := by
  have hb : 0<logicalB w (source e) (target e) := by
    have h : (1:ℝ)≤(logicalB w (source e) (target e):ℝ) := by
      rw [logicalB_cast]; exact one_le_bottleneck _ _ _
    have : (1:ℚ)≤logicalB w (source e) (target e) := by exact_mod_cast h
    linarith
  unfold pathActivity profile
  split_ifs
  · exact hb.trans_le (le_max_left _ _)
  · unfold BottleneckAlgorithm.edge
    split_ifs <;> exact hw _ _
  · exact hb.trans_le (le_max_left _ _)

def bagHeight (w : V → V → ℚ) (K : ℕ) (l : Label w K) : ℚ := 2^l.1.val

lemma bagHeight_one (w : V → V → ℚ) (K : ℕ) (l : Label w K) : 1≤bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

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

namespace MatchingFPRAS.Transport

open Finset

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
    [Fintype J] [DecidableEq J]

variable {b : V → Finset L} {c : V → Finset J}

def relabelEdge (e : L ≃ J) (h : ∀ v,(b v).image e=c v) (a : BagEdge b) : BagEdge c :=
  ⟨⟨(a.val.val.1,e a.val.val.2),a.val.property⟩,by
    intro v hv
    change e a.val.val.2∈c v
    rw [←h v]
    exact mem_image.mpr ⟨a.val.val.2,a.property v hv,rfl⟩⟩

def relabelEdgeEquiv (e : L ≃ J) (h : ∀ v,(b v).image e=c v) : BagEdge b ≃ BagEdge c where
  toFun:=relabelEdge e h
  invFun:=relabelEdge e.symm (image_symm_bags e h)
  left_inv a := by apply Subtype.ext; apply Subtype.ext; simp [relabelEdge]
  right_inv a := by apply Subtype.ext; apply Subtype.ext; simp [relabelEdge]


variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable {inc : E → V → Prop} {j : F → V → Prop}

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype F] in
lemma MatchingOn.image (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    {M : Finset E} {U : Finset V} (hM : MatchingOn inc M U) :
    MatchingOn j (M.image e) U := by
  constructor
  · intro f hf v hv
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hf
    exact hM.1 a ha v ((he a v).mp hv)
  · intro v hv
    obtain ⟨a,⟨ha,hav⟩,hu⟩:=hM.2 v hv
    refine ⟨e a,⟨mem_image.mpr ⟨a,ha,rfl⟩,(he a v).mpr hav⟩,?_⟩
    rintro f ⟨hf,hfv⟩
    obtain ⟨d,hd,rfl⟩:=mem_image.mp hf
    exact congrArg e (hu d ⟨hd,(he d v).mp hfv⟩)

def pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) : PM inc ≃ PM j where
  toFun M:=⟨M.val.image e,M.property.image e he⟩
  invFun M:=⟨M.val.image e.symm,M.property.image e.symm (by intro a v; simpa using (he (e.symm a) v).symm)⟩
  left_inv M:=by apply Subtype.ext; simp [image_image]
  right_inv M:=by apply Subtype.ext; simp [image_image]

omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma matchingWeight_pmEquiv [DecidableEq V] [Fintype E] [Fintype F]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) (M : PM inc) : matchingWeight w (pmEquiv e he M)=matchingWeight (w ∘ e) M := by
  unfold matchingWeight pmEquiv
  exact Finset.prod_image (fun _ _ _ _ h=>e.injective h)


end MatchingFPRAS.Transport

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqLabelOfFintype {X : Type*} [Fintype X] (B : X → X → ℝ)
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y) (H : ℕ) :
    DecidableEq (Hierarchy.Label B s t H) := Classical.decEq _

noncomputable def labelCast {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') :
    Hierarchy.Label B s t H ≃ Hierarchy.Label B' s' t' H' :=
  Equiv.cast (by cases hB;cases hH;rfl)

lemma labelCast_bags {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]
    {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    (u v : E → X) {H H' : ℕ} (hB : B=B') (hH : H=H') (x : X) :
    (memberships B s t u v H x).image (labelCast s t s' t' hB hH)=
      memberships B' s' t' u v H' x := by
  classical
  cases hB;cases hH
  simp [labelCast]

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

lemma labelCast_edgeLabel {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]
    {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    (u v : E → X) {H H' : ℕ} (hB : B=B') (hH : H=H') (e : E) :
    labelCast s t s' t' hB hH (Hierarchy.edgeLabel B s t u v H e)=
      Hierarchy.edgeLabel B' s' t' u v H' e := by
  cases hB;cases hH;rfl

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
noncomputable local instance instDecidableEqSourceLabelCastReal (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StageAnalysis

open Finset MatchingFPRAS.Switching MatchingFPRAS.Initializer

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma partition_pos_of_even (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (R : Finset V) (he : Even (Fintype.card V-R.card)) : 0 < partition w R := by
  have hm : 0 < (matchings R).card := by rw [matchings_card]; exact pairingCount_pos_of_even _ he
  apply Finset.sum_pos
  · intro m _
    unfold weight
    apply Finset.prod_pos
    intro x _
    split_ifs <;> first | exact hw _ _ | norm_num
  · exact Finset.card_pos.mp hm



open Finset MatchingFPRAS.Switching

end MatchingFPRAS.StageAnalysis

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset



open Finset

variable {n : ℕ}

structure ScaleInvariant (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : Prop where
  lower : ∀ i, alpha/2 ≤ v i
  upper : ∀ i, v i ≤ 2
  feasible : ∀ i j, i≠j → G i j ≤ v i*v j

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

lemma selected_increasing (s : LogicalEdge (Fin n) → Bool) :
    selectedEdges s ⊆ (completeGraph n).edges := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_map.mp he
  exact mem_filter.mpr ⟨mem_univ _,f.property⟩

lemma selected_edgeSelection (M : Finset (Fin n × Fin n)) (hM : M⊆(completeGraph n).edges) :
    selectedEdges (edgeSelection M)=M := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    simpa [edgeSelection,endpoints] using (mem_filter.mp hf).2
  · intro he
    have hi : e.1 < e.2 := (mem_filter.mp (hM he)).2
    apply mem_map.mpr
    exact ⟨⟨e,hi⟩,mem_filter.mpr ⟨mem_univ _,by simp [edgeSelection,he]⟩,rfl⟩

lemma logical_iff_perfect (s : LogicalEdge (Fin n) → Bool) :
    LogicalHoles source target ∅ ∅ s ↔ Perfect (completeGraph n) (selectedEdges s) := by
  constructor
  · intro hs
    refine ⟨selected_increasing s,?_⟩
    intro v
    obtain ⟨e,he,hu⟩ := hs.2.2 v (by simp)
    refine ⟨e.val,⟨(mem_selected s e).mpr he.1,he.2⟩,?_⟩
    intro f hf
    have hi := (completeGraph n).increasing f (selected_increasing s hf.1)
    have hf' : s ⟨f,hi⟩=true := (mem_selected s ⟨f,hi⟩).mp hf.1
    exact congrArg Subtype.val (hu ⟨f,hi⟩ ⟨hf',hf.2⟩)
  · intro hs
    refine ⟨by simp,by simp,?_⟩
    intro v _
    obtain ⟨e,he,hu⟩ := hs.2 v
    have hi := (completeGraph n).increasing e (hs.1 he.1)
    refine ⟨⟨e,hi⟩,⟨(mem_selected s ⟨e,hi⟩).mp he.1,he.2⟩,?_⟩
    intro f hf
    exact Subtype.ext (hu f.val ⟨(mem_selected s f).mpr hf.1,hf.2⟩)

noncomputable def perfectEquiv :
    {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s} ≃
      {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M} where
  toFun s := ⟨selectedEdges s.val,(logical_iff_perfect s.val).mp s.property⟩
  invFun M := ⟨edgeSelection M.val,(logical_iff_perfect _).mpr (by
    rw [selected_edgeSelection M.val M.property.1]; exact M.property)⟩
  left_inv s := Subtype.ext (edgeSelection_selected s.val)
  right_inv M := Subtype.ext (selected_edgeSelection M.val M.property.1)

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} {j K S : ℕ}

lemma ScaleState.cap (s : ScaleState G j) (h : j ≤ K) (a b : Fin G.n) (_hab : a≠b) :
    edgeActivity s.activity a b ≤ (4:ℝ)^K := by
  unfold edgeActivity
  split_ifs
  all_goals exact (s.activity_bound _ _).trans (pow_le_pow_right₀ (by norm_num) h)

lemma ScaleState.partition_pos (s : ScaleState G j) (he : Even G.n) : 0<partition s.activity ∅ := by
  apply partition_pos_of_even _ s.activity_pos
  simpa using he

def ScaleState.Balanced (hn : 2 ≤ G.n) (s : ScaleState G j) : Prop :=
  (∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using hn) s.activity i) ∧
  (∀ i,rowMax (by simpa using hn) s.activity i ≤ 1)

lemma initial_balanced (G : GraphInput) (hn : 2 ≤ G.n) (he : Even G.n) :
    (initialScaleState G hn).Balanced hn := by
  have h := Initializer.initial_balanced (V:=Fin G.n) (by simpa using hn) (by simpa using he)
  have ha : (initialScaleState G hn).activity=(fun _ _ : Fin G.n => (Initializer.initialScale G.n:ℝ)^2) := by
    funext a b
    simp [ScaleState.activity,raw_zero,initialScaleState,pow_two]
  simpa only [ScaleState.Balanced,ha,Fintype.card_fin] using h.2

variable [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_r8038f5_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable def ScaleState.matrix (s : ScaleState G j) (x : Fin S → SourceMarked s.activity K) :
    Fin G.n → Fin G.n → ℝ :=
  estimateMatrix (sourceD (V:=Fin G.n) K) (sampleAverage (observableD s.activity s.nextActivity K) x)
    (fun e => sampleAverage (observableProbe s.activity s.nextActivity K e) x)

noncomputable def ScaleState.ratioEstimate (s : ScaleState G j) (x : Fin S → SourceMarked s.activity K) : ℝ :=
  RealStage.ratioEstimate (sampleAverage (observableA s.activity K) x)
    (sampleAverage (observableD s.activity s.nextActivity K) x)

noncomputable def stageData (G : GraphInput) (hn : 2 ≤ G.n) (he : Even G.n) (K : ℕ) (hK : 0<K)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) (j : ℕ) (hj : j ≤ K) (s : ScaleState G j)
    (hs : s.Balanced hn) : StageData G.n K K where
  hn := hn
  w := s.activity
  next := s.nextActivity
  positive := s.activity_pos
  next_positive := s.nextActivity_pos
  partition_positive := s.partition_pos he
  lower := hs.1
  upper := hs.2
  cool_lower a b _ := (s.cooling a b).1
  cool_upper a b _ := (s.cooling a b).2
  cap := s.cap hj
  stages := hK
  epsilon := ε
  epsilon_positive := hε
  epsilon_lt_one := hε1

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TableMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TableMarking

open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

variable (inc : E → V → Prop)

abbrev Marked := Σ M : PM inc, (↥M.val → I)

def reveal (M : PM inc) (marks : E → I) : Marked (I:=I) inc := ⟨M,fun e=>marks e.val⟩

variable {A : Type*} [Fintype A] [Nonempty A]

def draw (f : A → PM inc) (c : E → WeightedOptions I) (k : ℕ)
    (bits : A×(E → Fin k → Bool)) : Marked (I:=I) inc :=
  reveal inc (f bits.1) (fun e=>(c e).draw k (bits.2 e))

noncomputable def law (w : E → ℝ) (c : E → WeightedOptions I) : Marked (I:=I) inc → ℝ :=
  sigmaLift (gibbs w) (fun M=>product (fun e : M.val=>portion c e.val))

end MatchingFPRAS.TableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelabelMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
def selectedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) :
    ↥M.val ≃ ↥(pmEquiv e he M).val where
  toFun a:=⟨e a.val,mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  invFun a:=⟨e.symm a.val,by
    obtain ⟨b,hb,heq⟩:=mem_image.mp a.property
    simpa [←heq] using hb⟩
  left_inv a:=by apply Subtype.ext; exact e.symm_apply_apply _
  right_inv a:=by apply Subtype.ext; exact e.apply_symm_apply _
def markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) :
    Marking.Marked (I:=I) inc ≃ Marking.Marked (I:=I) j :=
  Equiv.sigmaCongr (pmEquiv e he) (fun M=>Equiv.arrowCongr (selectedEquiv e he M) (Equiv.refl I))
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma markedEquiv_mark (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=I) inc) (x : a.1.val) :
    (markedEquiv e he a).2 (selectedEquiv e he a.1 x)=a.2 x := by
  change a.2 ((selectedEquiv e he a.1).symm (selectedEquiv e he a.1 x))=a.2 x
  rw [Equiv.symm_apply_apply]
end MatchingFPRAS.Transport

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
noncomputable local instance instDecidableEqSourceLabelCastReal_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalObservables
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
noncomputable local instance instDecidableEqSourceLabelCastReal_2 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _

def rawReweight (w w₁ : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : ℚ :=
  if e.2.val=2*(2*K+2) then BottleneckAlgorithm.edge w₁ (source e.1) (target e.1)/
    BottleneckAlgorithm.edge w (source e.1) (target e.1) else 1

omit [Fintype V] [Nontrivial V] in
lemma rawReweight_cast (w w₁ : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    (rawReweight w w₁ K q:ℝ)=Enlargement.rawReweight (fun x y=>(w x y:ℝ))
      (fun x y=>(w₁ x y:ℝ)) K q := by
  simp only [rawReweight,Enlargement.rawReweight]
  split_ifs
  · simp only [Rat.cast_div,BottleneckAlgorithm.edge,logicalActivity,Switching.edgeActivity]
    split_ifs <;> rfl
  · norm_cast
end MatchingFPRAS.RationalSource
namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma markedEquiv_marks_eq (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=I) inc) (r : F → I) :
    (markedEquiv e he a).2=(fun x=>r x.val) ↔ a.2=(fun x=>r (e x.val)) := by
  constructor
  · intro h
    funext x
    have hh:=congrFun h (selectedEquiv e he a.1 x)
    rw [markedEquiv_mark] at hh
    exact hh
  · intro h
    funext x
    obtain ⟨y,rfl⟩:=(selectedEquiv e he a.1).surjective x
    rw [markedEquiv_mark,congrFun h]
    rfl
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_zero (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) :
    (markedEquiv e he a).2=(fun _=>0) ↔ a.2=(fun _=>0) :=
  markedEquiv_marks_eq e he a (fun _=>0)
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelCastReal_3 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_3 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeFractionCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def height (x : Fraction) : ℕ := max x.1.size x.2.size
end MatchingFPRAS.TreeFraction

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
def logicalRepr (e : LogicalEdge (Fin n)) : RawLogical := (e.val.1.val,e.val.2.val)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePostRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

abbrev Alphabet := TM2to1.Γ' (K Reg) (fun _=>Bool)
end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitAssemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

noncomputable def resultRep {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) : Result := List.ofFn (fun i=>(p.pair.mate i |>.val,p.color i |>.val))

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeCycleTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] {V : Type} [Fintype V] [DecidableEq V]
variable (ends : E→Sym2 V) (p : C×(E×E)→Bool) (c : C)
variable (hp : ∀ a b,p (c,(a,b))=decide (∃ v,v∈ends a ∧ v∈ends b))
def pairRepr (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) : PairState E :=
  (a.1.val,a.2.val)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeMatchingCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

instance decideMatchingOn [Fintype E] [Fintype V] (inc : E→V→Prop) [DecidableRel inc] (M : Finset E) :
    Decidable (Transport.MatchingOn inc M Finset.univ) := by
  unfold Transport.MatchingOn ExistsUnique
  infer_instance

end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCertify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder

def pmEmbedding : @OrderEmbedding (Transport.PM (fun e v=>v∈ends e)) (Finset E)
    (Transport.Sparse.pmOrder ends).toLE (Transport.Sparse.finsetOrder (E:=E)).toLE :=
  { toFun := Subtype.val
    inj' := Subtype.val_injective
    map_rel_iff' := Iff.rfl }

end MatchingFPRAS.TreeTyped.SparseProgram

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

noncomputable local instance instDecidableEqBagPM : DecidableEq (BagPM bags) := Classical.decEq _
end MatchingFPRAS.NumericLadder

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
lemma pairIndex_involutive (he : Even n) : Function.Involutive (pairIndex he) := by
  intro i
  apply Fin.ext
  by_cases hi : i.val % 2 = 0
  · have hp : (i.val+1) % 2 ≠ 0 := by omega
    simp only [pairIndex, dite_eq_left hi, dite_eq_right hp]
    omega
  · have hp : (i.val-1) % 2 = 0 := by omega
    simp only [pairIndex, dite_eq_right hi, dite_eq_left hp]
    omega

def orderedMate (he : Even n) : Mate (Fin n) := ⟨pairIndex he,pairIndex_involutive he⟩
lemma orderedMate_holes (he : Even n) : HasHoles (orderedMate he) ∅ := by
  intro i
  simp only [Finset.notMem_empty,iff_false]
  exact pairIndex_ne he i

def selectMate (m : Mate (Fin n)) (e : LogicalEdge (Fin n)) : Bool :=
  decide (m.val (source e)=target e)
lemma selectMate_eq (m : Mate (Fin n)) : selectMate m=Representation.select m := by
  funext e
  exact rfl

def startSet (K : ℕ) (he : Even n) : Finset (SourceRealEdge (Fin n) K) :=
  univ.filter fun q=>alternating (selectMate (orderedMate he) q.1) q.2.val=true
variable [Nontrivial (Fin n)]
lemma startSet_matching (K : ℕ) (he : Even n) :
    MatchingOn (fun (q : SourceRealEdge (Fin n) K) x=>x∈edge source target (4*(2*K+2)) q.1 q.2)
      (startSet K he) univ := by
  have h:= (family_iff_matching source target (4*(2*K+2)) source_ne_target ∅ (fun _=>∅)
    (fun e i=>alternating (Representation.select (orderedMate he) e) i.val)).mp
      (intact_family (2*K+2) (orderedMate he) (orderedMate_holes he))
  rw [survivors_empty] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold startSet selectedSet
  rw [selectMate_eq]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

end MatchingFPRAS.RationalSource

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
def probeMatrix (z : LogicalEdge V → ℚ) (i j : V) : ℚ :=
  if hij : i=j then 0 else z (pairEdge i j hij)
lemma probeMatrix_cast (z : LogicalEdge V → ℚ) (i j : V) :
    (probeMatrix z i j:ℝ)=Enlargement.probeMatrix (fun e=>(z e:ℝ)) i j := by
  simp only [probeMatrix,Enlargement.probeMatrix]
  split_ifs <;> norm_cast
lemma probeMatrix_symm (z : LogicalEdge V → ℚ) (i j : V) : probeMatrix z i j=probeMatrix z j i := by
  apply Rat.cast_injective (α:=ℝ)
  rw [probeMatrix_cast,probeMatrix_cast,Enlargement.probeMatrix_symm]
def estimateMatrix (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) : ℚ :=
  Counting.upperEstimate D dbar (probeMatrix zbar i j)
lemma estimateMatrix_symm (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    estimateMatrix D dbar zbar i j=estimateMatrix D dbar zbar j i := by
  rw [estimateMatrix,estimateMatrix,probeMatrix_symm]
lemma estimateMatrix_bounds (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    Counting.alpha≤estimateMatrix D dbar zbar i j ∧ estimateMatrix D dbar zbar i j≤3 := by
  unfold estimateMatrix Counting.upperEstimate
  split_ifs
  · exact ⟨le_max_left _ _,max_le (by norm_num [Counting.alpha]) (min_le_left _ _)⟩
  · norm_num [Counting.alpha]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericSummaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

abbrev Summaries := (Fraction×Fraction)×List (ℕ×Fraction)

def logicalProbes (x : Bindings×List (ℕ×Fraction)) : ExecutableAdaptive.ProbeTable :=
  x.1.map (fun z=>(z.1,lookup (0,1) (x.2,z.2)))

abbrev UpdateConfig := (ℕ×List ℕ)×(Bindings×ExecutableScaling.Vector)

end MatchingFPRAS.NumericMarking

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
noncomputable local instance finiteStageSourceLabelDecidableEq_r8038f5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance finiteStageSourceBagEdgeFintype (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedCastReal_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
end MatchingFPRAS.RationalSource

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

namespace MatchingFPRAS.Transport
open Finset

lemma bagEdge_card_le {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
    (bags : V → Finset L) [Fintype (BagEdge bags)] :
    Fintype.card (BagEdge bags) ≤ (Fintype.card V)^2*Fintype.card L := by
  classical
  have hi : Function.Injective (fun e : BagEdge bags=>e.val.val) :=
    Subtype.val_injective.comp Subtype.val_injective
  exact (Fintype.card_le_of_injective _ hi).trans (by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul_right _ (sym2_card_le_square V))
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Transport Enlargement Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelCastReal_4_r8038f5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_4 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instFintypeSourceMarkedCastReal_2 (w : V → V → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource NumericMarking OnlineSchedule

def finish (x : Fraction×Bool) : Fraction := if x.2 then x.1 else (0,1)
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
abbrev vertexCount := Fintype.card (SourceVertex (Fin n) K)
abbrev labelCount := Fintype.card (RationalSource.Label w K)
abbrev tierCount := Transport.endpoint (vertexCount (n:=n) K) D K Fintype.card_pos
abbrev copies := ladderQ (vertexCount (n:=n) K) D
abbrev scansCount := discreteLadderSteps (vertexCount (n:=n) K) D K (tierCount (n:=n) K D) m
end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTransitionLaw
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
noncomputable local instance instFintypeSourceMarkedFinCastReal : Fintype (SourceMarked (fun a b=>(w a b:ℝ)) K) := Fintype.ofFinite _
end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineGuardLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement Variation TreeTyped.Numbered
open scoped Classical

noncomputable local instance instFintypeSourceMarkedFin {n : ℕ} [Nontrivial (Fin n)] (w : Fin n→Fin n→ℝ) (K : ℕ) :
    Fintype (SourceMarked w K) := Fintype.ofFinite _
attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
end MatchingFPRAS.OnlineGuard

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

def relation (a b : Fraction) : Prop := a.1*b.2≤b.1*a.2
instance instDecidableRelFractionRelation : DecidableRel relation := fun _ _=>inferInstanceAs (Decidable (_≤_))

def sorted (xs : List Fraction) : List Fraction := xs.insertionSort relation

def median (xs : List Fraction) : Fraction := (sorted xs).getD (xs.length/2) (0,1)
end MatchingFPRAS.OnlineMedian

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

abbrev PowerSearchInput := (Fraction×Fraction)×List Bool

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

def natCeil (x : Fraction) : ℕ := (x.1+x.2-1)/x.2

def inverse (x : Fraction) : Fraction := normalize (x.2,x.1)
end MatchingFPRAS.TreeFraction

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

abbrev CoolingInput := ℕ×Fraction
def scheduleBound (x : CoolingInput) : ℕ := x.1*(x.1*x.1+32*natCeil (inverse x.2))

abbrev CoolingPowerInput := CoolingInput×List Bool
def coolingPowerPlan (x : CoolingPowerInput) : Fraction×Fraction :=
  (TreeFraction.add ((1,1),TreeFraction.div ((1,1),(x.1.1,1))),
    TreeFraction.div (TreeFraction.mul ((32,1),fuelPower ((x.1.1,1),x.2)),x.1.2))

def coolingSearchInput (x : CoolingInput) : PowerSearchInput :=
  (coolingPowerPlan (x,List.replicate (x.1/2) false),List.replicate (scheduleBound x) false)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineSampleCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

abbrev SigmaInput := (ℕ×ℕ)×Fraction

abbrev SampleCountInput := ℕ×SigmaInput

def sampleSumFn (x : SampleCountInput) : Fraction := (x.1+x.2.1.2+1,1)

variable {G : GraphInput} [Nontrivial (Fin G.n)]

def repetitions (x : Fraction) : ℕ := 10*(Nat.clog 2 (natCeil (inverse x))+1)+1
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

abbrev Seed := GraphData×(Fraction×Fraction)
abbrev Config := (Seed×ℕ)×(ℕ×ℕ)

def seedD (x : (Seed×ℕ)×ℕ) : Config :=
  (x.1,(x.2,distortion (x.1.1.1.1.length,x.2)))
def initialScale (n : ℕ) : Fraction := TreeFraction.div ((1,1),(root n,1))

def scaleVector (vs : List ℕ) : Vector := vs.map (fun i=>(i,initialScale vs.length))
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
def graph (g : GraphData) : GraphData := (g.1,f g.2)
def seed (x : OnlineInitial.Seed) : OnlineInitial.Seed := (graph f x.1,x.2)
end MatchingFPRAS.OnlineGraph

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineCase
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

def code (P Q : OnlineProc.Proc (K Reg)) : Point→OnlineControl.Instr Reg Point
  | .split => .call (OnlineProc.deterministic (TreeFunction.split 1 0 (by decide))) .test
  | .test => .branch 1 .noClear .yesClear
  | .yesClear => .call (OnlineProc.deterministic (TreeFunction.clear 1)) .yes
  | .noClear => .call (OnlineProc.deterministic (TreeFunction.clear 1)) .no
  | .yes => .call P .halt
  | .no => .call Q .halt
  | .halt => .halt
end Case
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

def ratWord (x : TreeFraction.Fraction) : List Symbol := 4::natWord x.1++natWord x.2
end MatchingFPRAS.LiteralCodec

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

abbrev Parsed := ℕ×(List (ℕ×ℕ)×(TreeFraction.Fraction×TreeFraction.Fraction))
def ratTail (ns : List ℕ) : TreeFraction.Fraction×TreeFraction.Fraction :=
  ((ns.tail.tail.tail.headD 0,ns.tail.tail.headD 0),(ns.tail.headD 0,ns.headD 0))

def fromNumbers (ns : List ℕ) : Parsed :=
  (ns.headD 0,(pairs ns.tail.tail.reverse.tail.tail.tail.tail,ratTail ns.tail.tail.reverse))

def parseInput (as : List Symbol) : Parsed := fromNumbers (LiteralParse.parse as)
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

def empty (x : Parsed) : Bool := decide (x.1=0)

def invalid (x : Parsed) : Bool := !(decide (x.1%2=0)) || ExecutableInput.tooSparse (x.1,x.2.1)

def materialize (x : Parsed) : OnlineInitial.Seed := ((List.range x.1,x.2.1),x.2.2)
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSourceBounds
open BitComplexity Transport Polynomial TreeTyped

def normBound (x : ℕ) : ℕ :=
  2*x+boundK x+boundN x+boundD x+boundS x+
    tierPolynomial (boundN x) (boundD x) (boundK x)+
    ladderQ (boundN x) (boundD x)+(2*x)^2+3
end MatchingFPRAS.OnlineSourceBounds

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalSequential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

def seq (M : Table Γ Q) (N : Table Γ R) (r₀ : R) : Table Γ (Q⊕R)
  | .inl q,a,b => match M q a b with
    | none => some (.inr r₀,.write a)
    | some (q',act) => some (.inl q',act)
  | .inr r,a,b => (N r a b).map (fun ra=>(Sum.inr ra.1,ra.2))
def leftCfg (r₀ : R) (c : Cfg Γ Q) : Cfg Γ (Q⊕R) :=
  ⟨some (c.state.elim (Sum.inr r₀) Sum.inl),c.tape⟩
def rightCfg (c : Cfg Γ R) : Cfg Γ (Q⊕R) := ⟨c.state.map Sum.inr,c.tape⟩

def early (M : Table Γ Q) : ℕ→Cfg Γ Q→Experiment (Cfg Γ Q)
  | 0,c => .done c
  | n+1,c => match c.state with
    | none => .done c
    | some _ => .read (fun b=>early M n (tick M c b))
omit [Inhabited Γ] in
lemma seq_supported [Inhabited Γ] (M : Table Γ Q) (N : Table Γ R) (r₀ : R)
    (S : Finset Q) (T : Finset R) (hM : Supported M S) (hN : Supported N T) (hr : r₀∈T) :
    Supported (seq M N r₀) (S.disjSum T) := by
  intro q hq a b q' act he
  cases q with
  | inl q =>
    have hq':q∈S := Finset.inl_mem_disjSum.mp hq
    cases h:M q a b with
    | none => simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he;rcases he with ⟨rfl,rfl⟩;exact Finset.inr_mem_disjSum.mpr hr
    | some x =>
      rcases x with ⟨v,ac⟩
      simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact Finset.inl_mem_disjSum.mpr (hM q hq' a b v ac h)
  | inr r =>
    simp only [seq,Option.map_eq_some_iff] at he
    obtain ⟨⟨r',ac⟩,hh,e⟩:=he
    cases e
    exact Finset.inr_mem_disjSum.mpr (hN r (Finset.inr_mem_disjSum.mp hq) a b r' ac hh)
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TapeTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]

def Exec (M : Λ→TM1.Stmt Γ Λ σ) (c d : TM1.Cfg Γ Λ σ) (t : ℕ) : Prop :=
  ∃ k,k≤t ∧ MachineCost.run (TM1.step M) k c=d
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Physical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
noncomputable def table (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.table M (fun _=>none)
noncomputable def states (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.states M Finset.univ
omit [Inhabited Γ] [Inhabited σ] in
lemma supported (M : Λ→TM1.Stmt Γ Λ σ) : PhysicalPost.Supported (table M) (states M) :=
  CoinTM1.table_supported M Finset.univ (supports_univ M) (fun _=>none) (by simp)
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma entry_mem (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) : (Sum.inl l,v)∈states M :=
  CoinTM1.state_mem (CoinTM1.node_entry (Finset.mem_univ _))
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]

structure Program where
  State : Type
  table : Table Symbol State
  states : Finset State
  supported : Supported table states
  entry : State
  entry_mem : entry∈states
namespace Program
noncomputable def seq (P R : Program) : Program where
  State := P.State⊕R.State
  table := PhysicalPost.seq P.table R.table R.entry
  states := P.states.disjSum R.states
  supported := seq_supported _ _ _ _ _ P.supported R.supported R.entry_mem
  entry := .inl P.entry
  entry_mem := Finset.inl_mem_disjSum.mpr P.entry_mem
noncomputable def machine (P : Program) : RandomMachine :=
  restrictedMachine P.table P.states P.supported P.entry P.entry_mem

def initial (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨some P.entry,T⟩
def final (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨none,T⟩
def Realizes (P : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol)) (N : ℕ) : Prop :=
  ∃ p : Experiment (Tape Symbol),Implements P.table P.final (P.initial input) p ∧
    (∀ h,p.mean h=f.mean h) ∧ p.cost≤N

def earlyTapes (P : Program) (n : ℕ) (T : Tape Symbol) : Experiment (Tape Symbol) :=
  (early P.table n (P.initial T)).map Cfg.tape

noncomputable def ofTM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v : σ) : Program where
  State := CoinTM1.State Symbol Λ σ
  table := LiteralTape.table M
  states := LiteralTape.states M
  supported := LiteralTape.supported M
  entry := (.inl l,v)
  entry_mem := LiteralTape.entry_mem M l v
end Program
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Packed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

abbrev Row := K Reg→Option Bool
def baseRow : Row
  | .inl _ => some false
  | .inr _ => none
def bitRow (b : Bool) : Row := fun k=>if k=Sum.inl 0 then some b else none
def bottom : Alphabet := (true,baseRow)
def letter (b : Bool) : Alphabet := (false,bitRow b)

noncomputable def block (a : Alphabet) : List Symbol :=
  (FixedEncoding.enc Alphabet a).toList.map BoolPostCompiler.up
noncomputable def header : List Symbol := block bottom
noncomputable def width : ℕ := Fintype.card Alphabet
lemma map_enc_length {α : Type} [Fintype α] [Inhabited α] (a : α) :
    ((FixedEncoding.enc α a).toList.map BoolPostCompiler.up).length=Fintype.card α := by
  rw [List.length_map]
  exact (FixedEncoding.enc α a).2
lemma block_length (a : Alphabet) : (block a).length=width := by
  unfold width block
  exact map_enc_length a
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

noncomputable def erase : Program := Program.ofTM1 (LiteralTape.eraseCode header.length) () ()
noncomputable def eraseTime : ℕ := MachineCost.programCost (LiteralTape.eraseCode header.length)
end MatchingFPRAS.LiteralPhysical

end OAI
end


