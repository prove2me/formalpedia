-- Prove2me | Definitions.Def_OAIQ051M001
-- name    : OAIQ051M001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:12:34.367688+00:00
-- url     : https://prove2.me/theorems/e8ee8105-056e-4d8b-91d3-a1096b9e94d4
-- title:
--   Definitions bundle OAIQ051M001 of the split of OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 982 declarations of OpenAI's Lean: 625 definitions, 19 inductive types or structures, 20 instances and 318 theorems. The definitions and types are `OAI.MatchingFPRAS.ExecutableBottleneck.square`, `OAI.MatchingFPRAS.ExecutableDP.BInitial`, `OAI.MatchingFPRAS.ExecutableDP.Bag`, `OAI.MatchingFPRAS.ExecutableDP.Bags`, `OAI.MatchingFPRAS.ExecutableDP.CappedState`, `OAI.MatchingFPRAS.ExecutableDP.CountInput`, `OAI.MatchingFPRAS.ExecutableDP.EntryCtx`, `OAI.MatchingFPRAS.ExecutableDP.Parents`, `OAI.MatchingFPRAS.ExecutableDP.RawCtx`, `OAI.MatchingFPRAS.ExecutableDP.State`, `OAI.MatchingFPRAS.ExecutableDP.Table`, `OAI.MatchingFPRAS.ExecutableDP.UpdateInput`, `OAI.MatchingFPRAS.ExecutableDP.activeRep`, `OAI.MatchingFPRAS.ExecutableDP.bagRep`, `OAI.MatchingFPRAS.ExecutableDP.capBits`, `OAI.MatchingFPRAS.ExecutableDP.cappedCount`, `OAI.MatchingFPRAS.ExecutableDP.cappedEntry`, `OAI.MatchingFPRAS.ExecutableDP.cappedStep`, `OAI.MatchingFPRAS.ExecutableDP.cappedUpdate`, `OAI.MatchingFPRAS.ExecutableDP.context`, `OAI.MatchingFPRAS.ExecutableDP.entry`, `OAI.MatchingFPRAS.ExecutableDP.finish`, `OAI.MatchingFPRAS.ExecutableDP.initial`, `OAI.MatchingFPRAS.ExecutableDP.initialEntry`, `OAI.MatchingFPRAS.ExecutableDP.nLabels`, `OAI.MatchingFPRAS.ExecutableDP.nPlan`, `OAI.MatchingFPRAS.ExecutableDP.nVertices`, `OAI.MatchingFPRAS.ExecutableDP.orderedRep`, `OAI.MatchingFPRAS.ExecutableDP.parentRep`, `OAI.MatchingFPRAS.ExecutableDP.parentTag`, `OAI.MatchingFPRAS.ExecutableDP.privateFlag`, `OAI.MatchingFPRAS.ExecutableDP.privateNumber`, `OAI.MatchingFPRAS.ExecutableDP.rawEntry`, `OAI.MatchingFPRAS.ExecutableDP.rawTerm`, `OAI.MatchingFPRAS.ExecutableDP.read`, `OAI.MatchingFPRAS.ExecutableDP.runCapped`, `OAI.MatchingFPRAS.ExecutableDP.sharedFlag`, `OAI.MatchingFPRAS.ExecutableDP.sharedNumber`, `OAI.MatchingFPRAS.ExecutableDP.tableWeightBound`, `OAI.MatchingFPRAS.ExecutableDP.tabulate` and 604 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatchingCount, in whole or in part: `MatchingCount_Algorithm_AffineWeights`, `MatchingCount_Algorithm_OnlineHistorySize`, `MatchingCount_Algorithm_OnlineInitial`, `MatchingCount_Algorithm_OnlineLadderSchedule`, `MatchingCount_Algorithm_OnlineRequest`, `MatchingCount_Algorithm_OnlineScheduleNat`, `MatchingCount_Algorithm_OutputLengthBound`, `MatchingCount_Algorithm_RationalEstimator`, `MatchingCount_Algorithm_RationalScale`, `MatchingCount_Algorithm_RationalStart`, `MatchingCount_Algorithm_TreeGeneratedPrepared`, `MatchingCount_Algorithm_TreeNumericStatistics`, `MatchingCount_Algorithm_TreeNumericSummaries`, `MatchingCount_Algorithm_TreeObservables`, `MatchingCount_Algorithm_TreeStageStatisticsCorrect`, `MatchingCount_Algorithm_TreeStatistics`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Arithmetic_OnlineFractionParam`, `MatchingCount_Arithmetic_TreeGCD`, `MatchingCount_Arithmetic_TreeNatDivision`, `MatchingCount_Arithmetic_TreeStateNormalize`, `MatchingCount_Complexity_GuardMachineBase`, `MatchingCount_Complexity_OnlineRequestCost`, `MatchingCount_Complexity_OnlineRunCost`, `MatchingCount_Complexity_StackCompilerCost`, `MatchingCount_Complexity_TreePolynomialGrid`, `MatchingCount_Graphs_AdaptiveStream`, `MatchingCount_Graphs_Admissible`, `MatchingCount_Graphs_ColoredEdge`, `MatchingCount_Graphs_CompleteGraph`, `MatchingCount_Graphs_Cumulative`, `MatchingCount_Graphs_Cycle`, `MatchingCount_Graphs_Density`, `MatchingCount_Graphs_Edge2`, `MatchingCount_Graphs_EdgeLow`, `MatchingCount_Graphs_EnlargementRun`, `MatchingCount_Graphs_Evolve`, `MatchingCount_Graphs_ExperimentSupport`, `MatchingCount_Graphs_HoleBlocks`, `MatchingCount_Graphs_IndexedCycle`, `MatchingCount_Graphs_LabelCycle`, `MatchingCount_Graphs_LabelOrder`, `MatchingCount_Graphs_OnlineGraphInvariant`, `MatchingCount_Graphs_PM`, `MatchingCount_Graphs_PathStrength`, `MatchingCount_Graphs_PushedFlow`, `MatchingCount_Graphs_RatWeight`, `MatchingCount_Graphs_Related`, `MatchingCount_Graphs_Related2`, `MatchingCount_Graphs_RemainingBags`, `MatchingCount_Graphs_RowPeak`, `MatchingCount_Graphs_SafeSwitch`, `MatchingCount_Graphs_Sets`, `MatchingCount_Graphs_SumLiftMate`, `MatchingCount_Graphs_ThresholdGraph`, `MatchingCount_Graphs_TreeBagCorrect`, `MatchingCount_Graphs_TreeBagTable`, `MatchingCount_Graphs_TreeBags`, `MatchingCount_Graphs_TreeCycleTable`, `MatchingCount_Graphs_TreeGeometry`, `MatchingCount_Graphs_TreeHierarchyReindex`, `MatchingCount_Graphs_TreeInitialMatching`, `MatchingCount_Graphs_TreeMatchingCheck`, `MatchingCount_Graphs_TreeRankPlan`, `MatchingCount_Graphs_TreeSwitchRaw`, `MatchingCount_Graphs_TreeSwitchValid`, `MatchingCount_Machines_OnlineCase`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_OnlineTraverse`, `MatchingCount_Machines_OnlineUniform`, `MatchingCount_Machines_PhysicalPost`, `MatchingCount_Machines_SupportedCompiler`, `MatchingCount_Machines_TreeBindings`, `MatchingCount_Machines_TreeBottleneck`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeCappedAssembly`, `MatchingCount_Machines_TreeCertify`, `MatchingCount_Machines_TreeClippedCorrect`, `MatchingCount_Machines_TreeClippedRun`, `MatchingCount_Machines_TreeClosureReindex`, `MatchingCount_Machines_TreeColorRaw`, `MatchingCount_Machines_TreeEnumeration`, `MatchingCount_Machines_TreeFold`, `MatchingCount_Machines_TreeIndex`, `MatchingCount_Machines_TreeLabelCorrect`, `MatchingCount_Machines_TreeLabelTable`, `MatchingCount_Machines_TreeList`, `MatchingCount_Machines_TreeListMore`, `MatchingCount_Machines_TreeListOps`, `MatchingCount_Machines_TreeNaturalComb`, `MatchingCount_Machines_TreeNumberedSets`, `MatchingCount_Machines_TreePairProposal`, `MatchingCount_Machines_TreeParentTable`, `MatchingCount_Machines_TreeQuad`, `MatchingCount_Machines_TreeReach`, `MatchingCount_Machines_TreeRefreshCatalog`, `MatchingCount_Machines_TreeRefreshIndexed`, `MatchingCount_Machines_TreeRefreshNumbered`, `MatchingCount_Machines_TreeRepeat`, `MatchingCount_Machines_TreeSlotIndex`, `MatchingCount_Machines_TreeSlotWeight`, `MatchingCount_Machines_TreeStart`, `MatchingCount_Machines_TreeStateTable`, `MatchingCount_Machines_TreeSum`, `MatchingCount_Probability_LocalVariance`, `MatchingCount_Probability_Mean`, `MatchingCount_Probability_OnlineSampleLaw`, `MatchingCount_Probability_Tv`, `MatchingCount_Probability_Variance`, `MatchingCount_Sampling_AssignmentEquiv`, `MatchingCount_Sampling_Certify`, `MatchingCount_Sampling_ClippedEnvelope`, `MatchingCount_Sampling_Component`, `MatchingCount_Sampling_ComponentOrder`, `MatchingCount_Sampling_Components`, `MatchingCount_Sampling_Corner`, `MatchingCount_Sampling_DPEnvelope`, `MatchingCount_Sampling_DiscreteLadderSteps`, `MatchingCount_Sampling_EndpointPair`, `MatchingCount_Sampling_Endpoints`, `MatchingCount_Sampling_Endpoints2`, `MatchingCount_Sampling_IntervalPattern`, `MatchingCount_Sampling_LadderL`, `MatchingCount_Sampling_MetropolisChoice`, `MatchingCount_Sampling_OnlineSample`, `MatchingCount_Sampling_PM`, `MatchingCount_Sampling_PairStep`, `MatchingCount_Sampling_Plan`, `MatchingCount_Sampling_RankOrder`, `MatchingCount_Sampling_Relabel`, `MatchingCount_Sampling_RelationDestinations`, `MatchingCount_Sampling_Sewn`, `MatchingCount_Sampling_Span`, `MatchingCount_Sampling_Sym2Order`, `MatchingCount_Sampling_TableMarking`, `MatchingCount_Sampling_Through`, `MatchingCount_Sampling_TierClamp`, `MatchingCount_Sampling_TreeCategorical`, `MatchingCount_Sampling_TreeClippedDP`, `MatchingCount_Sampling_TreeDPCount`, `MatchingCount_Sampling_TreeDPCounts`, `MatchingCount_Sampling_TreeDPEntry`, `MatchingCount_Sampling_TreeDPProgram`, `MatchingCount_Sampling_TreeDPRepresentation`, `MatchingCount_Sampling_TreeFastDPEntry`, `MatchingCount_Sampling_TreeFastDescent`, `MatchingCount_Sampling_TreeFastSample`, `MatchingCount_Sampling_TreeFastUnit`, `MatchingCount_Sampling_TreeIndexedPair`, `MatchingCount_Sampling_TreeIndexedPairCorrect`, `MatchingCount_Sampling_TreeLadder`, `MatchingCount_Sampling_TreeLadderIndexed`, `MatchingCount_Sampling_TreeLadderPost`, `MatchingCount_Sampling_TreeLocalSampler`, `MatchingCount_Sampling_TreeMarking`, `MatchingCount_Sampling_TreeNumericLadder`, `MatchingCount_Sampling_TreeNumericMarking`, `MatchingCount_Sampling_TreePairTable`, `MatchingCount_Sampling_TreePreparedMarked`, `MatchingCount_Sampling_TreeScan`, `MatchingCount_Sampling_TreeScanChoice`, `MatchingCount_Sampling_TreeScanRun`, `MatchingCount_Sampling_TreeUnitAssemble`, `MatchingCount_Sampling_TreeUnitBranch`, `MatchingCount_Sampling_TreeUnitDraw`, `MatchingCount_Sampling_TreeUnitSampler`, `MatchingCount_Sampling_Underlying`, `MatchingCount_Tapes_BlockMap`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_FixedAlphabetCompiler`, `MatchingCount_Tapes_FixedEncoding`, `MatchingCount_Tapes_Input`, `MatchingCount_Tapes_OnlineStackCompiler`, `MatchingCount_Tapes_OnlineWord`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_PackedExecution`, `MatchingCount_Tapes_Parse`, `MatchingCount_Tapes_Physical`, `MatchingCount_Tapes_StackWords`, `MatchingCount_Tapes_TapeTools`, `MatchingCount_Tapes_TreeNumberedCodec`, `MatchingCount_Tapes_TreeSparseComponents`, `MatchingCount_Tapes_TreeSparseNeighbors`, `MatchingCount_Tapes_TreeSparseStage`.
--
--   **Imports.** It imports the published bundle `Def_MatchingFPRAS`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ051M002` and `OAIQ051M003`.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatchingCount at commit adc7f12

import Mathlib
import Definitions.Def_MatchingFPRAS

section
-- module Solutions.OAIQ051_MC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PathStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem sdiff_pair_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    (S \ {a,b}).card = S.card - 2 := by
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst x
      exact ha
    · have he := Finset.mem_singleton.mp h
      subst x
      exact hb
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hab]

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

def affineWeights (w d : V → V → ℝ) (t : ℝ) (a b : V) : ℝ := w a b + t * d a b

noncomputable def edgeSum [Fintype V] [LinearOrder V]
    (S : Finset V) (f : V → V → ℝ) : ℝ :=
  ∑ a, ∑ b, if a < b ∧ a ∉ S ∧ b ∉ S then f a b else 0

noncomputable def holeScale (V : Type*) [Fintype V] : ℝ :=
  100000000 * ((Fintype.card V : ℝ) + 1)^4

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_GuardMachineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

def statementCost {Γ Λ σ : Type*} : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => statementCost q+1
  | .write _ q => statementCost q+1
  | .load _ q => statementCost q
  | .branch _ q r => max (statementCost q) (statementCost r)
  | .goto _ => 1
  | .halt => 1

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

noncomputable def programCost [Fintype Λ] : ℕ := Finset.univ.sup (fun l=>statementCost (M l))
end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_StackCompilerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCost
open Turing Turing.TM2to1 Turing.TM2to1.Λ' MachineCost

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def accesses : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => accesses q+1
  | .peek _ _ q => accesses q+1
  | .pop _ _ q => accesses q+1
  | .load _ q => accesses q
  | .branch _ q r => max (accesses q) (accesses r)
  | .goto _ => 0
  | .halt => 0
def StackBound (S : ∀ k,List (Γ k)) (H : ℕ) : Prop := ∀ k,(S k).length≤H
end MatchingFPRAS.StackCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_SupportedCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SupportedCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
noncomputable def cost : ℕ := S.sup (fun l=>statementCost (M l))
end MatchingFPRAS.SupportedCompiler

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
def bitsWord (input : List Γ) : List Bool := input.flatMap (fun a=>(enc a).toList)
end MatchingFPRAS.FixedAlphabetCompiler

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_FixedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
noncomputable def enc (a : Γ) : List.Vector Bool (Fintype.card Γ) := by
  classical
  exact List.Vector.ofFn (fun i=>decide (a≠default ∧ Fintype.equivFin Γ a=i))
lemma blank : enc Γ default=List.Vector.replicate (Fintype.card Γ) false := by
  classical
  apply List.Vector.ext
  intro i
  simp [enc]
noncomputable def dec : List.Vector Bool (Fintype.card Γ) → Γ := Function.invFun (enc Γ)
end MatchingFPRAS.FixedEncoding

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
def rows (S : ∀ k,List (Γ k)) (H : ℕ) : List (∀ k,Option (Γ k)) :=
  List.ofFn (fun i : Fin H=>fun k=>(S k).reverse[i.val]?)
def word (S : ∀ k,List (Γ k)) (H : ℕ) : List (TM2to1.Γ' K Γ) :=
  (true,(rows S H).headI)::((rows S H).tail.map (fun a=>(false,a)))
end MatchingFPRAS.StackWords

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ColoredEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V L : Type*}

variable {E : Type*} [DecidableEq V] [DecidableEq E] (inc : E → V → Prop)

lemma union_val_add {F G : Finset E} (h : Disjoint F G) :
    (F ∪ G).val = F.val + G.val := by
  rw [← Finset.disjUnion_eq_union F G h, Finset.disjUnion_val]

lemma sdiff_val_add {F G : Finset E} (h : G ⊆ F) :
    (F \ G).val + G.val = F.val := by
  rw [← union_val_add Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

def pathPattern (edges : ℕ → E) (lo hi : ℕ) : Finset E :=
  ((Finset.Ico lo hi).filter (fun i => i % 2 = lo % 2)).image edges

lemma pathPattern_boundary (edges : ℕ → E) (lo hi : ℕ)
    (hlong : lo + 3 ≤ hi) (hodd : (hi - lo) % 2 = 1) :
    pathPattern edges lo hi = pathPattern edges (lo + 2) (hi - 2) ∪
      {edges lo, edges (hi - 1)} := by
  have hidx : (Finset.Ico lo hi).filter (fun i => i % 2 = lo % 2) =
      ((Finset.Ico (lo + 2) (hi - 2)).filter (fun i => i % 2 = (lo + 2) % 2)) ∪
        {lo, hi - 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold pathPattern
  rw [hidx, Finset.image_union]
  simp only [Finset.image_insert, Finset.image_singleton]

def overlayLineGraph (S : Finset E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ e ∈ S ∧ f ∈ S ∧ ∃ v, inc e v ∧ inc f v
  symm := ⟨by
    intro e f h
    rcases h with ⟨h, he, hf, v, hev, hfv⟩
    exact ⟨h.symm, hf, he, v, hfv, hev⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

omit [DecidableEq E] in
lemma multiset_product_comparison (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A : ℝ) (hA : 0 ≤ A) (drop add : Multiset E) (hcard : drop.card = add.card)
    (hcompare : ∀ e ∈ drop, ∀ f ∈ add, w e ≤ A * w f) :
    (drop.map w).prod ≤ A ^ drop.card * (add.map w).prod := by
  induction drop using Multiset.induction_on generalizing add with
  | empty =>
      have ha : add = 0 := Multiset.card_eq_zero.mp (by simpa using hcard.symm)
      subst add
      simp
  | @cons e drop ih =>
      obtain ⟨f, hf⟩ := Multiset.card_pos_iff_exists_mem.mp
        (show 0 < add.card by simp only [Multiset.card_cons] at hcard; omega)
      obtain ⟨add', rfl⟩ := Multiset.exists_cons_of_mem hf
      have hcard' : drop.card = add'.card := by simpa using hcard
      have hi := ih add' hcard' (fun a ha b hb =>
        hcompare a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      have he := hcompare e (Multiset.mem_cons_self _ _) f (Multiset.mem_cons_self _ _)
      have hp : 0 ≤ (drop.map w).prod := le_of_lt <| Multiset.prod_pos (by
        intro z hz
        obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hz
        exact hw a)
      have hb : 0 ≤ A * w f := mul_nonneg hA (le_of_lt (hw f))
      simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ,
        mul_assoc, mul_left_comm, mul_comm] using mul_le_mul he hi hp hb

omit [DecidableEq E] in
lemma four_edge_weight_bound (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A : ℝ) (hA : 1 ≤ A) (input output drop add : Multiset E)
    (hcons : input + add = output + drop)
    (hcard : drop.card = add.card) (hfour : drop.card ≤ 4)
    (hcompare : ∀ e ∈ drop, ∀ f ∈ add, w e ≤ A * w f) :
    (input.map w).prod ≤ A ^ 4 * (output.map w).prod := by
  have hnonneg : 0 ≤ A := by linarith
  have hc := multiset_product_comparison w hw A hnonneg drop add hcard hcompare
  have ha : 0 < (add.map w).prod := Multiset.prod_pos (by
    intro z hz
    obtain ⟨e, _, rfl⟩ := Multiset.mem_map.mp hz
    exact hw e)
  have ho : 0 ≤ (output.map w).prod := le_of_lt <| Multiset.prod_pos (by
    intro z hz
    obtain ⟨e, _, rfl⟩ := Multiset.mem_map.mp hz
    exact hw e)
  have hweight := congrArg (fun s : Multiset E => (s.map w).prod) hcons
  simp only [Multiset.map_add, Multiset.prod_add] at hweight
  have hpow : A ^ drop.card ≤ A ^ 4 := pow_le_pow_right₀ hA hfour
  have hc' : (drop.map w).prod ≤ A ^ 4 * (add.map w).prod :=
    hc.trans (mul_le_mul_of_nonneg_right hpow (le_of_lt ha))
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    _ = (output.map w).prod * (drop.map w).prod := hweight
    _ ≤ (output.map w).prod * (A ^ 4 * (add.map w).prod) :=
      mul_le_mul_of_nonneg_left hc' ho
    _ = _ := by ring

structure OddPath where
  length : ℕ
  positive : 0 < length
  odd : length % 2 = 1
  vertex : ℕ → V
  edge : ℕ → E
  simple : Set.InjOn vertex (Set.Icc 0 length)
  incidence : ∀ i, i < length → ∀ v,
    inc (edge i) v ↔ v = vertex i ∨ v = vertex (i + 1)

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

def span : Finset V := (Finset.Icc 0 p.length).image p.vertex

def inside : Finset V := (Finset.Icc 1 (p.length - 1)).image p.vertex

def ends : Finset V := {p.vertex 0, p.vertex p.length}

def through : Finset E := pathPattern p.edge 0 p.length

def interior : Finset E := pathPattern p.edge 1 (p.length - 1)

def closed (chord : E) : Finset E := p.interior ∪ {chord}

def boundary : Finset E := if p.length = 1 then {p.edge 0}
  else {p.edge 0, p.edge (p.length - 1)}

def repaired (repair : E) : Finset E := if p.length = 1 then ∅
  else pathPattern p.edge 2 (p.length - 2) ∪ {repair}

def repairAdded (repair : E) : Multiset E := if p.length = 1 then 0 else {repair}

omit [DecidableEq E] in
lemma inside_disjoint_ends : Disjoint p.inside p.ends := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hil, hih⟩ := Finset.mem_Icc.mp hi
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with h | h
  · have hh := p.simple ⟨by omega, by omega⟩ ⟨le_rfl, Nat.zero_le _⟩ h
    omega
  · have hh := p.simple ⟨by omega, by omega⟩ ⟨Nat.zero_le _, le_rfl⟩ h
    omega

omit [DecidableEq E] in
lemma inside_union_ends : p.inside ∪ p.ends = p.span := by
  ext v
  simp only [inside, ends, span, Finset.mem_union, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl | rfl)
    · exact ⟨i, ⟨by omega, by omega⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, Nat.zero_le _⟩, rfl⟩
    · exact ⟨p.length, ⟨Nat.zero_le _, le_rfl⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · exact Or.inr (Or.inl (congrArg p.vertex h0))
    by_cases hh : i = p.length
    · exact Or.inr (Or.inr (congrArg p.vertex hh))
    · exact Or.inl ⟨i, ⟨by omega, by omega⟩, rfl⟩

omit [DecidableEq V] [DecidableEq E] in
lemma edge_injective : Set.InjOn p.edge (Set.Ico 0 p.length) := by
  intro i hi j hj heq
  simp only [Set.mem_Ico] at hi hj
  have hiinc : inc (p.edge i) (p.vertex i) := (p.incidence i hi.2 _).mpr (Or.inl rfl)
  rw [heq] at hiinc
  have hjinc : inc (p.edge j) (p.vertex (i+1)) := by
    rw [← heq]
    exact (p.incidence i hi.2 _).mpr (Or.inr rfl)
  have hi₁ := (p.incidence j hj.2 _).mp hiinc
  have hi₂ := (p.incidence j hj.2 _).mp hjinc
  have hs₁ : i = j ∨ i = j + 1 := hi₁.imp
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  have hs₂ : i+1 = j ∨ i+1 = j+1 := hi₂.imp
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  omega

omit [DecidableEq V] in
lemma boundary_card : p.boundary.card = if p.length = 1 then 1 else 2 := by
  by_cases h : p.length = 1
  · simp [boundary, h]
  · have hpos := p.positive
    have hodd := p.odd
    have hneq : p.edge 0 ≠ p.edge (p.length - 1) := by
      intro heq
      have hh := p.edge_injective ⟨le_rfl, hpos⟩ ⟨by omega, by omega⟩ heq
      omega
    simp [boundary, h, hneq]

end OddPath

structure CellPaths where
  side : Fin 4 → OddPath inc
  joins : ∀ i, (side i).vertex (side i).length = (side (i+1)).vertex 0
  corners_injective : Function.Injective fun i => (side i).vertex 0
  interiors_disjoint : Pairwise fun i j => Disjoint (side i).inside (side j).inside
  interior_ends_disjoint : ∀ i j, Disjoint (side i).inside (side j).ends
  chord : Fin 4 → E
  chord_incidence : ∀ i v, inc (chord i) v ↔
    v = (side i).vertex 0 ∨ v = (side i).vertex (side i).length

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

def corner (i : Fin 4) : V := (c.side i).vertex 0

def vertices : Finset V :=
  ((c.side 0).inside ∪ (c.side 1).inside) ∪ ((c.side 2).inside ∪ (c.side 3).inside) ∪
    {c.corner 0, c.corner 1, c.corner 2, c.corner 3}

omit [DecidableEq E] in
lemma ends_eq (i : Fin 4) : (c.side i).ends = {c.corner i, c.corner (i+1)} := by
  simp only [OddPath.ends, c.joins, corner]

omit [DecidableEq E] in
lemma inside_disjoint_span (i j : Fin 4) (hij : i ≠ j) :
    Disjoint (c.side i).inside (c.side j).span := by
  rw [← (c.side j).inside_union_ends]
  exact Finset.disjoint_union_right.mpr
    ⟨c.interiors_disjoint hij, c.interior_ends_disjoint i j⟩

omit [DecidableEq E] in
lemma opposite_ends_even : Disjoint (c.side 0).ends (c.side 2).ends := by
  rw [c.ends_eq, c.ends_eq]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with h | h <;> rcases hw with k | k
  all_goals have hh := c.corners_injective (h.symm.trans k)
  all_goals exact absurd hh (by decide)

omit [DecidableEq E] in
lemma opposite_ends_odd : Disjoint (c.side 1).ends (c.side 3).ends := by
  rw [c.ends_eq, c.ends_eq]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with h | h <;> rcases hw with k | k
  all_goals have hh := c.corners_injective (h.symm.trans k)
  all_goals exact absurd hh (by decide)

omit [DecidableEq E] in
lemma opposite_span_even : Disjoint (c.side 0).span (c.side 2).span := by
  rw [← (c.side 0).inside_union_ends]
  apply Finset.disjoint_union_left.mpr
  refine ⟨c.inside_disjoint_span 0 2 (by decide), ?_⟩
  rw [← (c.side 2).inside_union_ends]
  exact Finset.disjoint_union_right.mpr ⟨(c.interior_ends_disjoint 2 0).symm,
    c.opposite_ends_even⟩

omit [DecidableEq E] in
lemma opposite_span_odd : Disjoint (c.side 1).span (c.side 3).span := by
  rw [← (c.side 1).inside_union_ends]
  apply Finset.disjoint_union_left.mpr
  refine ⟨c.inside_disjoint_span 1 3 (by decide), ?_⟩
  rw [← (c.side 3).inside_union_ends]
  exact Finset.disjoint_union_right.mpr ⟨(c.interior_ends_disjoint 3 1).symm,
    c.opposite_ends_odd⟩

omit [DecidableEq E] in
lemma even_blocks_union :
    ((c.side 0).span ∪ (c.side 2).span) ∪
      ((c.side 1).inside ∪ (c.side 3).inside) = c.vertices := by
  rw [← (c.side 0).inside_union_ends, ← (c.side 2).inside_union_ends,
    c.ends_eq, c.ends_eq]
  ext v
  simp only [vertices, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [DecidableEq E] in
lemma odd_blocks_union :
    ((c.side 1).span ∪ (c.side 3).span) ∪
      ((c.side 0).inside ∪ (c.side 2).inside) = c.vertices := by
  rw [← (c.side 1).inside_union_ends, ← (c.side 3).inside_union_ends,
    c.ends_eq, c.ends_eq]
  ext v
  simp only [vertices, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

def assemble (M : Fin 4 → Finset E) : Finset E := (M 0 ∪ M 2) ∪ (M 1 ∪ M 3)

def sideBit (i : Fin 4) : Bool := decide (i.val % 2 = 0)

def blocks (b : Bool) (i : Fin 4) : Finset V :=
  if sideBit i = b then (c.side i).span else (c.side i).inside

def pieces (b : Bool) (full inner : Fin 4 → Finset E) (i : Fin 4) : Finset E :=
  if sideBit i = b then full i else inner i

omit [DecidableEq E] in
lemma same_bit_spans (i j : Fin 4) (hij : i ≠ j) (hbit : sideBit i = sideBit j) :
    Disjoint (c.side i).span (c.side j).span := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals norm_num [sideBit] at hbit
  · exact c.opposite_span_even
  · exact c.opposite_span_odd
  · exact c.opposite_span_even.symm
  · exact c.opposite_span_odd.symm

def orientationPieces (b : Bool) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).through) (fun i => (c.side i).interior)

def switchPieces (b : Bool) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).closed (c.chord i)) (fun i => (c.side i).interior)

def repairPieces (b : Bool) (repair : Fin 4 → E) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).through) (fun i => (c.side i).repaired (repair i))

def guidePieces (b : Bool) (repair : Fin 4 → E) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).closed (c.chord i)) (fun i => (c.side i).repaired (repair i))

def Repairs (b : Bool) (repair : Fin 4 → E) : Prop :=
  ∀ i, sideBit i ≠ b → (c.side i).length ≠ 1 → ∀ v,
    inc (repair i) v ↔ v = (c.side i).vertex 1 ∨ v = (c.side i).vertex ((c.side i).length - 1)

def orientation (b : Bool) : Finset E := assemble (c.orientationPieces b)

def switched (b : Bool) : Finset E := assemble (c.switchPieces b)

def repaired (b : Bool) (repair : Fin 4 → E) : Finset E := assemble (c.repairPieces b repair)

def guide (b : Bool) (repair : Fin 4 → E) : Finset E := assemble (c.guidePieces b repair)

lemma component_subset_assemble (M : Fin 4 → Finset E) (i : Fin 4) : M i ⊆ assemble M := by
  intro e he
  fin_cases i <;> simp only [assemble, Finset.mem_union]
  · exact Or.inl (Or.inl he)
  · exact Or.inr (Or.inl he)
  · exact Or.inl (Or.inr he)
  · exact Or.inr (Or.inr he)

def drops (r : Bool) : Multiset E :=
  ∑ i, if sideBit i = r then 0 else (c.side i).boundary.val

def additions (b r : Bool) (repair : Fin 4 → E) : Multiset E :=
  (∑ i, if sideBit i = b then {c.chord i} else 0) +
    ∑ i, if sideBit i = r then 0 else (c.side i).repairAdded (repair i)

lemma two_orientation_pieces (i : Fin 4) :
    (c.orientationPieces true i).val + (c.orientationPieces false i).val =
      (c.side i).through.val + (c.side i).interior.val := by
  cases h : sideBit i <;> simp [orientationPieces, pieces, h, add_comm]

lemma boundary_card_eq (i : Fin 4) (repair : Fin 4 → E) :
    (c.side i).boundary.card = 1 + ((c.side i).repairAdded (repair i)).card := by
  rw [(c.side i).boundary_card]
  by_cases h : (c.side i).length = 1 <;> simp [OddPath.repairAdded, h]

omit [DecidableEq E] in
lemma additions_card (b r : Bool) (repair : Fin 4 → E) :
    (c.additions b r repair).card = 2 +
      ∑ i, if sideBit i = r then 0 else ((c.side i).repairAdded (repair i)).card := by
  simp only [additions, Multiset.card_add, Multiset.card_sum]
  have h1 : (∑ i : Fin 4, (if sideBit i = b then ({c.chord i} : Multiset E) else 0).card) = 2 := by
    cases b <;> norm_num [Fin.sum_univ_four, sideBit]
  rw [h1]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

lemma modification_cards (b r : Bool) (repair : Fin 4 → E) :
    (c.drops r).card = (c.additions b r repair).card ∧ (c.drops r).card ≤ 4 := by
  have hd : (c.drops r).card = 2 +
      ∑ i, if sideBit i = r then 0 else ((c.side i).repairAdded (repair i)).card := by
    simp only [drops, Multiset.card_sum]
    have hb := c.boundary_card_eq
    cases r <;> norm_num [Fin.sum_univ_four, sideBit]
    all_goals rw [hb _ repair, hb _ repair]; omega
  refine ⟨hd.trans (c.additions_card b r repair).symm, ?_⟩
  rw [hd]
  have hle (i : Fin 4) : ((c.side i).repairAdded (repair i)).card ≤ 1 := by
    by_cases h : (c.side i).length = 1 <;> simp [OddPath.repairAdded, h]
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  cases r <;> norm_num [Fin.sum_univ_four, sideBit]
  all_goals omega

omit [DecidableEq E] in
lemma span_subset_vertices (i : Fin 4) : (c.side i).span ⊆ c.vertices := by
  rw [← (c.side i).inside_union_ends, c.ends_eq]
  intro v hv
  fin_cases i <;> simp only [vertices, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hv ⊢ <;> tauto

def contextOne (b : Bool) (Y : Fin 4) : Finset E :=
  (c.orientation b \ (c.side Y).through) ∪ (c.side Y).closed (c.chord Y)

def guideOne (b : Bool) (repair : Fin 4 → E) (Y : Fin 4) : Finset E :=
  (c.guide b repair \ (c.side Y).closed (c.chord Y)) ∪ (c.side Y).through

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

section

variable {V E : Type*}

variable (inc : E → V → Prop)

structure IndexedCycle where
  size : ℕ
  four_le : 4 ≤ size
  even : size % 2 = 0
  vertex : Fin size → V
  simple : Function.Injective vertex
  edge : Fin size → E
  incidence : ∀ i v, inc (edge i) v ↔ v = vertex i ∨ v = vertex ⟨(i.val + 1) % size, Nat.mod_lt _ (by omega)⟩

namespace IndexedCycle

variable {inc} (c : IndexedCycle inc)

def index (i : ℕ) : Fin c.size := ⟨i % c.size, Nat.mod_lt i (by have := c.four_le; omega)⟩

def vertexAt (i : ℕ) : V := c.vertex (c.index i)

def edgeAt (i : ℕ) : E := c.edge (c.index i)

lemma index_succ (i : ℕ) : c.index (i + 1) = ⟨((c.index i).val + 1) % c.size, Nat.mod_lt _ (by have := c.four_le; omega)⟩ := by
  apply Fin.ext
  simp only [index, Nat.add_mod, Nat.mod_mod]

lemma vertexAt_periodic (i : ℕ) : c.vertexAt (i + c.size) = c.vertexAt i := by
  simp [vertexAt, index]

lemma edgeAt_incidence (i : ℕ) (v : V) :
    inc (c.edgeAt i) v ↔ v = c.vertexAt i ∨ v = c.vertexAt (i + 1) := by
  simpa [edgeAt, vertexAt, c.index_succ] using c.incidence (c.index i) v

lemma mod_of_lt_twice {m x : ℕ} (hx : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma vertexAt_eq_iff {a x y : ℕ} (ha : a < c.size)
    (hx : a ≤ x ∧ x < a + c.size) (hy : a ≤ y ∧ y < a + c.size) :
    c.vertexAt x = c.vertexAt y ↔ x = y := by
  constructor
  · intro h
    have hm : x % c.size = y % c.size := congrArg Fin.val (c.simple h)
    rw [mod_of_lt_twice (by omega), mod_of_lt_twice (by omega)] at hm
    split_ifs at hm <;> omega
  · exact congrArg c.vertexAt

def arc (start length : ℕ) (hstart : start < c.size) (hpos : 0 < length)
    (hlt : length < c.size) (hodd : length % 2 = 1) : OddPath inc where
  length := length
  positive := hpos
  odd := hodd
  vertex i := c.vertexAt (start + i)
  edge i := c.edgeAt (start + i)
  simple := by
    intro i hi j hj h
    change 0 ≤ i ∧ i ≤ length at hi
    change 0 ≤ j ∧ j ≤ length at hj
    have := (c.vertexAt_eq_iff hstart
      (x := start + i) (y := start + j) (by constructor <;> omega)
      (by constructor <;> omega)).mp h
    omega
  incidence := by
    intro i hi v
    simpa [Nat.add_assoc] using c.edgeAt_incidence (start + i) v

structure Corners where
  a₀ : ℕ
  a₁ : ℕ
  a₂ : ℕ
  a₃ : ℕ
  lt₀ : a₀ < a₁
  lt₁ : a₁ < a₂
  lt₂ : a₂ < a₃
  lt₃ : a₃ < c.size
  odd₀ : (a₁ - a₀) % 2 = 1
  odd₁ : (a₂ - a₁) % 2 = 1
  odd₂ : (a₃ - a₂) % 2 = 1
  odd₃ : (c.size + a₀ - a₃) % 2 = 1

namespace Corners

variable {c} (k : c.Corners)

def start : Fin 4 → ℕ := ![k.a₀, k.a₁, k.a₂, k.a₃]

def stop : Fin 4 → ℕ := ![k.a₁, k.a₂, k.a₃, c.size + k.a₀]

def length (i : Fin 4) : ℕ := k.stop i - k.start i

lemma bounds (i : Fin 4) :
    k.a₀ ≤ k.start i ∧ k.start i < c.size ∧
    k.start i < k.stop i ∧ k.stop i ≤ k.a₀ + c.size ∧
    k.stop i < k.start i + c.size := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> simp [start, stop] <;> omega

lemma length_pos (i : Fin 4) : 0 < k.length i := by
  have := k.bounds i
  dsimp [length]
  omega

lemma length_lt (i : Fin 4) : k.length i < c.size := by
  have := k.bounds i
  dsimp [length]
  omega

lemma length_odd (i : Fin 4) : k.length i % 2 = 1 := by
  fin_cases i
  · exact k.odd₀
  · exact k.odd₁
  · exact k.odd₂
  · exact k.odd₃

def side (i : Fin 4) : OddPath inc :=
  c.arc (k.start i) (k.length i) (k.bounds i).2.1 (k.length_pos i)
    (k.length_lt i) (k.length_odd i)

lemma side_vertex (i : Fin 4) (j : ℕ) :
    (k.side i).vertex j = c.vertexAt (k.start i + j) := rfl

lemma side_length (i : Fin 4) : (k.side i).length = k.length i := rfl

lemma side_first (i : Fin 4) : (k.side i).vertex 0 = c.vertexAt (k.start i) := by
  simp [side_vertex]

lemma side_last (i : Fin 4) : (k.side i).vertex (k.side i).length =
    c.vertexAt (k.stop i) := by
  rw [side_vertex, side_length]
  congr 1
  dsimp [length]
  have := k.bounds i
  omega

lemma joins (i : Fin 4) : (k.side i).vertex (k.side i).length =
    (k.side (i + 1)).vertex 0 := by
  rw [side_last, side_first]
  fin_cases i <;> simp [start, stop]
  simpa only [Nat.add_comm] using c.vertexAt_periodic k.a₀

lemma starts_injective : Function.Injective k.start := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [start] <;> omega

lemma corners_injective : Function.Injective fun i => (k.side i).vertex 0 := by
  intro i j h
  simp only [side_first] at h
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  apply k.starts_injective
  exact (c.vertexAt_eq_iff ha ⟨hi.1, by omega⟩ ⟨hj.1, by omega⟩).mp h

variable [DecidableEq V]

lemma inside_iff (i : Fin 4) (v : V) :
    v ∈ (k.side i).inside ↔
      ∃ t, k.start i < t ∧ t < k.stop i ∧ c.vertexAt t = v := by
  simp only [OddPath.inside, Finset.mem_image, Finset.mem_Icc, side_length, side_vertex]
  constructor
  · rintro ⟨j, hj, h⟩
    refine ⟨k.start i + j, by omega, ?_, h⟩
    have := k.bounds i
    dsimp [length] at hj
    omega
  · rintro ⟨t, hlow, hhigh, h⟩
    refine ⟨t - k.start i, ?_, ?_⟩
    · dsimp [length]
      constructor <;> omega
    · have he : k.start i + (t - k.start i) = t := by omega
      simpa [he] using h

omit [DecidableEq V] in
lemma interior_ranges_disjoint (i j : Fin 4) (hij : i ≠ j) (t : ℕ)
    (hi : k.start i < t ∧ t < k.stop i) :
    ¬ (k.start j < t ∧ t < k.stop j) := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> fin_cases j <;> simp_all [start, stop] <;> omega

lemma interiors_disjoint : Pairwise fun i j => Disjoint (k.side i).inside (k.side j).inside := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨x, hx₁, hx₂, hx⟩ := (k.inside_iff i v).mp hv
  obtain ⟨y, hy₁, hy₂, hy⟩ := (k.inside_iff j v).mp hw
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  have hxy := (c.vertexAt_eq_iff ha (x := x) (y := y)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).mp (hx.trans hy.symm)
  subst y
  exact k.interior_ranges_disjoint i j hij x ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

omit [DecidableEq V] in
lemma interior_not_corner_index (i j : Fin 4) (t : ℕ)
    (ht : k.start i < t ∧ t < k.stop i) : t ≠ k.start j := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> fin_cases j <;> simp_all [start, stop] <;> omega

lemma interior_ne_corner (i j : Fin 4) {v : V} (hv : v ∈ (k.side i).inside) :
    v ≠ (k.side j).vertex 0 := by
  intro heq
  obtain ⟨t, ht₁, ht₂, ht⟩ := (k.inside_iff i v).mp hv
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  have h := (c.vertexAt_eq_iff ha (x := t) (y := k.start j)
    ⟨by omega, by omega⟩ ⟨hj.1, by omega⟩).mp (ht.trans (by simpa [side_first] using heq))
  exact k.interior_not_corner_index i j t ⟨ht₁, ht₂⟩ h

lemma interior_ends_disjoint (i j : Fin 4) : Disjoint (k.side i).inside (k.side j).ends := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [OddPath.ends, Finset.mem_insert, Finset.mem_singleton, k.joins] at hw
  exact hw.elim (k.interior_ne_corner i j hv) (k.interior_ne_corner i (j+1) hv)

def cellPaths (chord : Fin 4 → E)
    (hchord : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length) : CellPaths inc where
  side := k.side
  joins := k.joins
  corners_injective := k.corners_injective
  interiors_disjoint := k.interiors_disjoint
  interior_ends_disjoint := k.interior_ends_disjoint
  chord := chord
  chord_incidence := hchord

end Corners

end IndexedCycle

end

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_mod (i : ℕ) : c.edgeAt (i % c.size) = c.edgeAt i := by
  exact congrArg c.edge (Fin.ext (Nat.mod_mod i c.size))

lemma consecutive_ne (i : ℕ) (hi : i < c.size) : c.edgeAt i ≠ c.edgeAt (i+1) := by
  intro he
  have hm : inc (c.edgeAt (i+1)) (c.vertexAt i) := he ▸
    (c.edgeAt_incidence i _).mpr (Or.inl rfl)
  rcases (c.edgeAt_incidence (i+1) _).mp hm with h | h
  · have := (c.vertexAt_eq_iff hi (x := i) (y := i+1)
      (by have := c.four_le; omega) (by have := c.four_le; omega)).mp h
    omega
  · have := (c.vertexAt_eq_iff hi (x := i) (y := i+1+1)
      (by have := c.four_le; omega) (by have := c.four_le; omega)).mp h
    omega

lemma edges_reachable (U : Finset E) (hU : ∀ i, c.edgeAt i ∈ U) (i : ℕ) :
    (overlayLineGraph inc U).Reachable (c.edgeAt 0) (c.edgeAt i) := by
  suffices hs : ∀ j, j < c.size →
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) (c.edgeAt j) by
    simpa only [c.edgeAt_mod] using hs (i % c.size)
      (Nat.mod_lt i (by have := c.four_le; omega))
  intro j hj
  induction j with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
      apply (ih (by omega)).trans
      apply SimpleGraph.Adj.reachable
      refine ⟨c.consecutive_ne j (by omega), hU j, hU (j+1), ?_⟩
      exact ⟨c.vertexAt (j+1), (c.edgeAt_incidence j _).mpr (Or.inr rfl),
        (c.edgeAt_incidence (j+1) _).mpr (Or.inl rfl)⟩

namespace Corners

variable {c} (k : c.Corners)

lemma parity_start (i : Fin 4) :
    k.start i % 2 = if CellPaths.sideBit i then k.a₀ % 2 else 1 - k.a₀ % 2 := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have ho₀ := k.odd₀
  have ho₁ := k.odd₁
  have ho₂ := k.odd₂
  fin_cases i <;> simp [start, CellPaths.sideBit] <;> omega

variable [DecidableEq V] [DecidableEq E]

lemma cell_orientation_subset (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (S : Finset E) (a : ℕ) (ha : a < 2)
    (hS : ∀ t, t % 2 = a → c.edgeAt t ∈ S) :
    (k.cellPaths chord hc).orientation (decide (k.a₀ % 2 = a)) ⊆ S := by
  have hh : ∀ i, (k.cellPaths chord hc).orientationPieces (decide (k.a₀ % 2 = a)) i ⊆ S := by
    intro i e he
    simp only [CellPaths.orientationPieces, CellPaths.pieces] at he
    split_ifs at he with hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hjr⟩ := Finset.mem_Ico.mp hb
      apply hS
      have hs := k.parity_start i
      have hp' : j % 2 = 0 := hp
      change CellPaths.sideBit i = decide (k.a₀ % 2 = a) at hi
      change (k.start i + j) % 2 = a
      rw [Nat.add_mod, hs, hp']
      cases hbit : CellPaths.sideBit i <;> simp_all
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hjr⟩ := Finset.mem_Ico.mp hb
      apply hS
      have hs := k.parity_start i
      have hp' : j % 2 = 1 := hp
      change CellPaths.sideBit i ≠ decide (k.a₀ % 2 = a) at hi
      change (k.start i + j) % 2 = a
      rw [Nat.add_mod, hs, hp']
      cases hbit : CellPaths.sideBit i <;> simp_all <;> omega
  intro e he
  change e ∈ CellPaths.assemble _ at he
  simp only [CellPaths.assemble, Finset.mem_union] at he
  rcases he with (he | he) | (he | he)
  · exact hh 0 he
  · exact hh 2 he
  · exact hh 1 he
  · exact hh 3 he

lemma cell_orientation_reachable (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (U : Finset E) (hU : ∀ i, c.edgeAt i ∈ U) (b : Bool) :
    ∀ e ∈ (k.cellPaths chord hc).orientation b,
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) e := by
  have hh : ∀ i e, e ∈ (k.cellPaths chord hc).orientationPieces b i →
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) e := by
    intro i e he
    simp only [CellPaths.orientationPieces, CellPaths.pieces] at he
    split_ifs at he <;>
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he <;>
      exact c.edges_reachable U hU (k.start i + j)
  intro e he
  change e ∈ CellPaths.assemble _ at he
  simp only [CellPaths.assemble, Finset.mem_union] at he
  rcases he with (he | he) | (he | he)
  · exact hh 0 e he
  · exact hh 2 e he
  · exact hh 1 e he
  · exact hh 3 e he

end Corners

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Sets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E L : Type*}

namespace IndexedCycle

variable {inc : E → V → Prop} (c : IndexedCycle inc)

def zindex (i : ℤ) : Fin c.size :=
  ⟨(i % (c.size : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ (by
    have := c.four_le; omega))).mpr (Int.emod_lt_of_pos _ (by have := c.four_le; omega))⟩

def vertexAtZ (i : ℤ) : V := c.vertex (c.zindex i)

def edgeAtZ (i : ℤ) : E := c.edge (c.zindex i)

lemma zindex_nat (i : ℕ) : c.zindex i = c.index i := by
  apply Fin.ext
  change ((i : ℤ) % (c.size : ℤ)).toNat = i % c.size
  rw [← Int.natCast_emod, Int.toNat_natCast]

lemma zindex_periodic (i : ℤ) : c.zindex (i + c.size) = c.zindex i := by
  apply Fin.ext
  simp [zindex]

lemma vertexAtZ_nat (i : ℕ) : c.vertexAtZ i = c.vertexAt i := by
  simp [vertexAtZ, vertexAt, c.zindex_nat]

lemma edgeAtZ_nat (i : ℕ) : c.edgeAtZ i = c.edgeAt i := by
  simp [edgeAtZ, edgeAt, c.zindex_nat]

lemma edgeAtZ_periodic (i : ℤ) : c.edgeAtZ (i + c.size) = c.edgeAtZ i := by
  simp [edgeAtZ, c.zindex_periodic]

lemma zindex_succ (i : ℤ) : c.zindex (i + 1) =
    ⟨((c.zindex i).val + 1) % c.size, Nat.mod_lt _ (by have := c.four_le; omega)⟩ := by
  have hsz : (c.size : ℤ) ≠ 0 := by have := c.four_le; omega
  apply Fin.ext
  apply Int.natCast_inj.mp
  change (((i + 1) % (c.size : ℤ)).toNat : ℤ) =
    (((((i % (c.size : ℤ)).toNat + 1) % c.size) : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hsz), Int.natCast_emod,
    Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (Int.emod_nonneg _ hsz)]
  simp only [Int.add_emod, Int.emod_emod]

lemma edgeAtZ_incidence (i : ℤ) (v : V) :
    inc (c.edgeAtZ i) v ↔ v = c.vertexAtZ i ∨ v = c.vertexAtZ (i+1) := by
  simpa [edgeAtZ, vertexAtZ, c.zindex_succ] using c.incidence (c.zindex i) v

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E L : Type*}
namespace IndexedCycle

variable {bags : V → Finset L}

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable [DecidableEq L]

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

lemma common_clamp_ratio {lo hi A x y : ℝ} (hlo : 0 ≤ lo) (hA : 1 ≤ A)
    (hxy : x ≤ A * y) :
    max lo (min hi x) ≤ A * max lo (min hi y) := by
  have hnonneg : 0 ≤ max lo (min hi y) := le_trans hlo (le_max_left _ _)
  have hupper : max lo (min hi y) ≤ A * max lo (min hi y) := by nlinarith
  apply max_le
  · exact le_trans (le_max_left _ _) hupper
  · by_cases hy : y ≤ hi
    · have hm : y ≤ max lo (min hi y) := by rw [min_eq_right hy]; exact le_max_right _ _
      exact le_trans (min_le_right _ _) (le_trans hxy (mul_le_mul_of_nonneg_left hm (by linarith)))
    · have hm : hi ≤ max lo (min hi y) := by rw [min_eq_left (le_of_not_ge hy)]; exact le_max_right _ _
      exact le_trans (min_le_left _ _) (le_trans hm hupper)

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_PM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq E]

variable (inc : E → V → Prop)

abbrev DemandTag := E × (Fin 4 → V) × Fin 64 × Bool × (Fin 4 → Option E) × (Fin 4 → Option E)

noncomputable def padOccurrences (m : Multiset E) : Fin 4 → Option E :=
  fun i => m.toList[i.val]?

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_IntervalPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_periodic (i : ℕ) : c.edgeAt (i + c.size) = c.edgeAt i := by
  simp [edgeAt, index]

variable [DecidableEq E]

def intervalPattern (x y a : ℕ) : Finset E :=
  ((Finset.Ico x y).filter (fun i => i % 2 = a)).image c.edgeAt

def parityPattern (a : ℕ) : Finset E := c.intervalPattern 0 c.size a

lemma mem_intervalPattern (e : E) (x y a : ℕ) :
    e ∈ c.intervalPattern x y a ↔ ∃ i, x ≤ i ∧ i < y ∧ i % 2 = a ∧ c.edgeAt i = e := by
  simp only [intervalPattern, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  aesop

lemma intervalPattern_union {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) (a : ℕ) :
    c.intervalPattern x y a ∪ c.intervalPattern y z a = c.intervalPattern x z a := by
  ext e
  simp only [Finset.mem_union, c.mem_intervalPattern]
  constructor
  · rintro (⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩)
    · exact ⟨i,hi,by omega,hp,he⟩
    · exact ⟨i,by omega,hj,hp,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    by_cases h : i < y
    · exact Or.inl ⟨i,hi,h,hp,he⟩
    · exact Or.inr ⟨i,by omega,hj,hp,he⟩

lemma intervalPattern_periodic {x y : ℕ} (a : ℕ) :
    c.intervalPattern (x + c.size) (y + c.size) a = c.intervalPattern x y a := by
  ext e
  simp only [c.mem_intervalPattern]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    have hn : c.size ≤ i := by omega
    refine ⟨i-c.size,by omega,by omega,?_,?_⟩
    · have hh := c.even
      omega
    · have eq : i - c.size + c.size = i := by omega
      rw [← c.edgeAt_periodic, eq]
      exact he
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i+c.size,by omega,by omega,?_,?_⟩
    · have hh := c.even
      omega
    · rw [c.edgeAt_periodic]; exact he

lemma rotatedPattern {x : ℕ} (hx : x ≤ c.size) (a : ℕ) :
    c.intervalPattern x (x+c.size) a = c.parityPattern a := by
  rw [← c.intervalPattern_union hx (by omega) a]
  have hh : c.intervalPattern c.size (x+c.size) a = c.intervalPattern 0 x a := by
    simpa only [zero_add] using (c.intervalPattern_periodic (x := 0) (y := x) a)
  rw [hh, Finset.union_comm, c.intervalPattern_union (by omega) hx a]
  rfl

lemma arc_through (x l : ℕ) (hx : x < c.size) (hl : 0 < l)
    (hlt : l < c.size) (ho : l % 2 = 1) :
    (c.arc x l hx hl hlt ho).through = c.intervalPattern x (x+l) (x%2) := by
  ext e
  simp only [OddPath.through, pathPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ico, c.mem_intervalPattern]
  dsimp only [arc]
  constructor
  · rintro ⟨j,⟨⟨_,hj⟩,hp⟩,he⟩
    exact ⟨x+j,by omega,by omega,by omega,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i-x,⟨⟨by omega,by omega⟩,by omega⟩,?_⟩
    simpa only [Nat.add_sub_of_le hi] using he

lemma arc_interior (x l : ℕ) (hx : x < c.size) (hl : 0 < l)
    (hlt : l < c.size) (ho : l % 2 = 1) :
    (c.arc x l hx hl hlt ho).interior = c.intervalPattern x (x+l) (1-x%2) := by
  ext e
  simp only [OddPath.interior, pathPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ico, c.mem_intervalPattern]
  dsimp only [arc]
  constructor
  · rintro ⟨j,⟨⟨hj₀,hj₁⟩,hp⟩,he⟩
    exact ⟨x+j,by omega,by omega,by omega,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i-x,⟨⟨by omega,by omega⟩,by omega⟩,?_⟩
    simpa only [Nat.add_sub_of_le hi] using he

end IndexedCycle

end

open scoped symmDiff

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

def exchange (M N S : Finset E) : Finset E := (M \ S) ∪ (N ∩ S)

lemma mem_exchange (M N S : Finset E) (e : E) :
    e ∈ exchange M N S ↔ (e ∈ M ∧ e ∉ S) ∨ (e ∈ N ∧ e ∈ S) := by
  simp only [exchange, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]

lemma exchange_union (M N S : Finset E) :
    exchange M N S ∪ exchange N M S = M ∪ N := by
  ext e
  simp only [Finset.mem_union, mem_exchange]
  tauto

lemma exchange_involution (M N S : Finset E) :
    exchange (exchange M N S) (exchange N M S) S = M := by
  ext e
  simp only [mem_exchange]
  tauto

def ExchangeCompatible (M N S : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ N, ∀ v, inc e v → inc f v → (e ∈ S ↔ f ∈ S)

omit [DecidableEq E] in
lemma ExchangeCompatible.symm {M N S : Finset E} (h : ExchangeCompatible (inc := inc) M N S) :
    ExchangeCompatible (inc := inc) N M S := by
  intro f hf e he v hfv hev
  exact (h e he f hf v hev hfv).symm

noncomputable def componentEdges (U : Finset E) (anchor : E) : Finset E := by
  classical
  exact U.filter ((overlayLineGraph inc U).Reachable anchor)

omit [DecidableEq E] in
lemma mem_componentEdges (U : Finset E) (a e : E) :
    e ∈ componentEdges (inc := inc) U a ↔ e ∈ U ∧ (overlayLineGraph inc U).Reachable a e := by
  classical
  simp only [componentEdges, Finset.mem_filter]

lemma shares_reachable {U : Finset E} {e f : E} (he : e ∈ U) (hf : f ∈ U)
    {v : V} (hev : inc e v) (hfv : inc f v) :
    (overlayLineGraph inc U).Reachable e f := by
  by_cases h : e = f
  · subst f; exact SimpleGraph.Reachable.refl e
  · exact (show (overlayLineGraph inc U).Adj e f from ⟨h,he,hf,v,hev,hfv⟩).reachable

lemma component_compatible (M N : Finset E) (anchor : E) :
    ExchangeCompatible (inc := inc) M N (componentEdges (inc := inc) (M ∪ N) anchor) := by
  intro e he f hf v hev hfv
  have heu := Finset.mem_union_left N he
  have hfu := Finset.mem_union_right M hf
  have hr := shares_reachable heu hfu hev hfv
  simp only [mem_componentEdges, heu, hfu, true_and]
  exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

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

noncomputable def components (U : Finset E) : Finset (Finset E) := by
  classical
  exact U.image (componentEdges (inc := inc) U)

lemma mem_components {U S : Finset E} :
    S ∈ components (inc := inc) U ↔ ∃ a ∈ U, componentEdges (inc := inc) U a = S := by
  classical
  simp only [components, Finset.mem_image]

omit [DecidableEq E] in
lemma componentEdges_self {U : Finset E} {a : E} (ha : a ∈ U) :
    a ∈ componentEdges (inc := inc) U a :=
  (mem_componentEdges U a a).mpr ⟨ha,SimpleGraph.Reachable.refl a⟩

lemma component_nonempty {U S : Finset E} (hS : S ∈ components (inc := inc) U) : S.Nonempty := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  exact ⟨a,componentEdges_self ha⟩

lemma component_exists_vertex (hinc : ∀ e, ∃ v, inc e v)
    {U S : Finset E} (hS : S ∈ components (inc := inc) U) :
    ∃ v, ∃ e ∈ S, inc e v := by
  obtain ⟨e,he⟩ := component_nonempty hS
  obtain ⟨v,hv⟩ := hinc e
  exact ⟨v,e,he,hv⟩

noncomputable def componentVertex (hinc : ∀ e, ∃ v, inc e v)
    {U : Finset E} (S : ↥(components (inc := inc) U)) : V :=
  (component_exists_vertex hinc S.property).choose

lemma component_exchange_compatible {M N S : Finset E}
    (hS : S ∈ components (inc := inc) (M ∪ N)) : ExchangeCompatible (inc := inc) M N S := by
  obtain ⟨a,_,rfl⟩ := mem_components.mp hS
  exact component_compatible M N a



namespace IndexedCycle

variable (c : IndexedCycle inc)

noncomputable def edgeSet : Finset E := Finset.univ.image c.edge

lemma mem_edgeSet (e : E) : e ∈ c.edgeSet ↔ ∃ i, i < c.size ∧ c.edgeAt i = e := by
  simp only [edgeSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.isLt,by simp [edgeAt,index,Nat.mod_eq_of_lt i.isLt]⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨c.index i,rfl⟩

end IndexedCycle

end

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

def conversionPieces (b : Bool) (S : Finset (Fin 4)) (i : Fin 4) : Finset E :=
  if i ∈ S then (c.side i).closed (c.chord i) else c.orientationPieces b i

def converted (b : Bool) (S : Finset (Fin 4)) : Finset E :=
  assemble (c.conversionPieces b S)

def canonicalGain (R : Finset E) (f : Finset E → ℝ) (b : Bool) (i : Fin 4) : ℝ :=
  f (R ∪ c.orientation b) - f (R ∪ c.contextOne b i)

def contextError (R : Finset E) (f : Finset E → ℝ) (b : Bool) (X Y : Fin 4) : ℝ :=
  (f (R ∪ c.contextOne b Y) -
    f (R ∪ ((c.contextOne b Y \ (c.side X).through) ∪ (c.side X).closed (c.chord X)))) -
  (f (R ∪ c.orientation b) - f (R ∪ c.contextOne b X))

end CellPaths

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

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

variable [DecidableEq E]

def sewn (x y : ℕ) (e : E) : Finset E :=
  (c.intervalPattern x y (1-x%2) ∪ c.intervalPattern y (x+c.size) (x%2)) ∪ {e}

end IndexedCycle

end

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

def signedGain (R : Finset E) (f : Finset E → ℝ) (x y : ℕ) (e : E) : ℝ :=
  if x%2=0 then f (R ∪ c.parityPattern 0) - f (R ∪ c.sewn x y e)
  else f (R ∪ c.sewn x y e) - f (R ∪ c.parityPattern 1)

namespace Corners

variable {c} (k : c.Corners)

def cornerSewn (chord : Fin 4 → E) : Fin 4 → Finset E :=
  ![c.sewn k.a₀ k.a₁ (chord 0), c.sewn k.a₁ k.a₂ (chord 1),
    c.sewn k.a₂ k.a₃ (chord 2), c.sewn k.a₀ k.a₃ (chord 3)]

variable [DecidableEq V]

def signedLocalTerm (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (R : Finset E) (f : Finset E → ℝ) : ℝ :=
  let P := k.cellPaths chord hc
  let t := (f (R ∪ P.switched true) - f (R ∪ P.switched false)) +
    P.contextError R f true 2 0 - P.contextError R f false 3 1
  if k.a₀%2=0 then t else -t

end Corners

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Cycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

abbrev PatternCode (inc : E → V → Prop) :=
  {s : Finset E × Finset E // ∃ c : IndexedCycle inc,
    c.parityPattern 0 = s.1 ∧ c.parityPattern 1 = s.2}

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Through
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

def through : Finset E := x.val.1

def closed : Finset E := x.val.2

def total : Finset E := x.through ∪ x.closed

variable [Fintype E]

noncomputable instance instFintype : Fintype (PatternCode inc) := Fintype.ofFinite _

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.PairEnergy

open scoped BigOperators

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

variable {ι Ω Δ : Type*} [Fintype ι] [Fintype Ω] [Fintype Δ]

noncomputable def guideMass (π : Law Ω) (closed : ι → Finset Ω) (X : ι) : ℝ :=
  ∑ B ∈ closed X, π.weight B

noncomputable def guideMean (π : Law Ω) (closed : ι → Finset Ω)
    (derivative : ι → Ω → ℝ) (X : ι) : ℝ :=
  (∑ B ∈ closed X, π.weight B * derivative X B) / guideMass π closed X

noncomputable def contextMass (ρ : Δ → ℝ) (arc : Δ → ι) (context : Δ → Ω)
    (X : ι) (A : Ω) : ℝ := by
  classical
  exact ∑ d with arc d = X ∧ context d = A, ρ d

noncomputable def swapSum (π : Law Ω) (through closed : ι → Finset Ω)
    (d₁ d₂ : ι → Ω → ℝ) : ℝ :=
  ∑ X, ∑ A ∈ through X, ∑ B ∈ closed X,
    π.weight A * π.weight B * (d₁ X A - d₂ X B) ^ 2

end MatchingFPRAS.PairEnergy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SafeSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

def commonInterior : Finset E := assemble fun i => (c.side i).interior

end CellPaths

end MatchingFPRAS.Transport

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

def underlying (M : Finset E) : SimpleGraph V where
  Adj v w := ∃ e ∈ M, ends e = s(v, w)
  symm := ⟨by
    rintro v w ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    rintro v ⟨e, he, h⟩
    exact hloop e (by rw [h]; simp)⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma exists_partner {e : E} {v : V} (hv : v ∈ ends e) :
    ∃ w, ends e = s(v,w) := by
  exact hv

open scoped symmDiff

def discrepancy (M N : Finset E) : SimpleGraph V :=
  underlying ends hloop M ∆ underlying ends hloop N

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma discrepancy_adj_iff [Fintype V] [DecidableEq V] [DecidableEq E] (M N : Finset E) (v w : V) :
    (discrepancy ends hloop M N).Adj v w ↔
      ((underlying ends hloop M).Adj v w ∧ ¬ (underlying ends hloop N).Adj v w) ∨
      ((underlying ends hloop N).Adj v w ∧ ¬ (underlying ends hloop M).Adj v w) := by
  rfl

omit [Fintype V] [DecidableEq V] in
lemma alternating_cycle_parity [Fintype V] [DecidableEq V] {G H : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (halt : G.IsAlternating H) :
    p.length % 2 = 0 := by
  let Q : ℕ → Prop := fun i => H.Adj (p.getVert i) (p.getVert (i + 1))
  have recur : ∀ i, i + 1 < p.length → (Q (i + 1) ↔ ¬ Q i) := by
    intro i hi
    have hn : p.getVert i ≠ p.getVert (i + 2) := by
      simpa using hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
    have h := halt hn (p.adj_getVert_succ (i := i) (by omega)).symm
      (p.adj_getVert_succ (i := i + 1) hi)
    dsimp [Q]
    have hsym := H.adj_comm (u := p.getVert (i + 1)) (v := p.getVert i)
    tauto
  have parity : ∀ i, i < p.length →
      (Q i ↔ if i % 2 = 0 then Q 0 else ¬ Q 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      rw [recur i hi, ih (by omega)]
      split_ifs <;> first | omega | tauto
  have hn : p.getVert 1 ≠ p.getVert (p.length - 1) := by
    simpa [SimpleGraph.Walk.snd, SimpleGraph.Walk.penultimate] using hp.snd_ne_penultimate
  have hfirst := p.adj_getVert_succ (i := 0) (by have := hp.three_le_length; omega)
  have hlast := p.adj_getVert_succ (i := p.length - 1) (by have := hp.three_le_length; omega)
  have he : p.length - 1 + 1 = p.length := by have := hp.three_le_length; omega
  have hclose : Q 0 ↔ ¬ Q (p.length - 1) := by
    have h := halt hn (by simpa using hfirst) (by simpa [he] using hlast.symm)
    simpa [Q, he, H.adj_comm] using h
  have hr := parity (p.length - 1) (by have := hp.three_le_length; omega)
  split_ifs at hr
  · tauto
  · have := hp.three_le_length
    omega

def cyclicVertex {G : SimpleGraph V} {v : V} (p : G.Walk v v) (i : ℕ) : V :=
  p.getVert (i % p.length)

omit [Fintype V] [DecidableEq V] in
lemma cyclicVertex_injOn [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) : Set.InjOn (cyclicVertex p) (Set.Ico 0 p.length) := by
  intro i hi j hj h
  have hi' := hi.2
  have hj' := hj.2
  simp only [cyclicVertex, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h
  exact hp.getVert_injOn' (by change i ≤ p.length - 1; omega)
    (by change j ≤ p.length - 1; omega) h

omit [Fintype V] [DecidableEq V] in
lemma cyclicVertex_next [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (i : ℕ) (hi : i < p.length) : cyclicVertex p (i + 1) = p.getVert (i + 1) := by
  by_cases h : i + 1 < p.length
  · simp [cyclicVertex, Nat.mod_eq_of_lt h]
  · have he : i + 1 = p.length := by omega
    simp [he, cyclicVertex]

lemma cyclicVertex_adj {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (i : ℕ) : G.Adj (cyclicVertex p i) (cyclicVertex p (i + 1)) := by
  have hm : i % p.length < p.length := Nat.mod_lt i (by have := hp.three_le_length; omega)
  have he : cyclicVertex p (i + 1) = cyclicVertex p (i % p.length + 1) := by
    simp only [cyclicVertex, Nat.add_mod, Nat.mod_mod]
  rw [he, cyclicVertex_next p _ hm]
  exact p.adj_getVert_succ hm

end Overlay

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ComponentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def componentOrder (U : Finset E) :
    Fin (components (inc := inc) U).card ≃ ↥(components (inc := inc) U) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

noncomputable def componentPrefix (U : Finset E) (i : ℕ) : Finset E := by
  classical
  exact (Finset.univ.filter (fun j : Fin (components (inc := inc) U).card => j.val < i)).biUnion
    (fun j => (componentOrder (inc := inc) U j).val)

omit [Fintype V] [DecidableEq V] in
lemma mem_componentPrefix (U : Finset E) (i : ℕ) (e : E) :
    e ∈ componentPrefix (inc := inc) U i ↔
      ∃ j : Fin (components (inc := inc) U).card, j.val < i ∧ e ∈ (componentOrder (inc := inc) U j).val := by
  classical
  simp only [componentPrefix, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_compatible (M N : Finset E) (i : ℕ) :
    ExchangeCompatible (inc := inc) M N (componentPrefix (inc := inc) (M ∪ N) i) := by
  intro e he f hf v hev hfv
  simp only [mem_componentPrefix]
  constructor
  · rintro ⟨j,hj,he'⟩
    exact ⟨j,hj,(component_exchange_compatible (componentOrder (M ∪ N) j).property
      e he f hf v hev hfv).mp he'⟩
  · rintro ⟨j,hj,hf'⟩
    exact ⟨j,hj,(component_exchange_compatible (componentOrder (M ∪ N) j).property
      e he f hf v hev hfv).mpr hf'⟩

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def componentAt (U : Finset E) (i : ℕ) : Finset E :=
  if h : i < (components (inc := inc) U).card then (componentOrder (inc := inc) U ⟨i,h⟩).val else ∅

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma componentAt_compatible (M N : Finset E) (i : ℕ) :
    ExchangeCompatible (inc := inc) M N (componentAt (inc := inc) (M ∪ N) i) := by
  classical
  unfold componentAt
  split_ifs with h
  · exact component_exchange_compatible (componentOrder (M ∪ N) ⟨i,h⟩).property
  · intro e he f hf v hev hfv
    simp

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_EndpointPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

include hbags hG in
omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma label_memberships_le_two (v : V) : (bags v).card ≤ 2 := by
  by_contra h
  have hc : G.IsNClique ((bags v).card) (bags v) := by
    constructor
    · intro a ha b hb hab
      exact (hbags v a ha b hb).resolve_left hab
    · rfl
  exact hc.not_cliqueFree (hG.cliqueFree (by omega))

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def cycleSquare (f g : Finset E → ℝ) (A B : Finset E) (S : Finset E) : ℝ :=
  ((f A+g B)-(f (exchange A B S)+g (exchange B A S)))^2

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteVariance

variable {Ω : Type*} [Fintype Ω]

noncomputable def variance (π f : Ω → ℝ) : ℝ :=
  ∑ x, π x * (f x - ∑ y, π y * f y)^2

end MatchingFPRAS.FiniteVariance

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
variable [Inhabited Λ] [Inhabited P]
omit [DecidableEq K] in
lemma supports_univ [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : TM2.Supports M Finset.univ := by
  constructor
  · simp
  · intro l _
    induction M l with
    | push k a q ih | peek k a q ih | pop k a q ih | load a q ih => exact ih
    | branch p q r ihq ihr => exact ⟨ihq,ihr⟩
    | goto l => simp [TM2.SupportsStmt]
    | halt => trivial

open Turing MachineCost

end MatchingFPRAS.StackComposition

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ThresholdGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

open Finset

variable {V : Type*}

inductive ChargeTrace [DecidableEq V] (B : V → V → ℝ) :
    Finset V → Finset V → ℝ → Prop
  | done (U) : ChargeTrace B U U 1
  | remove (U W : Finset V) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
      (Tj Tk f F : ℝ) (hj0 : 0 < Tj) (hk0 : 0 < Tk) (hf0 : 0 ≤ f) (hF0 : 0 ≤ F)
      (hTj : ∀ a, a ≠ j → B j a ≤ Tj) (hTk : ∀ a, a ≠ k → B k a ≤ Tk)
      (hf : f*Tj*Tk ≤ B j k) (next : ChargeTrace B (U \ {j,k}) W F) :
      ChargeTrace B U W (f*F)
  | replace (U W : Finset V) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
      (T f F : ℝ) (hT0 : 0 < T) (hf0 : 0 ≤ f) (hF0 : 0 ≤ F)
      (hT : ∀ a, a ≠ j → B j a ≤ T) (hf : f*T ≤ B j u)
      (next : ChargeTrace B (insert u (U.erase j)) W F) :
      ChargeTrace B U W (f*F)

def pairVertices (xs : List (V × V)) : List V := xs.flatMap (fun q => [q.1,q.2])

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

namespace MatchingFPRAS.Subdivision

open Finset

def wordWeight (a : Bool) : List ℝ → ℝ
  | [] => 1
  | x::xs => (if a then x else 1) * wordWeight (!a) xs

@[simp] theorem wordWeight_nil (a : Bool) : wordWeight a [] = 1 := rfl

@[simp] theorem wordWeight_pair (a : Bool) (x : ℝ) (xs : List ℝ) :
    wordWeight a (x::x::xs) = x * wordWeight a xs := by
  cases a <;> simp [wordWeight]

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

noncomputable def vertexPotential (p : ℕ) (B Hu Hv lam : ℝ) (k : ℕ) : ℝ :=
  if k ≤ 2*p then
    if Even k then 1 else max B (Hu/2^(k/2))
  else if Even k then max B (Hv/2^((4*p+1-k)/2))/lam else lam

@[simp] lemma vertexPotential_zero (p : ℕ) (B Hu Hv lam : ℝ) :
    vertexPotential p B Hu Hv lam 0 = 1 := by simp [vertexPotential]

@[simp] lemma vertexPotential_last (p : ℕ) (B Hu Hv lam : ℝ) :
    vertexPotential p B Hu Hv lam (4*p+1) = lam := by
  have hn : ¬ Even (4*p+1) := by simp [Nat.even_iff]; omega
  simp [vertexPotential,show ¬ 4*p+1 ≤ 2*p by omega,hn]

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

theorem acyclic_of_unique_lower {L : Type*} (G : SimpleGraph L) (rank : L → ℕ)
    (hdiff : ∀ {a b}, G.Adj a b → rank a ≠ rank b)
    (hparent : ∀ a b c, G.Adj a b → G.Adj a c → rank b < rank a → rank c < rank a → b=c) :
    G.IsAcyclic := by
  classical
  intro a p hp
  obtain ⟨b,hb,hmax⟩ := p.support.toFinset.exists_max_image rank
    ⟨a,by simp⟩
  have hb' : b ∈ p.support := List.mem_toFinset.mp hb
  let q := p.rotate b hb'
  have hq : q.IsCycle := hp.rotate hb'
  have hqs : q.snd ∈ p.support := (p.mem_support_rotate_iff b hb').mp (q.getVert_mem_support 1)
  have hqt : q.penultimate ∈ p.support :=
    (p.mem_support_rotate_iff b hb').mp (q.getVert_mem_support (q.length-1))
  have hs : rank q.snd < rank b := lt_of_le_of_ne
    (hmax q.snd (List.mem_toFinset.mpr hqs)) (hdiff (q.adj_snd hq.not_nil)).symm
  have ht : rank q.penultimate < rank b := lt_of_le_of_ne
    (hmax q.penultimate (List.mem_toFinset.mpr hqt)) (hdiff (q.adj_penultimate hq.not_nil))
  exact hq.snd_ne_penultimate (hparent b q.snd q.penultimate (q.adj_snd hq.not_nil)
    (q.adj_penultimate hq.not_nil).symm hs ht)

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
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

noncomputable def edgeLow (s : Sym2 V) : V := Sym2.lift ⟨min,min_comm⟩ s

noncomputable def edgeHigh (s : Sym2 V) : V := Sym2.lift ⟨max,max_comm⟩ s

omit [Fintype V] in
@[simp] lemma edgeLow_mk (x y : V) : edgeLow s(x,y)=min x y := rfl

omit [Fintype V] in
@[simp] lemma edgeHigh_mk (x y : V) : edgeHigh s(x,y)=max x y := rfl

omit [Fintype V] in
lemma edgeLow_mem (s : Sym2 V) : edgeLow s ∈ s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [min_def,h]

omit [Fintype V] in
lemma edge_low_high (s : Sym2 V) : s(edgeLow s,edgeHigh s)=s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [min_def,max_def,h,Sym2.eq_swap]

omit [Fintype V] in
lemma edgeLow_lt_high (s : Sym2 V) (hs : ¬s.IsDiag) : edgeLow s < edgeHigh s := by
  induction s using Sym2.inductionOn with
  | hf x y =>
    have hxy : x ≠ y := by simpa using hs
    rcases hxy.lt_or_gt with h | h <;> simp [h.le,h]

end

open Finset MatchingFPRAS.Switching

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

def inflationScale (D₀ : ℝ) : ℝ := 100*(Fintype.card V : ℝ)^2*D₀

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

noncomputable def density (p : I → Ω → ℝ) (s : I → Ω) : ℝ := ∏ i, p i (s i)

noncomputable def dot (p : I → Ω → ℝ) (f g : (I → Ω) → ℝ) : ℝ :=
  ∑ s, density p s * f s * g s

noncomputable def average (p : I → Ω → ℝ) (i : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) where
  toFun f s := ∑ a, p i a * f (Function.update s i a)
  map_add' f g := by funext s; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by funext s; simp [Finset.mul_sum,mul_left_comm]

omit [Fintype I] in
lemma average_apply (p : I → Ω → ℝ) (i : I) (f : (I → Ω) → ℝ) (s : I → Ω) :
    average p i f s = ∑ a, p i a * f (Function.update s i a) := rfl

omit [Fintype I] in
lemma average_idem (p : I → Ω → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i : I)
    (f : (I → Ω) → ℝ) : average p i (average p i f) = average p i f := by
  funext s
  simp only [average_apply, Function.update_idem]
  rw [← Finset.sum_mul, hp i, one_mul]

omit [Fintype I] in
lemma average_comm (p : I → Ω → ℝ) (i j : I) (f : (I → Ω) → ℝ) :
    average p i (average p j f) = average p j (average p i f) := by
  classical
  by_cases h : i = j
  · subst j; rfl
  funext s
  simp only [average_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm h]
  ring

noncomputable def swapDraw (i : I) : ((I → Ω) × Ω) ≃ ((I → Ω) × Ω) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by simp [Function.update_idem]
  right_inv z := by simp [Function.update_idem]

omit [Fintype Ω] in
lemma density_swap (p : I → Ω → ℝ) (i : I) (s : I → Ω) (a : Ω) :
    density p s * p i a = density p (Function.update s i a) * p i (s i) := by
  classical
  unfold density
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, p j (Function.update s i a j)) =
      ∏ j ∈ Finset.univ.erase i, p j (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

lemma average_adjoint (p : I → Ω → ℝ) (i : I) (f g : (I → Ω) → ℝ) :
    dot p (average p i f) g = dot p f (average p i g) := by
  classical
  unfold dot
  simp only [average_apply, Finset.mul_sum, Finset.sum_mul]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have h := Equiv.sum_comp (swapDraw (Ω := Ω) i)
    (fun z : (I → Ω) × Ω => density p z.1 * f z.1 * (p i z.2 * g (Function.update z.1 i z.2)))
  rw [← h]
  apply Finset.sum_congr rfl
  intro z _
  simp only [swapDraw, Equiv.coe_fn_mk, Function.update_idem,
    Function.update_eq_self]
  have hz := density_swap p i z.1 z.2
  nlinarith [congrArg (fun t : ℝ => t * f (Function.update z.1 i z.2) * g z.1) hz]

variable (p : I → Ω → ℝ)

lemma dot_sub_left (f g h : (I → Ω) → ℝ) :
    dot p (f-g) h = dot p f h - dot p g h := by
  simp [dot, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma dot_sub_right (f g h : (I → Ω) → ℝ) :
    dot p f (g-h) = dot p f g - dot p f h := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

structure Projection where
  op : (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ))
  idem : ∀ f, op (op f) = op f
  adj : ∀ f g, dot p (op f) g = dot p f (op g)

namespace Projection

variable {p}

noncomputable def complement (P : Projection p) : Projection p where
  op := LinearMap.id - P.op
  idem f := by
    change f-P.op f-P.op (f-P.op f) = f-P.op f
    rw [map_sub, P.idem]
    abel
  adj f g := by
    change dot p (f-P.op f) g = dot p f (g-P.op g)
    rw [dot_sub_left, dot_sub_right, P.adj]

noncomputable def comp (P Q : Projection p)
    (hc : ∀ f, P.op (Q.op f) = Q.op (P.op f)) : Projection p where
  op := P.op.comp Q.op
  idem f := by
    change P.op (Q.op (P.op (Q.op f))) = P.op (Q.op f)
    rw [← hc, Q.idem, P.idem]
  adj f g := by
    change dot p (P.op (Q.op f)) g = dot p f (P.op (Q.op g))
    rw [P.adj, Q.adj, hc]

end Projection

noncomputable def avgProjection (hp : ∀ i, ∑ a, p i a = 1) (i : I) : Projection p where
  op := average p i
  idem := average_idem p hp i
  adj := average_adjoint p i

noncomputable def avgList : List I → (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ))
  | [] => LinearMap.id
  | i::l => (average p i).comp (avgList l)

omit [Fintype I] in
lemma avgList_cons (i : I) (l : List I) (f : (I → Ω) → ℝ) :
    avgList p (i::l) f = average p i (avgList p l f) := rfl

omit [Fintype I] in
lemma average_comm_list (i : I) (l : List I) (f : (I → Ω) → ℝ) :
    average p i (avgList p l f) = avgList p l (average p i f) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [avgList_cons, average_comm, ih, avgList_cons]

omit [Fintype I] in
lemma avgList_idem (hp : ∀ i, ∑ a, p i a = 1) (l : List I) (f : (I → Ω) → ℝ) :
    avgList p l (avgList p l f) = avgList p l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [avgList_cons]
    rw [← average_comm_list, ih, average_idem p hp]

lemma avgList_adjoint (l : List I) (f g : (I → Ω) → ℝ) :
    dot p (avgList p l f) g = dot p f (avgList p l g) := by
  induction l generalizing g with
  | nil => rfl
  | cons i l ih =>
    rw [avgList_cons, average_adjoint, ih, ← average_comm_list, avgList_cons]

noncomputable def listProjection (hp : ∀ i, ∑ a, p i a = 1) (l : List I) : Projection p where
  op := avgList p l
  idem := avgList_idem p hp l
  adj := avgList_adjoint p l

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def outside (x y : I) : List I :=
  (Finset.univ.filter (fun i => x < i ∧ i ≠ y)).toList

noncomputable def pairCondition (x y : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) := avgList p (outside x y)

noncomputable def residual (x y : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) :=
  (LinearMap.id-average p x).comp
    ((LinearMap.id-average p y).comp (pairCondition p x y))

end

open Finset

end MatchingFPRAS.Replica

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def mean (f : (I → Ω) → ℝ) : ℝ := ∑ s, density p s*f s

noncomputable def variance (f : (I → Ω) → ℝ) : ℝ :=
  dot p (f-(fun _ => mean p f)) (f-(fun _ => mean p f))

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def future (S : Finset I) (x : I) := avgList p ((S.filter (x < ·)).toList)

noncomputable def increment (S : Finset I) (x : I) (f : (I → Ω) → ℝ) : (I → Ω) → ℝ :=
  future p S x f-average p x (future p S x f)

end

section

open Finset

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

noncomputable def localEnergy (q : Ω → Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (∑ a, ∑ b, q a b * (f a-f b)^2)/2

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

structure PairCapacity (x y : I) where
  q : (Ω × Ω) → (Ω × Ω) → ℝ
  nonneg : ∀ a b, 0 ≤ q a b
  row : ∀ a, ∑ b, q a b = p x a.1*p y a.2
  col : ∀ b, ∑ a, q a b = p x b.1*p y b.2

def replacePair (x y : I) (s : I → Ω) (a : Ω × Ω) : I → Ω :=
  Function.update (Function.update s x a.1) y a.2

def slice (x y : I) (f : (I → Ω) → ℝ) (s : I → Ω) (a : Ω × Ω) : ℝ :=
  f (replacePair x y s a)

noncomputable def pairEnergy (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) : ℝ :=
  mean p (fun s => localEnergy Q.q (slice x y f s))

end MatchingFPRAS.Replica

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TierClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

noncomputable def tierClamp (c : ℝ) (t : ℕ) (w : ℝ) : ℝ :=
  max (c^t)⁻¹ (min (c^t) w)

lemma tierClamp_pos {c : ℝ} (hc : 0 < c) (t : ℕ) (w : ℝ) : 0 < tierClamp c t w :=
  lt_of_lt_of_le (inv_pos.mpr (pow_pos hc t)) (le_max_left _ _)

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype E] in
lemma exchange_inter (M N S : Finset E) :
    exchange M N S ∩ exchange N M S = M ∩ N := by
  ext e
  simp only [Finset.mem_inter,mem_exchange]
  tauto

end

open Finset

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

noncomputable def relationDestinations (R : Ω → Ω → Prop) (a : Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun b => a ≠ b ∧ R a b)

noncomputable def relationOff (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : ℝ := by
  classical
  exact if b ∈ relationDestinations R a then (d:ℝ)⁻¹ else 0

noncomputable def relationProposal (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : ℝ := by
  classical
  exact if a = b then 1-∑ z, relationOff R d a z else relationOff R d a b

lemma relationOff_self (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) : relationOff R d a a = 0 := by
  classical
  simp [relationOff,relationDestinations]

lemma relationOff_nonneg (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : 0 ≤ relationOff R d a b := by
  classical
  unfold relationOff; split_ifs <;> positivity

lemma relationOff_sum (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) :
    (∑ b, relationOff R d a b) = (relationDestinations R a).card / (d:ℝ) := by
  classical
  unfold relationOff
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

lemma relationOff_sum_le_one (R : Ω → Ω → Prop) (d : ℕ) (a : Ω)
    (hd : (relationDestinations R a).card ≤ d) : (∑ b, relationOff R d a b) ≤ 1 := by
  rw [relationOff_sum]
  by_cases h : d = 0
  · simp [h]
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast hd

lemma relationProposal_nonneg (R : Ω → Ω → Prop) (d : ℕ)
    (hd : ∀ a, (relationDestinations R a).card ≤ d) (a b : Ω) : 0 ≤ relationProposal R d a b := by
  classical
  unfold relationProposal; split_ifs
  · exact sub_nonneg.mpr (relationOff_sum_le_one R d a (hd a))
  · exact relationOff_nonneg _ _ _ _

lemma relationProposal_symmetric (R : Ω → Ω → Prop) (d : ℕ)
    (hR : ∀ a b, R a b ↔ R b a) (a b : Ω) : relationProposal R d a b = relationProposal R d b a := by
  classical
  by_cases h : a = b
  · subst b; rfl
  · simp [relationProposal,h,Ne.symm h,relationOff,relationDestinations,hR a b]

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

variable (ends : E → Sym2 V)

noncomputable def edgeEndpoints (e : E) : V × V :=
  Classical.choose (show ∃ p : V × V, ends e = s(p.1,p.2) from
    Sym2.inductionOn (ends e) (fun a b => ⟨(a,b),rfl⟩))

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma edgeEndpoints_spec (e : E) : ends e = s((edgeEndpoints ends e).1,(edgeEndpoints ends e).2) :=
  Classical.choose_spec (show ∃ p : V × V, ends e = s(p.1,p.2) from
    Sym2.inductionOn (ends e) (fun a b => ⟨(a,b),rfl⟩))

noncomputable def pairRep (I : Finset E) (h : I.card = 2) : E × E :=
  Classical.choose (show ∃ p : E × E, p.1 ≠ p.2 ∧ I = {p.1,p.2} from by
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h
    exact ⟨(a,b),hab,he⟩)

omit [Fintype E] in
lemma pairRep_spec (I : Finset E) (h : I.card = 2) :
    (pairRep I h).1 ≠ (pairRep I h).2 ∧ I = {(pairRep I h).1,(pairRep I h).2} :=
  Classical.choose_spec (show ∃ p : E × E, p.1 ≠ p.2 ∧ I = {p.1,p.2} from by
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h
    exact ⟨(a,b),hab,he⟩)

noncomputable def withEnds (a b : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ends e = s(a,b))

omit [Fintype V] [DecidableEq E] in
lemma mem_withEnds (a b : V) (e : E) : e ∈ withEnds ends a b ↔ ends e = s(a,b) := by
  classical
  simp [withEnds]

omit [Fintype V] [DecidableEq E] in
lemma withEnds_card_le (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (a b : V) : (withEnds ends a b).card ≤ 2 := by
  classical
  by_cases h : (withEnds ends a b).Nonempty
  · obtain ⟨e,he⟩ := h
    have hh : withEnds ends a b = Finset.univ.filter (fun f => ends f = ends e) := by
      unfold withEnds
      rw [(mem_withEnds ends a b e).mp he]
    rw [hh]; exact hpar e
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

noncomputable def edgePairOptions (R : Finset E) (a b c d : V) : Finset (Finset E) := by
  classical
  exact (withEnds ends a b).biUnion fun e =>
    (withEnds ends c d).image fun f => R ∪ {e,f}

omit [Fintype V] in
lemma mem_edgePairOptions (R : Finset E) (a b c d : V) (e f : E)
    (he : ends e = s(a,b)) (hf : ends f = s(c,d)) :
    R ∪ {e,f} ∈ edgePairOptions ends R a b c d := by
  classical
  exact Finset.mem_biUnion.mpr ⟨e,(mem_withEnds ends a b e).mpr he,
    Finset.mem_image.mpr ⟨f,(mem_withEnds ends c d f).mpr hf,rfl⟩⟩

omit [Fintype V] in
lemma edgePairOptions_card_le
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (R : Finset E) (a b c d : V) : (edgePairOptions ends R a b c d).card ≤ 4 := by
  classical
  calc
    _ ≤ ∑ e ∈ withEnds ends a b, ((withEnds ends c d).image (fun f => R ∪ {e,f})).card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ withEnds ends a b, 2 := Finset.sum_le_sum (fun _ _ =>
      Finset.card_image_le.trans (withEnds_card_le ends hpar c d))
    _ ≤ 4 := by simp only [Finset.sum_const,smul_eq_mul]; have := withEnds_card_le ends hpar a b; omega

noncomputable def switchOptions (A : Finset E) (I : Finset E) : Finset (Finset E) := by
  classical
  exact if h : I.card = 2 then
    let p := pairRep I h
    let u := edgeEndpoints ends p.1
    let v := edgeEndpoints ends p.2
    edgePairOptions ends (A\I) u.1 v.1 u.2 v.2 ∪
      edgePairOptions ends (A\I) u.1 v.2 u.2 v.1
  else ∅

omit [Fintype V] in
lemma switchOptions_card_le
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A I : Finset E) : (switchOptions ends A I).card ≤ 8 := by
  classical
  unfold switchOptions
  split_ifs with h
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (edgePairOptions_card_le ends hpar _ _ _ _ _) (edgePairOptions_card_le ends hpar _ _ _ _ _))
  · simp

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [Fintype V] in
lemma mem_pairOptions_of_endpoints (R : Finset E) (p q f g : E) (a b c d : V)
    (hp : ends p = s(a,b)) (hq : ends q = s(c,d))
    (hf : ends f = s(b,c)) (hg : ends g = s(d,a)) :
    R ∪ {f,g} ∈
      edgePairOptions ends R (edgeEndpoints ends p).1 (edgeEndpoints ends q).1
        (edgeEndpoints ends p).2 (edgeEndpoints ends q).2 ∪
      edgePairOptions ends R (edgeEndpoints ends p).1 (edgeEndpoints ends q).2
        (edgeEndpoints ends p).2 (edgeEndpoints ends q).1 := by
  classical
  have hu := Sym2.eq_iff.mp ((edgeEndpoints_spec ends p).symm.trans hp)
  have hv := Sym2.eq_iff.mp ((edgeEndpoints_spec ends q).symm.trans hq)
  rcases hu with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hv with ⟨h3,h4⟩ | ⟨h3,h4⟩
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_right
    rw [Finset.pair_comm f g]
    exact mem_edgePairOptions ends R a d b c g f (hg.trans (Sym2.eq_swap)) hf
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_left
    rw [Finset.pair_comm f g]
    exact mem_edgePairOptions ends R a d b c g f (hg.trans (Sym2.eq_swap)) hf
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_left
    exact mem_edgePairOptions ends R b c a d f g hf (hg.trans (Sym2.eq_swap))
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_right
    exact mem_edgePairOptions ends R b c a d f g hf (hg.trans (Sym2.eq_swap))

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma inc_eq_ends (e : E) (a b : V) (hab : a ≠ b)
    (h : ∀ x, x ∈ ends e ↔ x = a ∨ x = b) : ends e = s(a,b) := by
  exact (Sym2.mem_and_mem_iff hab).mp ⟨(h a).mpr (Or.inl rfl),(h b).mpr (Or.inr rfl)⟩

end

open Finset

attribute [local instance] Classical.propDecidable

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

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def localVariance (π : Ω → ℝ) (a : Ω → ℝ) : ℝ :=
  ∑ u, π u*(a u-∑ v, π v*a v)^2

def PairPoincare (x y : I) (Q : PairCapacity p x y) (C : ℝ) : Prop :=
  ∀ a b : Ω → ℝ, localVariance (p x) a ≤ C*localEnergy Q.q (fun z => a z.1+b z.2)

noncomputable def baseEnergy (i : I) (f : (I → Ω) → ℝ) : ℝ :=
  dot p (f-average p i f) (f-average p i f)

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def allowed (guides : I → Finset I) : Finset (I × I) :=
  Finset.univ.filter (fun z => z.2 ∈ guides z.1)

noncomputable def pairTotal (guides : I → Finset I) (Q : ∀ x y, PairCapacity p x y)
    (f : (I → Ω) → ℝ) : ℝ := ∑ x, ∑ y ∈ guides x, pairEnergy p x y (Q x y) f

noncomputable def baseTotal (base : Finset I) (f : (I → Ω) → ℝ) : ℝ :=
  ∑ x ∈ base, baseEnergy p x f

noncomputable def scanEnergy (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (f : (I → Ω) → ℝ) : ℝ :=
  (pairTotal p guides Q f+baseTotal p base f)/(2*((∑ x, (guides x).card)+base.card : ℕ))

end

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

structure SymmetricProposal (Ω : Type*) [Fintype Ω] where
  q : Ω → Ω → ℝ
  nonneg : ∀ a b, 0 ≤ q a b
  row : ∀ a, ∑ b, q a b = 1
  symmetric : ∀ a b, q a b = q b a

noncomputable def offCapacity (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  min (π a) (π b)*P.q a b

noncomputable def metropolisCapacity (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  if a = b then π a - ∑ z ∈ Finset.univ.erase a, offCapacity P π a z
  else offCapacity P π a b

omit [DecidableEq Ω] in
lemma offCapacity_nonneg (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a b : Ω) : 0 ≤ offCapacity P π a b :=
  mul_nonneg (le_min (hπ a) (hπ b)) (P.nonneg a b)

omit [DecidableEq Ω] in
lemma offCapacity_le (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : offCapacity P π a b ≤ π a*P.q a b :=
  mul_le_mul_of_nonneg_right (min_le_left _ _) (P.nonneg a b)

omit [DecidableEq Ω] in
lemma offCapacity_symmetric (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : offCapacity P π a b = offCapacity P π b a := by
  simp only [offCapacity,min_comm (π a),P.symmetric]

lemma offCapacity_sum_le (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a : Ω) :
    (∑ z ∈ Finset.univ.erase a, offCapacity P π a z) ≤ π a := by
  calc
    _ ≤ ∑ z, offCapacity P π a z := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun z _ _ => offCapacity_nonneg P π hπ a z)
    _ ≤ ∑ z, π a*P.q a z := Finset.sum_le_sum (fun z _ => offCapacity_le P π a z)
    _ = π a := by rw [← Finset.mul_sum,P.row,mul_one]

lemma metropolisCapacity_nonneg (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a b : Ω) : 0 ≤ metropolisCapacity P π a b := by
  unfold metropolisCapacity
  split_ifs
  · exact sub_nonneg.mpr (offCapacity_sum_le P π hπ a)
  · exact offCapacity_nonneg P π hπ a b

noncomputable def metropolis (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  metropolisCapacity P π a b / π a

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def firstLift {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (a b : Ω × Ω) : ℝ := if a.2 = b.2 then q a.1 b.1 else 0

lemma firstLift_row {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (hq : ∀ a, ∑ b, q a b = 1) (a : Ω × Ω) : (∑ b, firstLift q a b) = 1 := by
  classical
  simp [Fintype.sum_prod_type,firstLift,hq]

lemma firstLift_symmetric {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (hq : ∀ a b, q a b = q b a) (a b : Ω × Ω) : firstLift q a b = firstLift q b a := by
  simp [firstLift,eq_comm,hq a.1 b.1]

end

open Finset MatchingFPRAS.Replica

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PushedFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {R A S : Type*} [Fintype R] [Fintype A] [Fintype S] [DecidableEq S]

noncomputable def pushedFlow (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ) (s t : S) : ℝ :=
  ∑ z : R × (A × A), if (F z.1 z.2.1,F z.1 z.2.2) = (s,t) then ρ z.1*q z.2.1 z.2.2 else 0

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def pairFlow (x y : I) (Q : PairCapacity p x y) : (I → Ω) → (I → Ω) → ℝ :=
  pushedFlow (density p) (replacePair x y) Q.q

noncomputable def baseFlow (i : I) : (I → Ω) → (I → Ω) → ℝ :=
  pushedFlow (density p) (fun s a => Function.update s i a) (fun a b => p i a*p i b)




noncomputable def updateCount (guides : I → Finset I) (base : Finset I) : ℕ :=
  (∑ x, (guides x).card)+base.card

noncomputable def scanFlow (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s t : I → Ω) : ℝ :=
  (if s=t then density p s else 0)/2+
    ((∑ x, ∑ y ∈ guides x, pairFlow p x y (Q x y) s t)+
      ∑ i ∈ base, baseFlow p i s t)/(2*(updateCount guides base:ℝ))

end

open Finset

end MatchingFPRAS.Replica

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def sqNorm (π f : Ω → ℝ) : ℝ := ∑ a, π a*(f a)^2

noncomputable def massMean (π f : Ω → ℝ) : ℝ := ∑ a, π a*f a

noncomputable def stepDensity (π : Ω → ℝ) (C : Ω → Ω → ℝ) (f : Ω → ℝ) (b : Ω) : ℝ :=
  (∑ a, C a b*f a)/π b

noncomputable def unlazyFlow (π : Ω → ℝ) (C : Ω → Ω → ℝ) (a b : Ω) : ℝ :=
  2*C a b-(if a=b then π a else 0)

end MatchingFPRAS.FiniteChain

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePairProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica.Ladder

open Finset

abbrev Slot (T q : ℕ) := Lex (Fin (T+1) × Fin q)

def rank {T q : ℕ} (x : Slot T q) : ℕ := (ofLex x).1.val

def tier {T q : ℕ} (x : Slot T q) : ℕ := T-rank x

def base (T q : ℕ) : Finset (Slot T q) := Finset.univ.image (fun j => toLex (⟨T,by omega⟩,j))

def guides {T q : ℕ} (x : Slot T q) : Finset (Slot T q) :=
  if h : rank x < T then Finset.univ.image (fun j => toLex (⟨rank x+1,by omega⟩,j)) else ∅

lemma base_card (T q : ℕ) : (base T q).card = q := by
  rw [base,Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg (fun x : Slot T q => (ofLex x).2) h

lemma base_nonempty (T q : ℕ) (hq : 0 < q) : (base T q).Nonempty := by
  rw [← Finset.card_pos,base_card]
  exact hq

end MatchingFPRAS.Replica.Ladder

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable def tierBase (V : Type*) [Fintype V] : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹

lemma tierBase_pos (V : Type*) [Fintype V] : 0 < tierBase V := by
  unfold tierBase; positivity

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Evolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def evolve (π : Ω → ℝ) (C : Ω → Ω → ℝ) : ℕ → (Ω → ℝ) → (Ω → ℝ)
  | 0, f => f
  | n+1, f => stepDensity π C (evolve π C n f)

noncomputable def deltaDensity (π : Ω → ℝ) (z a : Ω) : ℝ := if a=z then (π z)⁻¹ else 0

noncomputable def kernel (π : Ω → ℝ) (C : Ω → Ω → ℝ) (a b : Ω) : ℝ := C a b/π a

noncomputable def walk (π : Ω → ℝ) (C : Ω → Ω → ℝ) (z : Ω) : ℕ → Ω → ℝ
  | 0, a => if a=z then 1 else 0
  | n+1, b => ∑ a, walk π C z n a*kernel π C a b

end MatchingFPRAS.FiniteChain

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_LadderL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

def ladderL (N D : ℕ) : ℕ := (10^4*N*D)^100

def ladderQ (N D : ℕ) : ℕ := 32*ladderL N D

def ladderM (N D T : ℕ) : ℕ := T*(ladderQ N D)^2+ladderQ N D

def ladderLambda (N D K T : ℕ) : ℕ :=
  10*N*ladderQ N D*(T+1)*(K+Nat.clog 2 (N*D+2)+1)

noncomputable def ladderSteps (N D K T : ℕ) (ξ : ℝ) : ℕ :=
  20*ladderL N D*ladderM N D T*(ladderLambda N D K T+⌈Real.logb 2 ξ⁻¹⌉₊+1)

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

def probeHoles (p : ℕ) (hp : 1≤p) : Finset (Fin (4*p)) :=
  {⟨2*p-1,by omega⟩,⟨2*p,by omega⟩}


variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (p : ℕ) (hp : 1≤p) (e₀ : E)

def singleProbeHoles (e : E) : Finset (Fin (4*p)) :=
  if e=e₀ then probeHoles p hp else ∅


end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Tv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

noncomputable def tv (p q : Ω → ℝ) : ℝ := (∑ s,|p s-q s|)/2

noncomputable def event (p : Ω → ℝ) (P : Ω → Prop) : ℝ := ∑ x,if P x then p x else 0

noncomputable def bind (p : Ω → ℝ) (k : Ω → Ψ → ℝ) (y : Ψ) : ℝ := ∑ x,p x*k x y

noncomputable def push (p : Ω → ℝ) (f : Ω → Ψ) (y : Ψ) : ℝ :=
  ∑ x,if f x=y then p x else 0

omit [Fintype Ψ] in
lemma push_nonneg (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (f : Ω → Ψ) (y : Ψ) :
    0 ≤ push p f y := by
  unfold push; apply sum_nonneg; intro x _; split_ifs
  · exact hp x
  · exact le_rfl

lemma push_sum (p : Ω → ℝ) (hs : ∑ x,p x=1) (f : Ω → Ψ) : ∑ y,push p f y=1 := by
  unfold push; rw [sum_comm]; simpa using hs

noncomputable def tensor (p : Ω → ℝ) (q : Ψ → ℝ) (x : Ω×Ψ) : ℝ := p x.1*q x.2

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def product (p : I → Ω → ℝ) (x : I → Ω) : ℝ := ∏ i,p i (x i)

end Product


variable {B : Ω → Type*} [∀ a,Fintype (B a)]

noncomputable def sigmaLift (p : Ω → ℝ) (k : ∀ a,B a → ℝ) (s : Sigma B) : ℝ :=
  p s.1*k s.1 s.2


end MatchingFPRAS.Variation

namespace MatchingFPRAS.Transport

def tierBound (N D K : ℕ) : ℕ := N^2*(Nat.clog 2 D+2*K+2)

lemma base_block (N : ℕ) (hN : 0<N) : 2 ≤ (1+((N:ℝ)^2)⁻¹)^(N^2) := by
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have ha : -(2:ℝ)≤((N:ℝ)^2)⁻¹ := by
    have : (0:ℝ)≤((N:ℝ)^2)⁻¹ := by positivity
    linarith
  have h := one_add_mul_le_pow (a:=((N:ℝ)^2)⁻¹) ha (N^2)
  norm_cast at h
  have he : (N^2:ℝ)*((N:ℝ)^2)⁻¹=1 := mul_inv_cancel₀ (by positivity)
  norm_num only [Nat.cast_pow, he] at h
  linarith

lemma tierBound_reaches (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^(tierBound N D K) := by
  have hb := base_block N hN
  have hp : 0≤(1+((N:ℝ)^2)⁻¹)^(N^2) := by positivity
  have hD : (D:ℝ) ≤ 2^(Nat.clog 2 D) := by exact_mod_cast Nat.le_pow_clog (by decide : 1<2) D
  have hk : (3:ℝ)*4^K ≤ 2^(2*K+2) := by
    rw [pow_add,pow_mul]
    norm_num
    nlinarith [pow_pos (by norm_num : (0:ℝ)<4) K]
  have eD : Nat.clog 2 D ≤ Nat.clog 2 D+2*K+2 := by omega
  have eK : 2*K+2 ≤ Nat.clog 2 D+2*K+2 := by omega
  calc
    max (D:ℝ) (3*4^K) ≤ 2^(Nat.clog 2 D+2*K+2) := max_le
      (hD.trans (pow_le_pow_right₀ (by norm_num) eD))
      (hk.trans (pow_le_pow_right₀ (by norm_num) eK))
    _ ≤ _ := by
      unfold tierBound
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) hb _

noncomputable def ladderTier (N D K : ℕ) (hN : 0<N) : ℕ :=
  Nat.find (⟨tierBound N D K,tierBound_reaches N D K hN⟩ :
    ∃ t : ℕ,max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^t)

lemma ladderTier_spec (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^(ladderTier N D K hN) := by
  exact Nat.find_spec (p:=fun t : ℕ => max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^t)
    ⟨tierBound N D K,tierBound_reaches N D K hN⟩

lemma ladderTier_le (N D K : ℕ) (hN : 0<N) : ladderTier N D K hN ≤ tierBound N D K :=
  Nat.find_min' _ (tierBound_reaches N D K hN)

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

def topSlot (T q : ℕ) (hq : 0<q) : Slot T q := toLex (0,⟨0,hq⟩)

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

structure Pairing (α : Type*) where
  mate : α → α
  involutive : Function.Involutive mate
  no_fixed : ∀ x, mate x ≠ x

instance instFinitePairing {α : Type*} [Finite α] : Finite (Pairing α) := by
  apply Finite.of_injective Pairing.mate
  intro p q h
  cases p; cases q
  simp only [Pairing.mk.injEq] at *
  exact h

noncomputable instance instFintypePairing {α : Type*} [Fintype α] : Fintype (Pairing α) := Fintype.ofFinite _

@[ext] lemma Pairing.ext {α : Type*} {p q : Pairing α} (h : ∀ x, p.mate x=q.mate x) : p=q := by
  cases p; cases q
  simp only [Pairing.mk.injEq]
  exact funext h

variable {α β : Type*}

def Pairing.map (e : α ≃ β) (p : Pairing α) : Pairing β where
  mate y := e (p.mate (e.symm y))
  involutive y := by simp [p.involutive (e.symm y)]
  no_fixed y := by
    intro h
    apply p.no_fixed (e.symm y)
    have := congrArg e.symm h
    simpa using this

lemma Pairing.subtype_hext {P Q : α → Prop} (p : Pairing {x // P x}) (q : Pairing {x // Q x})
    (hPQ : ∀ x, P x ↔ Q x)
    (h : ∀ (x : {x // P x}) (y : {x // Q x}), x.val=y.val →
      (p.mate x).val=(q.mate y).val) : HEq p q := by
  have he : P=Q := funext fun x => propext (hPQ x)
  subst Q
  apply heq_of_eq
  ext x
  exact h x x rfl

variable [DecidableEq α]

def Pairing.remove (p : Pairing α) (a : α) : Pairing {x : α // x≠a ∧ x≠p.mate a} where
  mate x := ⟨p.mate x,by
    constructor
    · intro h
      have := congrArg p.mate h
      exact x.property.2 (by rw [p.involutive] at this; exact this)
    · intro h
      exact x.property.1 (p.involutive.injective h)⟩
  involutive x := Subtype.ext (p.involutive x)
  no_fixed x h := p.no_fixed x (congrArg Subtype.val h)

def pairingCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => (n+1)*pairingCount n

@[simp] lemma pairingCount_zero : pairingCount 0=1 := rfl

@[simp] lemma pairingCount_one : pairingCount 1=0 := rfl

@[simp] lemma pairingCount_add_two (n : ℕ) : pairingCount (n+2)=(n+1)*pairingCount n := rfl

lemma pairingCount_pos_recurrence {n : ℕ} (hn : 0<n) :
    pairingCount n = (n-1)*pairingCount (n-2) := by
  match n with
  | 0 => omega
  | 1 => rfl
  | n+2 => simp only [pairingCount_add_two,Nat.add_sub_cancel,show n+2-1=n+1 by omega]

lemma card_except_two [Fintype α] (a b : α) (hab : b≠a) :
    Fintype.card {x : α // x≠a ∧ x≠b}=Fintype.card α-2 := by
  classical
  calc
    _ = Fintype.card {x : α // ¬ (x=a ∨ x=b)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => not_or.symm)
    _ = Fintype.card α-Fintype.card {x : α // x=a ∨ x=b} := Fintype.card_subtype_compl _
    _ = _ := by rw [Fintype.card_subtype_eq_or_eq_of_ne hab.symm]

universe u

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Initializer

open Finset MatchingFPRAS.Switching MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma pairingCount_pos_of_even (n : ℕ) (h : Even n) : 0 < pairingCount n := by
  obtain ⟨k,rfl⟩ := h
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k+1+(k+1)=(k+k)+2 by omega,pairingCount_add_two]
    exact Nat.mul_pos (by omega) ih

def initialScale (n : ℕ) : ℚ := 1/(Nat.sqrt (n-1):ℚ)

lemma sqrt_square_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n-1:ℝ)/4 ≤ (Nat.sqrt (n-1):ℝ)^2 ∧ (Nat.sqrt (n-1):ℝ)^2 ≤ n-1 := by
  have hpos : 1 ≤ Nat.sqrt (n-1) := Nat.le_sqrt.mpr (by omega)
  have hlow := Nat.lt_succ_sqrt' (n-1)
  have hup := Nat.sqrt_le' (n-1)
  have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  have hlow' : (n:ℝ)-1 < ((Nat.sqrt (n-1):ℝ)+1)^2 := by
    rw [←hncast]
    exact_mod_cast hlow
  have hup' : (Nat.sqrt (n-1):ℝ)^2 ≤ (n:ℝ)-1 := by
    rw [←hncast]
    exact_mod_cast hup
  have hs : (1:ℝ) ≤ Nat.sqrt (n-1) := by exact_mod_cast hpos
  constructor
  · nlinarith [sq_nonneg ((Nat.sqrt (n-1):ℝ)-1)]
  · exact hup'

lemma initialScale_pos (n : ℕ) (hn : 2 ≤ n) : 0 < initialScale n := by
  unfold initialScale
  have hs : 0 < Nat.sqrt (n-1) := by have := Nat.le_sqrt.mpr (by omega : 1*1≤n-1); omega
  positivity

end MatchingFPRAS.Initializer

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Cumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

def cumulative {r : ℕ} (p : Fin r → ℚ) (i : ℕ) : ℚ := ∑ j, if j.val < i then p j else 0

lemma cumulative_zero {r : ℕ} (p : Fin r → ℚ) : cumulative p 0 = 0 := by simp [cumulative]

lemma cumulative_total {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : cumulative p r = 1 := by
  simp only [cumulative,Fin.isLt,ite_true]; exact hs

lemma options_pos {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : 0 < r := by
  by_contra h
  have hr : r=0 := by omega
  subst r
  simp at hs

def candidates {r K : ℕ} (p : Fin r → ℚ) (J : Fin K) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (J.val:ℚ)/K < cumulative p (i.val+1))

lemma candidates_nonempty {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) : (candidates p J).Nonempty := by
  have hr := options_pos p hs
  refine ⟨⟨r-1,by omega⟩,?_⟩
  simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]
  have he : r-1+1=r := by omega
  rw [he,cumulative_total p hs]
  apply (div_lt_one (by exact_mod_cast hK : (0:ℚ)<K)).mpr
  exact_mod_cast J.isLt

def choose {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (J : Fin K) : Fin r :=
  (candidates p J).min' (candidates_nonempty p hs hK J)

def outputLaw {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) : ℚ :=
  ((Finset.univ.filter (fun J : Fin K => choose p hs hK J=i)).card:ℚ)/K




def gridInterval (K : ℕ) (a b : ℚ) : Finset ℕ :=
  (Finset.range K).filter (fun j => a ≤ (j:ℚ)/K ∧ (j:ℚ)/K < b)

lemma cumulative_step {r : ℕ} (p : Fin r → ℚ) (i : Fin r) :
    cumulative p (i.val+1)-cumulative p i.val = p i := by
  unfold cumulative
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin r) : (if j.val < i.val+1 then p j else 0)-(if j.val < i.val then p j else 0) =
      if j=i then p j else 0 := by
    by_cases h : j=i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun hval => h (Fin.ext hval)
      by_cases hj : j.val < i.val
      · simp [h,hj,show j.val < i.val+1 by omega]
      · simp [h,hj,show ¬j.val < i.val+1 by omega]
  simp_rw [he]
  simp

lemma choose_upper {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) :
    (J.val:ℚ)/K < cumulative p ((choose p hs hK J).val+1) := by
  have hm := Finset.min'_mem (candidates p J) (candidates_nonempty p hs hK J)
  exact (Finset.mem_filter.mp hm).2

lemma choose_le {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) (i : Fin r)
    (hi : (J.val:ℚ)/K < cumulative p (i.val+1)) : choose p hs hK J ≤ i := by
  exact Finset.min'_le (candidates p J) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

lemma choose_lower {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) :
    cumulative p (choose p hs hK J).val ≤ (J.val:ℚ)/K := by
  let i := choose p hs hK J
  by_cases hi : i.val=0
  · rw [show (choose p hs hK J).val=0 from hi,cumulative_zero]
    positivity
  · by_contra hh
    have hx : (J.val:ℚ)/K < cumulative p i.val := lt_of_not_ge hh
    let j : Fin r := ⟨i.val-1,by have := i.isLt; omega⟩
    have he : j.val+1=i.val := by dsimp [j]; omega
    have hj : (J.val:ℚ)/K < cumulative p (j.val+1) := by rw [he]; exact hx
    have hm := choose_le p hs hK J j hj
    have hv : i.val ≤ j.val := hm
    dsimp [j] at hv
    omega

end MatchingFPRAS.FiniteChoice

namespace MatchingFPRAS.FiniteChoice

open Finset

def tapeIndex (k : ℕ) : (Fin k → Bool) ≃ Fin (2^k) :=
  (Equiv.piCongrRight (fun _ : Fin k => finTwoEquiv.symm)).trans finFunctionFinEquiv

def chooseBits {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ)
    (bits : Fin k → Bool) : Fin r :=
  choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) (tapeIndex k bits)

def tapeLaw {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ) (i : Fin r) : ℚ :=
  ((univ.filter (fun bits : Fin k → Bool => chooseBits p hs k bits=i)).card:ℚ)/(2:ℚ)^k

end MatchingFPRAS.FiniteChoice

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

def colorRaw (A : Finset E) : Finset (Finset E) :=
  A.biUnion fun e => (univ.filter (fun f => ends f = ends e)).image
    (fun f => insert f (A.erase e))

omit [Fintype V] in
@[simp] lemma mem_colorRaw [Fintype V] (A B : Finset E) :
    B ∈ colorRaw ends A ↔ ∃ e ∈ A, ∃ f, ends f = ends e ∧ B = insert f (A.erase e) := by
  simp only [colorRaw,mem_biUnion,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,he,f,hf,h⟩
    exact ⟨e,he,f,hf,h.symm⟩
  · rintro ⟨e,he,f,hf,h⟩
    exact ⟨e,he,f,hf,h.symm⟩

def switchPatterns (A : Finset E) : Finset ((Fin 4 → V) × (Fin 4 → E)) :=
  univ.filter fun p => Function.Injective p.1 ∧
    (∀ i x, x ∈ ends (p.2 i) ↔ x = p.1 i ∨ x = p.1 (i+1)) ∧
    p.2 0 ≠ p.2 2 ∧ {p.2 0,p.2 2} ⊆ A

def switchRaw (A : Finset E) : Finset (Finset E) :=
  (switchPatterns ends A).image fun p => (A \ {p.2 0,p.2 2}) ∪ {p.2 1,p.2 3}

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

instance decideOverlay (U : Finset E) :
    DecidableRel (overlayLineGraph (fun e v => v ∈ ends e) U).Adj := by
  intro e f
  change Decidable (e ≠ f ∧ e ∈ U ∧ f ∈ U ∧ ∃ v, v ∈ ends e ∧ v ∈ ends f)
  infer_instance

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS

structure WeightedOptions (Ω : Type*) where
  size : ℕ
  out : Fin size → Ω
  mass : Fin size → ℚ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

namespace WeightedOptions

open Finset

variable {Ω Ψ : Type*}

def pure (a : Ω) : WeightedOptions Ω where
  size := 1
  out := fun _ => a
  mass := fun _ => 1
  nonneg := by simp
  total := by simp

def map (f : Ω → Ψ) (c : WeightedOptions Ω) : WeightedOptions Ψ where
  size := c.size
  out := f ∘ c.out
  mass := c.mass
  nonneg := c.nonneg
  total := c.total

def mix (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : WeightedOptions Ω) : WeightedOptions Ω where
  size := a.size+b.size
  out := Fin.addCases a.out b.out
  mass := Fin.addCases (fun i => p*a.mass i) (fun i => (1-p)*b.mass i)
  nonneg i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
      exact mul_nonneg hp (a.nonneg i)
    · simp only [Fin.addCases_right]
      exact mul_nonneg (sub_nonneg.mpr hp1) (b.nonneg i)
  total := by
    simp only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,←mul_sum,a.total,b.total]
    ring

variable [DecidableEq Ω]

def law (c : WeightedOptions Ω) (b : Ω) : ℚ := ∑ i, if c.out i=b then c.mass i else 0

@[simp] lemma pure_law (a b : Ω) : (pure a).law b=if a=b then 1 else 0  := by
  change (∑ _i : Fin 1, if a=b then (1:ℚ) else 0)=_
  simp

def accept (c : WeightedOptions Ω) (hold : Ω) (p : Ω → ℚ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) : WeightedOptions Ω where
  size := c.size+c.size
  out := Fin.addCases c.out (fun _ => hold)
  mass := Fin.addCases (fun i => c.mass i*p (c.out i))
    (fun i => c.mass i*(1-p (c.out i)))
  nonneg i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
      exact mul_nonneg (c.nonneg i) (hp _)
    · simp only [Fin.addCases_right]
      exact mul_nonneg (c.nonneg i) (sub_nonneg.mpr (hp1 _))
  total := by
    simp only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,←sum_add_distrib]
    simp only [←mul_add,add_sub_cancel,mul_one,c.total]

variable [LinearOrder Ω]

def numbering (s : Finset Ω) : Fin s.card ≃ ↥s := (s.orderIsoOfFin rfl).toEquiv

def uniform (s : Finset Ω) (hs : s.Nonempty) : WeightedOptions Ω where
  size := s.card
  out := fun i => (numbering s i).val
  mass := fun _ => (s.card:ℚ)⁻¹
  nonneg := by intro i; positivity
  total := by
    have h : (s.card:ℚ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    simp [h]

def neighbors (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card ≤ d) : WeightedOptions Ω where
  size := s.card+1
  out := Fin.lastCases a (fun i => (numbering s i).val)
  mass := Fin.lastCases (1-(s.card:ℚ)/d) (fun _ => (d:ℚ)⁻¹)
  nonneg i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      by_cases h : d=0
      · simp [h]
      · have hh : (0:ℚ)<d := by exact_mod_cast Nat.pos_of_ne_zero h
        exact sub_nonneg.mpr ((div_le_one hh).mpr (by exact_mod_cast hd))
    · simp only [Fin.lastCases_castSucc]
      positivity
  total := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,sum_const,card_fin,nsmul_eq_mul]
    ring

end WeightedOptions

end MatchingFPRAS

namespace MatchingFPRAS.Transport.Sparse

open Finset WeightedOptions

variable {Ω : Type*} [Fintype Ω] [LinearOrder Ω] [DecidableEq Ω]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

local instance finsetOrder : LinearOrder (Finset E) :=
  LinearOrder.lift' toColex toColex.injective

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MetropolisChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WeightedOptions

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def metropolisChoice (c : WeightedOptions Ω) (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a : Ω) :
    WeightedOptions Ω := c.accept a (fun b => min 1 (w b / w a))
      (fun b => le_min zero_le_one (div_nonneg (hw b).le (hw a).le))
      (fun _ => min_le_left _ _)

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

noncomputable def uniform (A : Type*) [Fintype A] (_ : A) : ℝ := 1/Fintype.card A

lemma uniform_nonneg (a : A) : 0≤uniform A a := by unfold uniform; positivity

lemma uniform_sum [Nonempty A] : ∑ a : A,uniform A a=1 := by
  simp only [uniform,sum_const,nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card A:ℝ)≠0)

noncomputable def imageLaw (f : A → B) : B → ℝ := push (uniform A) f

omit [Fintype B] in
lemma imageLaw_nonneg (f : A → B) (b : B) : 0 ≤ imageLaw f b := push_nonneg _ uniform_nonneg _ _

lemma imageLaw_sum [Nonempty A] (f : A → B) : ∑ b,imageLaw f b=1 := push_sum _ uniform_sum _

open Finset
open scoped Classical

open scoped Classical

end MatchingFPRAS.Variation

namespace MatchingFPRAS.WeightedOptions

open Finset Variation FiniteChoice

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def draw (c : WeightedOptions Ω) (k : ℕ) (bits : Fin k → Bool) : Ω :=
  c.out (chooseBits c.mass c.total k bits)

end MatchingFPRAS.WeightedOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_PairStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def pairStep (x y : I) (Q : PairCapacity p x y) (s t : I → Ω) : ℝ :=
  ∑ b : Ω×Ω, if replacePair x y s b=t then Q.q (s x,s y) b/(p x (s x)*p y (s y)) else 0

noncomputable def baseStep (i : I) (s t : I → Ω) : ℝ :=
  ∑ a : Ω, if Function.update s i a=t then p i a else 0

noncomputable def localScan (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) : ℝ :=
  (if s=t then (1:ℝ) else 0)/2+
    ((∑ x,∑ y ∈ guides x,pairStep p x y (Q x y) s t)+∑ i ∈ base,baseStep p i s t)/
      (2*(updateCount guides base:ℝ))

end MatchingFPRAS.Replica

namespace MatchingFPRAS.WeightedOptions

open Finset Variation

variable {J Ω B : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

def drawThen (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ)
    (bits : (Fin k → Bool) × B) : Ω := g (c.draw k bits.1) bits.2

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

abbrev Update (I : Type*) := (I×I) ⊕ I

def updates (guides : I → Finset I) (base : Finset I) : Finset (Update I) :=
  ((univ : Finset (I×I)).filter (fun ij=>ij.2∈guides ij.1)).disjSum base

lemma updates_nonempty (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    (updates guides base).Nonempty := by
  obtain ⟨i,hi⟩:=hb
  exact ⟨Sum.inr i,by simp [updates,hi]⟩

variable (p : I → Ω → ℝ)

noncomputable def updateKernel (Q : ∀ x y,PairCapacity p x y) (s : I → Ω) :
    Option (Update I) → (I → Ω) → ℝ
  | none,t => if s=t then 1 else 0
  | some (.inl ij),t => pairStep p ij.1 ij.2 (Q ij.1 ij.2) s t
  | some (.inr i),t => baseStep p i s t

variable [LinearOrder (Update I)]

def scanChoice (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    WeightedOptions (Option (Update I)) :=
  WeightedOptions.mix (1/2) (by norm_num) (by norm_num) (WeightedOptions.pure none)
    ((WeightedOptions.uniform (updates guides base) (updates_nonempty guides base hb)).map some)



open Finset Variation

variable {I Ω B : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

def localSampler (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω)
    (s : I → Ω) : Option (Update I) → B → (I → Ω)
  | none,_ => s
  | some (.inl ij),b => replacePair ij.1 ij.2 s (pair ij.1 ij.2 (s ij.1,s ij.2) b)
  | some (.inr i),b => Function.update s i (refresh i b)

variable [LinearOrder (Update I)]

def sampleScan (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (k : ℕ) (s : I → Ω) :
    ((Fin k → Bool) × B) → (I → Ω) :=
  (scanChoice guides base hb).drawThen (localSampler pair refresh s) k

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Variation

open Finset

variable {Ω B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype B] [Nonempty B]

def runSample (g : Ω → B → Ω) (z : Ω) : (n : ℕ) → (Fin n → B) → Ω
  | 0,_ => z
  | n+1,bits => g (runSample g z n (Fin.init bits)) (bits (Fin.last n))

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Admissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω B : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B] [LinearOrder (Update I)]

def admissible (guides : I → Finset I) (base : Finset I) : Option (Update I) → Prop
  | none => True
  | some (.inl ij) => ij.2∈guides ij.1
  | some (.inr i) => i∈base



open Finset

end MatchingFPRAS.Replica

namespace MatchingFPRAS.FiniteChoice

lemma choose_pos {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ i,p i=1)
    (hK : 0<K) (J : Fin K) : 0<p (choose p hs hK J) := by
  have hl := choose_lower p hs hK J
  have hu := choose_upper p hs hK J
  have hd := cumulative_step p (choose p hs hK J)
  linarith

lemma chooseBits_pos {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i,p i=1)
    (k : ℕ) (bits : Fin k → Bool) : 0<p (chooseBits p hs k bits) :=
  choose_pos p hs _ _

end MatchingFPRAS.FiniteChoice

namespace MatchingFPRAS.UnitRefresh

variable {α β : Type*}

variable [DecidableEq α]

universe u



open Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]



open Finset Polynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

abbrev Assignment (bags : V → Finset L) := {f : V → L // ∀ x, f x ∈ bags x}

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Edge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}



open Finset

variable {U S W L : Type*} [Fintype U] [Fintype S] [Fintype W] [Fintype L]
  [DecidableEq U] [DecidableEq S] [DecidableEq W] [DecidableEq L]

def leafBags (l p : L) (b : W → Finset L) : U ⊕ S ⊕ W → Finset L
  | Sum.inl _ => {l}
  | Sum.inr (Sum.inl _) => {l,p}
  | Sum.inr (Sum.inr x) => b x

noncomputable def fiberCount {V : Type*} [Fintype V] (f : V → L) (l : L) : ℕ :=
  Fintype.card {x : V // f x=l}

noncomputable def assignmentPartition {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → Finset L) (w : L → ℕ → ℕ) : ℕ :=
  by classical exact ∑ f : Assignment b, ∏ l,w l (fiberCount f.val l)

def leafAssignment (l p : L) (b : W → Finset L) (T : Finset S) (f : Assignment b) :
    Assignment (leafBags (U := U) (S := S) l p b) :=
  ⟨Sum.elim (fun _ => l) (Sum.elim (fun x => if x∈T then l else p) f.val),by
    intro x
    rcases x with x | (x | x)
    · simp [leafBags]
    · by_cases hx : x∈T <;> simp [leafBags,hx]
    · exact f.property x⟩

noncomputable def leafAssignmentEquiv (l p : L) (hlp : l≠p) (b : W → Finset L) :
    Assignment (leafBags (U := U) (S := S) l p b) ≃ (Finset S) × Assignment b where
  toFun f := (univ.filter fun x => f.val (Sum.inr (Sum.inl x))=l,
    ⟨fun x => f.val (Sum.inr (Sum.inr x)),fun x => f.property _⟩)
  invFun q := leafAssignment l p b q.1 q.2
  left_inv f := by
    apply Subtype.ext
    funext x
    rcases x with x | (x | x)
    · have hf := f.property (Sum.inl x)
      have hfl : f.val (Sum.inl x)=l := by simpa [leafBags] using hf
      simpa [leafAssignment] using hfl.symm
    · by_cases h : f.val (Sum.inr (Sum.inl x))=l
      · simp [leafAssignment,h]
      · have hf := f.property (Sum.inr (Sum.inl x))
        simp only [leafBags,mem_insert,mem_singleton] at hf
        simp [leafAssignment,hf.resolve_left h,hlp.symm]
    · rfl
  right_inv q := by
    apply Prod.ext
    · ext x
      by_cases hx : x∈q.1 <;> simp [leafAssignment,hx,hlp.symm]
    · rfl

omit [Fintype L] in
lemma fiberCount_sum [Fintype L] {A B : Type*} [Fintype A] [Fintype B] (f : A ⊕ B → L) (l : L) :
    fiberCount f l = fiberCount (fun x : A => f (Sum.inl x)) l +
      fiberCount (fun x : B => f (Sum.inr x)) l := by
  unfold fiberCount
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]

omit [Fintype L] [DecidableEq U] in
lemma fiberCount_const [Fintype L] [DecidableEq U]
    (a l : L) : fiberCount (fun _ : U => a) l = if a=l then Fintype.card U else 0 := by
  classical
  by_cases h : a=l <;> simp [fiberCount,h]

omit [Fintype L] in
lemma fiberCount_zero [Fintype L] {A : Type*} [Fintype A] (f : A → L) (l : L) (h : ∀ x,f x≠l) :
    fiberCount f l=0 := by
  classical
  simp [fiberCount,h]

lemma prod_split_two (l p : L) (hlp : l≠p) (f : L → ℕ) :
    (∏ a,f a)=f l*f p*(∏ a∈(univ.erase l).erase p,f a) := by
  rw [←prod_erase_mul univ f (mem_univ l),
    ←prod_erase_mul (univ.erase l) f (mem_erase.mpr ⟨hlp.symm,mem_univ p⟩)]
  ac_rfl

omit [DecidableEq S] in
lemma sum_finset_card [DecidableEq S] (g : ℕ → ℕ) :
    (∑ T : Finset S,g T.card)=∑ k∈range (Fintype.card S+1),(Fintype.card S).choose k*g k := by
  classical
  have hu : (univ : Finset (Finset S))=(univ : Finset S).powerset := by ext T; simp
  rw [hu,sum_powerset]
  apply sum_congr rfl
  intro k hk
  simpa using (sum_powersetCard k (univ : Finset S) g)

noncomputable def leafUpdate (u s : ℕ) (l p : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if a=l then 1 else if a=p then
    ∑ k∈range (s+1),s.choose k*w l (u+k)*w p (s-k+r) else w a r

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

noncomputable def assignmentEquiv (b : V → Finset L) (c : W → Finset L)
    (e : V ≃ W) (he : ∀ x,c (e x)=b x) : Assignment b ≃ Assignment c where
  toFun f := ⟨fun y => f.val (e.symm y),fun y => by
    have hy : c y=b (e.symm y) := by simpa using he (e.symm y)
    rw [hy]; exact f.property (e.symm y)⟩
  invFun f := ⟨fun x => f.val (e x),fun x => by rw [←he]; exact f.property _⟩
  left_inv f := Subtype.ext (by funext x; simp)
  right_inv f := Subtype.ext (by funext x; simp)

omit [Fintype L] [DecidableEq V] [DecidableEq W] in
lemma fiberCount_equiv [Fintype L] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (f : V → L) (g : W → L)
    (h : ∀ x,g (e x)=f x) (l : L) : fiberCount f l=fiberCount g l := by
  unfold fiberCount
  exact Fintype.card_congr (e.subtypeEquiv (fun x => by rw [h]))

lemma assignmentPartition_equiv (b : V → Finset L) (c : W → Finset L)
    (e : V ≃ W) (he : ∀ x,c (e x)=b x) (w : L → ℕ → ℕ) :
    assignmentPartition b w = assignmentPartition c w := by
  classical
  unfold assignmentPartition
  apply Fintype.sum_equiv (assignmentEquiv b c e he)
  intro f
  apply prod_congr rfl
  intro l hl
  congr 1
  apply fiberCount_equiv e
  intro x
  simp [assignmentEquiv]

abbrev Private (b : V → Finset L) (l : L) := {x : V // b x={l}}

abbrev Shared (b : V → Finset L) (l : L) := {x : V // l∈b x ∧ b x≠{l}}

abbrev Outside (b : V → Finset L) (l : L) := {x : V // l∉b x}

noncomputable def splitLeaf (b : V → Finset L) (l : L) :
    V ≃ Private b l ⊕ Shared b l ⊕ Outside b l where
  toFun x := if h : b x={l} then .inl ⟨x,h⟩ else
    if h' : l∈b x then .inr (.inl ⟨x,h',h⟩) else .inr (.inr ⟨x,h'⟩)
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  left_inv x := by dsimp only; split_ifs <;> rfl
  right_inv x := by
    rcases x with x | (x | x)
    · simp [x.property]
    · simp [x.property.1,x.property.2]
    · have hx : b x.val≠{l} := by intro h; exact x.property (by simp [h])
      simp [hx,x.property]

def LeafAt (b : V → Finset L) (l p : L) : Prop :=
  ∀ x,l∈b x → b x={l} ∨ b x={l,p}

omit [Fintype V] [Fintype L] [DecidableEq V] in
lemma splitLeaf_bags [Fintype V] [Fintype L] [DecidableEq V]
    (b : V → Finset L) (l p : L) (h : LeafAt b l p) (x : V) :
    leafBags l p (fun y : Outside b l => b y.val) (splitLeaf b l x)=b x := by
  classical
  unfold splitLeaf
  simp only [Equiv.coe_fn_mk]
  split_ifs with he hm
  · exact he.symm
  · exact ((h x hm).resolve_left he).symm
  · rfl

def rootBags {U : Type*} (l : L) (b : W → Finset L) : U ⊕ W → Finset L :=
  Sum.elim (fun _ => {l}) b

noncomputable def rootAssignmentEquiv {U : Type*} [Fintype U] [DecidableEq U]
    (l : L) (b : W → Finset L) : Assignment (rootBags (U:=U) l b) ≃ Assignment b where
  toFun f := ⟨fun x => f.val (.inr x),fun x => f.property _⟩
  invFun f := ⟨Sum.elim (fun _ => l) f.val,by
    intro x; rcases x with x | x
    · simp [rootBags]
    · exact f.property x⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rcases x with x | x
    · have h := f.property (.inl x)
      have hx : f.val (.inl x)=l := by simpa [rootBags] using h
      exact hx.symm
    · rfl
  right_inv f := rfl

noncomputable def rootUpdate (u : ℕ) (l : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if a=l then w l u else w a r

noncomputable def splitRoot (b : V → Finset L) (l : L) :
    V ≃ {x : V // l∈b x} ⊕ Outside b l where
  toFun x := if h : l∈b x then .inl ⟨x,h⟩ else .inr ⟨x,h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv x := by dsimp only; split_ifs <;> rfl
  right_inv x := by rcases x with x | x <;> simp [x.property]

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

noncomputable def activePartition (b : V → Finset L) (R : Finset V) (w : L → ℕ → ℕ) : ℕ :=
  assignmentPartition (fun x : R => b x.val) w

def trim (b : V → Finset L) (R : Finset V) (l : L) : Finset V := R.filter fun x => l∉b x

def privateCount (b : V → Finset L) (R : Finset V) (l : L) : ℕ :=
  (R.filter fun x => b x={l}).card

def sharedCount (b : V → Finset L) (R : Finset V) (l : L) : ℕ :=
  (R.filter fun x => l∈b x ∧ b x≠{l}).card

noncomputable def activeFilterEquiv (R : Finset V) (P : V → Prop) [DecidablePred P] :
    {x : R // P x.val} ≃ (R.filter P) where
  toFun x := ⟨x.val.val,mem_filter.mpr ⟨x.val.property,x.property⟩⟩
  invFun x := ⟨⟨x.val,(mem_filter.mp x.property).1⟩,(mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] in
lemma active_card_filter [Fintype V] [DecidableEq V]
    (R : Finset V) (P : V → Prop) [DecidablePred P] :
    Fintype.card {x : R // P x.val}=(R.filter P).card := by
  rw [Fintype.card_congr (activeFilterEquiv R P),Fintype.card_coe]

omit [Fintype V] in
lemma active_outside [Fintype V]
    (b : V → Finset L) (R : Finset V) (l : L) (w : L → ℕ → ℕ) :
    assignmentPartition (fun x : Outside (fun y : R => b y.val) l => b x.val.val) w =
      activePartition b (trim b R l) w := by
  change assignmentPartition (fun x : {y : R // l∉b y.val} => b x.val.val) w =
    assignmentPartition (fun x : R.filter (fun y => l∉b y) => b x.val) w
  apply assignmentPartition_equiv _ _ (activeFilterEquiv R (fun x => l∉b x))
  intro x
  rfl

lemma partition_isEmpty {W : Type*} [Fintype W] [DecidableEq W] [IsEmpty W]
    (b : W → Finset L) (w : L → ℕ → ℕ) : assignmentPartition b w=∏ l,w l 0 := by
  classical
  let : Unique (Assignment b) :=
    { default := ⟨isEmptyElim,fun x => isEmptyElim x⟩
      uniq := fun f => Subtype.ext (by funext x; exact isEmptyElim x) }
  simp [assignmentPartition,fiberCount]

omit [Fintype V] in
lemma active_empty [Fintype V] (b : V → Finset L) (w : L → ℕ → ℕ) :
    activePartition b ∅ w=∏ l,w l 0 := partition_isEmpty _ _

def RankedBags (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L) : Prop :=
  ∀ x a,a ∈ b x → ∀ a'∈b x,a≠a' →
    (rank a < rank a' ∧ parent a'=some a) ∨ (rank a' < rank a ∧ parent a=some a')

noncomputable def advanceTable (b : V → Finset L) (R : Finset V) (parent : L → Option L)
    (l : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  match parent l with
  | some p => leafUpdate (privateCount b R l) (sharedCount b R l) l p w
  | none => rootUpdate ((R.filter fun x => l∈b x).card) l w

noncomputable def tableDP (b : V → Finset L) (parent : L → Option L) :
    List L → Finset V → (L → ℕ → ℕ) → (L → ℕ → ℕ)
  | [],_,w => w
  | l::ls,R,w => tableDP b parent ls (trim b R l) (advanceTable b R parent l w)

def LegalPlan (b : V → Finset L) (parent : L → Option L) : List L → Finset V → Prop
  | [],R => R=∅
  | l::ls,R =>
    (match parent l with
      | some p => l≠p ∧ LeafAt (fun x : R => b x.val) l p
      | none => ∀ x : R,l∈b x.val → b x.val={l}) ∧
    LegalPlan b parent ls (trim b R l)

omit [Fintype V] [Fintype L] [DecidableEq V] in
theorem rank_order_legal [Fintype V] [Fintype L] [DecidableEq V]
    (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags b rank parent)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (ls : List L) (hs : ls.Pairwise (fun a a' => rank a' ≤ rank a))
    (R : Finset V) (hne : ∀ x∈R,(b x).Nonempty)
    (hc : ∀ x∈R,∀ a∈b x,a∈ls) : LegalPlan b parent ls R := by
  induction ls generalizing R with
  | nil =>
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨a,ha⟩ := hne x hx
    exact List.not_mem_nil (hc x hx a ha)
  | cons l ls ih =>
    have hs' := List.pairwise_cons.mp hs
    have hmax (x : R) (a : L) (ha : a∈b x.val) : rank a ≤ rank l := by
      have h := hc x.val x.property a ha
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ le_rfl
      · exact hs'.1 a h
    have hparent (x : R) (hl : l∈b x.val) (a : L) (ha : a∈b x.val) (hal : a≠l) :
        parent l=some a := by
      rcases hb x.val l hl a ha (Ne.symm hal) with h | h
      · exact (Nat.not_lt_of_ge (hmax x a ha) h.1).elim
      · exact h.2
    constructor
    · cases hpar : parent l with
      | none =>
        intro x hl
        apply eq_singleton_iff_unique_mem.mpr
        exact ⟨hl,fun a ha => by
          by_contra hal
          have h := hparent x hl a ha hal
          rw [hpar] at h
          cases h⟩
      | some p =>
        constructor
        · intro h; subst p
          exact Nat.lt_irrefl _ (hp l l hpar)
        · intro x hl
          by_cases h : b x.val={l}
          · exact Or.inl h
          · right
            apply Subset.antisymm
            · intro a ha
              by_cases hal : a=l
              · simp [hal]
              · have hpa : p=a := Option.some.inj (hpar.symm.trans (hparent x hl a ha hal))
                simp [hpa]
            · intro a ha
              simp only [mem_insert,mem_singleton] at ha
              rcases ha with ha | ha
              · simpa [ha] using hl
              · rw [ha]
                by_contra hpn
                apply h
                apply eq_singleton_iff_unique_mem.mpr
                refine ⟨hl,fun a ha => ?_⟩
                by_contra hal
                have hpa : p=a := Option.some.inj (hpar.symm.trans (hparent x hl a ha hal))
                exact hpn (hpa ▸ ha)
    · apply ih hs'.2
      · intro x hx
        exact hne x (mem_filter.mp hx).1
      · intro x hx a ha
        have hx' := mem_filter.mp hx
        have h := hc x hx'.1 a ha
        rcases List.mem_cons.mp h with hh | hh
        · exact (hx'.2 (hh ▸ ha)).elim
        · exact hh

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

lemma active_univ (b : V → Finset L) (w : L → ℕ → ℕ) :
    activePartition b univ w=assignmentPartition b w := by
  change assignmentPartition (fun x : (univ : Finset V) => b x.val) w=assignmentPartition b w
  let e : (univ : Finset V) ≃ V :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,mem_univ x⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  apply assignmentPartition_equiv _ _ e
  intro x; rfl

omit [Fintype L] [DecidableEq V] in
lemma shared_le_card [Fintype L] [DecidableEq V] (b : V → Finset L) (R : Finset V) (l : L) :
    sharedCount b R l≤Fintype.card V := by
  exact (card_filter_le _ _).trans (card_le_univ R)

omit [Fintype L] in
lemma private_add_shared [Fintype L] (b : V → Finset L) (R : Finset V) (l : L) :
    privateCount b R l+sharedCount b R l≤Fintype.card V := by
  classical
  have he : (R.filter fun x => b x={l}) ∪ (R.filter fun x => l∈b x ∧ b x≠{l}) =
      R.filter (fun x => l∈b x) := by
    ext x
    simp only [mem_union,mem_filter]
    constructor
    · rintro (⟨hx,hb⟩|⟨hx,hl,_⟩)
      · exact ⟨hx,by simp [hb]⟩
      · exact ⟨hx,hl⟩
    · rintro ⟨hx,hl⟩
      by_cases h : b x={l}
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr ⟨hx,hl,h⟩
  have hd : Disjoint (R.filter fun x => b x={l}) (R.filter fun x => l∈b x ∧ b x≠{l}) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact (mem_filter.mp hx').2.2 (mem_filter.mp hx).2
  unfold privateCount sharedCount
  rw [← card_union_of_disjoint hd,he]
  exact (card_filter_le _ _).trans (card_le_univ R)

lemma advanceTable_congr (b : V → Finset L) (R : Finset V) (parent : L → Option L)
    (l : L) (w z : L → ℕ → ℕ) (B : ℕ)
    (h : ∀ a r,r≤B+Fintype.card V → w a r=z a r) (a : L) (r : ℕ) (hr : r≤B) :
    advanceTable b R parent l w a r=advanceTable b R parent l z a r := by
  classical
  have hs := shared_le_card b R l
  have hu := private_add_shared b R l
  unfold advanceTable
  cases hpar : parent l with
  | some p =>
    simp only
    unfold leafUpdate
    split_ifs
    · rfl
    · apply sum_congr rfl
      intro k hk
      have hk' : k ≤ sharedCount b R l := by simpa using (mem_range.mp hk)
      rw [h l _ (by omega),h _ _ (by omega)]
    · exact h a r (by omega)
  | none =>
    simp only
    unfold rootUpdate
    split_ifs
    · apply h
      have ht := (card_filter_le (s:=R) (p:=fun x => l∈b x)).trans (card_le_univ R)
      omega
    · exact h a r (by omega)

noncomputable def capTable (B : ℕ) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if r≤B then w a r else 0

noncomputable def finiteDP (b : V → Finset L) (parent : L → Option L) :
    List L → Finset V → (L → ℕ → ℕ) → (L → ℕ → ℕ)
  | [],_,w => w
  | l::ls,R,w => finiteDP b parent ls (trim b R l)
      (capTable (Fintype.card V*ls.length)
        (advanceTable b R parent l w))




abbrev withoutPair (a b : V) := {x : V // x≠a ∧ x≠b}

abbrev residualBags (bags : V → Finset L) (a b : V) : withoutPair a b → Finset L :=
  fun x => bags x.val

abbrev Partner (bags : V → Finset L) (a : V) :=
  {bc : V × L // bc.1≠a ∧ bc.2∈bags a ∧ bc.2∈bags bc.1}

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Table := List (List ℕ)

def read (t : Table) (a r : ℕ) : ℕ := (t.getD a []).getD r 0

def tabulate (m B : ℕ) (f : Fin m → ℕ → ℕ) : Table :=
  List.ofFn fun a : Fin m => List.ofFn fun r : Fin (B+1) => f a r.val

def entry {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (t : Table) (r : ℕ) : ℕ :=
  match parent l with
  | none => if a=l then read t l.val ((R.filter fun x=>l∈bags x).card) else read t a.val r
  | some p => if a=l then 1 else if a=p then
      ∑ k∈range (sharedCount bags R l+1),
        (sharedCount bags R l).choose k * read t l.val (privateCount bags R l+k) *
          read t p.val (sharedCount bags R l-k+r)
      else read t a.val r

omit [Fintype V] [DecidableEq V] in
lemma entry_eq [Fintype V] [DecidableEq V] {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (t : Table) (r : ℕ) :
    entry bags R parent l a t r =
      advanceTable bags R parent l (fun a r => read t a.val r) a r := by
  unfold entry advanceTable leafUpdate rootUpdate
  cases parent l <;> rfl

def update {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (B : ℕ) (t : Table) : Table :=
  tabulate m B (fun a r=>entry bags R parent l a t r)

def run {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m)) :
    List (Fin m) → Finset V → Table → Table
  | [],_,t => t
  | l::ls,R,t => run bags parent ls (trim bags R l)
      (update bags R parent l (Fintype.card V*ls.length) t)

def initial (m B : ℕ) : Table := tabulate m B (fun _=>pairingCount)

def count {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (plan : List (Fin m)) : ℕ :=
  let t := run bags parent plan univ (initial m (Fintype.card V*m))
  ∏ a : Fin m,read t a.val 0

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {A B : Type}
namespace Fold

inductive Point where | loop | check | splitHead | pushTail | pushArgs | body | popTail | rebuild | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.loop,.check,.splitHead,.pushTail,.pushArgs,.body,.popTail,.rebuild,.halt},by
  intro p; cases p <;> simp⟩
end Fold

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {A B C : Type}

def mulStep (x : Bool×(ℕ×ℕ)) : ℕ×ℕ :=
  (x.2.1,2*x.2.2+(if x.1 then x.2.1 else 0))

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeNatDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def divStep (x : Bool×(ℕ×(ℕ×ℕ))) : ℕ×(ℕ×ℕ) :=
  let n:=x.2.1
  let q:=x.2.2.1
  let r:=2*x.2.2.2+x.1.toNat
  (n,if r<n then (2*q,r) else (2*q+1,r-n))

lemma divStep_first (b : Bool) (n q r : ℕ) : (divStep (b,(n,q,r))).1=n := rfl
lemma divStep_lt (b : Bool) (n q r : ℕ) (_ : 0<n) (hr : r<n) :
    (divStep (b,(n,q,r))).2.2<n := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  simp only [divStep]
  split_ifs <;> simp only
  · assumption
  · omega
lemma divStep_mass (b : Bool) (n q r : ℕ) :
    n*(divStep (b,(n,q,r))).2.1+(divStep (b,(n,q,r))).2.2=
      2*(n*q+r)+b.toNat := by
  simp only [divStep]
  split_ifs with h
  · simp only; ring
  · simp only
    have hh : n ≤ 2*r+b.toNat := by omega
    have hs:=Nat.sub_add_cancel hh
    nlinarith

lemma divFold_first (A : List Bool) (n q r : ℕ) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).1=n := by
  induction A generalizing q r with
  | nil => rfl
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).1=n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _

lemma divFold_lt (A : List Bool) (n q r : ℕ) (hn : 0<n) (hr : r<n) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2<n := by
  induction A generalizing q r with
  | nil => exact hr
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).2.2<n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _ (divStep_lt b n q r hn hr)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {B : Type}

def countDown (f : ℕ×B → B) : ℕ → B → B
  | 0,b => b
  | n+1,b => countDown f n (f (n+1,b))

namespace Repeat

inductive Point where | loop | check | rebuild | body | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.loop,.check,.rebuild,.body,.halt},by intro p; cases p <;> simp⟩
def next (f : ℕ×B → B) (nb : ℕ×B) : ℕ×B := (nb.1-1,f nb)
end Repeat

def rangeStep (x : ℕ×List ℕ) : List ℕ := (x.1-1)::x.2
lemma countDown_range (n : ℕ) (as : List ℕ) : countDown rangeStep n as=List.range n++as := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => simp [countDown,rangeStep,ih,List.range_succ,List.append_assoc]
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeNaturalComb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def factStep (x : ℕ×ℕ) : ℕ := x.1*x.2
lemma fact_countDown (n a : ℕ) : countDown factStep n a=n.factorial*a := by
  induction n generalizing a with
  | zero => simp [countDown]
  | succ n ih =>
    rw [countDown,ih]
    simp only [factStep,Nat.factorial_succ]
    ring

def pairingStep (x : ℕ×(ℕ×ℕ)) : ℕ×ℕ := (x.2.2,(x.1+1)*x.2.1)
lemma pairing_range (n : ℕ) :
    (List.range n).foldl (fun z i=>pairingStep (i,z)) (1,0)=
      (UnitRefresh.pairingCount n,UnitRefresh.pairingCount (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,ih]
    simp [pairingStep,UnitRefresh.pairingCount]

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

variable {A B X : Type}

def dropStep (x : ℕ×List A) : List A := x.2.tail

def mapStep (g : X×A → B) (z : A×(X×List B)) : X×List B :=
  (z.2.1,g (z.2.1,z.1)::z.2.2)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def sortedPair (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then (x.2,x.1) else x

lemma sortedPair_order (x : ℕ×ℕ) : (sortedPair x).2≤(sortedPair x).1 := by
  unfold sortedPair; split_ifs <;> (try dsimp only) <;> omega
lemma sortedPair_gcd (x : ℕ×ℕ) : (sortedPair x).1.gcd (sortedPair x).2=x.1.gcd x.2 := by
  unfold sortedPair; split_ifs <;> simp [Nat.gcd_comm]
lemma sortedPair_size (x : ℕ×ℕ) : (sortedPair x).1.size+(sortedPair x).2.size=x.1.size+x.2.size := by
  unfold sortedPair
  split_ifs
  · exact Nat.add_comm _ _
  · rfl

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)

lemma mod_size_lt {a b : ℕ} (hb : 0<b) (hab : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := hb.trans_le hab
  have hr := Nat.mod_lt a hb
  have hq : 1≤a/b := Nat.div_pos hab hb
  have hd := Nat.mod_add_div a b
  have hm : 2*(a%b)<a := by nlinarith [Nat.mul_le_mul_left b hq]
  have hs := Nat.size_pos.mpr ha
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a.size≠0)
  have hpow:=Nat.lt_size_self a
  rw [hk,pow_succ] at hpow
  have hh : a%b<2^k := by omega
  have hsz := Nat.size_le.mpr hh
  omega

lemma gcdStep_order {x : ℕ×ℕ} (h : x.2≤x.1) : (gcdStep x).2≤(gcdStep x).1 := by
  unfold gcdStep; split_ifs with hz
  · exact h
  · exact (Nat.mod_lt _ (by omega)).le
lemma gcdStep_gcd (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep; split_ifs
  · rfl
  · simpa [Nat.gcd_comm] using (Nat.gcd_rec x.2 x.1).symm
lemma gcdStep_decrease {x : ℕ×ℕ} (h : x.2≤x.1) (hz : x.2≠0) :
    (gcdStep x).1.size+(gcdStep x).2.size<x.1.size+x.2.size := by
  simp only [gcdStep,hz,↓reduceIte]
  have hh:=mod_size_lt (by omega : 0<x.2) h
  omega

def gcdIterStep (x : ℕ×(ℕ×ℕ)) : ℕ×ℕ := gcdStep x.2
lemma gcdIter_zero (k a : ℕ) : countDown gcdIterStep k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [countDown,gcdIterStep,gcdStep,↓reduceIte] using ih

lemma gcdIter_result (k : ℕ) (x : ℕ×ℕ) (h : x.2≤x.1) (hs : x.1.size+x.2.size≤k) :
    countDown gcdIterStep k x=(x.1.gcd x.2,0) := by
  induction k generalizing x with
  | zero =>
    have hsz : x.1.size=0 := by omega
    have ha:=Nat.size_eq_zero.mp hsz
    have hb : x.2=0 := by omega
    simp [countDown,ha,hb]
    exact Prod.ext ha hb
  | succ k ih =>
    by_cases hz : x.2=0
    · obtain ⟨a,b⟩:=x; dsimp only at hz; subst b
      simp only [gcdIter_zero,Nat.gcd_zero_right]
    · rw [countDown]
      change countDown gcdIterStep k (gcdStep x)=_
      rw [ih _ (gcdStep_order h) (by have hd:=gcdStep_decrease h hz; omega),gcdStep_gcd]

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type}

def dedupStep [DecidableEq A] (x : A×List A) : List A := if x.1∈x.2 then x.2 else x.1::x.2

variable (r : A → A → Prop) [DecidableRel r]
def insertStep (x : A×(A×(List A×List A))) : A×(List A×List A) :=
  (x.2.1,(x.1::x.2.2.1,if r x.2.1 x.1 then x.2.1::x.1::x.2.2.1 else x.1::x.2.2.2))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev Table := List (List ℕ)
def read (x : Table×(ℕ×ℕ)) : ℕ := (x.1.getD x.2.1 []).getD x.2.2 0

abbrev EntryCtx := (Bool×ℕ) × (ℕ × (Table × (ℕ × (ℕ × ℕ))))
def term (x : (EntryCtx×ℕ)×ℕ) : ℕ :=
  let c := x.1.1
  let r := x.1.2
  let k := x.2
  c.2.2.2.2.1.choose k * read (c.2.2.1,(c.2.1,c.2.2.2.1+k)) *
    read (c.2.2.1,(c.1.2,c.2.2.2.2.1-k+r))

def entry (x : EntryCtx×(ℕ×ℕ)) : ℕ :=
  let c:=x.1
  let a:=x.2.1
  let r:=x.2.2
  if c.1.1 then
    if a=c.2.1 then 1 else if a=c.1.2 then
      ((List.range (c.2.2.2.2.1+1)).map fun k=>term ((c,r),k)).sum
    else read (c.2.2.1,(a,r))
  else if a=c.2.1 then read (c.2.2.1,(c.2.1,c.2.2.2.2.2))
    else read (c.2.2.1,(a,r))

variable {X Y : Type}
def tabulate (f : X×(ℕ×ℕ) → Y) (x : X×(ℕ×ℕ)) : List (List Y) :=
  (List.range x.2.1).map fun a=>(List.range (x.2.2+1)).map fun r=>f (x.1,(a,r))

lemma read_eq (t : Table) (a r : ℕ) : read (t,(a,r))=UnitRefresh.Materialized.read t a r := rfl

lemma entry_eq {V : Type} {m : ℕ}
    (bags : V → Finset (Fin m)) (R : Finset V) (parent : Fin m → Option (Fin m))
    (l a : Fin m) (t : Table) (r : ℕ) :
    entry (((match parent l with | none=>(false,0) | some p=>(true,p.val)),
      (l.val,(t,(UnitRefresh.privateCount bags R l,
        (UnitRefresh.sharedCount bags R l,(R.filter fun x=>l∈bags x).card))))),(a.val,r))=
      UnitRefresh.Materialized.entry bags R parent l a t r := by
  have he : (a.val=l.val) ↔ a=l := Fin.val_inj
  cases hp : parent l with
  | none => simp only [entry,UnitRefresh.Materialized.entry,hp,Bool.false_eq_true,↓reduceIte,he,read_eq]
  | some p =>
    have he' : (a.val=p.val) ↔ a=p := Fin.val_inj
    simp only [entry,UnitRefresh.Materialized.entry,hp,↓reduceIte,he,he']
    split_ifs <;> try rfl

lemma tabulate_eq {m B : ℕ} (f : ℕ×ℕ → ℕ) :
    (List.range m).map (fun a=>(List.range (B+1)).map fun r=>f (a,r))=
      UnitRefresh.Materialized.tabulate m B (fun a r=>f (a.val,r)) := by
  unfold UnitRefresh.Materialized.tabulate
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev Bag := List ℕ
abbrev Bags := List Bag
abbrev Parents := List (Bool×ℕ)

def privateFlag (x : ℕ×Bag) : Bool := decide (x.2.length=1) && decide (x.1∈x.2)
def sharedFlag (x : ℕ×Bag) : Bool := decide (x.1∈x.2) && !(privateFlag x)
def totalFlag (x : ℕ×Bag) : Bool := decide (x.1∈x.2)
def privateNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>privateFlag (l,b)).length
def sharedNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>sharedFlag (l,b)).length
def totalNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>totalFlag (l,b)).length
def trim (bs : Bags) (l : ℕ) := bs.filter fun b=>!(totalFlag (l,b))

def context (x : (Bags×Parents)×(ℕ×Table)) : EntryCtx :=
  (x.1.2.getD x.2.1 (false,0),
    (x.2.1,(x.2.2,(privateNumber x.1.1 x.2.1,
      (sharedNumber x.1.1 x.2.1,totalNumber x.1.1 x.2.1)))))

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
noncomputable def bagRep (b : Finset (Fin m)) : Bag := b.toList.map Fin.val

noncomputable def activeRep (bags : V → Finset (Fin m)) (R : Finset V) : Bags := R.toList.map (bagRep ∘ bags)

@[simp] lemma mem_bagRep (b : Finset (Fin m)) (l : Fin m) : l.val∈bagRep b ↔ l∈b := by
  simp [bagRep,Fin.val_inj]
@[simp] lemma length_bagRep (b : Finset (Fin m)) : (bagRep b).length=b.card := by
  simp [bagRep]
lemma card_one_mem (b : Finset (Fin m)) (l : Fin m) : b.card=1 ∧ l∈b ↔ b={l} := by
  constructor
  · rintro ⟨h,hl⟩
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
    have e : l=a := by simpa [ha] using hl
    simpa [e] using ha
  · rintro rfl; simp
@[simp] lemma privateFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    privateFlag (l.val,bagRep b)=decide (b={l}) := by
  apply Bool.eq_iff_iff.mpr
  simp [privateFlag,card_one_mem]
@[simp] lemma sharedFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    sharedFlag (l.val,bagRep b)=decide (l∈b ∧ b≠{l}) := by
  apply Bool.eq_iff_iff.mpr
  simp [sharedFlag,privateFlag_bagRep]
@[simp] lemma totalFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    totalFlag (l.val,bagRep b)=decide (l∈b) := by simp [totalFlag]

omit [Fintype V] [DecidableEq V] in
lemma filter_length_toList [Fintype V] [DecidableEq V]
    (R : Finset V) (P : V → Prop) [DecidablePred P] :
    (R.toList.filter fun x=>decide (P x)).length=(R.filter P).card := by
  rw [←List.toFinset_card_of_nodup ((Finset.nodup_toList R).filter _)]
  simp

@[simp] lemma privateNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    privateNumber (activeRep bags R) l.val=UnitRefresh.privateCount bags R l := by
  simp only [privateNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,privateFlag_bagRep]
  exact filter_length_toList R (fun x=>bags x={l})
@[simp] lemma sharedNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    sharedNumber (activeRep bags R) l.val=UnitRefresh.sharedCount bags R l := by
  simp only [sharedNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,sharedFlag_bagRep]
  exact filter_length_toList R (fun x=>l∈bags x ∧ bags x≠{l})
@[simp] lemma totalNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    totalNumber (activeRep bags R) l.val=(R.filter fun x=>l∈bags x).card := by
  simp only [totalNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,totalFlag_bagRep]
  exact filter_length_toList R (fun x=>l∈bags x)

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type}

def sumRep [Inhabited A] [Inhabited B] : A⊕B→Bool×(A×B)
  | .inl a => (true,(a,default))
  | .inr b => (false,(default,b))

def optionRep [Inhabited A] : Option A→Bool×A
  | none => (false,default)
  | some a => (true,a)
end MatchingFPRAS.TreeTyped

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

def plan {m : ℕ} (rank : Fin m → ℕ) : List (Fin m) :=
  (List.ofFn (fun l : Fin m => l)).mergeSort (fun a b=>decide (rank b ≤ rank a))

lemma plan_mem {m : ℕ} (rank : Fin m → ℕ) (a : Fin m) : a∈plan rank := by
  unfold plan
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

lemma plan_length {m : ℕ} (rank : Fin m → ℕ) : (plan rank).length=m := by
  unfold plan
  rw [(List.mergeSort_perm _ _).length_eq]
  simp

lemma plan_sorted {m : ℕ} (rank : Fin m → ℕ) :
    (plan rank).Pairwise (fun a b=>rank b ≤ rank a) := by
  let r := fun a b : Fin m => rank b ≤ rank a
  let : Std.Total r := ⟨fun a b => le_total (rank b) (rank a)⟩
  let : IsTrans (Fin m) r := ⟨fun a b c hab hbc => hbc.trans hab⟩
  exact List.pairwise_mergeSort' r _

lemma plan_legal {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l) :
    LegalPlan bags parent (plan rank) univ := by
  apply rank_order_legal bags rank parent hb hp _ (plan_sorted rank)
  · intro x _; exact hne x
  · intro x _ a _; exact plan_mem rank a



open Finset MatchingFPRAS.FiniteChoice

variable {n m : ℕ}

def validBranch (bags : Fin n → Finset (Fin m)) (a : Fin n) (bc : Fin n × Fin m) : Prop :=
  bc.1≠a ∧ bc.2∈bags a ∧ bc.2∈bags bc.1

instance instDecidableValidBranch (bags : Fin n → Finset (Fin m)) (a : Fin n) (bc : Fin n × Fin m) :
    Decidable (validBranch bags a bc) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {U V L : Type*} [Fintype U] [Fintype V] [Fintype L] [DecidableEq U] [DecidableEq V] [DecidableEq L]

def gapEquiv {n : ℕ} (a : Fin (n+1)) : Fin n ≃ {x : Fin (n+1) // x≠a} :=
  Equiv.optionSubtype a ⟨(finSuccEquiv' a).symm,rfl⟩

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RemainingBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Variation

def orderedEnum (α : Type*) [Fintype α] [LinearOrder α] : Fin (Fintype.card α) ≃ α :=
  ((univ : Finset α).orderIsoOfFin (card_univ)).toEquiv.trans
    (Equiv.subtypeUnivEquiv (fun _=>mem_univ _))

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] [DecidableEq L] [DecidableEq J]

open Finset MatchingFPRAS.Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

def numberedBags (bags : V → Finset L) : Fin (Fintype.card V) → Finset (Fin (Fintype.card L)) :=
  fun x=>(bags (orderedEnum V x)).map (orderedEnum L).symm.toEmbedding

lemma mem_numberedBags (bags : V → Finset L) (x : Fin (Fintype.card V)) (l : Fin (Fintype.card L)) :
    l∈numberedBags bags x ↔ orderedEnum L l∈bags (orderedEnum V x) := by
  simp [numberedBags]

def numberedRank (rank : L → ℕ) : Fin (Fintype.card L) → ℕ := fun l=>rank (orderedEnum L l)

def numberedParent (parent : L → Option L) : Fin (Fintype.card L) → Option (Fin (Fintype.card L)) :=
  fun l=>(parent (orderedEnum L l)).map (orderedEnum L).symm

lemma numberedParent_iff (parent : L → Option L) (l p : Fin (Fintype.card L)) :
    numberedParent parent l=some p ↔ parent (orderedEnum L l)=some (orderedEnum L p) := by
  simp [numberedParent,Equiv.symm_apply_eq]

lemma numberedRanked (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) :
    RankedBags (numberedBags bags) (numberedRank rank) (numberedParent parent) := by
  intro x a ha b hb' hab
  rcases hb (orderedEnum V x) (orderedEnum L a) ((mem_numberedBags bags x a).mp ha)
    (orderedEnum L b) ((mem_numberedBags bags x b).mp hb')
    (fun h=>hab ((orderedEnum L).injective h)) with ⟨hlt,hp⟩|⟨hlt,hp⟩
  · exact Or.inl ⟨hlt,(numberedParent_iff parent b a).mpr hp⟩
  · exact Or.inr ⟨hlt,(numberedParent_iff parent a b).mpr hp⟩

lemma numberedNonempty (bags : V → Finset L) (hne : ∀ x,(bags x).Nonempty) :
    ∀ x,(numberedBags bags x).Nonempty := fun x=>(hne (orderedEnum V x)).map

lemma numberedDecreasing (rank : L → ℕ) (parent : L → Option L)
    (hp : ∀ l p,parent l=some p → rank p < rank l) :
    ∀ l p,numberedParent parent l=some p → numberedRank rank p<numberedRank rank l := by
  intro l p h; exact hp _ _ ((numberedParent_iff parent l p).mp h)

open MatchingFPRAS.Transport

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

def rationalTierBase (V : Type*) [Fintype V] : ℚ := 1+((Fintype.card V:ℚ)^2)⁻¹

omit [LinearOrder V] in
lemma rationalTierBase_cast : (rationalTierBase V:ℝ)=tierBase V := by
  simp [rationalTierBase,tierBase]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L}



open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

@[instance_reducible] def prodOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A×B) := LinearOrder.lift' toLex toLex.injective

@[instance_reducible] def sumOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A⊕B) := LinearOrder.lift' toLex toLex.injective

attribute [local instance] prodOrder sumOrder

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

abbrev LocalBits (V : Type*) [Fintype V] (k : ℕ) :=
  (Fin k → Bool) × (Fin (Fintype.card V) → Fin k → Bool)

abbrev ScanBits (V : Type*) [Fintype V] (k : ℕ) := (Fin k → Bool) × LocalBits V k



open Finset Replica Replica.Ladder Variation

def bitPrecision (R : ℕ) (η : ℚ) : ℕ := Nat.clog 2 (R*⌈η⁻¹⌉₊)

def pairBitsEquiv (m n : ℕ) : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def matrixBitsEquiv (m n : ℕ) : (Fin (m*n) → Bool) ≃ (Fin m → Fin n → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def scanBitCount (N k : ℕ) : ℕ := k+(k+N*k)

def scanBitsEquiv (V : Type*) [Fintype V] (k : ℕ) :
    (Fin (scanBitCount (Fintype.card V) k) → Bool) ≃ ScanBits V k :=
  (pairBitsEquiv k (k+Fintype.card V*k)).trans
    (Equiv.prodCongr (Equiv.refl _) ((pairBitsEquiv k (Fintype.card V*k)).trans
      (Equiv.prodCongr (Equiv.refl _) (matrixBitsEquiv (Fintype.card V) k))))

def runBitsEquiv (V : Type*) [Fintype V] (k n : ℕ) :
    (Fin (n*scanBitCount (Fintype.card V) k) → Bool) ≃ (Fin n → ScanBits V k) :=
  (matrixBitsEquiv n _).trans (Equiv.piCongrRight fun _=>scanBitsEquiv V k)

attribute [local instance] prodOrder sumOrder

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

def discreteLadderSteps (N D K T m : ℕ) : ℕ :=
  20*ladderL N D*ladderM N D T*(ladderLambda N D K T+Nat.clog 2 m+1)

attribute [local instance] prodOrder sumOrder

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineScheduleNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type}
lemma clog_two_size_pred (n : ℕ) : Nat.clog 2 n=Nat.size (n-1) := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    have hp:=Nat.lt_size_self (n-1)
    omega
  · apply Nat.size_le.mpr
    have hp:=Nat.le_pow_clog (by decide : 1<2) n
    have hpos:=Nat.two_pow_pos (Nat.clog 2 n)
    omega
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Transport

abbrev ScanInput := ((ℕ×ℕ)×(ℕ×ℕ))×ℕ

end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_AdaptiveStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Stream := ℕ → Bool

def shift (n : ℕ) (b : Stream) : Stream := fun i => b (n+i)
@[simp] lemma shift_zero (b : Stream) : shift 0 b=b := by funext i; simp [shift]
def extend {n : ℕ} (b : Bits n) : Stream := fun i => if h : i<n then b ⟨i,h⟩ else false

def concat {n m : ℕ} (a : Bits n) (b : Bits m) : Bits (n+m) := Fin.append a b

def split (n m : ℕ) : Bits (n+m) ≃ Bits n × Bits m where
  toFun b := (fun i=>b (Fin.castAdd m i), fun j=>b (Fin.natAdd n j))
  invFun b := concat b.1 b.2
  left_inv b := by funext i; exact Fin.addCases (by simp [concat]) (by simp [concat]) i
  right_inv b := by ext i <;> simp [concat]

@[simp] lemma concat_left {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin n) :
    concat a b (Fin.castAdd m i)=a i := by simp [concat]
@[simp] lemma concat_right {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin m) :
    concat a b (Fin.natAdd n i)=b i := by simp [concat]

noncomputable def average {n : ℕ} (f : Bits n → ℚ) : ℚ :=
  (∑ b,f b)/(2:ℚ)^n

inductive Experiment (α : Type) where
  | done (a : α)
  | read (next : Bool → Experiment α)
  | delay (ticks : ℕ) (next : Experiment α)

namespace Experiment
variable {α β : Type}

def cost : Experiment α → ℕ
  | .done _ => 0
  | .read f => 1+max (cost (f false)) (cost (f true))
  | .delay n p => n+cost p

def run : Experiment α → Stream → α × ℕ
  | .done a,_ => (a,0)
  | .read f,b => let r := run (f (b 0)) (shift 1 b); (r.1,1+r.2)
  | .delay n p,b => let r := run p (shift n b); (r.1,n+r.2)

def mean : Experiment α → (α → ℚ) → ℚ
  | .done a,f => f a
  | .read p,f => (mean (p false) f+mean (p true) f)/2
  | .delay _ p,f => mean p f

def bind : Experiment α → (α → Experiment β) → Experiment β
  | .done a,f => f a
  | .read p,f => .read (fun b=>(p b).bind f)
  | .delay n p,f => .delay n (p.bind f)

lemma mean_bind (p : Experiment α) (q : α → Experiment β) (f : β → ℚ) :
    (p.bind q).mean f=p.mean (fun a=>(q a).mean f) := by
  induction p with
  | done a => rfl
  | read p ih => simp [bind,mean,ih]
  | delay n p ih => exact ih

lemma cost_bind_le (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (hq : ∀ a,(q a).cost ≤ N) : (p.bind q).cost ≤ p.cost+N := by
  induction p with
  | done a => simpa only [bind,cost,Nat.zero_add] using hq a
  | read p ih =>
    simp only [bind,cost]
    have h0:=ih false
    have h1:=ih true
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left ih n

def map (f : α → β) (p : Experiment α) : Experiment β := p.bind (fun a=>.done (f a))

@[simp] lemma cost_map (f : α → β) (p : Experiment α) : (p.map f).cost=p.cost := by
  induction p with
  | done a => rfl
  | read p ih => simp only [map,bind,cost]; change 1+max ((p false).map f).cost ((p true).map f).cost=_; rw [ih false,ih true]
  | delay n p ih => change n+(p.map f).cost=n+p.cost; rw [ih]

lemma mean_map (f : α → β) (p : Experiment α) (g : β → ℚ) :
    (p.map f).mean g=p.mean (fun a=>g (f a)) := by simp [map,mean_bind,mean]

def word : (n : ℕ) → Experiment (Bits n)
  | 0 => .done Fin.elim0
  | n+1 => .read (fun b=>(word n).map (Fin.cons b))

@[simp] lemma cost_word (n : ℕ) : (word n).cost=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [word,cost,cost_map,ih,max_self]; omega

end Experiment
end MatchingFPRAS.PhysicalStream

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

variable [Fintype Q] [Inhabited Q]

noncomputable def enumeration : Q ≃ Fin (Fintype.card Q-1+1) := by
  let e : Q ≃ Fin (Fintype.card Q-1+1) := Fintype.equivFinOfCardEq
    (Nat.sub_add_cancel Fintype.card_pos).symm
  exact e.trans (Equiv.swap (e default) 0)

@[simp] lemma enumeration_default : enumeration (Q:=Q) default=0 := by
  classical
  simp only [enumeration,Equiv.trans_apply,Equiv.swap_apply_left]

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
open Turing MachineCost PhysicalStream
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
abbrev Alpha (K : Type) (Γ : K → Type) := TM2to1.Γ' K Γ
abbrev L1 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM2to1.Λ' K Γ Λ σ
abbrev L2 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM1to1.Λ' (Alpha K Γ) (L1 K Γ Λ σ) σ

noncomputable def height (S : ∀ k,List (Γ k)) : ℕ := Finset.univ.sup (fun k=>(S k).length)
noncomputable def stackCfg (c : TM2.Cfg Γ Λ σ) : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ :=
  ⟨c.l.map TM2to1.Λ'.normal,c.var,Tape.mk₁ (StackWords.word c.stk (height c.stk))⟩

variable (M : Λ → TM2.Stmt Γ Λ σ)
noncomputable def program1 := TM2to1.tr M
noncomputable def enc := FixedEncoding.enc (Alpha K Γ)
noncomputable def dec := FixedEncoding.dec (Alpha K Γ)
lemma enc0 : enc (K:=K) (Γ:=Γ) default=List.Vector.replicate (Fintype.card (Alpha K Γ)) false :=
  FixedEncoding.blank (Alpha K Γ)
noncomputable def program2 := TM1to1.tr (enc (K:=K) (Γ:=Γ)) dec (program1 M)
noncomputable def support1 := TM2to1.trSupp M Finset.univ
noncomputable def support2 := TM1to1.trSupp (program1 M) (support1 M)
omit [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] in
lemma supports1 [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] :
    TM1.Supports (program1 M) (support1 M) :=
  TM2to1.tr_supports M (StackComposition.supports_univ M)
lemma supports2 : TM1.Supports (program2 M) (support2 M) :=
  TM1to1.tr_supports enc dec (program1 M) (supports1 M)

noncomputable def accesses : ℕ := Finset.univ.sup (fun l=>StackCost.accesses (M l))
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ExperimentSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
def All : Experiment α → (α → Prop) → Prop
  | .done a,P => P a
  | .read f,P => All (f false) P ∧ All (f true) P
  | .delay _ p,P => All p P
lemma All.mono {p : Experiment α} {P Q : α → Prop} (h : All p P) (hPQ : ∀ a,P a→Q a) : All p Q := by
  induction p with
  | done a => exact hPQ a h
  | read p ih => exact ⟨ih false h.1,ih true h.2⟩
  | delay n p ih => exact ih h
lemma mean_nonneg (p : Experiment α) (f : α → ℚ) (h : All p (fun a=>0≤f a)) : 0≤p.mean f := by
  induction p with
  | done a => exact h
  | read p ih => exact div_nonneg (add_nonneg (ih false h.1) (ih true h.2)) (by norm_num)
  | delay n p ih => exact ih h
lemma all_true (p : Experiment α) : All p (fun _=>True) := by
  induction p with
  | done a => trivial
  | read p ih => exact ⟨ih false,ih true⟩
  | delay n p ih => exact ih
lemma all_indicator (p : Experiment α) (P : α → Prop) [DecidablePred P] :
    All p P ↔ p.mean (fun a=>if P a then 0 else 1)=0 := by
  induction p with
  | done a => simp [All,mean]
  | delay n p ih => exact ih
  | read p ih =>
    have hz (b : Bool) : 0≤(p b).mean (fun a=>if P a then 0 else 1) :=
      mean_nonneg _ _ ((all_true _).mono (by intro a _; split <;> norm_num))
    simp only [All,mean,ih]
    constructor
    · rintro ⟨h0,h1⟩; rw [h0,h1]; norm_num
    · intro h
      have h0:=hz false
      have h1:=hz true
      constructor <;> linarith
lemma all_of_mean_eq {p q : Experiment α} (h : ∀ f : α → ℚ,q.mean f=p.mean f)
    (P : α → Prop) (hp : All p P) : All q P := by
  classical
  rw [all_indicator,h,←all_indicator]
  exact hp
lemma cost_bind_le_of_all (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (h : All p (fun a=>(q a).cost≤N)) : (p.bind q).cost≤p.cost+N := by
  induction p with
  | done a => simpa only [All,bind,cost,Nat.zero_add] using h
  | read p ih =>
    have h0:=ih false h.1
    have h1:=ih true h.2
    simp only [cost,bind]
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left (ih h) n

variable {α : Type}
def worst : Experiment α → (α → ℕ) → ℕ
  | .done a,f => f a
  | .read p,f => max (worst (p false) f) (worst (p true) f)
  | .delay _ p,f => worst p f
lemma all_worst (p : Experiment α) (f : α → ℕ) : All p (fun a=>f a≤p.worst f) := by
  induction p with
  | done a => exact le_rfl
  | read p ih => exact ⟨(ih false).mono (fun a ha=>ha.trans (le_max_left _ _)),
      (ih true).mono (fun a ha=>ha.trans (le_max_right _ _))⟩
  | delay n p ih => exact ih
end MatchingFPRAS.PhysicalStream.Experiment

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
open TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type}

def foldM (f : A×B → Experiment B) : List A → B → Experiment B
  | [],b => .done b
  | a::as,b => (f (a,b)).bind (foldM f as)
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
open TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type}
namespace Second

inductive Point where | split | save | body | pop | cons | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.split,.save,.body,.pop,.cons,.halt},by intro p; cases p <;> simp⟩
end Second

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineTraverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open PhysicalStream TreeTyped

variable {A B C : Type}

def traverseM (f : A → Experiment B) : List A → Experiment (List B)
  | [] => .done []
  | a::as => (f a).bind (fun b=>(traverseM f as).map (List.cons b))
def collectStep (f : A → Experiment B) (x : A×List B) : Experiment (List B) :=
  (f x.1).map (fun b=>b::x.2)
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
open PhysicalStream TreeTyped OnlineTree

def prepend : ℕ → List Bool → Experiment (List Bool)
  | 0,acc => .done acc
  | n+1,acc => .read (fun b=>prepend n (b::acc))

def reverseBits (n : ℕ) : Bits n ≃ Bits n where
  toFun w i:=w i.rev
  invFun w i:=w i.rev
  left_inv w:=by funext i; simp
  right_inv w:=by funext i; simp

def step (x : ℕ×List Bool) : Experiment (List Bool) := .read (fun b=>.done (b::x.2))
lemma fold_step (as : List ℕ) (acc : List Bool) :
    OnlineTree.foldM step as acc=prepend as.length acc := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih => simp only [OnlineTree.foldM,step,Experiment.bind,ih,List.length_cons,prepend]

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
noncomputable def qaverage (f : A → ℚ) : ℚ := (∑ a,f a)/Fintype.card A
def splitFunction (n : ℕ) (A : Type) : (Fin (n+1) → A) ≃ A×(Fin n → A) where
  toFun f := (f 0,fun i=>f i.succ)
  invFun f := Fin.cons f.1 f.2
  left_inv f := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  right_inv f := by rcases f with ⟨a,f⟩; rfl
end MatchingFPRAS.PhysicalStream

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

def related (t : ℚ) (x y : V) : Prop := x=y ∨ t≤B x y

instance relatedDec (t : ℚ) (x y : V) : Decidable (related B t x y) :=
  inferInstanceAs (Decidable (x=y ∨ t≤B x y))

def component (t : ℚ) (x : V) : Finset V := univ.filter (related B t x)

lemma component_self (t : ℚ) (x : V) : x∈component B t x := by simp [component,related]

def root (t : ℚ) (x : V) : V := (component B t x).min' ⟨x,component_self B t x⟩

lemma root_mem (t : ℚ) (x : V) : root B t x ∈ component B t x := min'_mem _ _

lemma related_root (t : ℚ) (x : V) : related B t x (root B t x) := by
  simpa [component] using root_mem B t x

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

include hsym in
omit [Fintype V] [LinearOrder V] in
lemma symmetric [Fintype V] [LinearOrder V] : ∀ x y,(B x y:ℝ)=(B y x:ℝ) := by intro x y; rw [hsym]

include htri in
omit [Fintype V] [LinearOrder V] in
lemma triangular [Fintype V] [LinearOrder V] : ∀ x y z,x≠y → x≠z → y≠z →
    min (B x z:ℝ) (B z y:ℝ)≤(B x y:ℝ) := by
  intro x y z hxy hxz hyz
  exact_mod_cast htri x y z hxy hxz hyz

include hsym in
omit [Fintype V] [LinearOrder V] in
lemma related_symm [Fintype V] [LinearOrder V] (t : ℚ) {x y : V}
    (hxy : related B t x y) : related B t y x := by
  rcases hxy with rfl|h
  · exact Or.inl rfl
  · exact Or.inr (by rwa [hsym])

abbrev NumberedComponent (t : ℚ) := {x : V // root B t x=x}

def level (H : ℕ) (x : ℚ) : Fin (H+1) :=
  ⟨Nat.findGreatest (fun k => (2:ℚ)^k≤x) H,Nat.lt_succ_of_le (Nat.findGreatest_le H)⟩

abbrev Label (H : ℕ) := (k : Fin (H+1)) × NumberedComponent B ((2:ℚ)^k.val)

def member {H : ℕ} (l : Label B H) (x : V) : Prop := root B ((2:ℚ)^l.1.val) x=l.2.val

instance memberDec {H : ℕ} (l : Label B H) (x : V) : Decidable (member B l x) :=
  inferInstanceAs (Decidable (root B _ x=l.2.val))

lemma member_self {H : ℕ} (l : Label B H) : member B l l.2.val := l.2.property

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

def profile (p : ℕ) (B Hu Hv lam : ℚ) (i : Fin (4*p+1)) : ℚ :=
  if i.val<2*p then max B (Hu/2^(i.val/2))
  else if i.val=2*p then lam else max B (Hv/2^((4*p-i.val)/2))

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

namespace MatchingFPRAS.NumberedHierarchy

open Finset MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ) (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

@[instance_reducible] def labelOrder (H : ℕ) : LinearOrder (Label B H) :=
  LinearOrder.lift' (fun l : Label B H=>toLex (l.1,l.2.val)) (by
    intro a b h
    have h' := toLex.injective h
    obtain ⟨k,a⟩:=a
    obtain ⟨j,b⟩:=b
    have hk : k=j:=congrArg Prod.fst h'
    cases hk
    exact congrArg (Sigma.mk k) (Subtype.ext (congrArg Prod.snd h')))

attribute [local instance] labelOrder

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}



open Finset Replica Replica.Ladder Variation

def rationalBase (N : ℕ) : ℚ := 1+((N:ℚ)^2)⁻¹

lemma rationalBase_cast (N : ℕ) : (rationalBase N:ℝ)=1+((N:ℝ)^2)⁻¹ := by
  simp [rationalBase]

lemma reaches_cast (N D K t : ℕ) :
    max (D:ℚ) (3*4^K)≤(rationalBase N)^t ↔
      max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^t := by
  rw [←rationalBase_cast]
  exact_mod_cast (Iff.rfl : max (D:ℚ) (3*4^K)≤(rationalBase N)^t ↔ _)

def endpoint (N D K : ℕ) (hN : 0<N) : ℕ :=
  ((range (tierBound N D K+1)).filter
    (fun t => max (D:ℚ) (3*4^K)≤(rationalBase N)^t)).min'
      (by refine ⟨tierBound N D K,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
          exact (reaches_cast _ _ _ _).mpr (tierBound_reaches N D K hN))

lemma endpoint_eq (N D K : ℕ) (hN : 0<N) : endpoint N D K hN=ladderTier N D K hN := by
  apply Nat.le_antisymm
  · apply min'_le
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by have := ladderTier_le N D K hN; omega),
      (reaches_cast _ _ _ _).mpr (ladderTier_spec N D K hN)⟩
  · have he : max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^(endpoint N D K hN) := by
      apply (reaches_cast _ _ _ _).mp
      unfold endpoint
      exact (mem_filter.mp (min'_mem ((range (tierBound N D K+1)).filter
        (fun t => max (D:ℚ) (3*4^K)≤(rationalBase N)^t)) _)).2
    unfold ladderTier
    exact Nat.find_min' _ he

end MatchingFPRAS.Transport

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

omit [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] in
lemma image_symm_bags (e : L ≃ J) (h : ∀ v,(b v).image e=c v) (v : V) :
    (c v).image e.symm=b v := by
  rw [←h v,image_image]
  simp


end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_CompleteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

@[reducible] noncomputable def completeGraph (n : ℕ) : GraphInput where
  n := n
  edges := by
    classical
    exact Finset.univ.filter (fun e => e.1 < e.2)
  increasing := by
    classical
    intro e he
    exact (Finset.mem_filter.mp he).2

noncomputable def rawWeight (G : GraphInput) (x : ℚ) (M : Finset (Fin G.n × Fin G.n)) : ℚ :=
  ∏ e ∈ M, if e ∈ G.edges then 1 else x

noncomputable def rawPartition (G : GraphInput) (x : ℚ) : ℚ :=
  ∑ M ∈ perfectMatchings (completeGraph G.n), rawWeight G x M



end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset

lemma others_nonempty {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : (univ.erase i).Nonempty := by
  let j : Fin n := ⟨if i.val=0 then 1 else 0, by split_ifs <;> omega⟩
  refine ⟨j,mem_erase.mpr ⟨?_,mem_univ _⟩⟩
  apply Fin.ne_of_val_ne
  dsimp [j]; split_ifs <;> omega

def rowMaximum {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.erase i).sup' (others_nonempty hn i) (fun j => G i j / v j)

def scaleUpdate {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  Function.update v i (rowMaximum hn G v i)

def scalingTrace {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 2
  | k+1 => if hk : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,hk⟩ else scalingTrace hn G k



open Finset

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RowPeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}



open Finset




def rowPeak {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.erase i).sup' (others_nonempty hn i) (g i)

def scaledHoleMatrix {n : ℕ} (g : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i j : Fin n) : ℝ :=
  g i j/(v i*v j)

def BalancedRows {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) : Prop :=
  ∀ i, (1:ℝ)/4 ≤ rowPeak hn g i ∧ rowPeak hn g i ≤ 1




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

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Switching

variable {n : ℕ}

noncomputable def rawActivity (G : GraphInput) (x : ℝ) (a b : Fin G.n) : ℝ :=
  if (min a b,max a b)∈G.edges then 1 else x

lemma rawActivity_pos (G : GraphInput) (x : ℝ) (hx : 0 < x) : ∀ a b,0 < rawActivity G x a b := by
  intro a b
  unfold rawActivity
  split_ifs <;> positivity

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision Hierarchy Transport
open scoped Classical

noncomputable def cooling (n : ℕ) : ℝ := (1+1/(n:ℝ))⁻¹

lemma cooling_pos (n : ℕ) : 0 < cooling n := by unfold cooling; positivity

lemma cooling_le_one (n : ℕ) : cooling n ≤ 1 := by
  unfold cooling
  apply inv_le_one_of_one_le₀
  have h : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
  linarith

noncomputable def raw (G : GraphInput) (j : ℕ) : Fin G.n → Fin G.n → ℝ :=
  GraphBridge.rawActivity G (cooling G.n^j)

lemma raw_pos (G : GraphInput) (j : ℕ) (a b : Fin G.n) : 0 < raw G j a b :=
  GraphBridge.rawActivity_pos G _ (pow_pos (cooling_pos G.n) j) a b

lemma raw_le_one (G : GraphInput) (j : ℕ) (a b : Fin G.n) : raw G j a b ≤ 1 := by
  unfold raw GraphBridge.rawActivity
  split_ifs
  · rfl
  · exact pow_le_one₀ (cooling_pos G.n).le (cooling_le_one G.n)

lemma raw_cooling (G : GraphInput) (j : ℕ) (a b : Fin G.n) :
    cooling G.n*raw G j a b ≤ raw G (j+1) a b ∧ raw G (j+1) a b ≤ raw G j a b := by
  unfold raw GraphBridge.rawActivity
  split_ifs
  · simpa using And.intro (cooling_le_one G.n) (le_refl (1:ℝ))
  · rw [pow_succ]
    constructor
    · exact le_of_eq (mul_comm _ _)
    · have h := mul_le_mul_of_nonneg_left (cooling_le_one G.n) (pow_pos (cooling_pos G.n) j).le
      simpa using h

lemma raw_zero (G : GraphInput) : raw G 0=(fun _ _=>1) := by
  funext a b
  simp [raw,GraphBridge.rawActivity]

structure ScaleState (G : GraphInput) (j : ℕ) where
  scale : Fin G.n → ℝ
  positive : ∀ i,0 < scale i
  upper : ∀ i,scale i ≤ (2:ℝ)^j

variable {G : GraphInput} {j K S : ℕ}

noncomputable def ScaleState.activity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => raw G j a b*s.scale a*s.scale b

noncomputable def ScaleState.nextActivity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => raw G (j+1) a b*s.scale a*s.scale b

lemma ScaleState.activity_pos (s : ScaleState G j) (a b : Fin G.n) : 0 < s.activity a b :=
  mul_pos (mul_pos (raw_pos G j a b) (s.positive a)) (s.positive b)

lemma ScaleState.nextActivity_pos (s : ScaleState G j) (a b : Fin G.n) : 0 < s.nextActivity a b :=
  mul_pos (mul_pos (raw_pos G (j+1) a b) (s.positive a)) (s.positive b)

lemma ScaleState.cooling (s : ScaleState G j) (a b : Fin G.n) :
    cooling G.n*s.activity a b  ≤  s.nextActivity a b ∧ s.nextActivity a b ≤ s.activity a b := by
  have h := raw_cooling G j a b
  constructor
  · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.1 (s.positive a).le) (s.positive b).le
    simpa [ScaleState.activity,ScaleState.nextActivity,mul_assoc] using hh
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.2 (s.positive a).le) (s.positive b).le

lemma ScaleState.activity_bound (s : ScaleState G j) (a b : Fin G.n) : s.activity a b ≤ (4:ℝ)^j := by
  calc
    _  ≤  1*(2:ℝ)^j*2^j := by
      apply mul_le_mul (mul_le_mul (raw_le_one G j a b) (s.upper a) (s.positive a).le (by norm_num))
        (s.upper b) (s.positive b).le (by positivity)
    _ = (4:ℝ)^j := by rw [one_mul,←mul_pow]; norm_num

noncomputable def initialScaleState (G : GraphInput) (hn : 2 ≤ G.n) : ScaleState G 0 where
  scale _ := (Initializer.initialScale G.n:ℝ)
  positive _ := by exact_mod_cast Initializer.initialScale_pos G.n hn
  upper _ := by
    unfold Initializer.initialScale
    push_cast
    simp only [pow_zero]
    have hs : 1 ≤ Nat.sqrt (G.n-1) := Nat.le_sqrt.mpr (by omega)
    have hs' : (1:ℝ) ≤ Nat.sqrt (G.n-1) := by exact_mod_cast hs
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs'

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

variable {A : Type*} [Fintype A] [Nonempty A]

noncomputable def portion (c : E → WeightedOptions I) (e : E) (i : I) : ℝ := (c e).law i

end MatchingFPRAS.TableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type}

variable {m n : A → ℕ} {f : A×(ℕ×ℕ) → B}

def clip (x : ℕ×ℕ) : ℕ := if x.2.size≤x.1 then x.2 else 0
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type}

def listMin (x : List ℕ×ℕ) : ℕ := x.1.foldl min x.2
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

def bitDenominator (bs : List Bool) : ℕ := bs.foldl (fun a _=>2*a) 1
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeQuad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type}

abbrev Quad (A : Type) := (A×A)×(A×A)
def quadList (q : Quad A) : List A := [q.1.1,q.1.2,q.2.1,q.2.2]
def quadFn (q : Quad A) : Fin 4→A := ![q.1.1,q.1.2,q.2.1,q.2.2]
def quadOfFn (f : Fin 4→A) : Quad A := ((f 0,f 1),(f 2,f 3))

def quads (s : List A) : List (Quad A) := (s.product s).product (s.product s)
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
open TreeTyped Polynomial

abbrev GeometryInput := List ℕ×List Bool

def internalCount (x : GeometryInput) : ℕ := 4*x.2.length
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped Polynomial

def square {A B : Type} (n : ℕ) (a : A) (f : A×(ℕ×ℕ)→B) : List (List B) :=
  (List.range n).map fun i=>(List.range n).map fun j=>f (a,(i,j))

end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableBottleneck Polynomial

abbrev LabelKey := ℕ×ℕ

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStateTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A : Type}
  [DecidableEq I]
  [Inhabited I]
abbrev StateTable (I A : Type) := List (I×A)

def lookup (d : A) (x : StateTable I A×I) : A :=
  ((x.1.filter (fun z=>decide (z.1=x.2))).headD (x.2,d)).2

def stateRep (keys : List I) (s : I→A) : StateTable I A := keys.map (fun i=>(i,s i))

def setState (x : StateTable I A×(I×A)) : StateTable I A :=
  x.1.map fun z=>(z.1,if z.1=x.2.1 then x.2.2 else z.2)

def setPair (x : StateTable I A×((I×I)×(A×A))) : StateTable I A :=
  setState (setState (x.1,(x.2.1.1,x.2.2.1)),(x.2.1.2,x.2.2.2))
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClosureReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma orderedEnum_lt {A : Type} [Fintype A] [LinearOrder A]
    (i j : Fin (Fintype.card A)) : orderedEnum A i < orderedEnum A j ↔ i < j := by
  change ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ) i).val <
    ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ) j).val ↔ _
  exact ((Finset.univ : Finset A).orderIsoOfFin (Finset.card_univ)).lt_iff_lt
end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeNumberedCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
def index (a : A) : ℕ := ((UnitRefresh.orderedEnum A).symm a).val
lemma index_injective : Function.Injective (index (A:=A)) := by
  intro a b h
  exact (UnitRefresh.orderedEnum A).symm.injective (Fin.ext h)
lemma index_le (a b : A) : index a ≤ index b ↔ a ≤ b := by
  change (UnitRefresh.orderedEnum A).symm a ≤ (UnitRefresh.orderedEnum A).symm b ↔ _
  rw [←not_lt,←not_lt,←UnitRefresh.orderedEnum_lt]
  simp

end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeNumberedSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
def embedding : A ↪ ℕ := ⟨index,index_injective⟩
def set (s : Finset A) : Finset ℕ := s.map embedding
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped ExecutableLadder

variable {C E : Type}
  [LinearOrder E]
  [Inhabited E]
abbrev MarkInput (C E : Type) := (C×StateTable E (List Bool))×Finset E
abbrev Marks (E : Type) := List (E×ℕ)

def marksRep (s : Finset E) (f : E→Fin 3) : Marks E :=
  (s.sort (·≤·)).map (fun e=>(e,(f e).val))
end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped ExecutableLadder ExecutableMarking TreeTyped.Numbered UnitRefresh

variable {E : Type} [Fintype E] [LinearOrder E]
def numericMarks (s : Finset E) (f : E→Fin 3) : Marks ℕ :=
  (s.sort (·≤·)).map (fun e=>(index e,(f e).val))
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableBottleneck Finset

abbrev key {n H : ℕ} {B : Fin n→Fin n→ℚ} (l : NumberedHierarchy.Label B H) : LabelKey := (l.1.val,l.2.val.val)

local instance instLinearOrderLabelFin {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
local instance (priority := 2000) instLELabelFin {n H : ℕ} (B : Fin n→Fin n→ℚ) : LE (NumberedHierarchy.Label B H) := (NumberedHierarchy.labelOrder B H).toLE
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped ExecutableBottleneck

attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance (priority := 2000) instLEProdOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) instLTProdOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) instLESumOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A⊕B) := Transport.sumOrder.toLE
local instance (priority := 2000) instLTSumOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A⊕B) := Transport.sumOrder.toLT
local instance (priority := 2000) instPreorderSumOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A⊕B) := Transport.sumOrder.toPreorder

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type}
  [DecidableEq A]
  [BEq A]
  [LawfulBEq A]

def indexStep (x : A×(A×ℕ)) : A×ℕ := (x.2.1,if x.2.1=x.1 then 0 else x.2.2+1)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev State := ℕ×(Bags×Table)

def update (x : ((Bags×Parents)×(ℕ×Table))×(ℕ×ℕ)) : Table :=
  tabulate entry (context x.1,x.2)

lemma tabulate_materialized {X : Type} (f : X×(ℕ×ℕ) → ℕ) (x : X) (m B : ℕ) :
    tabulate f (x,(m,B))=UnitRefresh.Materialized.tabulate m B (fun a r=>f (x,(a.val,r))) :=
  tabulate_eq (fun ar=>f (x,ar))

lemma update_eq {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (bags : V → Finset (Fin m)) (R : Finset V) (parent : Fin m → Option (Fin m))
    (l : Fin m) (t : Table) (B : ℕ) (ps : Parents)
    (hps : ps.getD l.val (false,0)=match parent l with | none=>(false,0) | some p=>(true,p.val)) :
    update (((activeRep bags R,ps),(l.val,t)),(m,B))=
      UnitRefresh.Materialized.update bags R parent l B t := by
  unfold update context
  simp only [hps,privateNumber_activeRep,sharedNumber_activeRep,totalNumber_activeRep]
  rw [tabulate_materialized]
  unfold UnitRefresh.Materialized.update
  congr 1
  funext a r
  exact entry_eq bags R parent l a t r

def parentTag {m : ℕ} : Option (Fin m) → Bool×ℕ
  | none => (false,0)
  | some p => (true,p.val)
def parentRep {m : ℕ} (p : Fin m → Option (Fin m)) : Parents := List.ofFn (parentTag ∘ p)
@[simp] lemma parentRep_length {m : ℕ} (p : Fin m → Option (Fin m)) : (parentRep p).length=m := by
  simp [parentRep]
@[simp] lemma parentRep_getD {m : ℕ} (p : Fin m → Option (Fin m)) (l : Fin m) :
    (parentRep p).getD l.val (false,0)=parentTag (p l) := by
  simp [parentRep,List.getD,l.isLt]

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

def initial (x : ℕ×ℕ) : Table :=
  tabulate (fun ar : ℕ×(ℕ×ℕ)=>UnitRefresh.pairingCount ar.2.2) (0,x)

def finish (x : Table×ℕ) : ℕ := ((List.range x.2).map fun a=>read (x.1,(a,0))).prod

abbrev CountInput := (Bags×Parents)×List ℕ

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDPEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

abbrev RawCtx := (Bags×Parents)×(ℕ×Table)

def rawTerm (x : (RawCtx×ℕ)×ℕ) : ℕ := term ((context x.1.1,x.1.2),x.2)

def rawEntry (x : RawCtx×(ℕ×ℕ)) : ℕ := entry (context x.1,x.2)
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeClippedDP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def nVertices (o : CountInput) : ℕ := o.1.1.length
def nLabels (o : CountInput) : ℕ := o.1.2.length
def nPlan (o : CountInput) : ℕ := o.2.length
def BInitial (o : CountInput) : ℕ := nVertices o*nLabels o
def capBits (o : CountInput) : ℕ := nVertices o*nPlan o+(BInitial o)^2*nLabels o+1

def initialEntry (x : CountInput×(ℕ×ℕ)) : ℕ := UnitRefresh.pairingCount (min x.2.2 (BInitial x.1))

abbrev UpdateInput := (CountInput×RawCtx)×ℕ
def updateRows (x : UpdateInput) := nLabels x.1.1
def updateColumns (x : UpdateInput) := nVertices x.1.1*min x.2 (nPlan x.1.1)

def cappedEntry (x : UpdateInput×(ℕ×ℕ)) : ℕ := clip (capBits x.1.1.1,rawEntry (x.1.1.2,x.2))

def cappedUpdate (x : UpdateInput) : Table := tabulate cappedEntry (x,(updateRows x,updateColumns x))

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClippedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

abbrev CappedState := CountInput×State

def cappedStep (x : ℕ×CappedState) : CappedState :=
  let o:=x.2.1
  let st:=x.2.2
  let rem:=st.1-1
  (o,(rem,(trim st.2.1 x.1,cappedUpdate ((o,((st.2.1,o.1.2),(x.1,st.2.2))),rem))))

def tableWeightBound (o : CountInput) : ℕ :=
  1+nLabels o*(2+(nVertices o*nPlan o+1)*(4*capBits o+2))

def cappedCount (o : CountInput) : ℕ :=
  finish ((o.2.foldl (fun z l=>cappedStep (l,z)) (o,(o.2.length,(o.1.1,initial (nLabels o,BInitial o))))).2.2.2,nLabels o)
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP

noncomputable def orderedRep {n m : ℕ} (bags : Fin n → Finset (Fin m)) : Bags :=
  List.ofFn (fun i=>bagRep (bags i))

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def skip (x : ℕ×ℕ) : ℕ := if x.1<x.2 then x.1 else x.1+1

def residual (x : Bags×ℕ) : Bags :=
  (List.range (x.1.length-2)).map (fun i=>x.1.getD (skip (i,x.2)) [])

abbrev Context := CountInput

def valid (x : Context×(ℕ×ℕ)) : Bool :=
  let bs:=x.1.1.1
  let b:=x.2.1
  let c:=x.2.2
  decide (b≠bs.length-1) && decide (c∈bs.getD (bs.length-1) []) && decide (c∈bs.getD b [])

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def decodeIndex (x : ℕ×ℕ) : ℕ×ℕ := (x.1/x.2,x.1%x.2)

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def fastBranch (x : Context×ℕ) : ℕ := cappedCount ((residual (x.1.1.1,x.2),x.1.1.2),x.1.2)

def fastEdgeCount (x : Context×(ℕ×ℕ)) : ℕ := if valid x then fastBranch (x.1,x.2.1) else 0
end MatchingFPRAS.ExecutableUnit

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

abbrev Result := List (ℕ×ℕ)
abbrev Frame := ℕ×(ℕ×ℕ)

def unskip (x : ℕ×ℕ) : ℕ := if x.1<x.2 then x.1 else x.1-1

def assembleAt (x : (Frame×Result)×ℕ) : ℕ×ℕ :=
  let n:=x.1.1.1
  let b:=x.1.1.2.1
  let c:=x.1.1.2.2
  let i:=x.2
  if i=n+1 then (b,c) else if i=b then (n+1,c) else
  let z:=x.1.2.getD (unskip (i,b)) (0,0)
  (skip (z.1,b),z.2)

def assemble (x : Frame×Result) : Result :=
  (List.range (x.1.1+2)).map (fun i=>assembleAt (x,i))
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCappedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def capacity (x : Context) : ℕ := x.1.1.length+x.1.2.length+2

def clippedAt (x : (Context×(Frame×Result))×ℕ) : ℕ×ℕ :=
  let r:=assembleAt (x.1.2,x.2)
  (min r.1 (capacity x.1.1),min r.2 (capacity x.1.1))

def clippedAssemble (x : Context×(Frame×Result)) : Result :=
  (List.range (min (x.2.1.1+2) (x.1.1.1.length+2))).map (fun i=>clippedAt (x,i))

def assemblyFoldStep (x : Frame×(Context×Result)) : Context×Result :=
  (x.2.1,clippedAssemble (x.2.1,(x.1,x.2.2)))
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeUnitSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

abbrev Bits := List (List Bool)
abbrev State := Context×(Bits×List Frame)
def nextContext (x : Context×(ℕ×ℕ)) : Context :=
  ((residual (x.1.1.1,x.2.1),x.1.1.2),x.1.2)
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def DescentInvariant (a : Context×Bits) (k : ℕ) (z : State) : Prop :=
  z.1.1.1.length≤a.1.1.1.length ∧
  (∀ b∈z.1.1.1,b∈a.1.1.1) ∧ z.1.1.2=a.1.1.2 ∧ z.1.2=a.1.2 ∧ z.2.1=a.2 ∧
  z.2.2.length+k≤a.1.1.1.length ∧
  ∀ f∈z.2.2,f.1≤a.1.1.1.length ∧ f.2.1≤a.1.1.1.length*a.1.1.2.length ∧ f.2.2≤a.1.1.1.length*a.1.1.2.length
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_DPEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}

def RowBound (t : Table) (w : Fin m → ℕ) : Prop := ∀ a r,read t a.val r ≤ w a

def mergeEnvelope (w : Fin m → ℕ) (l p : Fin m) (s : ℕ) : Fin m → ℕ :=
  fun a=>if a=l then 1 else if a=p then 2^s*w l*w p else w a

omit [Fintype V] in
lemma entry_rowBound (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (t : Table) (w : Fin m → ℕ)
    (_ : ∀ a,1≤w a) (ht : RowBound t w) :
    ∀ a r,entry bags R parent l a t r ≤
      match parent l with
      | none => w a
      | some p => mergeEnvelope w l p (sharedCount bags R l) a := by
  intro a r
  unfold entry
  cases hp : parent l with
  | none =>
    simp only
    split_ifs with h
    · subst a; exact ht l _
    · exact ht a r
  | some p =>
    simp only
    unfold mergeEnvelope
    split_ifs with h h'
    · exact le_rfl
    · subst a
      calc
        _ ≤ ∑ k∈range (sharedCount bags R l+1),
            (sharedCount bags R l).choose k*w l*w p := by
          apply sum_le_sum
          intro k hk
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (ht l _)) (ht p _)
        _ = 2^(sharedCount bags R l)*w l*w p := by
          rw [←sum_mul,←sum_mul,Nat.sum_range_choose]
    · exact ht a r

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ClippedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}
def nextEnvelope (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ) : Fin m → ℕ :=
  match parent l with | none=>w | some p=>mergeEnvelope w l p (sharedCount bags R l)
end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClippedCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Finset

def runCapped (o : CountInput) : List ℕ → Bags → Table → Bags×Table
  | [],bs,t => (bs,t)
  | l::ls,bs,t => runCapped o ls (trim bs l)
      (cappedUpdate ((o,((bs,o.1.2),(l,t))),ls.length))
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def unwindClipped (cap : Context) (fs : List Frame) (r : Result) : Result :=
  (fs.foldl (fun z f=>assemblyFoldStep (f,z)) (cap,r)).2

open UnitRefresh.Materialized

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

abbrev Key := (ℕ×ℕ)×ℕ

def ordered (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then x else (x.2,x.1)

def rowKey (x : Result×ℕ) : Key :=
  (ordered (x.2,(x.1.getD x.2 (0,0)).1),(x.1.getD x.2 (0,0)).2)

def entryIndex (x : (List Key×Result)×ℕ) : ℕ := x.1.1.idxOf (rowKey (x.1.2,x.2))

def matching (x : List Key×Result) : Finset ℕ :=
  ((List.range x.2.length).map (fun i=>entryIndex (x,i))).toFinset

abbrev Input := (List Key×CountInput)×Bits
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

def sharedKey (x : Bags×Key) : Bool :=
  decide (x.2.2∈x.1.getD x.2.1.1 [] ∧ x.2.2∈x.1.getD x.2.1.2 [])

open Transport UnitRefresh

attribute [local instance] Transport.prodOrder
local instance (priority := 2000) instLTProdOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) instPreorderProdOfLinearOrder_solutions {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)} {a : Bags}
lemma sym_mk_inf_sup (s : Sym2 (Fin n)) : s(s.inf,s.sup)=s :=
  (Sym2.sortEquiv.symm_apply_apply s)
lemma sym_inf_mem (s : Sym2 (Fin n)) : s.inf∈s := by
  have h:=Sym2.mem_mk_left s.inf s.sup
  rwa [sym_mk_inf_sup] at h
lemma sym_sup_mem (s : Sym2 (Fin n)) : s.sup∈s := by
  have h:=Sym2.mem_mk_right s.inf s.sup
  rwa [sym_mk_inf_sup] at h
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshNumbered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.prodOrder
local instance (priority := 2000) instLEProdOfLinearOrder_solutions_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) instLTProdOfLinearOrder_solutions_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
omit [Fintype V] in
lemma source_inf_mem (s : Sym2 V) : s.inf∈s := by
  have h:=Sym2.mem_mk_left s.inf s.sup
  have hs : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
  rwa [hs] at h
omit [Fintype V] in
lemma source_sup_mem (s : Sym2 V) : s.sup∈s := by
  have h:=Sym2.mem_mk_right s.inf s.sup
  have hs : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
  rwa [hs] at h
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A C : Type}
  [LinearOrder A]

namespace FiniteReach
abbrev Input (C A : Type) := (C×Finset A)×Finset A
variable (p : C×(A×A) → Bool)
def grow (x : Input C A) : Finset A :=
  x.2 ∪ x.1.2.filter (fun b=>∃ a∈x.2,p (x.1.1,(a,b))=true)
def sweep (x : Input C A) : Input C A := (x.1,grow p x)
def reach (x : Input C A) : Finset A := (countDown (fun x=>sweep p x.2) x.1.2.card x).2

end FiniteReach
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {A C : Type}
  [LinearOrder A]
attribute [local instance] Transport.Sparse.finsetOrder

variable (p : C×(A×A) → Bool)
def adjacent (x : (C×Finset A)×(A×A)) : Bool :=
  decide (x.2.1≠x.2.2) && (decide (x.2.1∈x.1.2) && (decide (x.2.2∈x.1.2) && p (x.1.1,x.2)))
variable {p}

abbrev ComponentInput (C A : Type) := ((C×Finset A)×Finset A)×A

def component (x : ComponentInput C A) : Finset A :=
  x.1.2 ∩ FiniteReach.reach (adjacent p) (((x.1.1.1,x.1.2),x.1.1.2),{x.2})

def allComponents (x : (C×Finset A)×Finset A) : Finset (Finset A) :=
  x.2.image (fun a=>component (p:=p) (x,a))

def discrepancies (x : (C×Finset A)×(Finset A×Finset A)) : Finset (Finset A) :=
  (allComponents (p:=p) (x.1,x.2.1∪x.2.2)).filter (fun s=>¬s⊆x.2.1∩x.2.2)
end MatchingFPRAS.TreeTyped.SparseProgram

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

variable {E C : Type}
  [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev PairState (E : Type) := Finset E×Finset E
abbrev CycleInput (C E : Type) := (C×Finset E)×PairState E

def exchange (x : PairState E×Finset E) : Finset E := (x.1.1\x.2)∪(x.1.2∩x.2)

def cycle (p : C×(E×E)→Bool) (x : CycleInput C E×Finset E) : PairState E :=
  if x.2∈allComponents (p:=p) (x.1.1,x.1.2.1∪x.1.2.2) then
    (exchange (x.1.2,x.2),exchange ((x.1.2.2,x.1.2.1),x.2)) else x.1.2

end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]
abbrev SwitchInput (C E V : Type) := (C×Finset E)×(Quad V×Quad E)
def switchValid (p : C×(E×(V×V))→Bool) (x : SwitchInput C E V) : Bool :=
  decide (Function.Injective (quadFn x.2.1) ∧
    (∀ i : Fin 4,p (x.1.1,(quadFn x.2.2 i,(quadFn x.2.1 i,quadFn x.2.1 (i+1))))=true) ∧
    x.2.2.1.1≠x.2.2.2.1 ∧ x.2.2.1.1∈x.1.2 ∧ x.2.2.2.1∈x.1.2)

end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeSwitchRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairSet (x : E×E) : Finset E := {x.1,x.2}

def switchEdit (x : Finset E×Quad E) : Finset E :=
  (x.1\pairSet (x.2.1.1,x.2.2.1))∪pairSet (x.2.1.2,x.2.2.2)

abbrev RawSwitchInput (C E V : Type) := (C×(Finset V×Finset E))×Finset E
def switchList (p : C×(E×(V×V))→Bool) (x : RawSwitchInput C E V) : List (Quad V×Quad E) :=
  ((quads (x.1.2.1.sort (·≤·))).product (quads (x.1.2.2.sort (·≤·)))).filter
    (fun q=>switchValid p ((x.1.1,x.2),q))

def switchRaw (p : C×(E×(V×V))→Bool) (x : RawSwitchInput C E V) : Finset (Finset E) :=
  ((switchList p x).map fun q=>switchEdit (x.2,q.2)).toFinset

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

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]

def matchingCheck (p : C×(E×V)→Bool) (x : (C×Finset V)×Finset E) : Bool :=
  decide (∀ v∈x.1.2,(x.2.filter (fun e=>p (x.1.1,(e,v))=true)).card=1)
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

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def certify (p : C×(E×V)→Bool) (x : (C×Finset V)×Finset (Finset E)) : Finset (Finset E) :=
  x.2.filter (fun a=>matchingCheck p (x.1,a)=true)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColorRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E C : Type}
  [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder

def colorRaw (p : C×(E×E)→Bool) (x : (C×Finset E)×Finset E) : Finset (Finset E) :=
  x.2.biUnion fun e=>(x.1.2.filter (fun f=>p (x.1.1,(f,e))=true)).image fun f=>insert f (x.2.erase e)
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev TableInput (C E V : Type) := (C×(Finset V×Finset E))×Finset E

def degree (n : ℕ) : ℕ := 8*(n/2).choose 2
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePairTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type}
  [LinearOrder E]
  [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev PairInput (C E V : Type) := (C×(Finset V×Finset E))×PairState E

end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.SparseProgram

def incident (x : (ℕ×ℕ)×ℕ) : Bool := decide (x.1.1=x.2 ∨ x.1.2=x.2)

def same (x : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  decide ((x.1.1=x.2.1 ∧ x.1.2=x.2.2) ∨ (x.1.1=x.2.2 ∧ x.1.2=x.2.1))

def adjacent (x : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  incident (x.1,x.2.1) || incident (x.1,x.2.2)
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeIndexedPairCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def endpointRep (s : Sym2 V) : ℕ×ℕ := (index s.inf,index s.sup)
end MatchingFPRAS.ExecutablePair

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeStateNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E : Type}
  [DecidableEq I]
  [Inhabited I]
  [LinearOrder E]
abbrev StateEnvelope (I E : Type) := List I×Finset E

def normalizeState (x : StateEnvelope I E×StateTable I (Finset E)) : StateTable I (Finset E) :=
  x.1.1.map (fun i=>(i,lookup ∅ (x.2,i)∩x.1.2))
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLocalSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type}
variable [DecidableEq I] [Inhabited I] [Inhabited A]
local instance treeLocalSamplerUpdateInhabited : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩

abbrev LocalContext (C I A B : Type) := C×(StateTable I A×B)
abbrev LocalPairInput (C I A B : Type) := (C×(I×I))×((A×A)×B)
abbrev LocalRefreshInput (C I B : Type) := (C×I)×B

def localPair (p : LocalPairInput C I A B→A×A)
    (x : LocalContext C I A B×(I×I)) : StateTable I A :=
  setPair (x.1.2.1,(x.2,p ((x.1.1,x.2),
    ((lookup default (x.1.2.1,x.2.1),lookup default (x.1.2.1,x.2.2)),x.1.2.2))))

def localRefresh (r : LocalRefreshInput C I B→A)
    (x : LocalContext C I A B×I) : StateTable I A :=
  setState (x.1.2.1,(x.2,r ((x.1.1,x.2),x.1.2.2)))

def localSampler (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
    (x : LocalContext C I A B×Option (Replica.Update I)) : StateTable I A :=
  x.2.elim x.1.2.1 (Sum.elim (fun ij=>localPair p (x.1,ij)) (fun i=>localRefresh r (x.1,i)))
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I C : Type}
  [Inhabited I]
  [LinearOrder I]
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance instInhabitedUpdate : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩
abbrev ScanSetup (C I : Type) := C×(Finset I×Finset I)

def updateList (g : C×(I×I)→Bool) (x : ScanSetup C I) : List (Replica.Update I) :=
  (((x.2.1.sort (·≤·)).product (x.2.1.sort (·≤·))).filter (fun ij=>g (x.1,ij))).map Sum.inl++
    (x.2.2.sort (·≤·)).map Sum.inr

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type}
variable [LinearOrder I] [Inhabited I] [Inhabited A]
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance treeScanUpdateInhabited : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩
abbrev ScanInput (C I A B : Type) := (ScanSetup C I×StateTable I A)×(List Bool×B)

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E B C : Type}
variable [LinearOrder I] [Inhabited I] [LinearOrder E]
attribute [local instance] Transport.prodOrder Transport.sumOrder
abbrev RunSetup (C I E : Type) := ScanSetup C I×StateEnvelope I E
abbrev RunState (C I E : Type) := RunSetup C I E×StateTable I (Finset E)

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped ExecutableLadder

abbrev RefreshSetup := List ExecutableRefresh.Key×ExecutableDP.CountInput
abbrev Bits := List Bool×ExecutableUnit.Bits

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLadderIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder

attribute [local instance] Transport.prodOrder Transport.sumOrder
variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
local instance instInhabitedUpdate : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩

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
open TreeTyped TreeTyped.Numbered ExecutableLadder Turing

variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
def numericState (x : StateTable I (Finset ℕ)) : StateTable ℕ (Finset ℕ) := x.map (fun a=>(index a.1,a.2))
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

attribute [local instance] Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)
variable {T q : ℕ} [Inhabited (Slot T q)]

def localBitsRep {k : ℕ} (b : LocalBits V k) : Bits :=
  (List.ofFn b.1,List.ofFn (fun i=>List.ofFn (b.2 i)))
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered Replica.Ladder

def coordinateEquiv (T q : ℕ) : Slot T q ≃ Fin ((T+1)*q) :=
  ({toFun:=ofLex,invFun:=toLex,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl} : Slot T q≃Fin (T+1)×Fin q).trans finProdFinEquiv
lemma coordinate_le {T q : ℕ} (a b : Slot T q) : coordinateEquiv T q a ≤ coordinateEquiv T q b ↔ a≤b := by
  change (ofLex a).2.val+q*(ofLex a).1.val≤(ofLex b).2.val+q*(ofLex b).1.val ↔ a≤b
  rw [Prod.Lex.le_iff]
  have ha:=(ofLex a).2.isLt
  have hb:=(ofLex b).2.isLt
  change _ ↔ ((ofLex a).1.val<(ofLex b).1.val ∨ (ofLex a).1=(ofLex b).1 ∧ (ofLex a).2.val≤(ofLex b).2.val)
  constructor
  · intro h
    by_cases hlt : (ofLex a).1.val<(ofLex b).1.val
    · exact Or.inl hlt
    · have hge : (ofLex b).1.val≤(ofLex a).1.val := Nat.le_of_not_gt hlt
      have he : (ofLex a).1.val=(ofLex b).1.val := by
        by_contra hh
        have hs : (ofLex b).1.val+1≤(ofLex a).1.val := by omega
        have hm:=Nat.mul_le_mul_left q hs
        nlinarith
      exact Or.inr ⟨Fin.ext he,by rw [he] at h; omega⟩
  · rintro (h|⟨h,h'⟩)
    · have hm:=Nat.mul_le_mul_left q h
      nlinarith
    · rw [h]; omega

def coordinateOrderIso (T q : ℕ) : Slot T q ≃o Fin ((T+1)*q) :=
  { coordinateEquiv T q with map_rel_iff' := fun {a b}=>coordinate_le a b }
lemma slot_card (T q : ℕ) : Fintype.card (Slot T q)=(T+1)*q := by simp [Slot]
def numberOrderIso (T q : ℕ) : Slot T q ≃o Fin ((T+1)*q) := by
  let e : Slot T q ≃o Fin (Fintype.card (Slot T q)) :=
    { toEquiv := (UnitRefresh.orderedEnum (Slot T q)).symm
      map_rel_iff' := by
        intro a b
        change ((UnitRefresh.orderedEnum (Slot T q)).symm a).val ≤
          ((UnitRefresh.orderedEnum (Slot T q)).symm b).val ↔ a ≤ b
        exact index_le a b }
  exact e.trans (Fin.castOrderIso (slot_card T q))
end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

abbrev TierInput := (ℕ×List Bool)×ℕ

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

abbrev SampleBits := List (List Bool×Bits)×StateTable ℕ (List Bool)

open Replica.Ladder Transport

attribute [local instance] Transport.prodOrder Transport.sumOrder
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

abbrev word (k : ℕ) : Experiment (List Bool) := OnlineWord.prepend k []

variable {A : Type}

def words (x : ℕ×ℕ) : Experiment (List (List Bool)) :=
  OnlineTree.traverseM word (List.replicate x.2 x.1)

def localWords (x : ℕ×ℕ) : Experiment NumericLadder.Bits :=
  (word x.1).bind (fun w=>(words x).map (Prod.mk w))

def scan (x : ℕ×ℕ) : Experiment (List Bool×NumericLadder.Bits) :=
  (word x.1).bind (fun w=>(localWords x).map (Prod.mk w))

def scans (x : (ℕ×ℕ)×ℕ) : Experiment (List (List Bool×NumericLadder.Bits)) :=
  OnlineTree.traverseM scan (List.replicate x.2 x.1)

def markWord (x : ℕ×ℕ) : Experiment (ℕ×List Bool) := (word x.2).map (Prod.mk x.1)

def markRequests (x : ℕ×List ℕ) : List (ℕ×ℕ) := x.2.map (fun i=>(i,x.1))
def marks (x : ℕ×List ℕ) : Experiment (List (ℕ×List Bool)) :=
  OnlineTree.traverseM markWord (markRequests x)

abbrev Request := ((ℕ×ℕ)×ℕ)×(ℕ×List ℕ)
def sample (x : Request) : Experiment NumericMarking.SampleBits :=
  (scans x.1).bind (fun s=>(marks x.2).map (Prod.mk s))
def many (x : ℕ×Request) : Experiment (List NumericMarking.SampleBits) :=
  OnlineTree.traverseM sample (List.replicate x.1 x.2)
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineSampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open PhysicalStream

abbrev LocalRandom (N k : ℕ) := Bits k × (Fin N → Bits k)
abbrev ScanRandom (N k : ℕ) := Bits k × LocalRandom N k
def localRep {N k : ℕ} (b : LocalRandom N k) : NumericLadder.Bits :=
  (List.ofFn b.1,List.ofFn (fun i=>List.ofFn (b.2 i)))
def scanRep {N k : ℕ} (b : ScanRandom N k) : List Bool×NumericLadder.Bits :=
  (List.ofFn b.1,localRep b.2)

abbrev Random (N k r m km : ℕ) := (Fin r→ScanRandom N k)×(Fin m→Bits km)
def sampleRep {N k r m km : ℕ} (keys : Fin m→ℕ) (bs : Random N k r m km) : NumericMarking.SampleBits :=
  (List.ofFn (fun i=>scanRep (bs.1 i)),List.ofFn (fun i=>(keys i,List.ofFn (bs.2 i))))
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeParentTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableBottleneck

local instance instLinearOrderLabelFin_1 {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableBottleneck Polynomial

def incident (x : ℕ×(ℕ×ℕ)) : Bool := decide (x.1=x.2.1 ∨ x.1=x.2.2)

local instance instLinearOrderLabelFin_2 {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableBottleneck

local instance instLinearOrderLabelFin_3 {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
def orderedIso (A : Type) [Fintype A] [LinearOrder A] : Fin (Fintype.card A)≃o A where
  toEquiv:=UnitRefresh.orderedEnum A
  map_rel_iff' := by intro a b; rw [←not_lt,←not_lt,UnitRefresh.orderedEnum_lt]
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
abbrev reindex : V→V→ℚ := fun i j=>B (e i) (e j)
lemma component_reindex (t : ℚ) (x y : V) :
    y∈component (reindex B e) t x ↔ e y∈component B t (e x) := by
  simp only [component,mem_filter,mem_univ,true_and,related,reindex,e.injective.eq_iff]
lemma root_reindex (t : ℚ) (x : V) : e (root (reindex B e) t x)=root B t (e x) := by
  apply le_antisymm
  · have hm : e.symm (root B t (e x)) ∈ component (reindex B e) t x := by
      rw [component_reindex,OrderIso.apply_symm_apply]
      exact root_mem B t (e x)
    have hle := Finset.min'_le (component (reindex B e) t x) _ hm
    have hh:=e.monotone hle
    simpa only [OrderIso.apply_symm_apply,root] using hh
  · exact Finset.min'_le (component B t (e x)) _
      ((component_reindex B e t x _).mp (root_mem (reindex B e) t x))

def componentReindex (t : ℚ) : NumberedComponent (reindex B e) t≃NumberedComponent B t where
  toFun x:=⟨e x.val,by rw [←root_reindex B e t x.val,x.property]⟩
  invFun x:=⟨e.symm x.val,by
    apply e.injective
    rw [root_reindex,OrderIso.apply_symm_apply,x.property]⟩
  left_inv x:=Subtype.ext (e.symm_apply_apply x.val)
  right_inv x:=Subtype.ext (e.apply_symm_apply x.val)
def labelReindex (H : ℕ) : Label (reindex B e) H≃Label B H :=
  Equiv.sigmaCongrRight (fun k=>componentReindex B e ((2:ℚ)^k.val))

attribute [local instance] labelOrder
local instance (priority := 2000) instLELabel {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE

def labelOrderReindex (H : ℕ) : Label (reindex B e) H≃o Label B H where
  toEquiv:=labelReindex B e H
  map_rel_iff' := by
    intro a b
    change toLex (a.1,e a.2.val)≤toLex (b.1,e b.2.val) ↔
      toLex (a.1,a.2.val)≤toLex (b.1,b.2.val)
    simp only [Prod.Lex.le_iff,ofLex_toLex,e.le_iff_le]

open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
omit [Fintype V] [Fintype W] in
include hsym in
lemma reindex_symm : ∀ a b,reindex B e a b=reindex B e b a := fun a b=>hsym (e a) (e b)
omit [Fintype V] [Fintype W] in
include htri in
lemma reindex_tri : ∀ x y z,x≠y → x≠z → y≠z →
    min (reindex B e x z) (reindex B e z y) ≤ reindex B e x y :=
  fun x y z hxy hxz hyz=>htri (e x) (e y) (e z) (e.injective.ne hxy) (e.injective.ne hxz) (e.injective.ne hyz)
end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

@[instance_reducible] def ordinaryLabelFintype (H : ℕ) : Fintype (Label B H) := inferInstance

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeInitialMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

abbrev InitialInput := List Key×CountInput

open Turing

end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeRankPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableDP Polynomial

def rankLe (a b : ℕ×ℕ) : Prop := b.1<a.1 ∨ (a.1=b.1 ∧ a.2≤b.2)
instance instDecidableRelProdNatRankLe : DecidableRel rankLe := fun a b=>inferInstanceAs (Decidable (b.1<a.1 ∨ (a.1=b.1 ∧ a.2≤b.2)))
instance instIsTransProdNatRankLe : IsTrans (ℕ×ℕ) rankLe := ⟨by intro a b c; simp only [rankLe]; omega⟩
instance instTotalProdNatRankLe : Std.Total rankLe := ⟨by intro a b; simp only [rankLe]; omega⟩
instance instAntisymmProdNatRankLe : Std.Antisymm rankLe := ⟨by intro a b hab hba; simp only [rankLe] at *; apply Prod.ext <;> omega⟩

def rankEntries (rs : List ℕ) : List (ℕ×ℕ) := (List.range rs.length).map fun i=>(rs.getD i 0,i)
def rankPlan (rs : List ℕ) : List ℕ := ((rankEntries rs).insertionSort rankLe).map Prod.snd
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Subdivision Switching

variable {n : ℕ}
def pairIndex (he : Even n) (i : Fin n) : Fin n :=
  if hi : i.val%2=0 then ⟨i.val+1,by obtain ⟨k,hk⟩:=he; have h:=i.isLt; omega⟩
  else ⟨i.val-1,by have h:=i.isLt; omega⟩
lemma pairIndex_ne (he : Even n) (i : Fin n) : pairIndex he i≠i := by
  intro h
  have hh:=congrArg Fin.val h
  unfold pairIndex at hh
  split_ifs at hh <;> simp only at hh <;> omega

attribute [local instance] NumberedHierarchy.labelOrder 
attribute [local instance] prodOrder sumOrder

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder

def rangeFromList {A : Type} (xs : List A) : Finset ℕ := (List.range xs.length).toFinset

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder

def mateIndex (n : ℕ) : ℕ := if n%2=0 then n+1 else n-1

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped

variable {C E : Type}
  [LinearOrder E]
  [Inhabited E]

def zeroMarks (xs : Marks E) : Bool := xs.all (fun z=>decide (z.2=0))

def probeExpected (x : E×(E×ℕ)) : ℕ := if x.2.1=x.1 then 2 else 0

def probeFlag (x : E×Marks E) : Bool :=
  x.2.any (fun z=>decide (z.1=x.1)) && x.2.all (fun z=>decide (z.2=probeExpected (x.1,z)))

def eraseMark (x : E×Marks E) : Marks E := x.2.filter (fun z=>decide (z.1≠x.1))
end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageStatisticsCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableStatistics
open TreeTyped ExecutableMarking

variable {C E : Type}
  [LinearOrder E]
  [Inhabited E]
variable {S : ℕ} (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
def sampleRep : List (Marks E) := List.ofFn (fun i=>marksRep (s i) (m i))
def scalarA (i : Fin S) : ℚ := if ∀ e∈s i,m i e=0 then 1 else 0
def scalarD (r : E→ℚ) (i : Fin S) : ℚ := if ∀ e∈s i,m i e=0 then ∏ e∈s i,r e else 0
def scalarProbe (r : E→ℚ) (e : E) (i : Fin S) : ℚ :=
  if e∈s i ∧ ∀ a∈s i,m i a=if a=e then 2 else 0 then ∏ a∈s i\{e},r a else 0
end MatchingFPRAS.ExecutableStatistics

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {E A : Type} [Fintype E] [LinearOrder E]
def extend (d : A) (f : E→A) (i : ℕ) : A :=
  if h:i<Fintype.card E then f (UnitRefresh.orderedEnum E ⟨i,h⟩) else d
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset

def cooling (n : ℕ) : ℚ := (1+1/(n:ℚ))⁻¹
lemma cooling_cast (n : ℕ) : (cooling n:ℝ)=Trial.cooling n := by
  simp [cooling,Trial.cooling]

def raw (G : GraphInput) (j : ℕ) (a b : Fin G.n) : ℚ :=
  if (min a b,max a b)∈G.edges then 1 else cooling G.n^j
lemma raw_cast (G : GraphInput) (j : ℕ) (a b : Fin G.n) :
    (raw G j a b:ℝ)=Trial.raw G j a b := by
  unfold raw Trial.raw GraphBridge.rawActivity
  split_ifs <;> simp [cooling_cast]

structure ScaleState (G : GraphInput) (j : ℕ) where
  scale : Fin G.n → ℚ
  positive : ∀ i,0 < scale i
  upper : ∀ i,scale i≤2^j

def ScaleState.toReal {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Trial.ScaleState G j where
  scale i:=(s.scale i:ℝ)
  positive i:=by exact_mod_cast s.positive i
  upper i:=by exact_mod_cast s.upper i

def ScaleState.activity {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b=>raw G j a b*s.scale a*s.scale b

def ScaleState.nextActivity {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b=>raw G (j+1) a b*s.scale a*s.scale b
lemma ScaleState.activity_cast {G : GraphInput} {j : ℕ} (s : ScaleState G j) :
    (fun a b=>(s.activity a b:ℝ))=s.toReal.activity := by
  funext a b
  simp only [ScaleState.activity,Trial.ScaleState.activity,Rat.cast_mul,raw_cast,ScaleState.toReal]
lemma ScaleState.nextActivity_cast {G : GraphInput} {j : ℕ} (s : ScaleState G j) :
    (fun a b=>(s.nextActivity a b:ℝ))=s.toReal.nextActivity := by
  funext a b
  simp only [ScaleState.nextActivity,Trial.ScaleState.nextActivity,Rat.cast_mul,raw_cast,ScaleState.toReal]
lemma ScaleState.activity_pos {G : GraphInput} {j : ℕ} (s : ScaleState G j) (a b : Fin G.n) :
    0 < s.activity a b := by
  have h:=s.toReal.activity_pos a b
  rw [←s.activity_cast] at h
  dsimp only at h
  exact_mod_cast h
lemma ScaleState.nextActivity_pos {G : GraphInput} {j : ℕ} (s : ScaleState G j) (a b : Fin G.n) :
    0 < s.nextActivity a b := by
  have h:=s.toReal.nextActivity_pos a b
  rw [←s.nextActivity_cast] at h
  dsimp only at h
  exact_mod_cast h

def initialScaleState (G : GraphInput) (hn : 2≤G.n) : ScaleState G 0 where
  scale _:=Initializer.initialScale G.n
  positive _:=Initializer.initialScale_pos G.n hn
  upper i:=by
    have h:=(Trial.initialScaleState G hn).upper i
    change (Initializer.initialScale G.n:ℝ)≤2^0 at h
    exact_mod_cast h
end MatchingFPRAS.FiniteTrial

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
open Finset Transport

variable {V : Type*} [LinearOrder V]
def sampleAverage {Ω : Type*} {S : ℕ} (f : Ω → ℚ) (x : Fin S → Ω) : ℚ :=
  (∑ i,f (x i))/(S:ℚ)
attribute [local instance] NumberedHierarchy.labelOrder 
attribute [local instance] prodOrder sumOrder
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
open TreeTyped TreeTyped.Numbered ExecutableStatistics ExecutableLadder

abbrev Bindings := List ((ℕ×ℕ)×ℕ)

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableBottleneck ExecutableSource
open Finset Transport

variable {E : Type} [DecidableEq E]
def selectedMarks (s : Finset E) (m : ↥s→Fin 3) (e : E) : Fin 3 :=
  if h:e∈s then m ⟨e,h⟩ else 0
attribute [local instance] NumberedHierarchy.labelOrder 
attribute [local instance] prodOrder sumOrder
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBindings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance (priority := 2000) instLEProdOfLinearOrder_solutions_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) instLTProdOfLinearOrder_solutions_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) instPreorderProdOfLinearOrder_solutions_1 {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.prodOrder Transport.sumOrder

abbrev StageControls := ((List Bool×List Bool)×ℕ)×(List Bool×List Bool)

open Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineRequest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Transport ExecutableSource NumericLadder
open TreeTyped.Numbered UnitRefresh
open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.prodOrder Transport.sumOrder

abbrev PrecisionData := ScanInput×(ℕ×ℕ)

def scanError (x : PrecisionData) : ℕ :=
  2*(1+(x.1.1.2.2*(ladderQ x.1.1.1.1 x.1.1.1.2)^2+ladderQ x.1.1.1.1 x.1.1.1.2))+
  4*(8*x.2.1^2+4*x.2.1+3)+2*x.1.1.1.1^2*x.2.2

def precisionPlan (x : PrecisionData) : ((ℕ×ℕ)×ℕ)×ℕ :=
  (((Nat.clog 2 (discreteLadderSteps x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2 *scanError x*x.1.2),
      x.1.1.1.1),discreteLadderSteps x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2),
    Nat.clog 2 (6*x.2.1*x.1.2))

end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

lemma clog_two_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=m)).le
lemma bitPrecision_le (R : ℕ) (η : ℚ) : bitPrecision R η ≤ R*⌈η⁻¹⌉₊ :=
  clog_two_le_self _
lemma sym2_card_le_square (V : Type*) [Fintype V] : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by
  simpa only [Fintype.card_prod,pow_two] using Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α:=V))
def tierPolynomial (N D K : ℕ) := N^2*(D+2*K+2)
def lambdaPolynomial (N D K T : ℕ) := 10*N*ladderQ N D*(T+1)*(K+(N*D+2)+1)
def stepsPolynomial (N D K m : ℕ) :=
  20*ladderL N D*ladderM N D (tierPolynomial N D K)*
    (lambdaPolynomial N D K (tierPolynomial N D K)+m+1)
def edgePolynomial (N K : ℕ) := N^2*((2*K+1)*N)
def scanErrorPolynomial (N D K : ℕ) :=
  2*(1+ladderM N D (tierPolynomial N D K))+
  4*(8*(edgePolynomial N K)^2+4*edgePolynomial N K+3)+2*N^2*((2*K+1)*N)
def totalBitsPolynomial (N D K m H : ℕ) :=
  let t:=stepsPolynomial N D K m
  let R:=scanErrorPolynomial N D K
  t*((t*R*H)+(t*R*H+N*(t*R*H)))+edgePolynomial N K*(6*edgePolynomial N K*H)
lemma endpoint_le_polynomial (N D K : ℕ) (hN : 0<N) : endpoint N D K hN ≤ tierPolynomial N D K := by
  rw [endpoint_eq]
  apply (ladderTier_le N D K hN).trans
  unfold tierBound tierPolynomial
  gcongr
  exact clog_two_le_self D
lemma lambda_le_polynomial (N D K T : ℕ) : ladderLambda N D K T ≤ lambdaPolynomial N D K T := by
  unfold ladderLambda lambdaPolynomial
  gcongr
  exact clog_two_le_self _
lemma discreteSteps_le_polynomial (N D K T m : ℕ) (hT : T ≤ tierPolynomial N D K) :
    discreteLadderSteps N D K T m ≤ stepsPolynomial N D K m := by
  have hl : ladderLambda N D K T ≤ lambdaPolynomial N D K (tierPolynomial N D K) :=
    (lambda_le_polynomial N D K T).trans (by unfold lambdaPolynomial; gcongr)
  have hm : ladderM N D T ≤ ladderM N D (tierPolynomial N D K) := by unfold ladderM; gcongr
  unfold discreteLadderSteps stepsPolynomial
  gcongr
  exact clog_two_le_self m
end MatchingFPRAS.Transport

namespace MatchingFPRAS.Variation
open Transport

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
def paddedBits {k B : ℕ} (h : k≤B) :
    (Fin B → Bool) ≃ ((Fin k → Bool) × (Fin (B-k) → Bool)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl Bool)).trans (pairBitsEquiv k (B-k))
def padSampler {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) : (Fin B → Bool) → A :=
  fun bits=>f ((paddedBits h bits).1)
noncomputable def markedBitsEquiv (E : Type*) [Fintype E] (t k : ℕ) :
    (Fin (t+Fintype.card E*k) → Bool) ≃ ((Fin t → Bool) × (E → Fin k → Bool)) :=
  (pairBitsEquiv t (Fintype.card E*k)).trans (Equiv.prodCongr (Equiv.refl _)
    ((matrixBitsEquiv (Fintype.card E) k).trans
      (Equiv.arrowCongr (Fintype.equivFin E).symm (Equiv.refl _))))
end MatchingFPRAS.Variation

namespace MatchingFPRAS.FiniteTrial
open Transport Variation

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder 
attribute [local instance] prodOrder sumOrder

open Transport Variation

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder 
attribute [local instance] prodOrder sumOrder
def successorBitsEquiv (j B : ℕ) : (Fin ((j+1)*B) → Bool) ≃ (Fin (j*B+B) → Bool) :=
  Equiv.arrowCongr (finCongr (Nat.succ_mul j B)) (Equiv.refl Bool)
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineRequestCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericBounds
open Polynomial TreeTyped

variable {A B : Type}
def Bound (f m : A→ℕ) : Prop := ∃ p : Polynomial ℕ,∀ x,f x≤p.eval (m x)
end MatchingFPRAS.NumericBounds

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial NumericBounds Transport ExecutableSource

def precisionNorm (x : PrecisionData) : ℕ :=
  x.1.1.1.1+x.1.1.1.2+x.1.1.2.1+x.1.1.2.2+x.1.2+x.2.1+x.2.2
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_OnlineFractionParam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial

abbrev RootInput := ℕ×List Bool
def rootCandidate (x : RootInput×ℕ) : Bool := decide (x.1.1<(x.2+1)^2)

def findRoot (x : RootInput) : ℕ :=
  listMin ((List.range (x.2.length+1)).filter (fun i=>rootCandidate (x,i)),x.2.length)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineLadderSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial ExecutableSource Transport

abbrev LadderInput := (ℕ×ℕ)×ℕ

def distortion (x : ℕ×ℕ) : ℕ := 100*x.2^2*(100000000*(x.1+1)^4)
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
open TreeTyped ExecutableSource OnlineSchedule

def root (n : ℕ) : ℕ := findRoot (n-1,List.replicate n false)
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
open TreeTyped ExecutableSource
open PhysicalStream OnlineSchedule

abbrev Edges := List (ℕ×ℕ)
end MatchingFPRAS.OnlineGraph

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
open TreeTyped PhysicalStream ExecutableSource
open Polynomial OnlineSchedule OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable def vectorPolynomial : Polynomial ℕ :=
  let B : Polynomial ℕ := X+1
  B*(4*B+8*(B+B*B*(19+B+2*(B+B*B+1))+1)+6)+1
noncomputable def productPolynomial : Polynomial ℕ :=
  let B : Polynomial ℕ := X+1
  8*(B+B*(2*(B+B*B+1)+1)+1)+3

noncomputable def statePolynomial : Polynomial ℕ := 100*(X+1)+2*vectorPolynomial+2*productPolynomial
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineRunCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

noncomputable def initialWeightPolynomial : Polynomial ℕ := 2*X+3+statePolynomial
end MatchingFPRAS.OnlineTrial

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
open TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type}
namespace Case

inductive Point where | split | test | yesClear | noClear | yes | no | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.split,.test,.yesClear,.noClear,.yes,.no,.halt},by intro p;cases p <;>simp⟩
end Case
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

namespace ExecutableInput
open TreeTyped

abbrev SparseInput := ℕ×List (ℕ×ℕ)
def tooSparse (x : SparseInput) : Bool := decide (2*x.2.length<x.1)

open Turing

end ExecutableInput
end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped

def parts (a : Symbol) : List Bool×List Bool :=
  (List.replicate a.val false,List.replicate (7-a.val) false)

def fromBit (b : Bool) : Symbol := if b then 2 else 1
def natWord (n : ℕ) : List Symbol := (n.bits.map fromBit)++[3]
end MatchingFPRAS.LiteralCodec

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
@[simp] lemma mk₂_head (a : Γ) (L R : List Γ) : (Tape.mk₂ L (a::R)).head=a := rfl
@[simp] lemma mk₂_right (a : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_left (a : Γ) (L R : List Γ) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_write (a b : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).write b=Tape.mk₂ L (b::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]

def select [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  vs.foldr (fun v tail=>.branch (fun _ s=>decide (s=v)) (f v) tail) fallback

def writeLeft (xs : List Γ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  xs.foldr (fun a tail=>.write (fun _ _=>a) (.move .left tail)) q

def eraseToLeft (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.move .left (.write (fun _ _=>default) tail)) n

variable {I : Type} [DecidableEq I]
def grab (is : List I) (q : TM1.Stmt Γ Λ (I→Γ)) : TM1.Stmt Γ Λ (I→Γ) :=
  is.foldr (fun i tail=>.load (fun a v=>Function.update v i a) (.move .right tail)) q
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_BlockMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

inductive Label
  | start | read | seek | back | stopSep | stopOut
  deriving DecidableEq, Inhabited
instance instFintypeLabel : Fintype Label := ⟨{.start,.read,.seek,.back,.stopSep,.stopOut}, by intro a; cases a <;> simp⟩
abbrev Block (w : ℕ) := Fin w→Symbol
noncomputable def code (w : ℕ) (h : Block w→List Symbol) (header : List Symbol) :
    Label→TM1.Stmt Symbol Label (Block w)
  | .start => .move .left (.write (fun _ _=>7) (.move .left (.write (fun _ _=>6)
      (.move .right (.move .right (.goto (fun _ _=>.read)))))))
  | .read => grab (List.finRange w)
      (.branch (fun _ b=>decide (b=fun _=>0))
        (.move .left (.goto (fun _ _=>.stopSep)))
        (.move .left (.write (fun _ _=>7) (eraseToLeft w (.move .left (.goto (fun _ _=>.seek)))))))
  | .seek => .branch (fun a _=>decide (a=6))
      (select Finset.univ.toList (fun b=>.write (fun _ _=>0)
        (writeLeft (h b).reverse (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>.back)))))) .halt)
      (.move .left (.goto (fun _ _=>.seek)))
  | .back => .branch (fun a _=>decide (a=7))
      (.move .right (.goto (fun _ _=>.read)))
      (.move .right (.goto (fun _ _=>.back)))
  | .stopSep => .branch (fun a _=>decide (a=7))
      (.write (fun _ _=>0) (.move .left (.goto (fun _ _=>.stopOut))))
      (.move .left (.goto (fun _ _=>.stopSep)))
  | .stopOut => .branch (fun a _=>decide (a=6))
      (.write (fun _ _=>0) (writeLeft header.reverse (.write (fun _ _=>0) (.move .right .halt))))
      (.move .left (.goto (fun _ _=>.stopOut)))
variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)

def working (out : List Symbol) (gap : ℕ) (input : List Symbol) : Tape Symbol :=
  Tape.mk₂ (7::(List.replicate gap 0++out.reverse++[6])) input

def budget (H n s : ℕ) : ℕ := (n+1)*(3+w+H+2*(s+n*(H+w)))

end MatchingFPRAS.LiteralBlockMap

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
open TreeTyped Polynomial LiteralCodec

def numStep (x : Symbol×List ℕ) : List ℕ :=
  if x.1=3 then 0::x.2
  else if x.1=1 then (2*x.2.headD 0)::x.2.tail
  else if x.1=2 then (2*x.2.headD 0+1)::x.2.tail
  else x.2

def parse (as : List Symbol) : List ℕ := as.foldr (fun a ns=>numStep (a,ns)) []
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped Polynomial LiteralParse

abbrev PairState := (Bool×ℕ)×List (ℕ×ℕ)
def pairStep (x : ℕ×PairState) : PairState :=
  if x.2.1.1 then ((false,0),(x.1,x.2.1.2)::x.2.2) else ((true,x.1),x.2.2)

def pairs (ns : List ℕ) : List (ℕ×ℕ) := (ns.foldl (fun s n=>pairStep (n,s)) ((false,0),[])).2

def edgeNumbers (G : GraphInput) : List (ℕ×ℕ) :=
  ((G.edges.map toLex.toEmbedding).sort (·≤·)).map (fun e=>((ofLex e).1.val,(ofLex e).2.val))
end MatchingFPRAS.LiteralInput

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
open TreeTyped

lemma flatMap_uniform_length {α β : Type} (as : List α) (f : α→List β) (w : ℕ)
    (h : ∀ a,(f a).length=w) : (as.flatMap f).length=as.length*w := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul];omega
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

def singletonBlock (a : Symbol) : Block 1 := fun _=>a
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
def eraseRight (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.write (fun _ _=>default) (.move .right tail)) n
noncomputable def eraseCode (n : ℕ) : Unit→TM1.Stmt Symbol Unit Unit := fun _=>eraseRight n .halt
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
omit [Inhabited Γ] [Fintype σ] [Inhabited σ] in
lemma supports_univ (M : Λ→TM1.Stmt Γ Λ σ) : TM1.Supports M Finset.univ := by
  classical
  refine ⟨Finset.mem_univ _,fun l _=>?_⟩
  induction M l with
  | move d q ih => exact ih
  | write f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ih jh => exact ⟨ih,jh⟩
  | goto f => exact fun a v=>Finset.mem_univ _
  | halt => trivial
end MatchingFPRAS.LiteralTape

end OAI
end


