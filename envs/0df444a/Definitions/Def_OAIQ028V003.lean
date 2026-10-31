-- Prove2me | Definitions.Def_OAIQ028V003
-- name    : OAIQ028V003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:10:09.529161+00:00
-- url     : https://prove2.me/theorems/2f9ac9ea-6bd0-4335-89db-d353ad352c8a
-- title:
--   Definitions bundle OAIQ028V003 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 551 declarations of OpenAI's Lean: 184 definitions, 2 inductive types or structures, 12 instances and 353 theorems. The definitions and types are `OAI.UniqueGames.Foundations.CorrelatedSampling.sharedProfileLeft`, `OAI.UniqueGames.Foundations.CorrelatedSampling.sharedProfileReject`, `OAI.UniqueGames.Foundations.CorrelatedSampling.sharedProfileRight`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.condition`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.expectation`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.mixture`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.product`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.pushforward`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.table`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.totalVariation`, `OAI.UniqueGames.Foundations.Games.FiniteDistribution.uniform`, `OAI.UniqueGames.Foundations.Games.Game.coordinateGame`, `OAI.UniqueGames.Foundations.Games.Game.coordinateWin`, `OAI.UniqueGames.Foundations.Games.Game.localEmbeddingLaw`, `OAI.UniqueGames.Foundations.Games.Game.selectedSuccess`, `OAI.UniqueGames.Foundations.Games.Game.selectedWins`, `OAI.UniqueGames.Foundations.Games.Game.success`, `OAI.UniqueGames.Foundations.Games.Game.value`, `OAI.UniqueGames.Foundations.Games.Game.wins`, `OAI.UniqueGames.Foundations.Games.KernelSampling.seedLaw`, `OAI.UniqueGames.Foundations.Hastad.EmptyContext.Address`, `OAI.UniqueGames.Foundations.Hastad.EmptyContext.equation`, `OAI.UniqueGames.Foundations.Hastad.EmptyContext.pairedEquations`, `OAI.UniqueGames.Foundations.Hastad.HalfCube`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.ClauseContext`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.VariableContext`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.canonicalSlot`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent`, `OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame`, `OAI.UniqueGames.Foundations.Hastad.SourceGame.eventLaw`, `OAI.UniqueGames.Foundations.Hastad.SourceGame.visibleQuestion`, `OAI.UniqueGames.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.GlobalKey`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.clauseAnswerEncoding`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.clauseEncoding`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.globalEncoding`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.iEncoding`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.jEncoding` and 146 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Fourier_EmptyContext`, `VertexCover_Fourier_Folding`, `VertexCover_Fourier_SourceContexts`, `VertexCover_Fourier_SourceGame`, `VertexCover_Fourier_SourceGap`, `VertexCover_Fourier_SourceHonest`, `VertexCover_Fourier_SourceNonempty`, `VertexCover_Fourier_SourceOccurrences`, `VertexCover_Fourier_SourceSoundness`, `VertexCover_Fourier_ThreeBitTest`, `VertexCover_Fourier_Walsh`, `VertexCover_Games_Basic`, `VertexCover_Games_Conditioning`, `VertexCover_Games_KernelSampling`, `VertexCover_Games_Mixture`, `VertexCover_Games_Sampling`, `VertexCover_Games_Stochastic`, `VertexCover_Games_TotalVariation`, `VertexCover_Games_Value`, `VertexCover_Information_Conditionals`, `VertexCover_Information_GamesAdapter`, `VertexCover_Information_SideInformation`, `VertexCover_Machines_NatWalk`, `VertexCover_PCP_AlphabetGraph`, `VertexCover_PCP_AlphabetGraphBounds`, `VertexCover_PCP_AlphabetReduction`, `VertexCover_PCP_AlphabetRetraction`, `VertexCover_PCP_AlphabetTableBounds`, `VertexCover_PCP_AlphabetTableEnumeration`, `VertexCover_PCP_AlphabetTableTable`, `VertexCover_PCP_AmplificationRound`, `VertexCover_PCP_AssignmentTester`, `VertexCover_PCP_ClauseVerifier`, `VertexCover_PCP_CloudPadding`, `VertexCover_PCP_CloudRounding`, `VertexCover_PCP_CodeComposition`, `VertexCover_PCP_ConstraintGraph`, `VertexCover_PCP_DegreeReplacement`, `VertexCover_PCP_ExpanderFamily`, `VertexCover_PCP_ExpanderTables`, `VertexCover_PCP_FinalBooleanVerifier`, `VertexCover_PCP_FinalConstants`, `VertexCover_PCP_FinalTableFormula`, `VertexCover_PCP_FiniteGraph`, `VertexCover_PCP_GenericGraphTables`, `VertexCover_PCP_GraphGap`, `VertexCover_PCP_GraphTables`, `VertexCover_PCP_GraphTransport`, `VertexCover_PCP_InitialGraph`, `VertexCover_PCP_LazyConstraint`, `VertexCover_PCP_LazySpectral`, `VertexCover_PCP_NameCompaction`, `VertexCover_PCP_Overlay`, `VertexCover_PCP_PCPIteration`, `VertexCover_PCP_PortTables`, `VertexCover_PCP_PoweringAddresses`, `VertexCover_PCP_PoweringLabels`, `VertexCover_PCP_PoweringLazy`, `VertexCover_PCP_PoweringPortReindex`, `VertexCover_PCP_PoweringReach`, `VertexCover_PCP_PoweringTest`, `VertexCover_PCP_PoweringWalks`, `VertexCover_PCP_Preprocessing`, `VertexCover_PCP_QueryIncidence`, `VertexCover_PCP_SpectralReturn`, `VertexCover_PCP_UniformRestriction`, `VertexCover_PCP_VerifierToCNF`, `VertexCover_PCP_ZigzagGraphs`, `VertexCover_PCP_ZigzagSpectral`, `VertexCover_Reduction_ReductionSound`, `VertexCover_Repetition_DistributionMaps`, `VertexCover_Repetition_GameConditioning`, `VertexCover_Sampling_Basic`, `VertexCover_Sampling_LabelBound`, `VertexCover_Sampling_Rectangle`, `VertexCover_Sampling_SharedProfiles`.
--
--   **Imports.** It imports the bundles `OAIQ028V000` and `OAIQ028V001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ028V006` and `OAIQ028V007`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ028V000
import Definitions.Def_OAIQ028V001

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_Walsh
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.bitSign_not _root_.OAI.UniqueGames.Foundations.Hastad.cubeFlip_cubeFlip _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_ThreeBitTest
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_Folding
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                   

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

end UniqueGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_EmptyContext
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                        
section

namespace UniqueGames.Foundations.Hastad

open UniqueGames.Reduction.CloneGap
open scoped BigOperators

namespace EmptyContext

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

omit [Fintype I] [DecidableEq I] in
@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

end EmptyContext
end UniqueGames.Foundations.Hastad

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ClauseVerifier
attribute [-instance] _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerInhabited _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP

open Target

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot
abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.«variables» → Bool

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

end UniqueGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceContexts
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.card_slot _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.to_fromClauseAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Hastad.SourceContexts

open Target PCP

abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.«variables»

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.«variables» ^ u := by simp [VariableContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

def baseAccepts (F : Formula) (v : Fin F.«variables») («c» : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F «c») j = true ∧
    localConsistent (clauseAt F «c») j = true ∧
    answerAt j (canonicalSlot (clauseAt F «c») v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.«variables»)
    («c» : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v «c» i j = true ↔
      localSatisfies (clauseAt F «c») j = true ∧
      localConsistent (clauseAt F «c») j = true ∧
      answerAt j (canonicalSlot (clauseAt F «c») v) = i := by
  simp [baseAccepts]

end UniqueGames.Foundations.Hastad.SourceContexts

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Basic
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

theorem success_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : 0 ≤ G.success strategy :=
  G.questions.probability_nonnegative _

theorem success_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤
      G.success (simulatedStrategy questionMap₁ questionMap₂ answerMap₁ answerMap₂ strategy) := by
  unfold success
  rw [questionLaw, FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions h
  exact acceptance questions.1 questions.2 _ _ h

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

theorem selectedWins_mono (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {selected selected' : Finset (Fin n)} (h : selected ⊆ selected') :
    (G.repetition n).questions.probability (G.selectedWins strategy selected') ≤
      (G.repetition n).questions.probability (G.selectedWins strategy selected) := by
  apply FiniteDistribution.probability_mono
  intro questions hwin
  simp only [selectedWins, decide_eq_true_eq] at hwin ⊢
  intro i hi
  exact hwin i (h hi)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

theorem selectedWins_univ (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedWins strategy Finset.univ = (G.repetition n).wins strategy := by
  classical
  funext questions
  simp [selectedWins, coordinateWin, repetition, wins]

end Game

end

end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Value
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : Game Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : Game Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_nonnegative (G : Game Q₁ Q₂ A₁ A₂) : 0 ≤ G.value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h]
  exact G.success_nonnegative strategy

end Game

end

end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Stochastic
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                     
section

namespace UniqueGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteDistribution

end
end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Conditioning
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedWins_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n) :
    G.selectedWins strategy (insert coordinate selected) =
      fun questions =>
        G.selectedWins strategy selected questions && G.coordinateWin strategy coordinate questions := by
  classical
  funext questions
  apply Bool.eq_iff_iff.mpr
  simp [selectedWins, and_comm]

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

theorem selectedSuccess_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : G.selectedSuccess strategy selected ≤ 1 :=
  (G.repetition n).questions.probability_le_one _

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

theorem selectedSuccess_univ (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy Finset.univ = (G.repetition n).success strategy := by
  rw [selectedSuccess, G.selectedWins_univ]
  rfl

theorem selectedSuccess_antitone (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Antitone (G.selectedSuccess strategy) := by
  intro selected selected' h
  exact G.selectedWins_mono strategy h

theorem selectedSuccess_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (positive : 0 < G.selectedSuccess strategy selected) :
    G.selectedSuccess strategy (insert coordinate selected) =
      G.selectedSuccess strategy selected *
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          (G.coordinateWin strategy coordinate) := by
  unfold selectedSuccess
  rw [G.selectedWins_insert]
  exact (G.repetition n).questions.probability_inter_eq_mul_conditional _ _ positive

end Game

end

end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Sampling
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Games.FiniteDistribution.probability_condition_given
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                   
section

namespace UniqueGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

end
end UniqueGames.Foundations.Games.FiniteDistribution

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceGame
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.to_fromClauseAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

noncomputable section
namespace UniqueGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.«variables» × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.«variables») («c» : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v «c» i j = baseAccepts F v «c» i j := rfl

end UniqueGames.Foundations.Hastad.SourceGame

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceOccurrences
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Hastad.SourceOccurrences

open UniqueGames.Reduction.CloneGap
open scoped BigOperators

abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) («c» : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((«c».prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) («c» : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v «c» i j).size =
      v.size * 2 ^ i.size + («c».size * 2 ^ j.size + 1) := rfl

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

section ConcreteSource

open SourceContexts

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.«variables»)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.«variables» ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def leftAnchor (u : ℕ) : I u := fun _ => false

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

end ConcreteSource

end UniqueGames.Foundations.Hastad.SourceOccurrences

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceHonest
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                        
section

namespace UniqueGames.Foundations.Hastad.SourceHonest

open UniqueGames.Reduction.CloneGap
open scoped BigOperators

def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl («c», g)) => g (right «c»)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) («c» : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl («c», g))) = g (right «c») := rfl

end UniqueGames.Foundations.Hastad.SourceHonest

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceSoundness
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                           
section

noncomputable section
namespace UniqueGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

end UniqueGames.Foundations.Hastad.SourceSoundness

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_TotalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                         
section

namespace UniqueGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGames.Foundations.Games.FiniteDistribution

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Conditionals
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_GamesAdapter
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_SideInformation
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Information
open scoped BigOperators

theorem mass_mul_posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {«c» : ℝ} (hmass : ∑ a, p a * e a = «c») (x : A) :
    «c» * posteriorOrOriginal p e «c» x = p x * e x := by
  classical
  by_cases hc : 0 < «c»
  · simp only [posteriorOrOriginal, ite_eq_left hc, posterior]
    field_simp [hc.ne']
  · have hcnonneg : 0 ≤ «c» := by
      rw [← hmass]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (he a))
    have hc0 : «c» = 0 := le_antisymm (le_of_not_gt hc) hcnonneg
    have hpoint := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => mul_nonneg (hp.1 a) (he a))
      (Finset.mem_univ x)
    rw [hmass, hc0] at hpoint
    have hzero : p x * e x = 0 := le_antisymm hpoint (mul_nonneg (hp.1 x) (he x))
    simp [posteriorOrOriginal, hc0, hzero]

theorem weighted_coordinate_posterior_recombine
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (p e : (I → A) → ℝ) (hp : IsProbability p) (he : ∀ x, 0 ≤ e x)
    {«c» : ℝ} (hmass : ∑ x, p x * e x = «c») (b z : ℝ) (i : I) (a : A) :
    (b * «c» / z) * coordinateMarginal (posteriorOrOriginal p e «c») i a =
      (b / z) * ∑ x, if x i = a then p x * e x else 0 := by
  classical
  simp only [coordinateMarginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x i = a
  · simp only [ite_eq_left hxa]
    calc
      (b * «c» / z) * posteriorOrOriginal p e «c» x =
          (b / z) * («c» * posteriorOrOriginal p e «c» x) := by ring
      _ = (b / z) * (p x * e x) := by
        rw [mass_mul_posteriorOrOriginal p e hp he hmass x]
  · simp [hxa]

variable {J I A : Type*}
variable [Fintype J] [Fintype I] [Fintype A] [DecidableEq I]

theorem side_information_bound
    (w b «c» : J → ℝ)
    (q : J → I → A → ℝ)
    (e : J → (I → A) → ℝ)
    (hw : IsProbability w)
    (hb : ∀ j, 0 ≤ b j)
    (hq : ∀ j i, IsProbability (q j i))
    (he : ∀ j x, 0 ≤ e j x)
    (he_one : ∀ j x, e j x ≤ 1)
    (hmass : ∀ j, ∑ x, independentProduct (q j) x * e j x = «c» j)
    {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hbase : ∑ j, b j = B)
    (hweight : ∀ j, w j = b j * «c» j / z) :
    (∑ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) («c» ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * Real.log (B / z)) := by
  classical
  let d : J → I → ℝ := fun j i => totalVariation
    (coordinateMarginal
      (posteriorOrOriginal (independentProduct (q j)) (e j) («c» j)) i)
    (q j i)
  have hbudget : ∀ j,
      w j * (∑ i, d j i ^ 2) ≤ w j * Real.log (1 / «c» j) := by
    intro j
    by_cases hwzero : w j = 0
    · simp [hwzero]
    have hcne : «c» j ≠ 0 := by
      intro hczero
      apply hwzero
      rw [hweight j, hczero, mul_zero, zero_div]
    have hcnonneg : 0 ≤ «c» j := by
      rw [← hmass j]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((independentProduct_isProbability (q j) (hq j)).1 x) (he j x))
    have hcpos : 0 < «c» j := lt_of_le_of_ne hcnonneg (Ne.symm hcne)
    have hlocal := posterior_coordinate_totalVariation_sq_sum_le_log
      (q j) (hq j) (e j) (he j) (he_one j) hcpos (hmass j)
    have hweighted := mul_le_mul_of_nonneg_left hlocal (hw.1 j)
    simpa only [d, posteriorOrOriginal, ite_eq_left hcpos] using hweighted
  have hcs := weighted_coordinate_sum_sq_le
    w d (fun j => Real.log (1 / «c» j)) hw hbudget
  have hlog := posterior_weighted_log_inverse_le w b «c» hw hb hz hB hbase hweight
  have hsq : (∑ i, ∑ j, w j * d j i)^2 ≤
      (Fintype.card I : ℝ) * Real.log (B / z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  have htv : ∀ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) («c» ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2) =
      ∑ j, w j * d j i := by
    intro i
    exact totalVariation_joint_common_weights w
      (fun j => coordinateMarginal
        (posteriorOrOriginal (independentProduct (q j)) (e j) («c» j)) i)
      (fun j => q j i) hw.1
  simp_rw [htv]
  have hradicand : 0 ≤ (Fintype.card I : ℝ) * Real.log (B / z) :=
    (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hradicand
  have hsqrt_nonneg := Real.sqrt_nonneg ((Fintype.card I : ℝ) * Real.log (B / z))
  nlinarith

variable {T V : Type*} [Fintype T] [Fintype V] [Nonempty V]

theorem finite_side_information_bound
    (pT : T → ℝ) (q : T → I → A → ℝ)
    (e : T × V → (I → A) → ℝ) («c» w : T × V → ℝ)
    (hpT : IsProbability pT)
    (hq : ∀ t i, IsProbability (q t i))
    (he : ∀ tv x, 0 ≤ e tv x)
    (he_sum : ∀ t x, (∑ v, e (t, v) x) ≤ 1)
    (hc : ∀ tv, ∑ x, independentProduct (q tv.1) x * e tv x = «c» tv)
    {z : ℝ} (hz : 0 < z)
    (hZ : ∑ tv, pT tv.1 * «c» tv = z)
    (hweight : ∀ tv, w tv = pT tv.1 * «c» tv / z) :
    (∑ i, totalVariation
      (fun tva : (T × V) × A => w tva.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q tva.1.1))
          (e tva.1) («c» tva.1)) i tva.2)
      (fun tva : (T × V) × A => w tva.1 * q tva.1.1 i tva.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) *
        (Real.log (Fintype.card V : ℝ) + Real.log (1 / z))) := by
  classical
  have hcnonneg : ∀ tv, 0 ≤ «c» tv := by
    intro tv
    rw [← hc tv]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg
      ((independentProduct_isProbability (q tv.1) (hq tv.1)).1 x) (he tv x))
  have hw : IsProbability w := by
    constructor
    · intro tv
      rw [hweight tv]
      exact div_nonneg (mul_nonneg (hpT.1 tv.1) (hcnonneg tv)) hz.le
    · simp_rw [hweight, div_eq_mul_inv]
      rw [← Finset.sum_mul, hZ, mul_inv_cancel₀ hz.ne']
  have he_one : ∀ tv x, e tv x ≤ 1 := by
    intro tv x
    have hsingle : e tv x ≤ ∑ v, e (tv.1, v) x :=
      Finset.single_le_sum (fun v _ => he (tv.1, v) x) (Finset.mem_univ tv.2)
    exact hsingle.trans (he_sum tv.1 x)
  have hB : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : (∑ tv : T × V, pT tv.1) = (Fintype.card V : ℝ) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hpT.2, mul_one]
  have h := side_information_bound w (fun tv : T × V => pT tv.1) «c»
    (fun tv => q tv.1) e hw (fun tv => hpT.1 tv.1) (fun tv => hq tv.1)
    he he_one hc hz hB hbase hweight
  have hlog : Real.log ((Fintype.card V : ℝ) / z) =
      Real.log (Fintype.card V : ℝ) + Real.log (1 / z) := by
    rw [Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  simpa only [hlog] using h

end UniqueGames.Foundations.Information
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_KernelSampling
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Games.FiniteDistribution.probability_condition_given
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                         
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

section Completion

variable {I A B S : Type*} [DecidableEq I]

theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate ys j q.1 (hright q ys h)

end Completion

end KernelSampling
end
end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Mixture
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Games.FiniteDistribution.probability_condition_given
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                  
section

namespace UniqueGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end
end UniqueGames.Foundations.Games.FiniteDistribution

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_DistributionMaps
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Games.FiniteDistribution.probability_condition_given
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro «c»
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end UniqueGames.Foundations.Games.FiniteDistribution
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

end FiniteWeights

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_Rectangle
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

theorem rectangle_row_mass (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : density a ∈ thresholds) (h0 : 0 ≤ density a) (h1 : density a ≤ 1) :
    (∑ i, if rectangleAccept thresholds density (a, i) then
      rectangleWeight thresholds (a, i) else 0) = density a / (Fintype.card α : ℝ) := by
  calc
    _ = (∑ i : Fin (thresholdPartition thresholds).length,
        if (thresholdPartition thresholds)[i].lo < density a then
          (thresholdPartition thresholds)[i].hi - (thresholdPartition thresholds)[i].lo else 0) /
        (Fintype.card α : ℝ) := by
      rw [sum_div_const]
      apply Finset.sum_congr rfl
      intro i _
      simp [rectangleAccept, rectangleWeight, ite_div]
    _ = density a / (Fintype.card α : ℝ) := by
      rw [sum_interval_get (fun I => if I.lo < density a then I.hi - I.lo else 0),
        partition_acceptance_mass thresholds (density a) hm h0 h1]

theorem rectangle_acceptance_mass (thresholds : List ℝ) (density : α → ℝ)
    (hm : ∀ a, density a ∈ thresholds) (h0 : ∀ a, 0 ≤ density a)
    (h1 : ∀ a, density a ≤ 1) :
    eventMass (rectangleWeight thresholds) (rectangleAccept thresholds density) =
      (∑ a, density a) / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [rectangle_row_mass thresholds density _ (hm _) (h0 _) (h1 _)]
  rw [sum_div_const]

theorem rectangle_label_mass [DecidableEq α] (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : ∀ x, density x ∈ thresholds) (h0 : ∀ x, 0 ≤ density x)
    (h1 : ∀ x, density x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds density seed && decide (seed.1 = a)) =
      density a / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : α, if x = a then density x / (Fintype.card α : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · simpa [hx] using rectangle_row_mass thresholds density x (hm x) (h0 x) (h1 x)
      · simp [hx]
    _ = density a / (Fintype.card α : ℝ) := by simp

omit [Fintype α] in theorem rectangle_and (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => min (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

omit [Fintype α] in theorem rectangle_or (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => max (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem rectangle_union_mass (thresholds : List ℝ) (p q : α → ℝ)
    (hpm : ∀ a, p a ∈ thresholds) (hqm : ∀ a, q a ∈ thresholds)
    (hp0 : ∀ a, 0 ≤ p a) (_hq0 : ∀ a, 0 ≤ q a)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ a, q a ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      unionMass p q / (Fintype.card α : ℝ) := by
  rw [rectangle_or]
  exact rectangle_acceptance_mass thresholds _
    (fun a => max_mem_thresholds thresholds (hpm a) (hqm a))
    (fun a => (hp0 a).trans (le_max_left _ _)) (fun a => max_le (hp1 a) (hq1 a))

theorem rectangle_common_label_mass [DecidableEq α] (thresholds : List ℝ)
    (p q : α → ℝ) (a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (_hq1 : ∀ x, q x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => (rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) &&
        decide (seed.1 = a)) = min (p a) (q a) / (Fintype.card α : ℝ) := by
  have hand := congrFun (rectangle_and thresholds p q)
  simp_rw [hand]
  exact rectangle_label_mass thresholds _ a
    (fun x => min_mem_thresholds thresholds (hpm x) (hqm x))
    (fun x => le_min (hp0 x) (hq0 x)) (fun x => (min_le_left _ _).trans (hp1 x))

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_LabelBound
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

section Rectangle

variable [Fintype α] [Nonempty α]

theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end Rectangle

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_SharedProfiles
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                      
section

namespace UniqueGames.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

end

end UniqueGames.Foundations.CorrelatedSampling
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_GameConditioning
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Games.Game

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

def localEmbeddingLaw (G : Game Q₁ Q₂ A₁ A₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂) :
    FiniteDistribution (R₁ × R₂) :=
  seedLaw.mixture fun seed =>
    G.questions.pushforward fun q => (left seed q.1, right seed q.2)

theorem success_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂)
    (answerLeft : Seed → Q₁ → B₁ → A₁)
    (answerRight : Seed → Q₂ → B₂ → A₂)
    (acceptance : ∀ seed x y a b,
      H.accepts (left seed x) (right seed y) a b = true →
      G.accepts x y (answerLeft seed x a) (answerRight seed y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤ G.value +
      H.questions.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  have localBound (seed : Seed) :
      (G.questions.pushforward (fun q => (left seed q.1, right seed q.2))).probability
        (H.wins strategy) ≤ G.value := by
    let embedded : Game R₁ R₂ B₁ B₂ :=
      { questions := G.questions.pushforward fun q => (left seed q.1, right seed q.2)
        accepts := H.accepts }
    change embedded.success strategy ≤ G.value
    exact (G.success_le_of_localSimulation embedded (left seed) (right seed)
      (answerLeft seed) (answerRight seed) rfl (acceptance seed) strategy).trans
      (G.success_le_value _)
  have mixtureBound :
      (G.localEmbeddingLaw seedLaw left right).probability (H.wins strategy) ≤ G.value :=
    seedLaw.probability_mixture_le _ _ _ localBound
  exact (H.questions.probability_le_add_totalVariation
    (G.localEmbeddingLaw seedLaw left right) (H.wins strategy)).trans
    (add_le_add mixtureBound (le_refl _))

def coordinateGame (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂))) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) where
  questions := law
  accepts x y a b := G.accepts (x coordinate) (y coordinate) (a coordinate) (b coordinate)

theorem coordinate_probability_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)))
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → Fin n → Q₁) (right : Seed → Q₂ → Fin n → Q₂)
    (left_preserves : ∀ seed x, left seed x coordinate = x)
    (right_preserves : ∀ seed y, right seed y coordinate = y)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    law.probability (G.coordinateWin strategy coordinate) ≤ G.value +
      law.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  apply G.success_le_value_add_embedding_distance (G.coordinateGame coordinate law)
    seedLaw left right (fun _ _ a => a coordinate) (fun _ _ b => b coordinate)
  intro seed x y a b h
  simpa only [coordinateGame, left_preserves, right_preserves] using h

end
end UniqueGames.Foundations.Games.Game

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                     
section

namespace UniqueGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open UniqueGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

end UniqueGames.Foundations.Hastad.SourceGap

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AssignmentTester
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

noncomputable section

namespace UniqueGames.Foundations.PCP.AssignmentTester

open UniqueGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let «c» := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, «c» s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, «c» t ^ 3) ≤ «c» s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < «c» s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        «c» s ^ 3 ≤ (∑ t, «c» t ^ 3) * «c» s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg («c» s))
      nlinarith
    have hlt : «c» s₀ ^ 3 < (∑ t, «c» t ^ 3) * «c» s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [«c»] at hs
  linarith

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases hfi : f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, ite_eq_right hij]
      cases hf : parity s f <;> cases hfi : f i <;> simp []
    rw [hD]
    exact four_truth_lower _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in

theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end UniqueGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CodeComposition
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.Hastad.bitSign_not _root_.OAI.UniqueGames.Foundations.Hastad.cubeFlip_cubeFlip _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGames.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open UniqueGames.Foundations.Hastad

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

theorem walsh_singletonMask {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (x : Cube A) : walsh (singletonMask a) x = bitSign (x a) := by
  classical
  unfold walsh singletonMask
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba
    simp [hba, bitSign]
  · simp

theorem singletonMask_ne {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    singletonMask a ≠ singletonMask b := by
  intro h
  have he := congrFun h a
  simp [singletonMask, hab] at he

theorem codeword_distance {A : Type*} [Fintype A] [DecidableEq A]
    {a b : A} (hab : a ≠ b) :
    relativeDistance (codeword a) (codeword b) = 1 / 2 := by
  rw [relativeDistance_eq_sign]
  have horth := walsh_orthogonality (singletonMask a) (singletonMask b)
  rw [ite_eq_right (singletonMask_ne hab)] at horth
  simp_rw [walsh_singletonMask] at horth
  change (1 - 𝔼 x : Cube A, bitSign (x a) * bitSign (x b)) / 2 = 1 / 2
  rw [horth]
  norm_num

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

theorem nearest_minimal {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword (nearest f)) ≤ relativeDistance f (codeword a) :=
  Classical.choose_spec (exists_nearest f) a

theorem distance_from_other_codeword {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (f : Cube A → Bool) {a : A} (ha : a ≠ nearest f) :
    1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword (nearest f)) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword (nearest f)) f] at htri
  have hmin := nearest_minimal f a
  linarith

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

theorem rejected_pair_far {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (accepts : A → A → Bool) (left right : Cube A → Bool)
    (hbad : accepts (nearest left) (nearest right) = false)
    (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right)
      (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = nearest left
  · have hb : b ≠ nearest right := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword right hb
    linarith
  · have hsep := distance_from_other_codeword left ha
    linarith

end UniqueGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetReduction
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

noncomputable section

namespace UniqueGames.Foundations.PCP.AlphabetReduction

open UniqueGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

theorem rejected_edge_tester_bound (accepts : A → A → Bool)
    (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool)
    (hbad : accepts (nearest left) (nearest right) = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far accepts left right hbad p.1.1 p.1.2 p.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

end UniqueGames.Foundations.PCP.AlphabetReduction
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ConstraintGraph
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

theorem rejected_exists_of_not_satisfiable (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    ∃ e, G.edgeSatisfied labeling e = false := by
  classical
  by_contra none
  apply unsat
  refine ⟨labeling, fun e => ?_⟩
  have notFalse : G.edgeSatisfied labeling e ≠ false := by
    intro h
    exact none ⟨e, h⟩
  cases h : G.edgeSatisfied labeling e <;> simp_all

theorem rejectionCount_positive [Fintype E] (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    1 ≤ G.rejectionCount labeling := by
  obtain ⟨e, he⟩ := G.rejected_exists_of_not_satisfiable unsat labeling
  exact Finset.one_le_card.mpr ⟨e, (G.mem_rejectedDarts labeling e).mpr he⟩

end ConstraintGraph

end UniqueGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_head _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_cloudRank _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.GraphTables

open UniqueGames.Foundations.Complexity

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

end UniqueGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                   

namespace UniqueGames.Foundations.PCP.PortTables

open PoweringWalks

variable {n d : Nat}

abbrev Input (ports : Nat) := (vertices : Nat) × Table vertices ports

end UniqueGames.Foundations.PCP.PortTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_QueryIncidence
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.dartEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_event_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

theorem honest_leftValid (T : Verifier E X q) (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) :
    LeftValid T event (response T assignment event) := by
  refine ⟨accepted, ?_⟩
  intro i j hij
  exact congrArg assignment hij

theorem honest_incidence [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) (slot : Fin q) :
    incidenceAccept T positive event slot
      (honestLabeling T assignment (.inl event))
      (honestLabeling T assignment (.inr (T.query event slot))) = true := by
  simp only [incidenceAccept, Bool.and_eq_true, honestLabeling,
    decode_encodeRight]
  refine ⟨_root_.decide_eq_true (honest_leftValid T assignment event accepted), ?_⟩
  exact _root_.decide_eq_true (congrArg assignment (canonicalSlot_query T event slot))

theorem perfect_completeness [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool)
    (accepted : ∀ event, T.accepts event (response T assignment event) = true) :
    ∀ dart, (graph T positive).edgeSatisfied (honestLabeling T assignment) dart = true := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  rw [edgeSatisfied_eq_incidence]
  exact honest_incidence T positive assignment event (accepted event) slot

theorem satisfiable_of_verifier_satisfiable [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q)
    (sat : ∃ assignment : X → Bool,
      ∀ event, T.accepts event (response T assignment event) = true) :
    (graph T positive).Satisfiable := by
  obtain ⟨assignment, h⟩ := sat
  exact ⟨honestLabeling T assignment, perfect_completeness T positive assignment h⟩

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

theorem all_incidences_imply_event [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (accepted : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true) :
    T.accepts event (response T (decodedAssignment positive labeling) event) = true := by
  have first := incidenceAccept_true T positive event (zeroSlot positive) _ _
    (accepted (zeroSlot positive))
  have labels_equal : labeling (.inl event) = response T (decodedAssignment positive labeling) event := by
    funext slot
    have info := incidenceAccept_true T positive event slot _ _ (accepted slot)
    exact (first.2.1 slot (canonicalSlot T event slot)
      (canonicalSlot_query T event slot).symm).trans info.2.2
  rw [← labels_equal]
  exact first.1

theorem rejected_event_forces_slot [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (rejected : T.accepts event (response T (decodedAssignment positive labeling) event) = false) :
    ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = false := by
  classical
  by_contra none
  have all : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true := by
    intro slot
    cases h : incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) with
    | false => exact False.elim (none ⟨slot, h⟩)
    | true => rfl
  have h := all_incidences_imply_event T positive labeling event all
  rw [rejected] at h
  cases h

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

theorem rejection_count_bound [Fintype E] [DecidableEq X]
    (T : Verifier E X q) (positive : 0 < q) (labeling : Vertex E X → Label q) :
    2 * verifierRejectionCount T (decodedAssignment positive labeling) ≤
      (graph T positive).rejectionCount labeling := by
  classical
  let failed := rejectedEvents T (decodedAssignment positive labeling)
  have witnesses : ∀ event, event ∈ failed →
      ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) = false := by
    intro event he
    apply rejected_event_forces_slot T positive labeling event
    simpa [failed, rejectedEvents] using he
  let chosen := fun event he => Classical.choose (witnesses event he)
  let inject : (failed.product (Finset.univ : Finset Bool)) →
      (graph T positive).rejectedDarts labeling := fun p =>
    ⟨((p.val.1, chosen p.val.1 (Finset.mem_product.mp p.property).1), p.val.2), by
      apply (ConstraintGraph.mem_rejectedDarts _ _ _).mpr
      rw [edgeSatisfied_eq_incidence]
      exact Classical.choose_spec (witnesses p.val.1 (Finset.mem_product.mp p.property).1)⟩
  have injective : Function.Injective inject := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d => d.val.1.1) h
    · exact congrArg (fun d => d.val.2) h
  have bound := Finset.card_le_card_of_injective injective
  simpa [failed, verifierRejectionCount, ConstraintGraph.rejectionCount,
    Finset.card_product, Nat.mul_comm] using bound

end UniqueGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_UniformRestriction
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

variable [DecidablePred p]

variable [Fintype B] [DecidableEq B]

theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

end UniqueGames.Foundations.PCP.UniformRestriction

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetGraph
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.equation_second_eq_third _root_.OAI.UniqueGames.Foundations.Hastad.EmptyContext.pairedEquations_length _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_left _root_.OAI.UniqueGames.Foundations.Hastad.SourceHonest.taggedAssignment_right _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.canonicalInput_half _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.dartEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.eventEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_event_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.AlphabetGraph

open UniqueGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem eventReject_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    eventReject G assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind k
        (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
        (restrictTape G e r₁) (restrictTape G e r₂) := by
  unfold eventReject
  rw [response_eq_local]
  rfl

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

theorem expect_restrict_five {B : Type*} [Fintype B] [DecidableEq B]
    (p : B → Prop) [DecidablePred p]
    (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ({b // p b} → Bool) →
      ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool,
      𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
        h (UniformRestriction.restrict p f) (UniformRestriction.restrict p g)
          (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
          (UniformRestriction.restrict p r₂)) =
    𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool,
      𝔼 r₀ : {b // p b} → Bool, 𝔼 r₁ : {b // p b} → Bool,
        𝔼 r₂ : {b // p b} → Bool, h f g r₀ r₁ r₂ := by
  rw [UniformRestriction.expect_restrict p
    (fun f => 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool,
      𝔼 r₂ : B → Bool, h f (UniformRestriction.restrict p g)
        (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro f _
  rw [UniformRestriction.expect_restrict p
    (fun g => 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro g _
  rw [UniformRestriction.expect_restrict p
    (fun r₀ => 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g r₀ (UniformRestriction.restrict p r₁) (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₀ _
  rw [UniformRestriction.expect_restrict p
    (fun r₁ => 𝔼 r₂ : B → Bool, h f g r₀ r₁ (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₁ _
  exact UniformRestriction.expect_restrict p (h f g r₀ r₁)

omit [Nonempty A] in
                                                                                    
theorem localAverage_eq_tester (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    localAverage G assignment e = AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold localAverage AlphabetReduction.edgeTesterReject AssignmentTester.explicitTesterReject
  simp only [LocalEvent, expect_prod, eventReject_eq_local, restrictTape]
  apply Finset.expect_congr rfl
  intro kind _
  apply Finset.expect_congr rfl
  intro side _
  apply Finset.expect_congr rfl
  intro tape _
  exact expect_restrict_five (legal G e)
    (AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
      (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
        (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind (side, tape))

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

theorem local_gap (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e)) / 2048 ≤
      localAverage G assignment e := by
  cases h : G.edgeSatisfied (decodedLabeling assignment) e with
  | false =>
      rw [localAverage_eq_tester]
      simpa [AssignmentTester.truth] using
        AlphabetReduction.rejected_edge_tester_bound (G.accepts e)
          (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
          (edgeOracle G assignment e) h
  | true =>
      simp only [Bool.not_true, AssignmentTester.truth, Bool.false_eq_true, ite_false, zero_div]
      apply Finset.expect_nonneg
      intro sample _
      exact AssignmentTester.truth_nonneg _

theorem average_gap [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    (𝔼 e : E, AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e))) / 2048 ≤
      average G assignment := by
  unfold average
  rw [expect_prod, Finset.expect_div]
  exact Finset.expect_le_expect (fun e _ => local_gap G assignment e)

theorem expect_rejection_eq_count {I : Type*} [Fintype I] (b : I → Bool) :
    (𝔼 i : I, AssignmentTester.truth (!(b i))) =
      ((Finset.univ.filter (fun i => b i = false)).card : ℝ) / Fintype.card I := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ i : I, AssignmentTester.truth (!(b i))) = ∑ i : I, if b i = false then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> norm_num [AssignmentTester.truth]
    _ = _ := Finset.sum_boole _ _

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

theorem rejection_count_bound [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    Fintype.card (LocalEvent A) * G.rejectionCount (decodedLabeling assignment) ≤
      2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
  classical
  cases isEmpty_or_nonempty E with
  | inl empty =>
      let := empty
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  | inr inhabited =>
      let := inhabited
      have h := average_gap G assignment
      rw [average_eq_count, expect_rejection_eq_count, card_event, Nat.cast_mul,
        div_div] at h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      have hl : (0 : ℝ) < Fintype.card (LocalEvent A) := by
        exact_mod_cast Fintype.card_pos
      have hc := (div_le_div_iff₀ (mul_pos he (by norm_num)) (mul_pos he hl)).mp h
      have hc' :
          ((Fintype.card (LocalEvent A) : ℝ) *
            (G.rejectionCount (decodedLabeling assignment) : ℝ)) * Fintype.card E ≤
          (2048 * (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ)) * Fintype.card E := by
        simpa only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
          mul_assoc, mul_comm, mul_left_comm] using hc
      have result := (mul_le_mul_iff_left₀ he).mp hc'
      exact_mod_cast result

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_edgeOracle (G : ConstraintGraph V E A) (labeling : V → A) (e : E)
    (h : G.edgeSatisfied labeling e = true) :
    edgeOracle G (honestAssignment G labeling) e =
      fun tape => tape ⟨(labeling (G.tail e), labeling (G.head e)), h⟩ := by
  funext tape
  exact UniformRestriction.extend_apply_of_mem (legal G e) tape
    (labeling (G.tail e), labeling (G.head e)) h

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_event (G : ConstraintGraph V E A) (labeling : V → A)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) (event : Event E A) :
    (verifier G).accepts event (QueryIncidence.response (verifier G) (honestAssignment G labeling) event) =
      true := by
  rcases event with ⟨e, kind, k, f, g, r₀, r₁, r₂⟩
  rw [response_eq_local, honest_edgeOracle G labeling e (satisfied e)]
  simp only [honest_vertexBlock]
  exact AssignmentTester.event_perfect_completeness (AlphabetReduction.pairEncoding (G.accepts e))
    ⟨(labeling (G.tail e), labeling (G.head e)), satisfied e⟩ kind k
    (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
    (restrictTape G e r₁) (restrictTape G e r₂)

omit [DecidableEq A] [Nonempty A] in
theorem perfect_completeness [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A)
    (satisfied : G.Satisfiable) : (graph G).Satisfiable := by
  obtain ⟨labeling, h⟩ := satisfied
  exact QueryIncidence.satisfiable_of_verifier_satisfiable (verifier G) (by omega)
    ⟨honestAssignment G labeling, honest_event G labeling h⟩

end UniqueGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_NameCompaction
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.BinaryFormula.eval_compact_extend _root_.OAI.UniqueGames.BinaryFormula.eval_compact_restrict _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.NameCompaction

open UniqueGames.Foundations.Target

def evaluationList (F : Formula) (A : Fin F.«variables» → Bool) : List Bool :=
  F.clauses.map (fun «c» => «c».eval A)

def failedCount (F : Formula) (A : Fin F.«variables» → Bool) : Nat :=
  (evaluationList F A).count false

theorem failureCount_evaluations (F : Formula) (A : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

theorem evaluations_allIndices (F : Formula) (A : Fin F.«variables» → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun «c» => «c».eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

theorem verifier_failureCount (F : Formula) (A : Fin F.«variables» → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end UniqueGames.Foundations.PCP.NameCompaction

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VerifierToCNF
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.compactLiteral_positive _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.BinaryFormula.eval_compact_extend _root_.OAI.UniqueGames.BinaryFormula.eval_compact_restrict _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.patternRelationIndex_eq _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.nBits_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.PCP.VerifierToCNF

open Target

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, «c»] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: «c» :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: «c» :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.«variables») :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, «c»], [] => [#v[a, b, «c»]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun «c» => «c».eval A)).count false

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun «c» => «c».eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, «c»] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun «c» => «c».eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun «c» hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) «c» hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

end UniqueGames.Foundations.PCP.VerifierToCNF

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

theorem rejection_count_eq [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) :
    VerifierToCNF.rejectedEventCount (verifier G vertices edges) assignment =
      G.rejectionCount (labelsOfBits vertices assignment) := by
  classical
  change ((List.finRange m).map
    (VerifierToCNF.eventValue (verifier G vertices edges) assignment)).count false = _
  rw [count_false_finRange]
  change (Finset.univ.filter (fun e : Fin m =>
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e = false)).card =
      (G.rejectedDarts (labelsOfBits vertices assignment)).card
  apply Finset.card_equiv edges.symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ConstraintGraph.rejectedDarts, eventValue_eq]

theorem verifier_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (labeling : V → Label)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, VerifierToCNF.eventValue (verifier G vertices edges)
      (bitsOfLabels vertices labeling) e = true := by
  intro e
  rw [eventValue_eq, labelsOfBits_bitsOfLabels]
  exact satisfied (edges.symm e)

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

theorem cnf_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (sat : G.Satisfiable) : (cnf G vertices edges).Satisfiable := by
  obtain ⟨labeling, satisfied⟩ := sat
  exact VerifierToCNF.convert_completeness (verifier G vertices edges) (by decide)
    (bitsOfLabels vertices labeling) (verifier_completeness G vertices edges labeling satisfied)

theorem cnf_count_bridge [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) :
    G.rejectionCount (extractLabeling G vertices edges assignment) ≤
      NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have h := VerifierToCNF.convert_count_bridge (verifier G vertices edges) (by decide) assignment
  rw [rejection_count_eq] at h
  exact h

theorem failedCount_zero_of_satisfied (F : Formula) (assignment : Fin F.«variables» → Bool)
    (satisfied : ∀ «c» ∈ F.clauses, «c».eval assignment = true) :
    NameCompaction.failedCount F assignment = 0 := by
  apply (VerifierToCNF.zero_false_count_iff_all _).mpr
  have h := List.all_eq_true.mpr satisfied
  simpa only [NameCompaction.evaluationList, List.all_map, Function.comp_def, id_eq] using h

theorem all_satisfied_of_rejectionCount_zero [Fintype E] (G : ConstraintGraph V E Label)
    (labeling : V → Label) (zero : G.rejectionCount labeling = 0) :
    ∀ e, G.edgeSatisfied labeling e = true := by
  intro e
  cases h : G.edgeSatisfied labeling e with
  | true => rfl
  | false =>
    have member : e ∈ G.rejectedDarts labeling := (G.mem_rejectedDarts labeling e).mpr h
    have positive : 0 < G.rejectionCount labeling := Finset.card_pos.mpr ⟨e, member⟩
    omega

theorem cnf_reflects [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (sat : (cnf G vertices edges).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨assignment, satisfied⟩ := sat
  have zero := failedCount_zero_of_satisfied (cnf G vertices edges) assignment satisfied
  have bound := cnf_count_bridge G vertices edges assignment
  have graphZero : G.rejectionCount (extractLabeling G vertices edges assignment) = 0 := by omega
  exact ⟨extractLabeling G vertices edges assignment,
    all_satisfied_of_rejectionCount_zero G _ graphZero⟩

theorem cnf_satisfiable_iff [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (cnf G vertices edges).Satisfiable ↔ G.Satisfiable :=
  ⟨cnf_reflects G vertices edges, cnf_completeness G vertices edges⟩

theorem cnf_variable_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).«variables» = n * 6 + m * 36864 := by
  change n * 6 + m * (VerifierToCNF.patterns 12).length * (12 - 3) = _
  rw [VerifierToCNF.patterns_length, Nat.mul_assoc, twelve_query_auxiliary_factor]

theorem cnf_nonempty (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (nonempty : 0 < m) : (cnf G vertices edges).clauses ≠ [] :=
  VerifierToCNF.convert_nonempty (verifier G vertices edges) (by decide) nonempty

theorem cnf_gap [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : Nat)
    (source : ∀ labeling : V → Label, a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (assignment : OutputAssignment G vertices edges) :
    a * (cnf G vertices edges).clauses.length ≤
      (b * 40960) * NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have cardEdges : Fintype.card E = m := by simpa using Fintype.card_congr edges
  have testGap (bits : Fin (n * 6) → Bool) :
      a * m ≤ b * VerifierToCNF.rejectedEventCount (verifier G vertices edges) bits := by
    rw [rejection_count_eq]
    simpa only [cardEdges] using source (labelsOfBits vertices bits)
  simpa only [cnf, VerifierToCNF.twelve_query_factor] using
    VerifierToCNF.convert_gap (verifier G vertices edges) (by decide) a b testGap assignment

end UniqueGames.Foundations.PCP.FinalBooleanVerifier

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceNonempty
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Hastad.SourceNonempty

open Target PCP

theorem real_clause_gap_of_count (F : Formula) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.«variables» → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment)
    (assignment : Fin F.«variables» → Bool) :
    (a : ℝ) / (b : ℝ) * F.clauses.length ≤
      (failureCount F assignment (allIndices F) : ℝ) := by
  rw [NameCompaction.verifier_failureCount]
  have hreal : (a : ℝ) * F.clauses.length ≤
      (b : ℝ) * (NameCompaction.failedCount F assignment : ℝ) := by
    exact_mod_cast hgap assignment
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hb)).mpr
  simpa only [mul_comm] using hreal

theorem clauseGap_of_count (F : Formula) (a b : ℕ) (hne : F.clauses ≠ [])
    (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.«variables» → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment) :
    SourceGap.ClauseGap F ((a : ℚ) / (b : ℚ)) := by
  refine ⟨hne, fun assignment => ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    real_clause_gap_of_count F a b hb hgap assignment

variable {V E : Type*} {n m : ℕ}

theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

theorem cnf_clauseGap [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      a * Fintype.card E ≤ b * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      ((a : ℚ) / ((b : ℚ) * 40960)) := by
  have h := clauseGap_of_count (FinalBooleanVerifier.cnf G vertices edges) a (b * 40960)
    (cnf_nonempty_of_nonempty_darts G vertices edges)
    (Nat.mul_pos hb (by decide)) (FinalBooleanVerifier.cnf_gap G vertices edges a b hgap)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

theorem cnf_clauseGap_unit [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (walkLength : ℕ)
    (hwalk : 0 < walkLength)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      Fintype.card E ≤ walkLength * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      (1 / (40960 * (walkLength : ℚ))) := by
  have h := cnf_clauseGap G vertices edges 1 walkLength hwalk
    (by simpa only [one_mul] using hgap)
  simpa only [Nat.cast_one, mul_comm] using h

end UniqueGames.Foundations.Hastad.SourceNonempty

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralReturn
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left («c» : ℝ) (f : A → ℝ) :
    mean (fun x => «c» * f x) = «c» * mean f :=
  (Finset.mul_expect _ f «c»).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) («c» : ℝ) :
    energy (fun x => f x - «c») = energy f - 2 * «c» * mean f + «c» ^ 2 := by
  have h : (fun x => (f x - «c») ^ 2) =
      (fun x => (f x) ^ 2 - (2 * «c») * f x + «c» ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

end Graph

end

end UniqueGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ZigzagGraphs
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

noncomputable section

def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end UniqueGames.Foundations.PCP.ZigzagGraphs

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ZigzagSpectral
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b «c» : A → ℝ) :
    energy (a + b + «c») ≤ 3 * (energy a + energy b + energy «c») := by
  calc
    energy (a + b + «c») ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + «c» x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + «c» x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + «c» x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - «c» x), sq_nonneg (b x - «c» x)]
    _ = 3 * (energy a + energy b + energy «c») := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let «c» := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + «c» := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + «c» =
      a + (cloudOperator H (graphPermutation G u) - a) + «c»
    funext x
    change cloudOperator H (graphPermutation G u) x + «c» x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + «c» x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy «c» ≤ lambdaH ^ 2 * energy v := by
    calc
      energy «c» ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + «c») ≤ 3 * (energy a + energy b + energy «c») := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end UniqueGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

end UniqueGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableEnumeration
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                  

namespace UniqueGames.Foundations.PCP.AlphabetTable.Enumeration

open UniqueGames.Foundations.Hastad
open scoped BigOperators

@[simp] theorem localCount_formula (q : Nat) :
    localCount q = 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5 := rfl

end UniqueGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_DegreeReplacement
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

open scoped BigOperators

namespace UniqueGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ «c», (paddedGraph G dummy).edgeSatisfied labeling «c» = true := by
  intro «c»
  cases «c» with
  | inl e => exact h e
  | inr z => rfl

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : G.edgeSatisfied labeling e = false <;> simp only [h, ite_true]

end UniqueGames.Foundations.PCP.DegreeReplacement

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Overlay
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                

open scoped BigOperators

namespace UniqueGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in
                                                                                       
theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

end UniqueGames.Foundations.PCP.Overlay

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLazy
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGames.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem averagingOperator_lazy [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (v : V) :
    averagingOperator (lazyGraph G) f v = (f v + averagingOperator G f v) / 2 := by
  change mean (fun bd : Bool × D => f ((lazyGraph G).rot (v, bd)).1) = _
  rw [mean_prod]
  change Finset.univ.expect (fun b : Bool =>
    mean (fun d : D => f ((lazyGraph G).rot (v, (b, d))).1)) = _
  rw [LazySmoothing.expect_bool]
  simp only [lazyGraph_rot_false, lazyGraph_rot_true]
  rw [mean_const]
  rfl

end UniqueGames.Foundations.PCP.PoweringLazy

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_LazyConstraint
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

end UniqueGames.Foundations.PCP.LazyConstraint

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_LazySpectral
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

noncomputable section

variable {V D : Type*}

theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end UniqueGames.Foundations.PCP.LazySpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end UniqueGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

end UniqueGames.Foundations.PCP.ExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CloudPadding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

end UniqueGames.Foundations.PCP.CloudPadding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CloudRounding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_cloudRank _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem mismatch_card_eq_sum (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (mismatchSet G ell rounded).card =
      ∑ v, (minoritySet (fun e : Cloud G v => ell e.val) (rounded v)).card := by
  have h := Fintype.card_congr (mismatchFiberEquiv G ell rounded)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem disagreement_card_eq_sum (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (innerDisagreementSet G H ell).card =
      ∑ v, (disagreementSet (fun e : Cloud G v => ell e.val)
        (fun ed => ((H v).rot ed).1)).card := by
  have h := Fintype.card_congr (disagreementFiberEquiv G H ell)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

theorem rounded_mismatch_expansion [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (h : ℚ)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell (roundLabels G ell)).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (roundLabels G ell v) h
    (majority_maximal (fun e : Cloud G v => ell e.val)) (expansion v)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
theorem rounded_endpoint_bound (G : ConstraintGraph V E A)
    (ell : E → A) (rounded : V → A) :
    G.rejectionCount rounded ≤ copiedRejectionCount G ell +
      2 * (mismatchSet G ell rounded).card :=
  dart_rejection_count_le G.tail G.reverse G.accepts ell rounded

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
                                                                                     
theorem replacement_rejection_split (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (replacementGraph G H).rejectionCount ell =
      copiedRejectionCount G ell + (innerDisagreementSet G H ell).card := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    copied_satisfied_inl, copied_satisfied_inr, decide_eq_false_iff_not,
    Fintype.sum_unique, Finset.sum_add_distrib]
  simp only [copiedRejectionCount, innerDisagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  exact Nat.add_comm _ _

theorem replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) :
    G.rejectionCount (roundLabels G ell) ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion G H ell 2 (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell (roundLabels G ell)).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell (roundLabels G ell)).trans
    (Nat.add_le_add_left hcNat _)

theorem padded_replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) :
    G.rejectionCount (roundLabels (paddedGraph G dummy) ell) ≤
      (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness (paddedGraph G dummy) H expansion ell

end GraphRounding

end UniqueGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

end UniqueGames.Foundations.PCP.Preprocessing
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ExpanderTables
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

def stepLookup {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    Fin (v * ((d * d) * (d * d))) × Fin (d * d) :=
  let vc := (rowIndex v ((d * d) * (d * d))).symm x.1
  let ports := (rowIndex d d).symm x.2
  let first := lookup H (vc.2, ports.1)
  let squarePorts := (rowIndex (d * d) (d * d)).symm first.1
  let outerFirst := lookup G (vc.1, squarePorts.1)
  let outerSecond := lookup G (outerFirst.1, squarePorts.2)
  let last := lookup H (rowIndex (d * d) (d * d) (outerSecond.2, outerFirst.2), ports.2)
  (rowIndex v ((d * d) * (d * d)) (outerSecond.1, last.1),
    rowIndex d d (last.2, first.2))

theorem lookup_step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    lookup (step G H) x = stepLookup G H x := by
  simp [step, stepGraph, GraphTransport.reindex,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, vertexIndex, Equiv.apply_symm_apply,
    ZigzagGraphs.zigzag, ZigzagGraphs.square, ZigzagGraphs.involutionEquiv,
    ZigzagGraphs.cloudFirst, ZigzagGraphs.crossCloud, graph_rot,
    stepLookup, Prod.map, Equiv.symm_symm]
  all_goals repeat' constructor

theorem step_certificate {v d : Nat} [NeZero v] [NeZero d]
    (G : Table v (d * d)) (H : Table ((d * d) * (d * d)) d)
    (hG : SpectralCertificate (graph G) (1 / 2 : ℝ))
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) :
    SpectralCertificate (graph (step G H)) (1 / 2 : ℝ) := by
  rw [step, graph_ofGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply ZigzagSpectral.square_zigzag_halfCertificate
  · exact hG
  · exact GraphTransport.reindex_spectralCertificate _ _ _ _ hH

def initial (d : Nat) : Table 1 (d * d) :=
  ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

theorem family_certificate {d : Nat} [NeZero d]
    (H : Table ((d * d) * (d * d)) d)
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph (family H n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact initial_certificate d
  | succ n ih =>
    let : NeZero (vertexCount (d * d) n) :=
      ⟨Nat.ne_of_gt (vertexCount_positive (Nat.mul_pos (NeZero.pos d) (NeZero.pos d)) n)⟩
    exact step_certificate _ _ ih hH

theorem exists_base_table : ∃ H : Table
    ((Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree,
    SpectralCertificate (graph H) (1 / 100 : ℝ) := by
  classical
  have hv : Fintype.card ExpanderFamily.CloudPort =
      (Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree) := by
    rw [ExpanderFamily.card_cloudPort]
    unfold ExpanderFamily.growth
    ring
  let vertices := Fintype.equivFinOfCardEq hv
  let ports := Fintype.equivFinOfCardEq Expanders.card_basePort
  let G := GraphTransport.reindex ExpanderFamily.baseOnCloud vertices ports
  refine ⟨ofGraph G, ?_⟩
  rw [graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    ExpanderFamily.baseOnCloud_certificate

end UniqueGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphGap
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem le_gap_iff [Nonempty E] (G : ConstraintGraph V E A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : V → A,
      ε * Fintype.card E ≤ (G.rejectionCount labeling : ℝ) := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  change ε ≤ (G.minimumRejections : ℝ) / Fintype.card E ↔ _
  rw [le_div_iff₀ he]
  constructor
  · intro h labeling
    exact h.trans (Nat.cast_le.mpr (G.minimumRejections_le labeling))
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    simpa only [heq] using h labeling

theorem inverse_card_le_gap_of_unsatisfiable [Nonempty E]
    (G : ConstraintGraph V E A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card E : ℝ) ≤ G.gap := by
  apply (G.le_gap_iff _).mpr
  intro labeling
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (1 : ℝ) ≤ (G.rejectionCount labeling : ℝ) := by
    exact_mod_cast G.rejectionCount_positive unsat labeling
  simpa only [div_mul_cancel₀ _ he] using hc

end Minimum

variable {W D B : Type*}

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end UniqueGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GenericGraphTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.GenericGraphTables

open UniqueGames.Foundations.Complexity

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) :
    ConstraintGraph (Fin n) (Fin m) (Label q) where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) : (Table q) :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

end UniqueGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableTable
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

theorem semantics_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

theorem edgeSatisfied_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    (GraphTables.semantics (build input)).edgeSatisfied
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)))
      (Enumeration.dartEquiv input.darts q dart) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).edgeSatisfied labeling dart := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_edgeSatisfied _ _ _ _ labeling dart

theorem rejectionCount_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6) :
    (GraphTables.semantics (build input)).rejectionCount
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).rejectionCount labeling := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_rejectionCount _ _ _ _ labeling

theorem perfect_completeness [Nonempty (Fin q)] (input : GenericGraphTables.Table q)
    (satisfied : (GenericGraphTables.semantics input).Satisfiable) :
    (GraphTables.semantics (build input)).Satisfiable := by
  obtain ⟨labeling, accepted⟩ :=
    AlphabetGraph.perfect_completeness (GenericGraphTables.semantics input) satisfied
  refine ⟨fun v => Enumeration.labelEquiv
    (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)), ?_⟩
  intro index
  have h := edgeSatisfied_build input labeling
    ((Enumeration.dartEquiv input.darts q).symm index)
  have index_eq := (Enumeration.dartEquiv input.darts q).apply_symm_apply index
  rw [index_eq] at h
  exact h.trans (accepted _)

end UniqueGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.NatWalkMachine
open UniqueGames.Foundations.PCP

abbrev State (d : ℕ) := PortTables.Input d × ℕ

end VertexCover.Machine.NatWalkMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetGraphBounds
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith

end UniqueGames.Foundations.PCP.AlphabetGraphBounds

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_InitialGraph
attribute [-instance] _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerInhabited _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.BinaryFormula.eval_compact_extend _root_.OAI.UniqueGames.BinaryFormula.eval_compact_restrict _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_J _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_clauseAnswer _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_slot _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.InitialGraph

open Target

abbrev Vertex (F : Formula) := (Fin F.«variables» ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

def variableVertex (F : Formula) (v : Fin F.«variables») : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()
def dummyDart (F : Formula) : Dart F := .inr ()

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩
instance dartNonempty (F : Formula) : Nonempty (Dart F) := ⟨dummyDart F⟩

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

def honestLabeling (F : Formula) (A : Fin F.«variables» → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

theorem incidence_honest (F : Formula) (A : Fin F.«variables» → Bool)
    (sat : ∀ «c» ∈ F.clauses, «c».eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.«variables» → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun «c» hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.«variables» + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end UniqueGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetRetraction
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b «c» => G.accepts e (decode b) (decode «c»)
  reverse_accepts := fun e b «c» => G.reverse_accepts e (decode b) (decode «c»)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

theorem satisfiable_pullback_iff (G : ConstraintGraph V E A)
    (decode : B → A) (encode : A → B) (sectionLaw : ∀ a, decode (encode a) = a) :
    (pullback G decode).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    exact ⟨decode ∘ labeling, h⟩
  · rintro ⟨labeling, h⟩
    refine ⟨encode ∘ labeling, fun e => ?_⟩
    change G.accepts e (decode (encode (labeling (G.tail e))))
      (decode (encode (labeling (G.head e)))) = true
    simpa only [ConstraintGraph.edgeSatisfied, sectionLaw] using h e

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, «c»⟩
  rfl

end UniqueGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetTableBounds
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

theorem build_darts (input : GenericGraphTables.Table q) :
    (Table.build input).darts = input.darts * AlphabetGraphBounds.dartFactor q := by
  rw [Table.build_darts]
  simp only [Enumeration.dartCount, Enumeration.eventCount, Enumeration.localCount,
    Enumeration.tapeCount, Enumeration.pairTapeCount, Enumeration.fiveTapeCount,
    AlphabetGraphBounds.dartFactor, AlphabetGraphBounds.localEventFactor]
  ring

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

end UniqueGames.Foundations.PCP.AlphabetTableBounds

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalConstants
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.FinalConstants

def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def windowSize : Nat := 2 * windowHalf + 1
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end UniqueGames.Foundations.PCP.FinalConstants

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringReach
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end UniqueGames.Foundations.PCP.PoweringReach

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringTest
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringEnumeration.decodeLabel_encodeLabel _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach

variable {V D A : Type*}

def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

end UniqueGames.Foundations.PCP.PoweringTest

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AmplificationRound
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                           

noncomputable section

namespace UniqueGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end UniqueGames.Foundations.PCP.AmplificationRound
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FiniteGraph
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                    
section

noncomputable section

namespace UniqueGames.Foundations.PCP.FiniteGraph

structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype
instance instDecidableEqVertex (G : Bundle A) : DecidableEq G.Vertex := G.vertexDecidableEq
instance instDecidableEqDart (G : Bundle A) : DecidableEq G.Dart := G.dartDecidableEq
instance instNonemptyDart (G : Bundle A) : Nonempty G.Dart := G.dartNonempty

instance instNonemptyVertex (G : Bundle A) : Nonempty G.Vertex := by
  obtain ⟨d⟩ := G.dartNonempty
  exact ⟨G.graph.tail d⟩

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

end Bundle

end UniqueGames.Foundations.PCP.FiniteGraph

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringAddresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

namespace UniqueGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end UniqueGames.Foundations.PCP.PoweringAddresses

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PCPIteration
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                     
section

noncomputable section

namespace UniqueGames.Foundations.PCP.PCPIteration

open FiniteGraph

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

end UniqueGames.Foundations.PCP.PCPIteration

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalTableFormula
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).«variables» = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

theorem clauseGap (table : GraphTables.Table) (hd : 0 < table.darts)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling) :
    Hastad.SourceGap.ClauseGap (output table) PCPIteration.finalClauseGap := by
  let : Nonempty (Fin table.darts) := ⟨⟨0, hd⟩⟩
  exact Hastad.SourceNonempty.cnf_clauseGap_unit (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) FinalConstants.walkLength
    FinalConstants.walkLength_positive (tableGraph_count_lower table _ hgap)

end UniqueGames.Foundations.PCP.FinalTableFormula
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringPortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

noncomputable section
namespace UniqueGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

end UniqueGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ReductionSound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
noncomputable section

def baseGap : ℝ := (PCP.PCPIteration.finalClauseGap : ℝ) / 3

end
end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


