-- Prove2me | Definitions.Def_OAIQ076M010
-- name    : OAIQ076M010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:05:43.624975+00:00
-- url     : https://prove2.me/theorems/d61b67cf-c4ac-4715-aa3c-c97dcdd1ac00
-- title:
--   Definitions bundle OAIQ076M010 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 296 declarations of OpenAI's Lean: 79 definitions, 1 inductive type or structure, 4 instances and 212 theorems. The definitions and types are `OAI.MinUncut.Enumeration.bind`, `OAI.MinUncut.Enumeration.filterSubtype`, `OAI.MinUncut.Enumeration.mapEquiv`, `OAI.MinUncut.FiniteGaussian.cell`, `OAI.MinUncut.FiniteGaussian.cubeCell`, `OAI.MinUncut.FiniteGaussian.gCell`, `OAI.MinUncut.FiniteGaussian.gridStep`, `OAI.MinUncut.FiniteGaussian.qCell`, `OAI.MinUncut.GaussianBudget.packEquiv`, `OAI.MinUncut.Inner.evaluationProof`, `OAI.MinUncut.Inner.labelFunctional`, `OAI.MinUncut.OuterSmoothness.JointForms.Block`, `OAI.MinUncut.OuterSmoothness.JointForms.HiddenRaw`, `OAI.MinUncut.OuterSmoothness.JointForms.densityDualDecidableEq`, `OAI.MinUncut.OuterSmoothness.JointForms.dualFintype`, `OAI.MinUncut.OuterSmoothness.hiddenDensity`, `OAI.MinUncut.OuterSmoothness.mixture`, `OAI.MinUncut.PathRealization.edge`, `OAI.MinUncut.PathRealization.edgePair`, `OAI.MinUncut.PathRealization.edgeSet`, `OAI.MinUncut.PathRealization.extend`, `OAI.MinUncut.PathRealization.graph`, `OAI.MinUncut.PathRealization.output`, `OAI.MinUncut.PathRealization.uncut`, `OAI.MinUncutGames.BinaryEncoding.namesBitSize`, `OAI.MinUncutGames.BinaryOccurrenceRename.clause`, `OAI.MinUncutGames.BinaryOccurrenceRename.literal`, `OAI.MinUncutGames.BinaryOccurrenceRename.renamed`, `OAI.MinUncutGames.BinaryRenameWords.token`, `OAI.MinUncutGames.BinaryTokenMachine.cfg`, `OAI.MinUncutGames.BinaryTokenMachine.machine`, `OAI.MinUncutGames.BinaryTokenMachine.program`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program.Tape.enumList`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program.source`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFPattern.leftHalf`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFPattern.rightHalf`, `OAI.MinUncutGames.Foundations.Complexity.MachineCopy.drainedTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineDrainMany.haltTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineDrainMany.lengthSum`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.cutAt` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianDensityError`, `MinUncut_Analysis_GaussianPacking`, `MinUncut_Analysis_GaussianRows`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Analysis_LiteralGaussian`, `MinUncut_Encoding_Serialization`, `MinUncut_Encoding_ThreeBitTest`, `MinUncut_Estimates_AlgebraicSigns`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_LiftedVectors`, `MinUncut_Estimates_TableTestFunctions`, `MinUncut_Games_Basic`, `MinUncut_Games_FinalCNFPattern`, `MinUncut_Games_FiniteNoise`, `MinUncut_Games_HintSections`, `MinUncut_Games_HintSimulation`, `MinUncut_Games_KernelSampling`, `MinUncut_Games_LabelBound`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_GraphOutput`, `MinUncut_Graphs_HonestComparisons`, `MinUncut_Graphs_HonestRows`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Machines_MachineBinaryFormula`, `MinUncut_Machines_MachineBinaryNameMachine`, `MinUncut_Machines_MachineBinaryOccurrenceRename`, `MinUncut_Machines_MachineBinaryParsing`, `MinUncut_Machines_MachineDrain`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineFiniteSequence`, `MinUncut_Machines_MachineUnaryCounter`, `MinUncut_Machines_RawInitialMachineFinish`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ClauseVerifier`, `MinUncut_PCP_Completion`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_Folding`, `MinUncut_PCP_Generator`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_HonestTest`, `MinUncut_PCP_InitialGraph`, `MinUncut_PCP_Occurrences`, `MinUncut_PCP_Overlap`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SelectedInformation`, `MinUncut_PCP_SelectedLikelihood`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_TableIteration`, `MinUncut_PCP_Walsh`, `MinUncut_Search_EnumerationPlain`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_RationalBasics`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002`, `OAIQ076M003` and `OAIQ076M004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M018`, `OAIQ076M019` and `OAIQ076M020`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003
import Definitions.Def_OAIQ076M004

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Walsh
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_ThreeBitTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def support (s : Cube I) : Finset I := Finset.univ.filter fun i => s i = true

def noiseWeight (ε : ℝ) (μ : Cube I) : ℝ :=
  ∏ i, if μ i then ε else 1 - ε

theorem noiseWeight_sum (ε : ℝ) : (∑ μ : Cube I, noiseWeight ε μ) = 1 := by
  unfold noiseWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then ε else 1 - ε)]
  simp

theorem noise_walsh (ε : ℝ) (s : Cube I) :
    (∑ μ, noiseWeight ε μ * walsh s μ) = (1 - 2 * ε) ^ (support s).card := by
  unfold noiseWeight walsh
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if b then ε else 1 - ε) * bitSign (s i && b))]
  have hc (i : I) : (∑ b : Bool,
      (if b then ε else 1 - ε) * bitSign (s i && b)) =
        if s i then 1 - 2 * ε else 1 := by
    cases s i <;> simp [bitSign]
    ring
  simp_rw [hc]
  simp [support, Finset.prod_ite]

def testAcceptance (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Folding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end MinUncutGames.Foundations.Hastad

end
namespace MinUncutGames.Reduction.CloneGap

variable {α β : Type*} {Name : Type}

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs

end MinUncutGames.Reduction.CloneGap

namespace MinUncutGames.Foundations.Hastad.FoldedEquation

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

theorem correction_eq (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) :
    (f i₀ ^^ g j₀ ^^ thirdQuery π f g μ j₀) = rhsCorrection π i₀ j₀ f μ := by
  change (f i₀ ^^ g j₀ ^^ (g j₀ ^^ (f (π j₀) ^^ μ j₀))) =
    (f i₀ ^^ f (π j₀) ^^ μ j₀)
  cases f i₀ <;> cases g j₀ <;> cases f (π j₀) <;> cases μ j₀ <;> rfl

theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _

theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl

theorem restrict_thirdQuery (valid : J → Bool) (π : J → I)
    (f : Cube I) (g μ : Cube J) :
    restrictQuery valid (thirdQuery π f g μ) =
      thirdQuery (fun j : {j : J // valid j = true} => π j.val) f
        (restrictQuery valid g) (restrictQuery valid μ) := rfl

theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]

end MinUncutGames.Foundations.Hastad.FoldedEquation

namespace MinUncutGames.Foundations.Hastad

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type}

theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl

end EmptyContext
end MinUncutGames.Foundations.Hastad

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Serialization
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity

open Target

theorem literalBits_length_le {n : Nat} (literal : Literal n) :
    (encodeWords (literalWords literal)).length ≤ n + 2 := by
  have hindex := literal.variableIndex.isLt
  cases hp : literal.positive <;> simp [literalWords, hp]

theorem clauseBits_length_le {n : Nat} (clause : Clause n) :
    (encodeWords (clauseWords clause)).length ≤ 3 * (n + 2) := by
  have h0 := literalBits_length_le clause[0]
  have h1 := literalBits_length_le clause[1]
  have h2 := literalBits_length_le clause[2]
  simp only [clauseWords, encodeWords_append, List.length_append]
  omega

theorem clausesBits_length_le {n : Nat} (clauses : List (Clause n)) :
    (encodeWords (clauses.flatMap clauseWords)).length ≤ clauses.length * (3 * (n + 2)) := by
  induction clauses with
  | nil => simp [encodeWords]
  | cons clause clauses ih =>
      have hc := clauseBits_length_le clause
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem formulaBits_length_le (formula : Formula) :
    (formulaBits formula).length ≤
      formula.«variables» + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.«variables» + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MinUncutGames.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseVerifier
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP

open Target

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

end MinUncutGames.Foundations.PCP

end
section
namespace MinUncutGames.Foundations.Hastad.SourceContexts

open Target PCP

instance slotInhabited : Inhabited Slot := ⟨.first⟩

theorem canonicalSlot_name {n : ℕ} (clause : Clause n) (v : Fin n)
    (hv : ∃ s, nameAt clause s = v) : nameAt clause (canonicalSlot clause v) = v := by
  by_cases hfirst : nameAt clause .first = v
  · simp [canonicalSlot, hfirst]
  by_cases hsecond : nameAt clause .second = v
  · simp [canonicalSlot, hfirst, hsecond]
  obtain ⟨s, hs⟩ := hv
  cases s with
  | first => exact False.elim (hfirst hs)
  | second => exact False.elim (hsecond hs)
  | third => simpa [canonicalSlot, hfirst, hsecond] using hs

theorem sampledVariables_supported (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) :
    ∀ t, ∃ slot, nameAt (clauseAt F (c t)) slot = sampledVariables F c s t :=
  fun t => ⟨s t, rfl⟩

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.«variables» → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

theorem pi_honest_sampled (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (assignment : Fin F.«variables» → Bool) :
    pi F c (sampledVariables F c s) (honestJ F c assignment) =
      honestI F (sampledVariables F c s) assignment :=
  pi_honest F c _ assignment (sampledVariables_supported F c s)

end MinUncutGames.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FiniteNoise
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Reduction.FiniteNoise

open scoped BigOperators
open MinUncutGames.Foundations.Hastad (noiseWeight)

theorem realizedBit_eq_true_iff {D : Nat} (positive : 0 < D) (z : Fin D) :
    realizedBit z = true ↔ z = ⟨0, positive⟩ := by
  simp [realizedBit, Fin.ext_iff]

theorem coordinate_fiber_sum {D : Nat} (positive : 0 < D) (b : Bool) :
    (∑ z : Fin D, if realizedBit z = b then (D : ℝ)⁻¹ else 0) =
      if b then (D : ℝ)⁻¹ else 1 - (D : ℝ)⁻¹ := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have ht : (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) =
      (D : ℝ)⁻¹ := by
    simp_rw [realizedBit_eq_true_iff positive]
    simp
  have htotal :
      (∑ z : Fin D, if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
      (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    have he (z : Fin D) :
        (if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
          (if realizedBit z = true then (D : ℝ)⁻¹ else 0) = (D : ℝ)⁻¹ := by
      cases realizedBit z <;> simp
    simp_rw [he]
    simp [hd]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · linarith
  · exact ht

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem noiseWeight_eq_fiber_sum {D : Nat} (positive : 0 < D) (μ : A → Bool) :
    noiseWeight ((D : ℝ)⁻¹) μ =
      ∑ z : A → Fin D,
        ∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0 := by
  rw [← Fintype.prod_sum (fun (a : A) (z : Fin D) =>
    if realizedBit z = μ a then (D : ℝ)⁻¹ else 0)]
  unfold noiseWeight
  apply Finset.prod_congr rfl
  intro a _
  exact (coordinate_fiber_sum positive (μ a)).symm

omit [DecidableEq A] in
theorem fiber_product_eq_indicator {D : Nat} (z : A → Fin D) (μ : A → Bool) :
    (∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0) =
      if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0 := by
  classical
  by_cases h : realizedNoise z = μ
  · rw [ite_eq_left h]
    have ha (a : A) : realizedBit (z a) = μ a := congrFun h a
    simp [ha]
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact ite_eq_right ha

theorem expect_realizedNoise {D : Nat} (positive : 0 < D) (H : (A → Bool) → ℝ) :
    (𝔼 z : A → Fin D, H (realizedNoise z)) =
      ∑ μ : A → Bool, noiseWeight ((D : ℝ)⁻¹) μ * H μ := by
  classical
  symm
  simp_rw [noiseWeight_eq_fiber_sum positive, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [fiber_product_eq_indicator]
  have he (z : A → Fin D) :
      (∑ μ : A → Bool,
        (if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0) * H μ) =
      ((D : ℝ)⁻¹) ^ Fintype.card A * H (realizedNoise z) := by
    simp [eq_comm]
  simp_rw [he]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_eq_mul_inv, inv_pow]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

end MinUncutGames.Reduction.FiniteNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HonestTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open MinUncutGames.Reduction.FiniteNoise

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

theorem dictator_test_parity (π : J → I) (i : I) (j : J) (hπ : π j = i)
    (f : Cube I) (g μ : Cube J) :
    (f i ^^ g j ^^ (thirdQuery π f g μ) j) = μ j := by
  simp only [thirdQuery, cubeXor, hπ]
  cases f i <;> cases g j <;> cases μ j <;> rfl

def realizedTestAcceptance (D : Nat) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J,
    if A f ^^ B g ^^ B (thirdQuery π f g (realizedNoise z)) then 0 else 1

theorem realizedTestAcceptance_eq_testAcceptance {D : Nat} (positive : 0 < D)
    (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) :
    realizedTestAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  unfold realizedTestAcceptance testAcceptance
  apply Finset.expect_congr rfl
  intro f _
  exact expect_realizedNoise positive
    (fun μ => 𝔼 g : Cube J, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

end MinUncutGames.Foundations.Hastad

namespace MinUncutGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open MinUncutGames.Reduction.FiniteNoise

section Tape

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {D : ℕ}

theorem expect_testTape (H : TestTape I J D → ℝ) :
    (𝔼 t : TestTape I J D, H t) =
      𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J, H (f, z, g) := by
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro f _
  exact expect_prod _

def tapeAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 t : TestTape I J D,
    if A t.1 ^^ B t.2.2 ^^ B (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))
      then 0 else 1

theorem tapeAcceptance_eq_realizedTestAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = realizedTestAcceptance D π A B :=
  expect_testTape _

theorem tapeAcceptance_eq_testAcceptance (positive : 0 < D) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  rw [tapeAcceptance_eq_realizedTestAcceptance,
    realizedTestAcceptance_eq_testAcceptance positive]

end Tape

end MinUncutGames.Foundations.Hastad.SourceTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Occurrences
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceOccurrences

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

namespace Encoding

theorem card_eq_size {α : Type} [Fintype α] (a : Encoding α) :
    Fintype.card α = a.size := by
  simpa only [Fintype.card_fin] using Fintype.card_congr a.code

end Encoding

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedOccurrence_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (bits : Fin (globalEncoding vE cE iE jE).size → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ) bits =
      !(foldedAnswer i₀ (fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))) f ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) g ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) (thirdQuery π f g μ)) := by
  rw [conditionedOccurrence, satisfied_mapEquation]
  let tableA : HalfCube i₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))
  let tableB : HalfCube j₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code
      (.inr (.inl (c, extendRestricted valid h.val))))
  have hbits : bits ∘ localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment tableA tableB := by
    funext a
    cases a <;> rfl
  rw [hbits]
  exact FoldedEquation.conditionedEquation_satisfied valid π i₀ j₀ tableA tableB f g μ

end LocalEquations

theorem countP_enumerate {Tape : Type} [Fintype Tape]
    (tape : Encoding Tape) (p : Tape → Bool) :
    (tape.enumerate.countP p : ℝ) = ∑ x, if p x then (1 : ℝ) else 0 := by
  rw [countP_cast_eq_sum]
  simp only [Encoding.enumerate, List.map_ofFn, List.sum_ofFn]
  exact Fintype.sum_equiv tape.code.symm _ _ (fun _ => rfl)

theorem occurrenceList_acceptance {Tape Name : Type} [Fintype Tape]
    (tape : Encoding Tape) (emit : Tape → Equation Name) (bits : Name → Bool) :
    ((occurrenceList tape emit).countP (fun e => satisfied e bits) : ℝ) /
        (occurrenceList tape emit).length =
      𝔼 x, if satisfied (emit x) bits then (1 : ℝ) else 0 := by
  rw [occurrenceList_length, Fintype.expect_eq_sum_div_card, tape.card_eq_size]
  congr 1
  simpa only [occurrenceList, List.countP_map, Function.comp_def] using
    countP_enumerate tape (fun x => satisfied (emit x) bits)

section ConcreteSource

open SourceContexts
open MinUncutGames.Reduction.FiniteNoise

theorem contextEquation_satisfied (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) (bits : Fin (nBits F u) → Bool) :
    satisfied (contextEquation F u D c v t) bits =
      !(leftResponse F u bits v t.1 ^^ rightResponse F u bits c t.2.2 ^^
        rightResponse F u bits c (thirdQuery (pi F c v) t.1 t.2.2 (realizedNoise t.2.1))) := by
  cases ha : rightAnchor F c with
  | none =>
    simp only [contextEquation, ha, satisfied_mapEquation, EmptyContext.equation_satisfied,
      rightResponse, Bool.xor_false]
    rfl
  | some j₀ =>
    simp only [contextEquation, ha, rightResponse]
    exact conditionedOccurrence_satisfied (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      bits t.1 t.2.2 (realizedNoise t.2.1)

theorem rawSourceList_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (bits : Fin (nBits F u) → Bool) :
    ((rawSourceList F u D).countP (fun e => satisfied e bits) : ℝ) /
        (rawSourceList F u D).length =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
          (leftResponse F u bits (sampledVariables F c s)) (rightResponse F u bits c) := by
  rw [rawSourceList, occurrenceList_acceptance, SourceTape.expect_prod]
  rw [SourceTape.expect_prod]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro s _
  rw [← SourceTape.tapeAcceptance_eq_testAcceptance hD]
  unfold SourceTape.tapeAcceptance
  apply Finset.expect_congr rfl
  intro t _
  rw [sourceEquation, contextEquation_satisfied]
  cases h : leftResponse F u bits (sampledVariables F c s) t.1 ^^
    rightResponse F u bits c t.2.2 ^^
      rightResponse F u bits c
        (thirdQuery (pi F c (sampledVariables F c s)) t.1 t.2.2 (realizedNoise t.2.1)) <;> rfl

end ConcreteSource

end MinUncutGames.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

lemma density_bounds {T v : ℝ} (hT : 0 ≤ T) (hv : |v| ≤ T) (r : ℕ) :
    0 ≤ densityPolynomial r v-Real.exp (-v^2/2) ∧
      densityPolynomial r v-Real.exp (-v^2/2) ≤ error r (T^2/2) := by
  have hu : 0 ≤ v^2/2 := by positivity
  have hb : v^2/2 ≤ T^2/2 := by
    have hh := (sq_le_sq₀ (abs_nonneg v) hT).mpr hv
    rw [sq_abs] at hh
    linarith
  obtain ⟨h0,h1⟩ := evenExp_error hu r
  have he : error r (v^2/2) ≤ error r (T^2/2) := by
    unfold error
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hu hb _) (by positivity)
  simpa only [densityPolynomial,neg_div] using ⟨h0,h1.trans he⟩

open scoped BigOperators
open MeasureTheory

lemma endpoint_zero (T : ℚ) (L : ℕ) : endpoint T L 0 = -T := by simp [endpoint]
lemma endpoint_end (T : ℚ) {L : ℕ} (hL : 0 < L) : endpoint T L L=T := by
  have hh : (L:ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold endpoint
  field_simp
  ring

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

lemma endpoint_mono {T : ℚ} (hT : 0 ≤ T) {L i j : ℕ} (hij : i ≤ j) :
    endpoint T L i ≤ endpoint T L j := by
  unfold endpoint
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)

def cell (T : ℚ) (L : ℕ) (i : Fin L) : Set ℝ :=
  Ioc (endpoint T L i) (endpoint T L (i+1))

lemma cell_subset {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (i : Fin L) :
    cell T L i ⊆ Ioc (-(T:ℝ)) T := by
  apply Ioc_subset_Ioc
  · have hh := endpoint_mono hT (Nat.zero_le i.val) (L := L)
    rw [endpoint_zero] at hh
    exact_mod_cast hh
  · have hh := endpoint_mono hT (Nat.succ_le_of_lt i.isLt) (L := L)
    rw [endpoint_end T hL] at hh
    exact_mod_cast hh

lemma exists_cell {T : ℚ} {L : ℕ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Ioc (-(T:ℝ)) T) :
    ∃ i : Fin L, x ∈ cell T L i := by
  have hh := Ioc_subset_biUnion_Ioc L (fun i => (endpoint T L i:ℝ))
  rw [endpoint_zero,endpoint_end T hL] at hh
  have hx' := hh (by simpa only [Rat.cast_neg] using hx)
  obtain ⟨i,hi,hx'⟩ := Set.mem_iUnion₂.mp hx'
  exact ⟨⟨i,Finset.mem_range.mp hi⟩,hx'⟩

lemma disjoint_cells {T : ℚ} (hT : 0 ≤ T) {L : ℕ} {i j : Fin L} (hij : i ≠ j) :
    Disjoint (cell T L i) (cell T L j) := by
  rcases lt_or_gt_of_ne hij with h|h
  · apply Set.Ioc_disjoint_Ioc_of_le
    exact_mod_cast endpoint_mono hT (show i.val+1 ≤ j.val by exact Nat.succ_le_of_lt h) (L := L)
  · apply Disjoint.symm
    apply Set.Ioc_disjoint_Ioc_of_le
    exact_mod_cast endpoint_mono hT (show j.val+1 ≤ i.val by exact Nat.succ_le_of_lt h) (L := L)

variable {ι : Type*} [Fintype ι]
def cubeCell (T : ℚ) (L : ℕ) (j : ι → Fin L) : Set (ι → ℝ) := Set.pi Set.univ (fun i => cell T L (j i))

lemma cubeCell_measurable (T : ℚ) (L : ℕ) (j : ι → Fin L) : MeasurableSet (cubeCell T L j) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioc)

omit [Fintype ι] in
lemma cubeCell_subset {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (j : ι → Fin L) :
    cubeCell T L j ⊆ cube T := by
  intro x hx i hi
  exact cell_subset hT hL (j i) (hx i hi)

omit [Fintype ι] in
lemma cube_union {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) :
    (⋃ j : ι → Fin L, cubeCell T L j)=cube T := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (cubeCell_subset hT hL)
  · intro x hx
    have hh : ∀ i : ι, ∃ j : Fin L, x i ∈ cell T L j := fun i => exists_cell hL (hx i (by simp))
    choose j hj using hh
    exact Set.mem_iUnion.mpr ⟨j,fun i _ => hj i⟩

omit [Fintype ι] in
lemma cubeCell_disjoint {T : ℚ} (hT : 0 ≤ T) {L : ℕ} {j k : ι → Fin L} (hjk : j ≠ k) :
    Disjoint (cubeCell T L j) (cubeCell T L k) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hjk
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (disjoint_cells hT hi) (hx i (by simp)) (hy i (by simp))

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def gridStep (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ j, (cubeCell T L j).indicator (fun _ => F j) x

lemma gridStep_of_mem {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (F : (ι → Fin L) → ℝ)
    {j : ι → Fin L} {x : ι → ℝ} (hx : x ∈ cubeCell T L j) :
    gridStep T L F x=F j := by
  unfold gridStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro k _ hk
    exact Set.indicator_of_notMem (fun hkx =>
      Set.disjoint_left.mp (cubeCell_disjoint hT hk) hkx hx) _
  · simp

lemma gridStep_of_notMem {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) {x : ι → ℝ} (hx : x ∉ cube T) : gridStep T L F x=0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact Set.indicator_of_notMem (fun hj => hx (cubeCell_subset hT hL j hj)) _

lemma gridStep_range {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) (hF : ∀ j, 0 ≤ F j ∧ F j ≤ 1) (x : ι → ℝ) :
    0 ≤ gridStep T L F x ∧ gridStep T L F x ≤ 1 := by
  by_cases hx : x ∈ cube T
  · rw [← cube_union hT hL] at hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    simpa only [gridStep_of_mem hT F hj] using hF j
  · rw [gridStep_of_notMem hT hL F hx]; norm_num

lemma gridStep_integrable {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) : Integrable (gridStep T L F) μ := by
  exact integrable_finsetSum _ (fun j _ => (integrable_const (F j)).indicator (cubeCell_measurable T L j))

lemma integral_gridStep {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) :
    (∫ x, gridStep T L F x ∂μ)=∑ j, μ.real (cubeCell T L j)*F j := by
  unfold gridStep
  rw [integral_finsetSum _ (fun j _ => (integrable_const (F j)).indicator (cubeCell_measurable T L j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (cubeCell_measurable T L j),setIntegral_const,smul_eq_mul]

lemma setIntegral_gridStep {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (F : (ι → Fin L) → ℝ) :
    (∫ x in cube T, gridStep T L F x ∂μ)=∑ j, μ.real (cubeCell T L j)*F j := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => gridStep_of_notMem hT hL F hx)]
  exact integral_gridStep T L F

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

omit [Fintype S] in
lemma thresholdTable_measurable (v : S → ι → ℝ) : Measurable (thresholdTable v) := by
  apply Measurable.of_eval
  intro s
  exact thresholdBit_measurable.comp (by unfold score; fun_prop)

lemma tableTest_integrable (v : S → ι → ℝ) (F : (S → Bool) → ℝ)
    (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    Integrable (fun x => F (thresholdTable v x)) (gaussianLaw ι) := by
  apply Integrable.of_bound ((measurable_of_countable F).comp (thresholdTable_measurable v)).aestronglyMeasurable 1
  filter_upwards [] with x
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (hF _).1] using (hF (thresholdTable v x)).2

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDensityError
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace MinUncut.FiniteGaussian

lemma residual_bounds {T : ℚ} (hT : 0 ≤ T) (r : ℕ) :
    0 ≤ (qIntegral r (-T) T:ℝ)-gIntegral (-T) T ∧
      (qIntegral r (-T) T:ℝ)-gIntegral (-T) T ≤ 2*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT' : (0:ℝ) ≤ T := by exact_mod_cast hT
  have hh : (qIntegral r (-T) T:ℝ)-gIntegral (-T) T =
      ∫ v in -(T:ℝ)..(T:ℝ), densityPolynomial r v-baseDensity v := by
    rw [qIntegral_cast]
    push_cast
    rw [intervalIntegral.integral_sub (continuous_density r |>.intervalIntegrable _ _)
      (continuous_baseDensity.intervalIntegrable _ _)]
    rfl
  rw [hh]
  have hf : IntervalIntegrable (fun v => densityPolynomial r v-baseDensity v) volume (-T) T :=
    ((continuous_density r).sub continuous_baseDensity).intervalIntegrable _ _
  constructor
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro v hv
    exact (density_bounds hT' (abs_le.mpr hv) r).1
  · have hb := intervalIntegral.integral_mono_on (a := -(T:ℝ)) (b := (T:ℝ))
      (by linarith) hf intervalIntegrable_const
      (fun v hv => (density_bounds hT' (abs_le.mpr hv) r).2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_neg_eq_add,two_mul] using hb

open scoped BigOperators
open MeasureTheory

def gCell (T : ℚ) (L : ℕ) (i : Fin L) : ℝ :=
  gIntegral (endpoint T L i) (endpoint T L (i+1))

def qCell (r : ℕ) (T : ℚ) (L : ℕ) (i : Fin L) : ℝ :=
  qIntegral r (endpoint T L i) (endpoint T L (i+1))

lemma sum_gCell (T : ℚ) {L : ℕ} (hL : 0 < L) :
    (∑ i : Fin L, gCell T L i)=gIntegral (-T) T := by
  unfold gCell gIntegral
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ v in (endpoint T L i:ℝ)..(endpoint T L (i+1):ℝ), baseDensity v)]
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => continuous_baseDensity.intervalIntegrable _ _)]
  rw [endpoint_zero,endpoint_end T hL]
  norm_cast

lemma sum_qCell (r : ℕ) (T : ℚ) {L : ℕ} (hL : 0 < L) :
    (∑ i : Fin L, qCell r T L i)=(qIntegral r (-T) T:ℝ) := by
  unfold qCell qIntegral
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((primitive r (endpoint T L (i+1))-primitive r (endpoint T L i):ℚ):ℝ))]
  push_cast
  rw [Finset.sum_range_sub (fun i => (primitive r (endpoint T L i):ℝ)),endpoint_zero,endpoint_end T hL]

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiftedVectors
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianBudget
attribute [local instance] Classical.propDecidable
variable {X C : Type*} [Fintype X] [Fintype C]

lemma liftVector_norm_sq (v : X → ℝ) (σ η : ℝ) (z : C) :
    ‖vector (liftVector v σ η z)‖^2=(1+σ^2)*‖vector v‖^2+η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,vector,Fintype.sum_sum_type,liftVector,mul_pow,ite_pow,zero_pow (by norm_num : (2:ℕ)≠0)]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma liftVector_base_norm (v : X → ℝ) (hv : ‖vector v‖=1) (z : C) :
    ‖vector (liftVector v 0 0 z)‖=1 := by
  have h := liftVector_norm_sq v 0 0 z
  rw [hv] at h
  have hn := norm_nonneg (vector (liftVector v 0 0 z))
  nlinarith

lemma liftVector_norm_pos (v : X → ℝ) (hv : ‖vector v‖=1) (σ η : ℝ) (z : C) :
    1 ≤ ‖vector (liftVector v σ η z)‖ := by
  have h := liftVector_norm_sq v σ η z
  rw [hv] at h
  have hn := norm_nonneg (vector (liftVector v σ η z))
  nlinarith [sq_nonneg σ,sq_nonneg η]

lemma liftVector_perturb_sq (v : X → ℝ) (σ η : ℝ) (z : C) :
    ‖vector (liftVector v 0 0 z)-vector (liftVector v σ η z)‖^2=
      σ^2*‖vector v‖^2+η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,Fintype.sum_sum_type,liftVector,
    zero_mul,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero,zero_sub,neg_sq,mul_pow]
  rw [← Finset.mul_sum]
  simp [ite_pow]

lemma liftVector_perturb_le (v : X → ℝ) (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    ‖vector (liftVector v 0 0 z)-vector (liftVector v σ η z)‖ ≤ σ+η := by
  have h := liftVector_perturb_sq v σ η z
  rw [hv] at h
  nlinarith [mul_nonneg hσ hη,norm_nonneg (vector (liftVector v 0 0 z)-vector (liftVector v σ η z))]

lemma liftVector_distance_sq (v w : X → ℝ) (σ η : ℝ) (z z' : C) :
    ‖vector (liftVector v σ η z)-vector (liftVector w σ η z')‖^2 ≤
      (1+σ^2)*‖vector v-vector w‖^2+4*η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,Fintype.sum_sum_type,liftVector]
  simp_rw [← mul_sub,mul_pow]
  rw [← Finset.mul_sum]
  have h := delta_distance_le η z z'
  linarith

lemma liftVector_distance_le (v w : X → ℝ) {σ η : ℝ} (hσ : 0≤σ) (hη : 0≤η) (z z' : C) :
    ‖vector (liftVector v σ η z)-vector (liftVector w σ η z')‖ ≤
      (1+σ)*‖vector v-vector w‖+2*η := by
  have hs := liftVector_distance_sq v w σ η z z'
  have hD := norm_nonneg (vector v-vector w)
  have hQ := norm_nonneg (vector (liftVector v σ η z)-vector (liftVector w σ η z'))
  have hc : 0≤σ*‖vector v-vector w‖^2 := mul_nonneg hσ (sq_nonneg _)
  have hd : 0≤(1+σ)*‖vector v-vector w‖*η := mul_nonneg (mul_nonneg (by linarith) hD) hη
  apply (sq_le_sq₀ hQ (by positivity)).mp
  nlinarith only [hs,hc,hd]

lemma lift_sign_first {v : X → ℝ} (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    (∫ c, signFailure (score (liftVector v 0 0 z) c) (score (liftVector v σ η z) c)
      ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) ≤ 4*(σ+η) := by
  rw [integral_score_sign]
  exact (sign_inner_normalize_le (liftVector_base_norm v hv z)
    (lt_of_lt_of_le (by norm_num) (liftVector_norm_pos v hv σ η z))).trans
    (mul_le_mul_of_nonneg_left (liftVector_perturb_le v hv hσ hη z) (by norm_num))

lemma lift_sign_second {v w : X → ℝ} (hv : ‖vector v‖=1) (hw : ‖vector w‖=1)
    {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (z z' : C) :
    (∫ c, signFailure (score (liftVector v σ η z) c) (score (liftVector w σ η z') c)
      ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) ≤ 4*‖vector v-vector w‖+4*η := by
  rw [integral_score_sign]
  have hn : ‖vector (liftVector w σ η z')‖=‖vector (liftVector v σ η z)‖ := by
    have h := liftVector_norm_sq v σ η z
    have h' := liftVector_norm_sq w σ η z'
    rw [hv] at h
    rw [hw] at h'
    nlinarith [norm_nonneg (vector (liftVector v σ η z)),norm_nonneg (vector (liftVector w σ η z'))]
  have hge := liftVector_norm_pos v hv σ η z
  have hp : 0<‖vector (liftVector v σ η z)‖ := by linarith
  have he := sign_inner_common_norm hp rfl hn
  have hc : 2/‖vector (liftVector v σ η z)‖ ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
  have hb := liftVector_distance_le v w hσ hη z z'
  have hd := norm_nonneg (vector v-vector w)
  exact he.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by nlinarith [mul_le_mul_of_nonneg_right hσ1 hd]))
end MinUncut.GaussianBudget

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianPacking
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MinUncut.GaussianBudget
variable {X C : Type*} [Fintype X] [Fintype C]

def packEquiv : ((X → ℝ) × ((X → ℝ) × (C → ℝ))) ≃ᵐ (Coordinates X C → ℝ) :=
  ((MeasurableEquiv.refl (X → ℝ)).prodCongr
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ C => ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ (X ⊕ C) => ℝ)).symm

lemma pack_preserving : MeasurePreserving (packEquiv (X := X) (C := C))
    (productLaw X C) (Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) := by
  exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ (X ⊕ C) => gaussianReal 0 1)).comp
    ((MeasurePreserving.id _).prod (measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ C => gaussianReal 0 1)))

lemma score_packed (v : X → ℝ) (σ η : ℝ) (z : C)
    (p : (X → ℝ) × ((X → ℝ) × (C → ℝ))) :
    score (liftVector v σ η z) (packEquiv p)=score v p.1+σ*score v p.2.1+η*p.2.2 z := by
  classical
  simp only [score,Fintype.sum_sum_type,liftVector,packEquiv,MeasurableEquiv.trans_apply]
  change (∑ x, v x*p.1 x)+((∑ x, (σ*v x)*p.2.1 x)+∑ c, (if c=z then η else 0)*p.2.2 c)=_
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_assoc,← Finset.mul_sum]
  ring

lemma integral_pack_sign (v w : Coordinates X C → ℝ) :
    (∫ c, ∫ g, ∫ l, signFailure (score v (packEquiv (c,g,l)))
      (score w (packEquiv (c,g,l))) ∂Measure.pi (fun _ : C => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)) =
    ∫ q, signFailure (score v q) (score w q) ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1) := by
  have hv : Measurable (score v) := by unfold score; fun_prop
  have hw : Measurable (score w) := by unfold score; fun_prop
  have hp := pack_preserving (X := X) (C := C)
  have hi : Integrable (fun p : (X → ℝ) × ((X → ℝ) × (C → ℝ)) =>
      signFailure (score v (packEquiv p)) (score w (packEquiv p))) (productLaw X C) :=
    signFailure_integrable (hv.comp hp.measurable) (hw.comp hp.measurable)
  rw [← hp.integral_comp packEquiv.measurableEmbedding (fun q => signFailure (score v q) (score w q))]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with c hc
  exact (integral_prod _ hc).symm

lemma first_triple_bound {v : X → ℝ} (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    (∫ c, ∫ g, ∫ l, signFailure (score v c) (score v c+σ*score v g+η*l z)
      ∂Measure.pi (fun _ : C => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1)) ≤ 4*(σ+η) := by
  have h := lift_sign_first hv hσ hη z
  rw [← integral_pack_sign] at h
  simpa only [score_packed,zero_mul,add_zero] using h

lemma second_triple_bound {v w : X → ℝ} (hv : ‖vector v‖=1) (hw : ‖vector w‖=1)
    {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (z z' : C) :
    (∫ c, ∫ g, ∫ l, signFailure (score v c+σ*score v g+η*l z)
      (score w c+σ*score w g+η*l z')
      ∂Measure.pi (fun _ : C => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1)) ≤ 4*‖vector v-vector w‖+4*η := by
  have h := lift_sign_second hv hw hσ hσ1 hη z z'
  rw [← integral_pack_sign] at h
  simpa only [score_packed] using h
end MinUncut.GaussianBudget

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Density
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.OuterSmoothness

namespace Density
variable {A : Type*} [Fintype A]

lemma ofMap_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B C : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] (f : ∀ i, B i → C i)
    (c : ∀ i, C i) :
    ofMap (fun b : ∀ i, B i => fun i => f i (b i)) c = ∏ i, ofMap (f i) (c i) := by
  have heq (b : ∀ i, B i) :
      (if (fun i => f i (b i)) = c then (1 : ℝ) else 0) =
        ∏ i, if f i (b i) = c i then (1 : ℝ) else 0 := by
    rw [Finset.prod_boole]
    simp [funext_iff]
  simp only [ofMap, heq]
  rw [expect_prod (fun i b => if f i b = c i then (1 : ℝ) else 0), Fintype.card_pi, Nat.cast_prod, Finset.prod_mul_distrib]

lemma ofMap_fst {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : B → A) (a : A) : ofMap (fun p : B × C => f p.1) a = ofMap f a := by
  change (Fintype.card A : ℝ) * (𝔼 p : B × C, if f p.1 = a then 1 else 0) = _
  rw [expect_pair]
  congr 1
  apply Finset.expect_congr rfl
  intro b _
  exact Fintype.expect_const (ι := C) (if f b = a then (1 : ℝ) else 0)

lemma ofMap_snd {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : C → A) (a : A) : ofMap (fun p : B × C => f p.2) a = ofMap f a := by
  change (Fintype.card A : ℝ) * (𝔼 p : B × C, if f p.2 = a then 1 else 0) = _
  rw [expect_pair]
  congr 1
  exact Fintype.expect_const (ι := B) (𝔼 c : C, if f c = a then (1 : ℝ) else 0)

lemma ofMap_family {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : B → C → A) (a : A) :
    ofMap (fun p : B × C => f p.1 p.2) a = 𝔼 b, ofMap (f b) a := by
  simp only [ofMap, expect_pair, Finset.mul_expect]

lemma ofMap_uniform_shift {G B C : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Fintype B] [Nonempty B] [Fintype C] [DecidableEq C]
    (f : B → C) (offset : B → G) (y : G) (c : C) :
    ofMap (fun p : G × B => (p.1 + offset p.2, f p.2)) (y,c) = ofMap f c := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hsplit (g : G) (b : B) :
      (if (g + offset b, f b) = (y,c) then (1 : ℝ) else 0) =
        (if g = y - offset b then (1 : ℝ) else 0) * (if f b = c then 1 else 0) := by
    simp only [Prod.mk.injEq, ← eq_sub_iff_add_eq]
    split_ifs <;> simp_all
  simp only [ofMap, expect_pair, hsplit]
  rw [Finset.expect_comm]
  simp_rw [← Finset.expect_mul]
  have hind (b : B) : (𝔼 g : G, if g = y - offset b then (1 : ℝ) else 0) =
      (Fintype.card G : ℝ)⁻¹ := by simp
  simp only [hind, ← Finset.mul_expect, Fintype.card_prod, Nat.cast_mul]
  field_simp

end Density

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

def hiddenDensity (p : ∀ i, Density (A i)) (H : Finset ι) : Density (∀ i, A i) where
  val x := ∏ i, if i ∈ H then p i (x i) else 1
  nonneg x := Finset.prod_nonneg (fun _ _ => by split_ifs; exact (p _).nonneg _; norm_num)
  mean_one := by
    rw [expect_prod (fun i a => if i ∈ H then p i a else 1)]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ H <;> simp [hi, Density.mean_one]

lemma hiddenDensity_eq_prod (p : ∀ i, Density (A i)) (H : Finset ι) (x : ∀ i, A i) :
    hiddenDensity p H x = ∏ i ∈ H, p i (x i) := by
  simp [hiddenDensity]

lemma hiddenDensity_cross_disjoint (p : ∀ i, Density (A i))
    {H K : Finset ι} (hHK : Disjoint H K) :
    (𝔼 x, hiddenDensity p H x * hiddenDensity p K x) = 1 := by
  simp only [hiddenDensity]
  simp_rw [← Finset.prod_mul_distrib]
  rw [expect_prod (fun i a => (if i ∈ H then p i a else 1) *
    (if i ∈ K then p i a else 1))]
  apply Finset.prod_eq_one
  intro i _
  have hnot : ¬ (i ∈ H ∧ i ∈ K) := by
    intro hi
    exact Finset.disjoint_left.mp hHK hi.1 hi.2
  by_cases hi : i ∈ H <;> by_cases hk : i ∈ K
  · exact (hnot ⟨hi, hk⟩).elim
  all_goals simp [hi, hk, Density.mean_one]

lemma hiddenDensity_le (p : ∀ i, Density (A i)) {b : ℝ} (_hb : 0 ≤ b)
    (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ b) (H : Finset ι) (x : ∀ i, A i) :
    hiddenDensity p H x ≤ b ^ H.card := by
  rw [hiddenDensity_eq_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => (p i).nonneg _) (fun i _ =>
    ((p i).pointwise_le_card _).trans (hcard i))

def mixture {S : Type*} [Fintype S] [Nonempty S] (H : S → Finset ι)
    (p : ∀ i, Density (A i)) : Density (∀ i, A i) where
  val x := 𝔼 s, hiddenDensity p (H s) x
  nonneg x := Finset.expect_nonneg (fun s _ => (hiddenDensity p (H s)).nonneg x)
  mean_one := by
    rw [Finset.expect_comm]
    simp [Density.mean_one]

lemma mixture_variance {S : Type*} [Fintype S] [Nonempty S]
    (H : S → Finset ι) (p : ∀ i, Density (A i)) :
    (𝔼 x, (mixture H p x - 1)^2) =
      (𝔼 s, 𝔼 t, 𝔼 x, hiddenDensity p (H s) x * hiddenDensity p (H t) x) - 1 := by
  have hs (x) : (mixture H p x - 1)^2 =
      (𝔼 s, 𝔼 t, hiddenDensity p (H s) x * hiddenDensity p (H t) x) -
        2 * mixture H p x + 1 := by
    simp only [mixture, ← Finset.mul_expect, ← Finset.expect_mul]
    ring
  simp_rw [hs]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    (mixture H p).mean_one, Fintype.expect_const, Finset.expect_comm]
  conv_lhs => arg 1; arg 1; arg 2; ext s; rw [Finset.expect_comm]
  ring

namespace JointForms

local instance dualFintype {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] :
    Fintype (Module.Dual F₂ V) := by
  classical
  exact Fintype.ofInjective (fun f : Module.Dual F₂ V => (f : V → F₂)) DFunLike.coe_injective
local instance densityDualDecidableEq {V : Type*} [AddCommGroup V] [Module F₂ V] : DecidableEq (Module.Dual F₂ V) := Classical.decEq _

abbrev Block (r d : ℕ) := Fin d → Module.Dual F₂ (Fin r → F₂)
abbrev HiddenRaw (d : ℕ) := Fin 3 × (Fin d → F₂)

lemma card_block (r d : ℕ) : Fintype.card (Block r d) = 2^(r*d) := by
  rw [Fintype.card_fun, Module.card_eq_pow_finrank (K := F₂),
    Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  simp [F₂, ZMod.card, ← pow_mul]

end JointForms
end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_OuterQuestions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def simulatedStrategy {R₁ R₂ B₁ B₂ : Type*}
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (strategy : Strategy R₁ R₂ B₁ B₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => answerMap₁ x (strategy.1 (questionMap₁ x)),
   fun y => answerMap₂ y (strategy.2 (questionMap₂ y)))

end Game

end
end MinUncutGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

open scoped BigOperators

end MinUncutGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSimulation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

omit [Fintype I] in
lemma patch_comp {X Y : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (f : X → Y) :
    (fun i => f (patch A background active i)) = patch A (fun i => f (background i)) (fun i => f (active i)) := by
  funext i
  by_cases h : A i <;> simp [patch,h]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Basic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

variable {σ : Type*} [Fintype σ]

variable [DecidableEq σ]

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_LabelBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_KernelSampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution

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
end MinUncutGames.Foundations.Games.FiniteDistribution

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Completion
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) : FiniteDistribution X :=
  if h : 0 < ∑ x, w x then
    { weight := normalizedWeight w
      nonnegative := (normalizedWeight_isProbability w hw h).1
      normalized := (normalizedWeight_isProbability w hw h).2 }
  else fallback

theorem sum_mul_normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) (x : X) :
    (∑ z, w z) * (normalizeOr w hw fallback).weight x = w x := by
  classical
  have hs : 0 ≤ ∑ z, w z := Finset.sum_nonneg (fun z _ => hw z)
  by_cases h : 0 < ∑ z, w z
  · simp only [normalizeOr, dite_eq_left h, normalizedWeight]
    field_simp
  · have hz : ∑ z, w z = 0 := le_antisymm (le_of_not_gt h) hs
    have hx : w x = 0 := by
      apply le_antisymm _ (hw x)
      have hl := Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ x)
      simpa only [hz] using hl
    simp [normalizeOr, hz, hx]

theorem local_completion_recombination
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (x : X) (y : Y) :
    (c * (∑ z, left z) * (∑ z, right z)) *
      ((normalizeOr left hl defaultLeft).weight x *
        (normalizeOr right hr defaultRight).weight y) = c * left x * right y := by
  calc
    _ = c * ((∑ z, left z) * (normalizeOr left hl defaultLeft).weight x) *
        ((∑ z, right z) * (normalizeOr right hr defaultRight).weight y) := by ring
    _ = _ := by rw [sum_mul_normalizeOr, sum_mul_normalizeOr]

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedInformation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

open scoped BigOperators

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlap
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Information

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

open scoped BigOperators
open Games
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedLikelihood
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

def selectedLocalAnswers {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q)
    (remaining : {i : Fin n // i ∉ selected} → Q) : selected → A :=
  fun i => strategy (mergeCoordinates selected fixed remaining) i.1

def selectedLocalTest {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) : ℝ := by
  classical
  exact if selectedLocalAnswers strategy selected fixed remaining = label then 1 else 0

theorem selectedLocalTest_nonnegative {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) :
    0 ≤ selectedLocalTest strategy selected fixed label remaining := by
  classical
  unfold selectedLocalTest
  split <;> norm_num

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_left (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).1 =
      mergeCoordinates selected (fun i => (fixed i).1) (fun i => (remaining i).1) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_right (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).2 =
      mergeCoordinates selected (fun i => (fixed i).2) (fun i => (remaining i).2) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

open scoped BigOperators
open Games

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSections
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

omit [Fintype Name] [Fintype I] [Fintype S] [Nonempty S] in
lemma sampledPositions_patch (A : I → Prop)
    (bg : I → S × Fin 3) (w : {i // A i} → S × Fin 3) :
    sampledPositions (patch A bg w)=
      patch A (sampledPositions bg) (sampledPositions w) := patch_comp A bg w Prod.snd

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IndexedLists
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

lemma expect_split_tuple {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (f : (I → A) → (I → B) → ℝ) :
    (𝔼 w : I → A × B, f (fun i => (w i).1) (fun i => (w i).2)) =
      𝔼 a : I → A, 𝔼 b : I → B, f a b := by
  rw [← expect_pair (fun z : (I → A) × (I → B) => f z.1 z.2)]
  exact Fintype.expect_equiv tupleProductEquiv _ _ (fun _ => rfl)

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

lemma hiddenSet_card (H : Finset I) : Fintype.card {i // hiddenSet H i=true}=H.card := by
  simpa only [hiddenSet,decide_eq_true_eq] using Fintype.card_coe H

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient

variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

lemma rest_card (r : Row m n) : Fintype.card {t : Row m n // t≠r}=Fintype.card (Row m n)-1 := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique (α := {t : Row m n // t=r})]

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AlgebraicSigns
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.FiniteGaussian

lemma algebraicNonneg_eq (a b : ℚ) (N : ℕ) :
    algebraicNonneg a b N = true ↔ 0 ≤ (a:ℝ)+(b:ℝ)*Real.sqrt (N:ℝ) := by
  have hs := Real.sqrt_nonneg (N:ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hb2 : ((b:ℝ)*Real.sqrt (N:ℝ))^2=(N:ℝ)*(b:ℝ)^2 := by rw [mul_pow,hs2]; ring
  unfold algebraicNonneg
  split_ifs with hb ha ha
  · have hbr : (0:ℝ) ≤ b := by exact_mod_cast hb
    have har : (0:ℝ) ≤ a := by exact_mod_cast ha
    simp only [true_iff]
    positivity
  · have hbr : (0:ℝ) ≤ b := by exact_mod_cast hb
    have har : (a:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have hprod : 0 ≤ (b:ℝ)*Real.sqrt (N:ℝ) := mul_nonneg hbr hs
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have h' : (a:ℝ)^2 ≤ (N:ℝ)*(b:ℝ)^2 := by exact_mod_cast h
      nlinarith
    · intro h
      have h' : (a:ℝ)^2 ≤ (N:ℝ)*(b:ℝ)^2 := by nlinarith
      exact_mod_cast h'
  · have hbr : (b:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb)
    have har : (a:ℝ) < 0 := by exact_mod_cast ha
    have hprod : (b:ℝ)*Real.sqrt (N:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbr.le hs
    simp only [false_iff,not_le]
    linarith
  · have hbr : (b:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb)
    have har : (0:ℝ) ≤ a := by exact_mod_cast (le_of_not_gt ha)
    have hprod : (b:ℝ)*Real.sqrt (N:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbr.le hs
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have h' : (N:ℝ)*(b:ℝ)^2 ≤ (a:ℝ)^2 := by exact_mod_cast h
      nlinarith
    · intro h
      have h' : (N:ℝ)*(b:ℝ)^2 ≤ (a:ℝ)^2 := by nlinarith
      exact_mod_cast h'

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def evaluationProof (a : A) : FoldedProof A where
  answer P := P a
  folded _ := rfl

def labelFunctional (a : A) (x : Point m n) : Module.Dual F₂ (FaceArray A m n) where
  toFun B := ∑ i : Fin m, B ⟨i,face x i⟩ a
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

omit [Fintype A] in
lemma character_label (a : A) (x : Point m n) (B : FaceArray A m n) :
    character (labelFunctional a x) B=BinaryFourier.sign ((labelCode B a).val x) := rfl

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LiteralGaussian
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

lemma liftVector_l1 {X C : Type*} [Fintype X] [Fintype C]
    (v : X → ℝ) (σ η : ℝ) (z : C) :
    (∑ i, |liftVector v σ η z i|)=(1+|σ|)*(∑ x, |v x|)+|η| := by
  simp only [Fintype.sum_sum_type,liftVector,abs_mul,← Finset.mul_sum]
  simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TableTestFunctions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

lemma disagreement_range (b c : Bool) : 0≤disagreement b c ∧ disagreement b c≤1 := by
  unfold disagreement
  split <;> norm_num

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineDrain
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineDrain

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem drainTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[word.length + 1]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source []⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) (ambient, register)
        (Function.update base source [])) = _
      rw [atDrain]
      cases exit <;> simp [drain, TM2.stepAux, Reduction.MachineTransfer.exitAt]
  | cons symbol word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[word.length + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (Function.update base source (symbol :: word)))) = _
      rw [atDrain]
      simpa [drain, TM2.stepAux] using ih (some symbol)

end MinUncutGames.Foundations.Complexity.MachineDrain

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteSequence
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFiniteSequence

open _root_.Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

end MinUncutGames.Foundations.Complexity.MachineFiniteSequence

namespace MinUncutGames.Foundations.Complexity.MachineDrainMany

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

end MinUncutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryCounter
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCopy

open _root_.Turing

variable {K Λ σ β : Type} [DecidableEq K]

theorem update_fork_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      source replacement = forkTapes source left right base replacement leftOutput rightOutput := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, sourceLeft, sourceRight]
  · by_cases hl : k = left
    · subst k; simp [forkTapes, Ne.symm sourceLeft, leftRight]
    · by_cases hr : k = right
      · subst k; simp [forkTapes, Ne.symm sourceRight]
      · simp [forkTapes, hs, hl, hr]

theorem update_fork_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      left replacement = forkTapes source left right base input replacement rightOutput := by
  funext k
  by_cases hl : k = left
  · subst k; simp [forkTapes, leftRight]
  · by_cases hr : k = right
    · subst k; simp [forkTapes, Ne.symm leftRight]
    · simp [forkTapes, hl, hr]

theorem update_fork_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      right replacement = forkTapes source left right base input leftOutput replacement := by
  simp [forkTapes]

theorem forkStep_empty (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (leftOutput rightOutput : List β) (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), forkTapes source left right base [] leftOutput rightOutput⟩ =
        some ⟨exit, (ambient, none), forkTapes source left right base [] leftOutput rightOutput⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base [] leftOutput rightOutput)) = _
  rw [atLoop]
  cases exit <;>
    simp [forkLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, sourceLeft, sourceRight,
      leftRight, update_fork_source]

theorem forkStep_cons (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (head : β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩ =
      some ⟨some loopLabel, (ambient, some head),
        forkTapes source left right base input (head :: leftOutput) (head :: rightOutput)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base (head :: input) leftOutput rightOutput)) = _
  rw [atLoop]
  simp [forkLoop, TM2.stepAux, sourceLeft, sourceRight, leftRight,
    update_fork_source, update_fork_left, update_fork_right]

theorem forkTrace (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register),
        forkTapes source left right base input leftOutput rightOutput⟩) =
      some ⟨exit, (ambient, none), forkTapes source left right base []
        (input.reverse ++ leftOutput) (input.reverse ++ rightOutput)⟩ := by
  induction input generalizing leftOutput rightOutput register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, List.reverse_nil, List.nil_append] using
        forkStep_empty source left right sourceLeft sourceRight leftRight fallback loopLabel exit
          program atLoop base leftOutput rightOutput ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩) = _
    rw [forkStep_cons source left right sourceLeft sourceRight leftRight fallback loopLabel exit
      program atLoop base head input leftOutput rightOutput ambient register, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def drainedTapes (source scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse

theorem restoredTapes (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    forkTapes scratch source destination (drainedTapes source scratch base) []
      (base source) (base source ++ base destination) =
        Function.update base destination (base source ++ base destination) := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [forkTapes, sourceDestination]
  · by_cases hd : k = destination
    · subst k; simp [forkTapes]
    · by_cases ht : k = scratch
      · subst k
        simp [forkTapes, Ne.symm sourceScratch, Ne.symm destinationScratch, scratchEmpty]
      · simp [forkTapes, drainedTapes, Reduction.MachineTransfer.tapesAt, hs, hd, ht]

end MinUncutGames.Foundations.Complexity.MachineCopy

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Generator
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

end ConstraintGraph

end MinUncutGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_InitialGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.InitialGraph

open Target

def variableLabel (value : Bool) : Label := (value, false, false)

end MinUncutGames.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.GraphTables

open MinUncutGames.Foundations.Complexity

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

end MinUncutGames.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DegreeReplacement
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.DegreeReplacement

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
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

end MinUncutGames.Foundations.PCP.DegreeReplacement

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace MinUncutGames.Foundations.PCP.Expanders

open scoped BigOperators
open MinUncutGames.Foundations.Hastad
open CayleySpectral

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · simpa only [baseDimension, initialDegree, basePower] using
      CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

end MinUncutGames.Foundations.PCP.Expanders

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

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

end MinUncutGames.Foundations.PCP.ExpanderFamily

namespace MinUncutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

end MinUncutGames.Foundations.PCP.ExpanderTables

namespace MinUncutGames.Foundations.PCP.PreprocessingLevels

theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

theorem paddedSize_power (k : Nat) :
    paddedSize k = ExpanderFamily.growth ^ boundedLevel k := by
  simpa only [paddedSize, boundedLevel, searchResult, pow_zero] using
    levelLoop_power ExpanderFamily.growth k k 0

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  exact levelLoop_covers ExpanderFamily.growth k k 0 1
    ExpanderFamily.growth_gt_one (by omega) (by omega)

theorem boundedLevel_eq_level (k : Nat) :
    boundedLevel k = ExpanderFamily.level k := by
  apply Nat.le_antisymm
  · simpa only [boundedLevel, searchResult, pow_zero] using
      levelLoop_le_of_covering_power ExpanderFamily.growth k k 0
        (ExpanderFamily.level k) (Nat.zero_le _) (ExpanderFamily.le_size k)
  · apply (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2
    rw [← paddedSize_power]
    exact le_paddedSize k

theorem paddedSize_eq_size (k : Nat) : paddedSize k = ExpanderFamily.size k := by
  rw [paddedSize_power, boundedLevel_eq_level]
  rfl

theorem paddedSize_positive (k : Nat) : 0 < paddedSize k := by
  rw [paddedSize_power]
  exact Nat.pow_pos (by have h := ExpanderFamily.growth_gt_one; omega)

theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

def cloudPaddedSize (k : Nat) : Nat := if k = 0 then 0 else paddedSize k

@[simp] theorem cloudPaddedSize_zero : cloudPaddedSize 0 = 0 := rfl

theorem cloudPaddedSize_of_pos {k : Nat} (hk : 0 < k) :
    cloudPaddedSize k = paddedSize k := by
  simp only [cloudPaddedSize, Nat.ne_of_gt hk, ite_false]

theorem cloudPaddedSize_bounds (k : Nat) :
    k ≤ cloudPaddedSize k ∧ cloudPaddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp only [cloudPaddedSize_zero, Nat.mul_zero, le_refl, and_self]
  · rw [cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
    exact paddedSize_bounds (Nat.pos_of_ne_zero hk)

theorem table_vertexCount_eq_paddedSize (k : Nat) :
    ExpanderTables.vertexCount (Expanders.baseDegree * Expanders.baseDegree)
        (boundedLevel k) = paddedSize k := by
  rw [ExpanderTables.vertexCount_eq]
  have hg : (Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree) = ExpanderFamily.growth := by
    unfold ExpanderFamily.growth
    ring
  rw [hg]
  exact (paddedSize_power k).symm

end MinUncutGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

end MinUncutGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

end MinUncutGames.Foundations.PCP.Preprocessing

end
namespace MinUncutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

end MinUncutGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

end MinUncutGames.Foundations.PCP.PoweringEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

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

end MinUncutGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalConstants

def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2
def walkLength : Nat := 2 * endpointLength + 1

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

end MinUncutGames.Foundations.PCP.FinalConstants

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

end MinUncutGames.Foundations.PCP.RoundTables

end
section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

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

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.«variables» + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

end MinUncutGames.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFPattern
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

end MinUncutGames.Foundations.Complexity.FinalCNFPattern

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

variable {V D : Type*}

def edge (e : D → Demand V) (p : EdgeIndex e) : Sym2 (Vertex V D) :=
  s((ends e p.val).1,(ends e p.val).2)

lemma edge_injective (e : D → Demand V) : Function.Injective (edge e) := by
  intro p q he
  obtain ⟨⟨d,i⟩,hi⟩ := p
  obtain ⟨⟨f,j⟩,hj⟩ := q
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;>
    simp only [edge,ends] at he <;> (try split_ifs at he) <;>
    simp_all

variable [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]

def edgeSet (e : D → Demand V) : Finset (Sym2 (Vertex V D)) :=
  Finset.univ.image (edge e)

omit [Fintype V] in
lemma edgeSet_nondiag (e : D → Demand V) (z : Sym2 (Vertex V D)) (hz : z ∈ edgeSet e) :
    ¬ z.IsDiag := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
  simpa only [edge,Sym2.mk_isDiag_iff] using ends_ne e p

def graph (e : D → Demand V) : SimpleGraph (Vertex V D) where
  Adj x y := s(x,y) ∈ edgeSet e
  symm := ⟨by intro x y h; simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨by intro x hx; exact edgeSet_nondiag e s(x,x) hx (by simp)⟩

instance instDecidableRelVertexAdjGraph (e : D → Demand V) : DecidableRel (graph e).Adj := Classical.decRel _

def uncut (e : D → Demand V) (s : Vertex V D → Bool) : ℕ :=
  ∑ p : EdgeIndex e, mono (s (ends e p.val).1) (s (ends e p.val).2)

def extend (e : D → Demand V) (s : V → Bool) : Vertex V D → Bool
  | .inl v => s v
  | .inr (d,i) => if i.val=1 then s (e d).left else !(s (e d).left)

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_locals (e : D → Demand V) (s : Vertex V D → Bool) :
    uncut e s = ∑ d, localCost (e d).equal (s (.inl (e d).left)) (s (.inl (e d).right))
      (s (.inr (d,0))) (s (.inr (d,1))) (s (.inr (d,2))) := by
  unfold uncut
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : D×Fin 4 => p.2.val < if (e p.1).equal then 4 else 3)) (by simp) (fun p : D×Fin 4 => mono (s (ends e p).1) (s (ends e p).2))]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fin.sum_univ_four]
  cases h : (e d).equal <;> simp [h,ends,localCost,add_assoc]

end MinUncut.PathRealization

end
namespace MinUncut.FiniteProof

variable {Q : Type*} {A : Q → Type*} (base : ∀ q, A q)

lemma answer_of_folded (f : ∀ q, (A q → Bool) → Bool) (hf : Folded f) :
    answer base (fun p => f p.1 p.2.val)=f := by
  funext q P
  unfold answer vertex
  cases h : P (base q)
  · have hr : (rep (base q) P).val=(fun x => !(P x)) := by
      funext x
      simp [rep,h]
    simp only [hr,orient,Bool.false_eq_true,ite_false,hf q P,Bool.not_not]
  · have hr : (rep (base q) P).val=P := by
      funext x
      simp [rep,h]
    simp [hr,orient]

end MinUncut.FiniteProof

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphOutput
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable
variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]
variable {N : ℕ}

def output (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k) : MinUncut.Output where
  vertices := N
  adjacent u v := decide ((graph e).Adj (number.symm u) (number.symm v))
  symmetric u v := by simp only [decide_eq_decide]; exact (graph e).adj_comm _ _
  loopless u := by simp
  threshold := k
  threshold_pos := hk

def edgePair (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) : Fin N × Fin N :=
  (Sym2.sortEquiv (Sym2.map number (edge e p))).val

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_sym (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) :
    s((edgePair e number p).1,(edgePair e number p).2)=Sym2.map number (edge e p) :=
  Sym2.sortEquiv.symm_apply_apply _

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_injective (e : D → Demand V) (number : Vertex V D ≃ Fin N) :
    Function.Injective (edgePair e number) := by
  intro p q h
  apply edge_injective e
  apply Sym2.map.injective number.injective
  rw [← edgePair_sym,← edgePair_sym,h]

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_lt (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) :
    (edgePair e number p).1 < (edgePair e number p).2 := by
  have hl := (Sym2.sortEquiv (Sym2.map number (edge e p))).property
  apply lt_of_le_of_ne hl
  intro he
  have hd : (Sym2.map number (edge e p)).IsDiag := by
    rw [← edgePair_sym,Sym2.mk_isDiag_iff]
    exact he
  exact ends_ne e p ((Sym2.isDiag_map number.injective).mp hd)

omit [Fintype V] in
lemma output_adjacent_iff (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (u v : Fin N) :
    (output e number k hk).adjacent u v=true ↔ ∃ p : EdgeIndex e, s(u,v)=Sym2.map number (edge e p) := by
  simp only [output,decide_eq_true_eq,graph,edgeSet,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    simpa using (congrArg (Sym2.map number) hp).symm
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    apply Sym2.map.injective number.injective
    simpa using hp.symm

omit [Fintype V] in
lemma output_forward_edge_iff (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (u v : Fin N) :
    (u<v ∧ (output e number k hk).adjacent u v=true) ↔ ∃ p : EdgeIndex e, edgePair e number p=(u,v) := by
  rw [output_adjacent_iff]
  constructor
  · rintro ⟨hu,p,hp⟩
    refine ⟨p,?_⟩
    unfold edgePair
    rw [← hp]
    simp [Sym2.sortEquiv,le_of_lt hu]
  · rintro ⟨p,hp⟩
    refine ⟨?_,p,?_⟩
    · simpa only [hp] using edgePair_lt e number p
    · rw [← edgePair_sym,hp]

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_mono (e : D → Demand V) (number : Vertex V D ≃ Fin N)
    (s : Fin N → Bool) (p : EdgeIndex e) :
    mono (s (edgePair e number p).1) (s (edgePair e number p).2)=
      mono (s (number (ends e p.val).1)) (s (number (ends e p.val).2)) := by
  have he := edgePair_sym e number p
  change s((edgePair e number p).1,(edgePair e number p).2)=s(number (ends e p.val).1,number (ends e p.val).2) at he
  rcases Sym2.eq_iff.mp he with h|h
  · rw [h.1,h.2]
  · rw [h.1,h.2]; simp only [mono,eq_comm]

omit [Fintype V] in
lemma output_uncut (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (s : Fin N → Bool) :
    (output e number k hk).uncut s=uncut e (s ∘ number) := by
  have he : (Finset.univ.filter fun uv : Fin N×Fin N =>
      uv.1<uv.2 ∧ (output e number k hk).adjacent uv.1 uv.2=true ∧ s uv.1=s uv.2)=
      (Finset.univ.filter fun p : EdgeIndex e => s (edgePair e number p).1=s (edgePair e number p).2).image (edgePair e number) := by
    ext uv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨hu,ha,hs⟩
      obtain ⟨p,hp⟩ := (output_forward_edge_iff e number k hk uv.1 uv.2).mp ⟨hu,ha⟩
      exact ⟨p,by simpa only [hp] using hs,hp⟩
    · rintro ⟨p,hs,hp⟩
      have hh := (output_forward_edge_iff e number k hk uv.1 uv.2).mpr ⟨p,hp⟩
      exact ⟨hh.1,hh.2,by simpa only [hp] using hs⟩
  unfold MinUncut.Output.uncut
  erw [he,Finset.card_image_of_injective _ (edgePair_injective e number)]
  change _=∑ p : EdgeIndex e, mono (s (number (ends e p.val).1)) (s (number (ends e p.val).2))
  simp_rw [← edgePair_mono]
  simp only [mono,Finset.card_filter]

end MinUncut.PathRealization

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization

lemma canonicalOutput_eq {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k) :
    canonicalOutput e k hk=output e (number N M) k hk := by
  have ha : canonicalAdjacent e=(output e (number N M) k hk).adjacent := by
    funext u v
    apply Bool.eq_iff_iff.mpr
    rw [output_adjacent_iff]
    simp only [canonicalAdjacent,decide_eq_true_eq]
    constructor
    · rintro ⟨d,j,hj,h⟩
      refine ⟨⟨(d,j),hj⟩,?_⟩
      change s(u,v)=s(number N M (ends e (d,j)).1,number N M (ends e (d,j)).2)
      exact Sym2.eq_iff.mpr (h.imp id And.symm)
    · rintro ⟨⟨⟨d,j⟩,hj⟩,h⟩
      exact ⟨d,j,hj,(Sym2.eq_iff.mp h).imp id And.symm⟩
  unfold output at ha
  unfold canonicalOutput output
  congr 1

end MinUncut.PathRealization

end

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma extendAssignment_apply {V W : Type*} (f : V → W) (hf : Function.Injective f) (s : V → Bool) (v : V) :
    extendAssignment f s (f v)=s v := by
  rw [extendAssignment,dite_eq_left ⟨v,rfl⟩]
  exact congrArg s (hf (Classical.choose_spec (show ∃u, f u=f v from ⟨v,rfl⟩)))

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestComparisons
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.Inner
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma score_add_noise (v c g : Point m n → ℝ) (σ : ℝ) :
    score v (c+σ•g)=score v c+σ*score v g := by
  simp only [score,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryFormula
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryEncoding

open BinaryFormula

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

end MinUncutGames.BinaryEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

open _root_.Turing

theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

end MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryNameMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryNameMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source, update_destination]

theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

end MinUncutGames.BinaryNameMachine

end
section
namespace MinUncutGames.BinaryNameSearch

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem update_source (source counter : K) (distinct : source ≠ counter)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) source replacement =
      tapesAt source counter base replacement count := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hc : k = counter
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hc]

theorem update_counter (source counter : K)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) counter replacement =
      tapesAt source counter base input replacement := by
  simp [tapesAt]

end Program

end MinUncutGames.BinaryNameSearch

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryOccurrenceRename
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryOccurrenceRename

open BinaryFormula MinUncutGames.Foundations

theorem literal_mem_names (F : Formula) (c : Clause) (hc : c ∈ F.clauses)
    (i : Fin 3) : (c)[i].name ∈ sourceNames F := by
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def literal (F : Formula) (l : Literal) (mem : l.name ∈ sourceNames F) :
    Target.Literal (sourceNames F).length :=
  ⟨nameIndex F l.name mem, l.positive⟩

def clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Target.Clause (sourceNames F).length :=
  #v[literal F (c)[0] (literal_mem_names F c mem 0),
    literal F (c)[1] (literal_mem_names F c mem 1),
    literal F (c)[2] (literal_mem_names F c mem 2)]

def renamed (F : Formula) : Target.Formula where
  «variables» := (sourceNames F).length
  clauses := F.clauses.attach.map (fun c => clause F c.val c.property)

end MinUncutGames.BinaryOccurrenceRename

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryParsing
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

end MinUncutGames.BinaryParsing

namespace MinUncutGames.BinaryTokenMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

def program : Label → TM2.Stmt Alphabet Label State
  | .clause => clauseInstruction
  | .sign slot => signInstruction slot
  | .name slot => nameInstruction slot
  | .restore => loopAt 1 2 id false .restore (some .accept)
  | .accept => .halt
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Label
  main := .clause
  σ := State
  initialState := ((), none)
  m := program

def cfg (label : Option Label) (input reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input reversed output⟩

theorem clauseStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (true :: input) reversed output register) =
      some (cfg (some (.sign 0)) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]; rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]; rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

theorem nameTrace (slot : Fin 3) (bits suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some (.name slot)) (frame bits ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix ((frame bits).reverse ++ reversed) output) := by
  induction bits generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        frame, List.singleton_append, List.reverse_singleton] using
        nameEndStep slot suffix reversed output register
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [frame, List.cons_append, advance_some]
      rw [nameDigitStep, ih]
      simp only [List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

theorem literalTrace (slot : Fin 3) (literal : Literal)
    (suffix reversed output : List Bool) (register : Option Bool) :
    (advance machine.step)^[literal.name.size + 2]
      (some (cfg (some (.sign slot)) (literalBits literal ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix
        ((literalBits literal).reverse ++ reversed) output) := by
  rw [show literal.name.size + 2 = (literal.name.bits.length + 1) + 1 by
    rw [Nat.size_eq_bits_len]]
  rw [Function.iterate_succ_apply]
  simp only [literalBits, List.cons_append, advance_some]
  rw [signStep]
  change (advance machine.step)^[literal.name.bits.length + 1]
    (some (cfg (some (.name slot)) (frame literal.name.bits ++ suffix)
      (literal.positive :: reversed) output)) = _
  rw [nameTrace]
  simp only [nameBits, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .clause) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltStep (output : List Bool) :
    machine.step (cfg (some .accept) [] [] output) = some (cfg none [] [] output) := by
  change some (TM2.stepAux (program .accept) _ _) = _
  rfl

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MinUncutGames.BinaryTokenMachine

namespace MinUncutGames.BinaryRenameWords

open BinaryFormula MinUncutGames.Foundations

def token (literal : Literal) : BinaryNameSearch.Token :=
  (literal.positive, literal.name.bits)

end MinUncutGames.BinaryRenameWords

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RawInitialMachineFinish
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine

open _root_.Turing
open PCP

namespace Program

open PCP.AlphabetTable

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .scratch, .vertices,
  .darts, .tail, .head, .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

end Program

end MinUncutGames.Foundations.Complexity.FinalCNFMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringFinalConstants
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PCPIteration

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

end MinUncutGames.Foundations.PCP.PCPIteration

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TableIteration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.TableGapReduction

open RoundTables SpectralReturn Target

theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end MinUncutGames.Foundations.PCP.TableGapReduction

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_EnumerationPlain
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Enumeration
variable {A B C : Type}
def mapEquiv (E : Enumeration A) (e : A ≃ B) : Enumeration B where
  values := E.values.map e
  nodup := E.nodup.map e.injective
  complete b := List.mem_map.mpr ⟨e.symm b,E.complete _,e.apply_symm_apply b⟩
def bind (E : Enumeration A) {B : A → Type} (F : ∀a,Enumeration (B a)) : Enumeration (Σa,B a) where
  values := E.values.flatMap (fun a=>(F a).values.map (Sigma.mk a))
  nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro a _
      exact (F a).nodup.map (by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2)
    · apply E.nodup.pairwise_of_forall_ne
      intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hx hy
      obtain ⟨u,_,rfl⟩:=List.mem_map.mp hx
      obtain ⟨v,_,he⟩:=List.mem_map.mp hy
      exact hab (Sigma.mk.inj he).1.symm
  complete x := by
    rcases x with ⟨a,b⟩
    exact List.mem_flatMap.mpr ⟨a,E.complete a,List.mem_map.mpr ⟨b,(F a).complete b,rfl⟩⟩
def filterSubtype (E : Enumeration A) (p : A → Prop) [DecidablePred p] : Enumeration {a // p a} where
  values := (E.values.filter p).attach.map (fun a=>(⟨a.val,by simpa only [decide_eq_true_eq] using (List.mem_filter.mp a.property).2⟩ : {a // p a}))
  nodup := (List.nodup_attach.mpr (E.nodup.filter _)).map (by intro a b h; apply Subtype.ext; exact congrArg (fun x : {a // p a}=>x.val) h)
  complete a := by
    apply List.mem_map.mpr
    exact ⟨⟨a.val,List.mem_filter.mpr ⟨E.complete a.val,by simpa only [decide_eq_true_eq] using a.property⟩⟩,List.mem_attach _ _,rfl⟩
lemma filterSubtype_flatMap (E : Enumeration A) (p : A → Prop) [DecidablePred p]
    (f : A → List B) :
    (E.filterSubtype p).values.flatMap (fun a=>f a.val)=
      E.values.flatMap (fun a=>if p a then f a else []) := by
  unfold filterSubtype
  simp only [List.flatMap_map]
  rw [show List.flatMap (fun a : {a // a∈E.values.filter p}=>f a.val) (E.values.filter p).attach =
      (E.values.filter p).flatMap f by
    rw [←List.flatMap_map (g:=f) (f:=Subtype.val),List.attach_map_subtype_val]]
  generalize E.values = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons,List.flatMap_cons]
    by_cases hx:p x <;> simp [hx,ih]
end MinUncut.Enumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteQueryFamily
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma foldedProof_ext {A : Type*} {f g : FoldedProof A} (h : f.answer=g.answer) : f=g := by
  cases f
  cases g
  cases h
  rfl

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma rational_source_bounds {J : ℕ} (hJ : 1≤J) :
    0 ≤ rationalSigma J ∧ rationalSigma J≤1 ∧ 0 ≤ rationalEta J ∧ rationalEta J≤1 := by
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  have hs := sourceSigma_pos hJ'
  have hs1 := sourceSigma_le_one hJ'
  have he := sourceEta_pos hJ'
  have he1 := (sourceEta_le_sigma hJ').trans hs1
  rw [← rationalSigma_cast] at hs hs1
  rw [← rationalEta_cast] at he he1
  exact ⟨by exact_mod_cast hs.le,by exact_mod_cast hs1,by exact_mod_cast he.le,by exact_mod_cast he1⟩

end MinUncut.Outer

end
end

end OAI
end


