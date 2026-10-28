-- Prove2me | Definitions.Def_OAIQ087A027
-- name    : OAIQ087A027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:41:17.929991+00:00
-- url     : https://prove2.me/theorems/38e38af2-142c-4277-a72a-5f585cb24588
-- title:
--   Definitions bundle OAIQ087A027 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 302 declarations of OpenAI's Lean: 68 definitions, 1 inductive type or structure, 6 instances and 227 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorContract.NonemptyFormula`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorContract.inputEncoding`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorContract.sourceMap`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.average`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.edgeOracle`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.eventReject`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.localAverage`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraphBounds.OutputDart`, `OAI.MaxCutGames.Foundations.PCP.AlphabetGraphBounds.OutputVertex`, `OAI.MaxCutGames.Foundations.PCP.AlphabetReduction.edgeTesterReject`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Body.clearFieldsInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Body.clearFieldsTapes`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Body.incrementInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup.cleanupInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.CompareLoop.rowLoop`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.CompareLoop.rowState`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Driver.machine`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows.rowContext`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows.rowValues`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.afterReversal`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.cleanupInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.completedPolynomial`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.finishAfterPolynomialPrefix`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.finishAfterPrefix`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.finishBudget`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.finishInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Finish.reverseInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Lookup.readRowCost`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Lookup.readRowTapes`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.LoopState.inputBits`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Runtime.time`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Setup.setupInTime`, `OAI.MaxCutGames.Foundations.PCP.AssignmentTester.andLawFailure`, `OAI.MaxCutGames.Foundations.PCP.AssignmentTester.andReject`, `OAI.MaxCutGames.Foundations.PCP.AssignmentTester.eventReject`, `OAI.MaxCutGames.Foundations.PCP.AssignmentTester.explicitTesterReject`, `OAI.MaxCutGames.Foundations.PCP.AssignmentTester.testerReject`, `OAI.MaxCutGames.Foundations.PCP.FinalBooleanVerifier.OutputAssignment`, `OAI.MaxCutGames.Foundations.PCP.FinalBooleanVerifier.extractLabeling`, `OAI.MaxCutGames.Foundations.PCP.InitialGraph.honestLabeling` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_BinaryParityReduction`, `MaxCut_Encoding_BitPairWeightQ`, `MaxCut_Encoding_NameCompaction`, `MaxCut_Estimates_Dictator`, `MaxCut_Estimates_ListSum`, `MaxCut_Estimates_Sample`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_MatrixNoise`, `MaxCut_Games_Probability`, `MaxCut_Graphs_TestCut`, `MaxCut_Machines_AlphabetGraph`, `MaxCut_Machines_AlphabetReduction`, `MaxCut_Machines_AlphabetRetraction`, `MaxCut_Machines_Body`, `MaxCut_Machines_CompareLoop`, `MaxCut_Machines_EmitRows`, `MaxCut_Machines_Input`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Relations`, `MaxCut_Machines_Runtime2`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_FinalBooleanVerifier`, `MaxCut_PCP_Gap`, `MaxCut_PCP_GraphGap`, `MaxCut_PCP_GraphTableComplexity`, `MaxCut_PCP_Hastad`, `MaxCut_PCP_InitialGraph`, `MaxCut_PCP_PortTables`, `MaxCut_PCP_PoweringDecoding`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PoweringTableSemantics`, `MaxCut_PCP_PreprocessingRegularSoundness`, `MaxCut_PCP_PreprocessingRegularTables`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_RoundGap`, `MaxCut_PCP_TableIteration`.
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`; the bundles `OAIQ087A014`, `OAIQ087A015`, `OAIQ087A016`, `OAIQ087A017`, `OAIQ087A018` and `OAIQ087A019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A032`; the statement `OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness`; the proofs of `OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters` and `OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017
import Definitions.Def_OAIQ087A018
import Definitions.Def_OAIQ087A019

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_NameCompaction
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An explicit name compaction for finite three-literal CNF formulas. Only the
occurring names are scanned: the declared variable count is never enumerated.
Both assignment transports preserve every clause evaluation and therefore
every finite clause-score gap. The encoding bound is a size theorem; a machine
running-time bound and the constant-gap PCP construction remain separate.
-/

namespace MaxCutGames.Foundations.PCP.NameCompaction

open MaxCutGames.Foundations.Target

theorem failureCount_evaluations (F : Formula) (A : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

/-- The semantic score is the checked verifier's actual failed-clause count. -/
theorem verifier_failureCount (F : Formula) (A : Fin F.«variables» → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end MaxCutGames.Foundations.PCP.NameCompaction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Gap
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorContract

open Target Complexity

abbrev NonemptyFormula := { F : Formula // F.clauses ≠ [] }

def inputEncoding (F : NonemptyFormula) : List Bool := formulaBits F.val

def sourceMap (u D : Nat) (hD : 0 < D) (F : NonemptyFormula) :
    MaxCutGames.Reduction.SourceEncoding.Input :=
  SourceOccurrences.sourceInput F.val u D hD

end MaxCutGames.Foundations.Hastad.SourceGeneratorContract

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

theorem clauseRank_le_power (F : Target.Formula) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val ≤ (formulaBits F).length ^ u := by
  have hr := ((clauseEncoding F u).code c).isLt
  change _ < F.clauses.length ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

theorem leftBlock_le_numberBound (F : Target.Formula) :
    2 ^ (2 ^ u) * F.«variables» ^ u ≤
      SourceBounds.bitCoefficient u * (formulaBits F).length ^ u := by
  apply Nat.le_trans (m := nBits F u)
  · rw [Nat.mul_comm (2 ^ (2 ^ u)) (F.«variables» ^ u), nBits_eq]
    omega
  · exact SourceBounds.nBits_le_input F u

end MaxCutGames.Foundations.Hastad.SourceTupleBound

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal.instDecidableEqExtra
/-- Startup already supplies exactly the reset odometer digits. -/
theorem resetDigits_ready (F : Target.Formula) :
    setDigits F.clauses.length (fun _ : Fin u => 0)
      (SourceStartup.readyTapes (u := u) (D := D) F) = SourceStartup.readyTapes F := by
  funext k
  cases k <;> simp [setDigits]

end

end MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PortTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.AssignmentTester

open MaxCutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

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

/-- The actual BLR test yields a nearby parity, with no stability theorem
or Fourier-structure hypothesis assumed. -/
theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

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

/-- Every parity involving two or more distinct coordinates violates Boolean
AND with probability at least one quarter under two independent queries. -/
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
    exact four_truth_lower_inline_AssignmentTester _ _ _
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

/-- Six oracle queries, using three independent self-correction masks. -/
def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

variable {K : Type*} [Fintype K] [Nonempty K]

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

/-- Proximity soundness of the actual four finite tests. The only promise
is the property being tested: the queried input is δ-far from every legal label. -/
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

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

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
/-- The honest proof satisfies each explicit event separately, including all
padding slots, so it supplies actual satisfying labels in the incidence graph. -/
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

/-- One finite uniform sample space for the executable six-address test. -/
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

end MaxCutGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

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

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

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

end MaxCutGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphGap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

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

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A lower bound on the actual minimum is exactly the universal count bound. -/
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

end MaxCutGames.Foundations.PCP.ConstraintGraph

end

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem baseGraph_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (htail : G.tail = Prod.fst) :
    PortTables.baseGraph (materialize G ports) =
      G.reindex (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) ports) (Equiv.refl _) := by
  apply constraintGraph_ext_inline_PreprocessingOverlayTables
  · intro x
    rw [PortTables.baseGraph_reverse, rotation_materialize]
    rfl
  · intro x
    change x.1 = G.tail (x.1, ports.symm x.2)
    rw [htail]
  · intro x a b
    rw [PortTables.baseGraph_accepts, accepts_materialize]
    rfl

theorem overlay_semantics {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.baseGraph (overlay G H) =
      (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (overlayPorts d e))
        (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

theorem lazy_semantics {n d : Nat} (G : PortTables.Table n d) :
    PortTables.baseGraph (lazy G) =
      (LazyConstraint.constraintGraph (PortTables.baseGraph G)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (lazyPorts d)) (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

end MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

/-- Erasing a proof-equal table size preserves its exact spectral certificate. -/
theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

end MaxCutGames.Foundations.PCP.PreprocessingRegularSoundness

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

/-- Materialization retains exactly the explicitly reindexed rotation. -/
theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext_inline_PreprocessingTableSpectral
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

/-- The stored overlaid graph is the actual semantic overlay in numbered
port coordinates. This is equality of reversible port graphs. -/
theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

/-- The stored lazy graph is exactly the Boolean-flag lazy graph, with the
declared false-first port encoding. -/
theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

/-- An actual half-spectral expander overlay gives a `7/8` certificate for
the stored table. The original table needs no spectral certificate.
The degree hypothesis supplies nonempty old and expander port types. -/
theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

end MaxCutGames.Foundations.PCP.PreprocessingTableSpectral

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree )

variable {n d e : Nat}

theorem overlay_rejectionCount (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.overlay G H)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.overlay_semantics]
  calc
    _ = (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1 ; rfl
    _ = _ := Overlay.rejectionCount_eq _ _ rfl labels

theorem lazy_rejectionCount (G : PortTables.Table n d)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.lazy G)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.lazy_semantics]
  calc
    _ = (LazyConstraint.constraintGraph (PortTables.baseGraph G)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (LazyConstraint.constraintGraph (PortTables.baseGraph G))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1 ; rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

end MaxCutGames.Foundations.PCP.PreprocessingGuarantees
end

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace MaxCutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

end MaxCutGames.Foundations.PCP.PoweringLabels

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringDecoding
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Modal decoding is an actual maximum of finite empirical letter masses.
Its reciprocal-alphabet lower bound is derived from their total mass one. -/

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

/-!
# Full-radius access to the endpoints of each actual walk edge

The tail of each traversed edge is reachable from the walk's start. Its head
is reachable from the walk's end by reversing the remaining suffix with the
actual arrival ports. These facts supply values in the two neighborhood-ball
types used by the endpoint label decoders.
-/

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

/-- Perfect completeness for the actual powered graph and its common alphabet. -/
theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

/-- The witness forces failure of the actual kth checked path constraint.
The opinion/decode identities use the genuine reach certificates. -/
theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

end MaxCutGames.Foundations.PCP.PoweringTest

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace MaxCutGames.Foundations.PCP.GenericGraphTables

open MaxCutGames.Foundations.Complexity

variable {q : Nat}

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
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

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MaxCutGames.Foundations.PCP.GenericGraphTables

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

namespace MaxCutGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

/-- An arbitrary constraint graph's rejection probability is its actual
rejected-dart cardinal ratio, including the empty-dart case. -/
theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1 ; try rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

/-- Multiplying a normalized lower bound by the actual positive dart count. -/
theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

/-- The edge-profile definition equals its actual directed-edge indicator
mean without any nonemptiness assumption on vertices or ports. -/
theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1 ; try rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases h : bad (v, d) <;> simp [PoweringMoment.bit]

/-- Decoded badness is exactly rejection in the actual base constraint graph. -/
theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

end MaxCutGames.Foundations.PCP.PoweringCounting

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

/-- Actual program placement is the only execution premise. Header values and
unread row bits specify the input, and every auxiliary role starts empty. -/
def setupInTime (ports : Ports K) (distinct : Function.Injective ports)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ label, program (labels label) = statement ports labels exit label)
    (base : K → List Bool) (n m : Nat) (rows : List Bool)
    (initial : ∀ i : Fin 7, base (ports i) =
      if i = 0 then encodeWord n ++ (encodeWord m ++ rows) else [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩)
      (2 * (encodeWord n ++ (encodeWord m ++ rows)).length + n + 3 * m + 11) := by
  let input := encodeWord n ++ (encodeWord m ++ rows)
  let t₀ := Function.update base (ports 1) input
  let t₁ := SourceMachine.afterField (ports 1) (ports 2) t₀ n (encodeWord m ++ rows)
  let t₂ := SourceMachine.afterField (ports 1) (ports 3) t₁ m rows
  let t₃ := Function.update t₂ (ports 4) (encodeWord m)
  have hne {i j : Fin 7} (h : i ≠ j) : ports i ≠ ports j := fun e => h (distinct e)
  have run₀ := MachineCopy.copyInTime (ports 0) (ports 1) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .copyFirst) (labels .copySecond) (some (labels .verticesStart))
    program (atLabels .copyFirst) (atLabels .copySecond) base
    (by simp [initial]) ambient register
  have hb0 : base (ports 0) = input := by simpa [input] using initial 0
  have hb1 : base (ports 1) = [] := by simpa using initial 1
  rw [hb0, hb1, List.append_nil] at run₀
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (labels .copyFirst), (ambient, register), base⟩
    (some ⟨some (labels .verticesStart), (ambient, none), t₀⟩)
    (2 * (input.length + 1)) at run₀
  have run₁ := SourceMachine.fieldInTime (ports 1) (ports 2) (hne (by decide))
    (labels .verticesStart) (labels .verticesLoop) (some (labels .dartsStart))
    program (atLabels .verticesStart) (atLabels .verticesLoop)
    t₀ n (encodeWord m ++ rows) (by simp [t₀, input]) ambient none
  have run₂ := SourceMachine.fieldInTime (ports 1) (ports 3) (hne (by decide))
    (labels .dartsStart) (labels .dartsLoop) (some (labels .counterFirst))
    program (atLabels .dartsStart) (atLabels .dartsLoop)
    t₁ m rows (by simp [t₁, SourceMachine.afterField, distinct.eq_iff]) ambient none
  have h₂m : t₂ (ports 3) = encodeWord m := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂c : t₂ (ports 4) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂s : t₂ (ports 5) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have run₃ := MachineCopy.copyInTime (ports 3) (ports 4) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .counterFirst) (labels .counterSecond) (some (labels .initialize_))
    program (atLabels .counterFirst) (atLabels .counterSecond) t₂ h₂s ambient none
  rw [h₂m, h₂c, List.append_nil, encodeWord_length] at run₃
  have h₃e : t₃ (ports 6) = [] := by
    simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have hresult : Function.update t₃ (ports 6) [false] =
      resultTapes ports base n m rows := by
    funext tape
    by_cases h1 : tape = ports 1
    · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
        SourceMachine.fieldTapes, resultTapes, distinct.eq_iff]
    · by_cases h2 : tape = ports 2
      · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
          SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
      · by_cases h3 : tape = ports 3
        · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
            SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
        · simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
            resultTapes, Function.update_apply, h1, h2, h3, encodeWord]
  have run₄ : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .initialize_), (ambient, none), t₃⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels .initialize_)) (ambient, none) t₃) = _
      rw [atLabels]
      cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
        h₃e, hresult]
    steps_le_m := Nat.le_refl _ }
  let r₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₀ run₁
  let r₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁ run₂
  let r₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂ run₃
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂₃ run₄
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := by
      have h := run.steps_le_m
      dsimp [input] at h
      omega }

end MaxCutGames.Foundations.PCP.AlphabetTable.Setup

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open MaxCutGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

/-- Each stored register bit is obtained from its actual serialized field. -/
theorem stepAux_readSlots (source : K) (indices : List (Fin (q * q)))
    (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlots source indices next) ((ambient, initial), register)
      (Function.update base source (encodeWords (indexedWords relation indices) ++ suffix)) =
      TM2.stepAux next ((ambient, fillSlots relation indices initial), none)
        (Function.update base source suffix) := by
  induction indices generalizing initial register with
  | nil => simp [readSlots, fillSlots, indexedWords, encodeWords, TM2.stepAux]
  | cons i indices ih =>
    simp only [readSlots, indexedWords, List.map_cons, encodeWords, List.append_assoc, fillSlots]
    rw [stepAux_readSlot]
    exact ih _ none

theorem stepAux_readRelation (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register)
      (Function.update base source (encodeWords (relationWords relation) ++ suffix)) =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  simpa only [readRelation, indexedWords_finRange, fillSlots_finRange] using
    stepAux_readSlots source (List.finRange (q * q)) relation next
      base suffix ambient initial register

theorem parserStep (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.step program
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩ =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program readLabel) ((ambient, initial), register)
    (Function.update base source (encodeWords (relationWords relation) ++ suffix))) = _
  rw [atRead, parser, stepAux_readRelation]
  rfl

/-- One transition executes the fixed chain of `q*q` slot readers. -/
theorem parserTrace (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩) =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    parserStep source readLabel exitLabel program atRead base relation suffix ambient initial register

end MaxCutGames.Foundations.PCP.AlphabetTable.ReadRelation

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open MaxCutGames.Foundations.Complexity

variable {Λ : Type} {q : Nat}

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

end MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

section TableTransport

/-- The denominator equality comes from the same explicit dart bijection. -/
theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

end TableTransport

end MaxCutGames.Foundations.PCP.PoweringTableSemantics


/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace MaxCutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

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

/-- Every rejected event contributes two distinct rejected darts, one in each
orientation. A classical witness is used only in this counting proof. -/
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

end MaxCutGames.Foundations.PCP.QueryIncidence



end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetReduction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The explicit assignment tester applied to the encoded satisfying pairs of an
actual finite edge predicate.  The resulting soundness loss is independent of
the alphabet size.  Uniform padding of the finite sample space and assembly of
the global incidence graph are separate constructions.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.AlphabetReduction

open MaxCutGames.Foundations.Hastad
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

end MaxCutGames.Foundations.PCP.AlphabetReduction
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetGraph
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.AlphabetGraph

open MaxCutGames.Foundations.Hastad
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

omit [Nonempty A] in
/-- Five independent full tapes restrict to five independent uniform legal tapes. -/
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

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

/-- The actual event count has a uniform loss of 2048, with no edge-dependent
sample multiplicities. This count statement also permits an empty dart type. -/
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

end MaxCutGames.Foundations.PCP.AlphabetGraph

end

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

/-! Executable six-query generation on fixed full Boolean cubes. The event
type is exactly `AlphabetGraph.LocalEvent`, including all five full tapes.
Only the returned joint-table addresses are masked outside the input relation;
no legal-pair enumeration or change of sample multiplicities occurs. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Relations
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace MaxCutGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

section Semantics

theorem semantics_rows_congr_inline_Table {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

/-- Full decoded graph equality, including reversal, endpoints, and every predicate bit. -/
theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr_inline_Table (rows_eq_graphRows input) (rows_valid input)
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

/-- The serialized row list follows the same explicit occurrence order as the vector. -/
theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

/-- Complete output words: two headers followed by every ordered row block. -/
theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

end Semantics

end MaxCutGames.Foundations.PCP.AlphabetTable.Table


/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Real gaps transfer without rational approximation, including an empty
old dart type. The loss is exactly `2048 * 6 = 12288`. -/
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


end MaxCutGames.Foundations.PCP.AlphabetGraphBounds



namespace MaxCutGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- The actual table output obeys the real gap bound, with no rational
approximation and with empty input dart sets allowed. -/
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

end MaxCutGames.Foundations.PCP.AlphabetTableBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CompareLoop
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

def rowLoop (table : GenericGraphTables.Table q) (e : Fin table.darts) : Bool :=
  decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val)

def rowState (table : GenericGraphTables.Table q) (e : Fin table.darts) : State q :=
  normal table.rows[e].relation (rowLoop table e)

end MaxCutGames.Foundations.PCP.AlphabetTable.CompareLoop

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Addresses

open MaxCutGames.Foundations.Hastad
open Enumeration

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

theorem eventVertexField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (tail head : Nat) :
    eval (eventVertexField q event) (values n m edge.val tail head) =
      (vertexEquiv n m q (.inl (edge, event))).val := by
  rw [vertexEquiv_event_val, eventEquiv_val]
  simp [eval, eventVertexField, eventOffset, values, Emitter.affineValue, Nat.mul_comm]

theorem rawQueryField_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (query : Queries.RawQuery q) :
    eval (rawQueryField q query) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (.inr (Queries.globalize tail head edge query))).val := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    cases side <;>
      simp [eval, rawQueryField, rawQueryTerms, vertexQueryTerms, rawQueryOffset,
        values, Emitter.affineValue, Queries.globalize, eventCount,
        Nat.mul_comm, Nat.add_assoc]
  | inr tape =>
    simp [eval, rawQueryField, rawQueryTerms, edgeQueryTerms, rawQueryOffset,
      values, Emitter.affineValue, Queries.globalize, eventCount,
      Nat.mul_comm, Nat.add_assoc]

theorem reverseDartField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (tail head : Nat) :
    eval (reverseDartField q event slot orientation) (values n m edge.val tail head) =
      (dartEquiv m q (QueryIncidence.reverse (((edge, event), slot), orientation))).val := by
  rw [dartEquiv_reverse_val, eventEquiv_val]
  simp [eval, reverseDartField, reverseOffset, values, Emitter.affineValue,
    Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_assoc]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

theorem fieldForDartTail_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForDartTail q event slot orientation P)
      (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (if orientation then
        .inr (Queries.globalize tail head edge (Queries.query P event slot))
        else .inl (edge, event))).val := by
  cases orientation with
  | false => exact eventVertexField_eval n m q edge event tail.val head.val
  | true => exact fieldForQueryEvent_eval n m q edge tail head event slot P

end MaxCutGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_EmitRows
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open MaxCutGames.Foundations.Complexity
open Emitter

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

theorem encodedRow_inline_EmitRows {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

/-- The executable command semantics equals the precise stored row, including
the orientation-specific tail, reverse index, and every predicate bit. -/
theorem rowCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (rowCommands q event slot orientation).flatMap
      (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (GraphTables.rowWords
        (Table.rowFromDart input (((edge, event), slot), orientation))) := by
  rw [rowCommands, List.flatMap_append, List.flatMap_append,
    affineCommands_bits, affineCommands_bits, bitCommands_bits, relationBits_values]
  have htail := Addresses.fieldForDartTail_eval input.vertices input.darts q edge
    input.rows[edge].tail input.rows[input.rows[edge].reverseIndex].tail event slot orientation
    (Relations.oldPredicate input.rows[edge].relation)
  have hreverse := Addresses.reverseDartField_eval input.vertices input.darts q edge
    event slot orientation input.rows[edge].tail.val
      input.rows[input.rows[edge].reverseIndex].tail.val
  let row := Table.rowFromDart input (((edge, event), slot), orientation)
  have tailEq : affineValue (Addresses.dartTailTerms q event slot orientation)
      (rowValues input edge) (Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate (rowContext input edge).1)).val = row.tail.val := htail
  have reverseEq : affineValue (Addresses.reverseDartField q event slot orientation).terms
      (rowValues input edge) (Addresses.reverseDartField q event slot orientation).offset.val =
      row.reverseIndex.val := hreverse
  have relationEq : Relations.relationFromTable (rowContext input edge).1
      (rowContext input edge).2 event slot orientation = row.relation := rfl
  rw [encodedRow_inline_EmitRows]
  have combined := congrArg₂ (fun a b : List Bool => a ++ b)
    (congrArg encodeWord tailEq)
    (congrArg₂ (fun a b : List Bool => a ++ b) (congrArg encodeWord reverseEq)
      (congrArg (fun relation => encodeWords (GraphTables.relationWords relation)) relationEq))
  simpa only [List.append_assoc] using combined

theorem tableWords_eq_blocks {q : Nat}
    (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (Table.build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
      (List.finRange input.darts).flatMap (blockWords input) := by
  rw [Table.tableWords_eq_ordered, Enumeration.ordered_dart]
  unfold blockWords
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem headerCommands_bits {σ : Type} (q n m : Nat) (ambient : σ) :
    (headerCommands q σ).flatMap (commandBits ![n, m] ambient) =
      encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q] := by
  rw [headerCommands, List.flatMap_append, affineCommands_bits, affineCommands_bits]
  have vertices : affineValue
      [(0, Enumeration.tapeCount q), (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      ![n, m] (Addresses.zeroOffset q).val = Enumeration.vertexCount n m q := by
    exact Addresses.headerVertices_eval q n m 0 0 0
  have darts : affineValue [(1, 12 * Enumeration.localCount q)] ![n, m]
      (Addresses.zeroOffset q).val = Enumeration.dartCount m q := by
    exact Addresses.headerDarts_eval q n m 0 0 0
  rw [vertices, darts]
  simp [encodeWords]

theorem blockCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) :
    (blockCommands q).flatMap (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommands, blockWords, List.flatMap_assoc, encodeWords_flatMap_inline_EmitRows,
    rowCommands_bits]

theorem blockCommandsIn_bits {σ : Type} {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge) :
    (blockCommandsIn q context).flatMap (commandBits (rowValues input edge) ambient) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommandsIn, List.flatMap_map, commandBits_mapAmbient]
  rw [hcontext]
  exact blockCommands_bits input edge

end MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- The trace is derived solely from the actual drain instructions and final
reset instruction. No execution of the entire cleanup is assumed. -/
theorem cleanupTrace {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[actualCost selected base]
      (some ⟨some (labels 0), (ambient, register), base⟩) =
      some ⟨exit, (initial, none), clearTapes selected base⟩ := by
  induction n generalizing base ambient register with
  | zero =>
      change some (TM2.stepAux (program (labels 0)) (ambient, register) base) = _
      rw [show program (labels 0) = finish initial exit from atFinish]
      cases exit <;> rfl
  | succ n ih =>
      rw [actualCost, Function.iterate_add_apply]
      have first := MachineDrain.drainTrace (selected 0) (labels (0 : Fin (n + 1)).castSucc)
        (some (labels (0 : Fin (n + 1)).succ)) program (atDrain 0)
        base (base (selected 0)) ambient register
      simp only [Function.update_eq_self, Fin.castSucc_zero] at first
      rw [first]
      exact ih (fun i : Fin n => selected i.succ) (fun i => labels i.succ)
        (fun i => atDrain i.succ) atFinish (Function.update base (selected 0) []) ambient none

/-- Actual cleanup execution, bounded using the original selected-stack lengths. -/
def cleanupInTime {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register), base⟩
      (some ⟨exit, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) where
  steps := actualCost selected base
  evals_in_steps := cleanupTrace selected labels initial exit program atDrain atFinish
    base ambient register
  steps_le_m := actualCost_le selected base

end MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open RuntimeModel

/-- Every state component is finite; the q-dependent relation register is
enumerated by the explicit vector/function equivalence of the parser. -/
def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

end MaxCutGames.Foundations.PCP.AlphabetTable.Driver

/-!
Exact tape invariant for the old-dart loop. The cursor stores the remaining
input rows, while the reversed tape stores precisely the output headers and
the blocks already emitted. The scan and index-scan tapes are unconstrained:
the next lookup prefixes fresh copies and retains old residues as suffixes.
Finite control state is specified by the actual execution theorems using this
tape invariant.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

/-- At the terminal guard the stored prefix is the complete concrete output encoding. -/
theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

end MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Body
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual iteration of the alphabet-table driver. The positive unary guard,
row parser, preserving head lookup, comparison, finite emission plan, three
drains, and unary index increment all execute inside `Driver.program`.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Body

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def clearFieldsTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .tail []) .reverseIndex []) .head []

/-- The three cleanup phases are actual drains in the concrete program. -/
def clearFieldsInTime (base : Tape → List Bool) (ambient : Ambient q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (.clearField 0), (ambient, none), base⟩
      (some ⟨some .increment, (ambient, none), clearFieldsTapes base⟩)
      ((base .tail).length + (base .reverseIndex).length + (base .head).length + 3) := by
  let first := MachineDrain.drainInTime Tape.tail (Driver.Label.clearField 0)
    (some (.clearField 1)) (Driver.program q) (by rfl) base ambient none
  let second := MachineDrain.drainInTime Tape.reverseIndex (Driver.Label.clearField 1)
    (some (.clearField 2)) (Driver.program q) (by rfl)
    (Function.update base .tail []) ambient none
  let third := MachineDrain.drainInTime Tape.head (Driver.Label.clearField 2)
    (some .increment) (Driver.program q) (by rfl)
    (Function.update (Function.update base .tail []) .reverseIndex []) ambient none
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simp only [Function.update_of_ne (by decide : Tape.reverseIndex ≠ .tail),
    Function.update_of_ne (by decide : Tape.head ≠ .reverseIndex),
    Function.update_of_ne (by decide : Tape.head ≠ .tail)] at h
  omega

def incrementInTime (base : Tape → List Bool) (ambient : Ambient q)
    (e : Nat) (he : base .edge = encodeWord e) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .increment, (ambient, none), base⟩
      (some ⟨some .guard, (ambient, none), Function.update base .edge (encodeWord (e + 1))⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (nextRow (Driver.Label.guard : Driver.Label q))
      (ambient, none) base) = _
    simpa only [List.append_nil] using congrArg some
      (stepAux_nextRow (Driver.Label.guard : Driver.Label q) (ambient, none) base e []
        (by simpa only [List.append_nil] using he))
  steps_le_m := Nat.le_refl _

theorem emitterView_at_inline_Body (label :
    Emitter.Label (Driver.rowPlan q).length (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.emit label) =
      Emitter.statement (Emitter.listCommands (Driver.rowPlan q)) rowSources
        Tape.scratch Tape.reversed Driver.Label.emit (some (.clearField 0)) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

end MaxCutGames.Foundations.PCP.AlphabetTable.Body

/-!
Actual setup-to-guard execution of the alphabet-table driver. The preserved
input is parsed by Setup; the finite header template runs through an explicit
state equivalence. The resulting loop invariant is a complete tape equation.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

theorem headerView_at_inline_Initialization (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

end MaxCutGames.Foundations.PCP.AlphabetTable.Initialization

/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/

/-! The actual final driver phases: reverse the accumulated output, drain all
fifteen nonoutput stacks, reset the finite state, and reach `haltList`.
Polynomial resource bounds below require an actual preceding execution. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel
open scoped BigOperators

def afterReversal (base : Tape → List Bool) (word : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .reversed .output base [] word

@[simp] theorem afterReversal_output (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .output = word := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

@[simp] theorem afterReversal_reversed (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .reversed = [] := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

def finishBudget (base : Tape → List Bool) (word : List Bool) : Nat :=
  word.length + 1 + (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16

/-- The actual driver's reversal loop enters its first cleanup label. -/
def reverseInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩)
      (word.length + 1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (σ := Ambient q) Tape.reversed Tape.output (by decide) id false
    Driver.Label.reverseOutput (some (.cleanup 0)) (Driver.program q) rfl
    base state.1 state.2
  simpa only [hreversed, houtput, List.length_reverse, List.reverse_reverse,
    List.map_id, List.append_nil, afterReversal, Driver.machine, FinTM2.step] using! run

theorem cleared_eq_haltList (q : Nat) (base : Tape → List Bool) :
    (⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩ : (Driver.machine q).Cfg) =
      haltList (Driver.machine q) (base .output) := by
  have tapes := Cleanup.clearTapes_outputOnly cleanupPorts Tape.output base
    cleanupPorts_ne_output cleanupPorts_cover
  congr 1

/-- All remaining driver stacks are actually popped, and the exact initial
finite state is restored before the halting configuration is reached. -/
def cleanupInTime (q : Nat) (base : Tape → List Bool) (state : State q) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some (.cleanup 0), state, base⟩
      (some (haltList (Driver.machine q) (base .output)))
      ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 16) := by
  have run := Cleanup.cleanupInTime cleanupPorts Driver.Label.cleanup (initial q).1 none
    (Driver.program q)
    (fun i => by simp only [Driver.program, Cleanup.instruction_drain])
    (by simp only [Driver.program, Cleanup.instruction_finish]) base state.1 state.2
  change StateTransition.EvalsToInTime (Driver.machine q).step
    ⟨some (.cleanup 0), state, base⟩
    (some ⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩)
    ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 15 + 1) at run
  rw [cleared_eq_haltList] at run
  simpa only [Nat.add_assoc] using run

def finishInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some (haltList (Driver.machine q) word)) (finishBudget base word) := by
  have first := reverseInTime q base word state hreversed houtput
  have last := cleanupInTime q (afterReversal base word) (state.1, none)
  rw [afterReversal_output] at last
  have run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    ⟨some .reverseOutput, state, base⟩
    ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩
    (some (haltList (Driver.machine q) word)) first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have budgetEq : ((∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16) +
      (word.length + 1) =
      finishBudget base word := by
    dsimp only [finishBudget]
    omega
  exact run.steps_le_m.trans (Nat.le_of_eq budgetEq)

theorem afterReversal_selected_length_le (base : Tape → List Bool) (word : List Bool)
    (i : Fin 15) :
    (afterReversal base word (cleanupPorts i)).length ≤ (base (cleanupPorts i)).length := by
  have ho := cleanupPorts_ne_output i
  by_cases hr : cleanupPorts i = .reversed <;>
    simp [afterReversal, Reduction.MachineTransfer.tapesAt, ho, hr]

/-- Every stack bound here is derived from the actual preceding driver trace. -/
theorem stackLength_after_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (k : Tape) :
    (base k).length ≤ input.length + budget * Runtime.programPushBound (Driver.machine q) := by
  have bound := Runtime.executionSizeBound (Driver.machine q).step
    (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (Driver.machine q))
    (Runtime.stepStackLength (Driver.machine q) k) prefixRun
  exact bound.trans (Nat.add_le_add_right
    (Runtime.initialStackLength (Driver.machine q) input k) _)

theorem finishBudget_le_of_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) :
    finishBudget base word ≤
      16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17 := by
  let B := input.length + budget * Runtime.programPushBound (Driver.machine q)
  have wordBound : word.length ≤ B := by
    simpa only [hreversed, List.length_reverse] using
      stackLength_after_prefix q input base state budget prefixRun .reversed
  have sumBound : (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) ≤ 15 * B := by
    calc
      _ ≤ ∑ _i : Fin 15, B := by
        apply Finset.sum_le_sum
        intro i _
        exact (afterReversal_selected_length_le base word i).trans
          (stackLength_after_prefix q input base state budget prefixRun (cleanupPorts i))
      _ = 15 * B := by simp
  dsimp only [finishBudget]
  omega

/-- A polynomial time allowance for the whole prefixRun followed by actual
reversal and cleanup. The fixed push bound belongs to the concrete driver. -/
noncomputable def completedPolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  prefixTime + Polynomial.C 16 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound (Driver.machine q)) * prefixTime) +
    Polynomial.C 17

def finishAfterPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      (budget + 16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17) := by
  have last := finishInTime q base word state hreversed houtput
  let run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    (initList (Driver.machine q) input) ⟨some .reverseOutput, state, base⟩
    (some (haltList (Driver.machine q) word)) prefixRun last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have finishBound := finishBudget_le_of_prefix q input base word state budget prefixRun hreversed
  have allBound := run.steps_le_m
  omega

def finishAfterPolynomialPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (prefixTime : Polynomial Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩)
      (prefixTime.eval input.length))
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      ((completedPolynomial q prefixTime).eval input.length) := by
  have run := finishAfterPrefix q input base word state (prefixTime.eval input.length)
    prefixRun hreversed houtput
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [completedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm] using run.steps_le_m

end MaxCutGames.Foundations.PCP.AlphabetTable.Finish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

end MaxCutGames.Foundations.PCP.AlphabetTable.Runtime

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable

open MaxCutGames.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

end MaxCutGames.Foundations.PCP.AlphabetTable

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Probability
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.SourceProbability

open ActualSource

theorem Source_failure_eq_count (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A =
      (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) / S.occurrences := by
  have hp := IncidenceProbability.expect_bool_indicator_eq_count_ofFn
    (fun i : Fin S.occurrences => !S.satisfied A i)
  have he : Finset.univ.expect
      (fun i : Fin S.occurrences => if !S.satisfied A i then (1 : ℚ) else 0) =
      S.failure A := by
    unfold Source.failure
    congr 1
    funext i
    cases S.satisfied A i <;> rfl
  rw [he] at hp
  rw [hp]
  congr 2
  have hmap : List.ofFn (fun i : Fin S.occurrences => !S.satisfied A i) =
      S.sourceList.map (fun e => !CloneGap.satisfied e A) := by
    simp only [Source.sourceList, List.map_ofFn, Source.satisfied, Function.comp_def]
  rw [hmap, List.countP_map]
  rfl

theorem failure_add_satisfaction (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [Source_failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

end MaxCutGames.Reduction.SourceProbability

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_InitialGraph
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace MaxCutGames.Foundations.PCP.InitialGraph

open Target

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩

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
    (sat : ∀ c ∈ F.clauses, c.eval A = true) (event : RandomEvent F) :
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

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

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
  refine ⟨A, fun c hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

end MaxCutGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetRetraction
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pull a graph predicate back through a surjective label decoder.  This preserves
every rejection count after decoding.  A concrete section embeds the initial
eight-label graph into the fixed 64-label alphabet used throughout amplification.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

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

end MaxCutGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace MaxCutGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end MaxCutGames.Foundations.PCP.RawInitialTables

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.FiniteGraph

namespace Bundle

variable {A : Type}

instance instDecidableEqVertex (G : Bundle A) : DecidableEq G.Vertex := G.vertexDecidableEq
instance instDecidableEqDart (G : Bundle A) : DecidableEq G.Dart := G.dartDecidableEq
instance instNonemptyDart (G : Bundle A) : Nonempty G.Dart := G.dartNonempty

/-- A dart supplies a vertex through the actual tail map. -/
instance instNonemptyVertex (G : Bundle A) : Nonempty G.Vertex := by
  obtain ⟨d⟩ := G.dartNonempty
  exact ⟨G.graph.tail d⟩

end Bundle

end MaxCutGames.Foundations.PCP.FiniteGraph

end

namespace MaxCutGames.Foundations.PCP.FinalConstants

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

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

/-- The exact fixed constants make a whole round double the input gap until
the fixed positive threshold `cap` is reached. -/
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

end MaxCutGames.Foundations.PCP.FinalConstants

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace MaxCutGames.Foundations.PCP.AmplificationIteration

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min_inline_AmplificationIteration _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

/-- An inverse-size initial gap reaches the fixed threshold after the concrete loop. -/
theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end MaxCutGames.Foundations.PCP.AmplificationIteration

namespace MaxCutGames.Foundations.PCP.VerifierToCNF

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

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

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

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

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

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
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
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

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

/-- The actual answer pattern forces a failed chain, even when queried names
repeat and regardless of the labels on all allocated auxiliary «variables». -/
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

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

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

end MaxCutGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

/-- Acceptance is the actual graph predicate on the two recovered labels. -/
theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

/-- The enumeration preserves the exact directed-dart rejection count. -/
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
    (satisfied : ∀ c ∈ F.clauses, c.eval assignment = true) :
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

/-! Direct application to the checked alphabet-reduction graph. -/

end MaxCutGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphTableComplexity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

namespace MaxCutGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

/-- A constant scalar passes through every iterate of the actual graph mean. -/
theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) (c : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => c * h x) =
      fun x => c * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => c * h x)) =
      fun x => c * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left c (fun d => iterateOperator G n h (G.rot (v, d)).1)

/-- The actual pivot dart is marked and both endpoint opinions pass their
tests. For indicator opinions this is the indicator of their conjunction. -/
noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

/-- Vertex-indexed opinions are tested at the two endpoints of the pivot dart. -/
noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

/-- Pointwise bounds on the two genuine earlier-length graph iterates give
the witness first moment. The hypotheses are only needed on marked darts. -/
theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

/-- The two endpoint-opinion tests each retain probability at least `1/(2q)`
at every middle pivot. The walk has `2N+1` edges, with `N=(4qM)^2`, so the
prefix and suffix lengths are exactly `k` and `2N-k`.

The only modal input is the actual centered lazy iterate at each vertex. It
will be supplied by the finite modal-opinion decoder, not by a witness law.
-/
theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end MaxCutGames.Foundations.PCP.PoweringWitness

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

namespace MaxCutGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

theorem window_second_moment_eq (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      (m : ℝ) * edgeDensity bad +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, returnMass G bad gap := by
  rw [show mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      ∑ i, ∑ j, mean (fun w => bit (windowEvent G bad n start m h i w ∧
        windowEvent G bad n start m h j w)) from
    PoweringMoment.second_moment_eq (windowEvent G bad n start m h)]
  apply symmetric_gap_matrix_sum
  · intro i j
    congr 1
    funext w
    simp only [and_comm]
  · intro i
    simp only [and_self]
    exact hit_mean G bad n (windowIndex n start m h i)
  · intro i j hij
    have hwin : windowIndex n start m h i < windowIndex n start m h j :=
      Nat.add_lt_add_left hij start
    have hp := pair_event_mean G bad n (windowIndex n start m h i)
      (windowIndex n start m h j) hwin
    simpa only [windowEvent, windowIndex, Nat.add_sub_add_left] using hp

/-- All moment terms come from actual walk events; the only analytic input
is the stated spectral contraction certificate of the given graph. -/
theorem window_second_moment_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) ≤
      (m : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((m : ℝ) - 1) * edgeDensity bad) := by
  rw [window_second_moment_eq]
  exact secondMoment_return_envelope G lambda certificate bad reversal m

end MaxCutGames.Foundations.PCP.PoweringMomentBound

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] in
omit [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

/-- Positive decoded error forces rejection of the actual powered graph.
The cap and amplification coefficient are explicit constants. -/
theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end MaxCutGames.Foundations.PCP.PoweringSoundness
end

namespace MaxCutGames.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end MaxCutGames.Foundations.PCP.PoweringGap

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace MaxCutGames.Foundations.PCP.PoweringFinalConstants

/-- The composed powering and alphabet-reduction coefficient yields the
fixed doubling bound after the checked preprocessing loss. -/
theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end MaxCutGames.Foundations.PCP.PoweringFinalConstants

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RoundGap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

end MaxCutGames.Foundations.PCP.RoundGap
end

/-!
# Size of the actual fixed amplification round

All constants below depend only on the fixed port alphabet and walk length.
The round itself is the checked preprocessing, powering, and alphabet graph
construction in `AmplificationRound`; no second graph constructor is introduced.
Closed constants are kept symbolic rather than evaluated.
-/

namespace MaxCutGames.Foundations.Hastad.SourceNonempty

open Target PCP

/-- Convert an actual natural-number clause-count inequality to the real
inequality used by the clause-variable game. -/
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

variable {V E : Type*} {n m : ℕ}

/-- The actual final graph bundle carries a nonempty dart type, so its
explicitly numbered Boolean CNF is nonempty even before using any gap. -/
theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

end MaxCutGames.Foundations.Hastad.SourceNonempty

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PCPIteration

open FiniteGraph

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

end MaxCutGames.Foundations.PCP.PCPIteration

end

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace MaxCutGames.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

/-- Boolean labels and numeric labels have exactly the same rejected darts. -/
theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

/-- A uniform numeric-label count bound transfers to the machine's Boolean-label graph. -/
theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

end MaxCutGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace MaxCutGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

/-- Pull target raw labels back to old port coordinates; this is a bijection. -/
def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _u := rfl
  right_inv _u := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

/-- Use the target selector, including its concrete enumeration choices. -/
def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in
/-- The generic lazy-graph gap survives a genuine rotation-preserving port
change and the target's chosen selectors, for every raw target labeling. -/
theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

end MaxCutGames.Foundations.PCP.PoweringPortReindex

end

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

namespace MaxCutGames.Foundations.PCP.TableGapReduction

open RoundTables SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

omit certificate in
theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end MaxCutGames.Foundations.PCP.TableGapReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Hastad
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.HastadSource

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

theorem failure_add_success (input : SourceEncoding.Input)
    (bits : Fin input.«variables» → Bool) :
    (asSource input).failure bits + success input bits = 1 := by
  have h := SourceProbability.failure_add_satisfaction (asSource input) bits
  rw [show (asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

end MaxCutGames.Outer.HastadSource

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.Clone100

open MaxCutGames.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

theorem equation_distinct {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    (equation e t).first ≠ (equation e t).second ∧
      (equation e t).first ≠ (equation e t).third ∧
      (equation e t).second ≠ (equation e t).third := by
  obtain ⟨h12, h13, h23⟩ := clone_distinct e t
  exact ⟨fun h => h12 ((nameEquiv n).injective h),
    fun h => h13 ((nameEquiv n).injective h),
    fun h => h23 ((nameEquiv n).injective h)⟩

def clonedSource (input : SourceEncoding.Input) : Source :=
  Source.ofList (clonedInput input).equations (clonedInput input).nonempty

theorem clonedSource_distinct (input : SourceEncoding.Input) :
    (clonedSource input).DistinctNames := by
  intro i
  have hm : (clonedInput input).equations[i.val] ∈ equations input.equations :=
    List.getElem_mem i.isLt
  obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, _, he⟩ := List.mem_map.mp ht
  change ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).second ∧
    ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).third ∧
    ((clonedInput input).equations[i.val]).second ≠
      ((clonedInput input).equations[i.val]).third
  rw [← he]
  exact equation_distinct e t

theorem equation_lift {n : Nat} (e : Equation (Fin n)) (t : GoodTriple)
    (a : Fin n → Bool) : satisfied (equation e t) (lift a) = satisfied e a := by
  simp [equation, lift, satisfied]

theorem completeness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin n → Bool) :
    (equations es).countP (fun e => satisfied e (lift a)) =
      es.countP (fun e => satisfied e a) * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.countP_append, List.countP_map,
      Function.comp_def] at *
    simp_rw [equation_lift]
    rw [CloneGap.count_const, triples_length, ih]
    cases h : satisfied e a <;> simp [h, Nat.add_mul, Nat.add_comm]

theorem completeness (input : SourceEncoding.Input)
    (a : Fin input.«variables» → Bool) :
    success (clonedInput input).equations (lift a) = success input.equations a := by
  simp only [success, clonedInput, completeness_count, equations_length, Nat.cast_mul]
  have hn : (input.equations.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (List.length_pos_iff.mpr input.nonempty)
  field_simp

theorem equation_count_le {n : Nat} (e : Equation (Fin n))
    (a : Fin (n * 100) → Bool) :
    ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((1 + if satisfied e (majority a) then (1 : ℚ) else 0) / 2 + 3 / 100) := by
  have bound := conditionedScore_le good card_goodTriple
    (fun i => a (nameEquiv n (e.first, i)))
    (fun i => a (nameEquiv n (e.second, i)))
    (fun i => a (nameEquiv n (e.third, i))) e.rhs
  have he : ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) =
      ∑ t : GoodTriple, parityIndicator (a (nameEquiv n (e.first, t.val.1)))
        (a (nameEquiv n (e.second, t.val.2.1)))
        (a (nameEquiv n (e.third, t.val.2.2))) e.rhs := by
    rw [List.countP_map, count_as_sum_inline_Clone100]
    exact (Finset.sum_map_toList (Finset.univ : Finset GoodTriple)
        (fun t => parityIndicator (a (nameEquiv n (e.first, t.val.1)))
          (a (nameEquiv n (e.second, t.val.2.1)))
          (a (nameEquiv n (e.third, t.val.2.2))) e.rhs))
  rw [he]
  unfold conditionedScore at bound
  have hb := (div_le_iff₀ (show (0 : ℚ) < 970200 by norm_num)).mp bound
  rw [mul_comm _ (970200 : ℚ)] at hb
  exact hb

theorem soundness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin (n * 100) → Bool) :
    ((equations es).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((53 / 100 : ℚ) * es.length +
        (es.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    have he := equation_count_le e a
    simp only [equations, List.flatMap_cons, List.countP_append, Nat.cast_add,
      List.length_cons] at *
    cases h : satisfied e (majority a) <;>
      simp [h] at * <;> linarith

theorem soundness (input : SourceEncoding.Input)
    (a : Fin (clonedInput input).«variables» → Bool) :
    success (clonedInput input).equations a ≤
      (1 + success input.equations (majority a)) / 2 + 3 / 100 := by
  have h := soundness_count input.equations a
  have hn : (0 : ℚ) < input.equations.length := by
    exact_mod_cast List.length_pos_iff.mpr input.nonempty
  change (_ : ℚ) / _ ≤ _
  simp only [clonedInput, equations_length, Nat.cast_mul]
  rw [div_le_iff₀ (mul_pos hn (by norm_num))]
  calc
    _ ≤ 970200 * ((53 / 100 : ℚ) * input.equations.length +
        (input.equations.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := h
    _ = _ := by
      unfold success
      field_simp
      ring

theorem soundness_four_fifths (input : SourceEncoding.Input) (ξ : ℚ)
    (hξ : ξ < 1 / 100)
    (hsource : ∀ a, success input.equations a ≤ (1 + ξ) / 2)
    (a : Fin (clonedInput input).«variables» → Bool) :
    success (clonedInput input).equations a ≤ 4 / 5 := by
  have h := soundness input a
  have hs := hsource (majority a)
  linarith

end
end MaxCutGames.Outer.Clone100

namespace MaxCutGames.Outer.SourceIncidence

open MaxCutGames.Reduction ActualSource
open MaxCutGames.Foundations Games Target PCP
open MaxCutGames.Soundness.IncidenceExtraction
open MaxCutGames.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

theorem paritySuccess_eq (S : Source) (a : Fin S.«variables» → Bool) :
    paritySuccess (incidence S) (FiniteDistribution.uniform (Fin S.occurrences)) a =
      (((S.sourceList.countP (fun e => CloneGap.satisfied e a) : ℚ) /
        S.occurrences : ℚ) : ℝ) := by
  unfold paritySuccess
  rw [uniform_probability_eq_expect_inline_SourceIncidence]
  have hevent (o : Fin S.occurrences) :
      decide (xorTriple (fun i => a ((incidence S).name o i)) = (incidence S).rhs o) =
        S.satisfied a o := by
    have hb : ∀ x y : Bool, decide (x = y) = (x == y) := by decide
    exact hb _ _
  simp_rw [hevent]
  rw [IncidenceProbability.expect_bool_indicator_eq_count_ofFn]
  congr 2
  have hm : List.ofFn (S.satisfied a) =
      S.sourceList.map (fun e => CloneGap.satisfied e a) := by
    simp [Source.sourceList, List.map_ofFn, Function.comp_def]
    rfl
  simp [hm, List.countP_map]

theorem paritySuccess_input (input : SourceEncoding.Input)
    (a : Fin input.«variables» → Bool) :
    paritySuccess (incidence (HastadSource.asSource input))
      (FiniteDistribution.uniform (Fin (HastadSource.asSource input).occurrences)) a =
      (Clone100.success input.equations a : ℝ) := by
  have h := paritySuccess_eq (HastadSource.asSource input) a
  rw [show (HastadSource.asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

end
end MaxCutGames.Outer.SourceIncidence

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BinaryParityReduction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.BinaryParityReduction

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

structure Reduction (ξ : ℚ) where
  reduce : List Bool → SourceEncoding.Input
  distinct : ∀ word, (HastadSource.asSource (reduce word)).DistinctNames
  completeness : ∀ word, BinaryLanguage.language word →
    ∃ a, 1 - ξ ≤ Clone100.success (reduce word).equations a
  soundness : ∀ word, ¬ BinaryLanguage.language word →
    ∀ a, Clone100.success (reduce word).equations a ≤ 4 / 5
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem failure_completeness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (yes : BinaryLanguage.language word) :
    ∃ a, (HastadSource.asSource (R.reduce word)).failure a ≤ ξ := by
  obtain ⟨a, ha⟩ := R.completeness word yes
  refine ⟨a, ?_⟩
  have hsum := HastadSource.failure_add_success (R.reduce word) a
  change _ + Clone100.success (R.reduce word).equations a = 1 at hsum
  linarith

theorem parity_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    MaxCutGames.Clean.IncidenceGap.parityValue
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (MaxCutGames.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences)) ≤ 4 / 5 := by
  unfold MaxCutGames.Clean.IncidenceGap.parityValue
  apply Finset.sup'_le
  intro a _
  have hq := R.soundness word no a
  have hreal : (Clone100.success (R.reduce word).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (SourceIncidence.paritySuccess_input (R.reduce word) a).trans_le hreal

end
end MaxCutGames.Outer.BinaryParityReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Graphs_TestCut
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

/-- Value of the usual correlated long-code Max-Cut test, before aggregating
its finite rational outcomes into graph weights. -/
noncomputable def testCut (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) : ℝ :=
  G.rightLaw.avg (fun y => (1 - corrAverage t q (fun z z' =>
    G.averageCode f y z * G.averageCode f y (antipode z'))) / 2)

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitPairWeightQ
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

/-- Every atom records exactly the finite random choices made by the long-code
Max-Cut test. In particular no real random numbers occur in the construction. -/
def sampleLaw (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) :
    Law (Y × (E × (E × (Cube (Fin q) × Cube (Fin q))))) :=
  G.rightLaw.bind (fun y => (G.edgeLaw y).bind (fun _ =>
    (G.edgeLaw y).bind (fun _ => jointLaw t ht q)))

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixNoise
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MaxCutGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open MaxCutGames.Integration.BinaryLinear (Vector)
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def linearNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

/-- Weighted probability that the dual map annihilates the sampled noise vector. -/
def linearNoiseEigenvalue [Fintype F] (weight : F → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ v, weight v * if S v = 0 then 1 else 0

def linearRealNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ v, weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

end MaxCutGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Dictator
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

/-- Fixed explicit vertex enumeration, supplied as a finite equivalence. The
semantic theorem does not hide an unweighted conversion or an edge multiset. -/
def edgeDistribution (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) : Law (Fin N × Fin N) :=
  (G.sampleLaw t ht).push (fun a => (enum (G.queries a).1, enum (G.queries a).2))

def weights (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) : Fin N → Fin N → ℚ :=
  aggregate (G.edgeDistribution t ht enum)

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Sample
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.Game
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

noncomputable def gridWeights (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) : Fin N → Fin N → ℚ :=
  roundedWeights (G.sampleLaw t ht) (fun a => (enum (G.queries a).1, enum (G.queries a).2))
    anchor (gridSize Y E q K) (gridSize_pos K)

noncomputable def gridOutput (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) : ScaledGraph :=
  deterministicOutput (K+1) (G.gridWeights t ht enum anchor K) (aggregate_symm _)

end OptimalMaxCut.LongCode.Game

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_ListSum
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open CounterMachine.Expr
attribute [local instance] Classical.propDecidable

@[simp] theorem rowWords_length {n q : ℕ} (c : Constraint n q) :
    (rowWords c).length = q+2 := by simp [rowWords]

end OptimalMaxCut.LongCode.InstanceAdapter

namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open CounterMachine.Expr LongCode
attribute [local instance] Classical.propDecidable

def lookup {q : ℕ} (x : Cube (Fin q)) (j : ℕ) : ℕ :=
  ∑ i : Fin q, if i.val=j then (finTwoEquiv.symm (x i)).val else 0
end OptimalMaxCut.RawGrid

end

end OAI
end


