-- Prove2me | Definitions.Def_OAIQ076M020
-- name    : OAIQ076M020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:14:08.641628+00:00
-- url     : https://prove2.me/theorems/f5488d76-f63a-4be1-a206-7700274faaca
-- title:
--   Definitions bundle OAIQ076M020 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 356 declarations of OpenAI's Lean: 84 definitions, 3 inductive types or structures, 2 instances and 267 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Face.rowEquiv`, `OAI.MinUncut.Preprocess.Face.rows`, `OAI.MinUncut.Preprocess.Source.answers`, `OAI.MinUncut.Preprocess.Source.fc`, `OAI.MinUncut.Preprocess.Source.gc`, `OAI.MinUncut.Preprocess.Source.keys`, `OAI.MinUncut.Preprocess.Source.lefts`, `OAI.MinUncut.Preprocess.Source.ls`, `OAI.MinUncut.Preprocess.Source.rights`, `OAI.MinUncut.Preprocess.Source.rs`, `OAI.MinUncut.Preprocess.Source.tapes`, `OAI.MinUncut.Preprocess.Syntax.C`, `OAI.MinUncut.Preprocess.Syntax.O`, `OAI.MinUncut.Preprocess.Syntax.powCode`, `OAI.MinUncut.Preprocess.Syntax.sumCode`, `OAI.MinUncut.Preprocess.UEncoding.equation`, `OAI.MinUncut.Preprocess.UEncoding.equationEquiv`, `OAI.MinUncut.SourceTemplate.paddedRep`, `OAI.MinUncut.SourceTemplate.rawLocal`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.NestedCycle`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.NestedCycle.LeafBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.NestedCycle.steps`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.VisitTraces`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.ascendingCycleInTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.bodyConfiguration`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.checkConfiguration`, `OAI.MinUncutGames.Foundations.Complexity.MachineTupleOdometer.cycleExit`, `OAI.MinUncutGames.Foundations.Games.Game.responseTableLaw`, `OAI.MinUncutGames.Foundations.Games.Game.stochasticSuccess`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.operandLength`, `OAI.MinUncutGames.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.MinUncutGames.Foundations.Hastad.SourceOdometerSchedule.BodyTrace`, `OAI.MinUncutGames.Foundations.Hastad.SourceOdometerSchedule.currentAt`, `OAI.MinUncutGames.Foundations.Hastad.SourceOdometerSchedule.remainingAt`, `OAI.MinUncutGames.Foundations.Hastad.SourceQueryOrder.occurrenceBits`, `OAI.MinUncutGames.Foundations.Hastad.SourceQueryOrder.slotBits`, `OAI.MinUncutGames.Foundations.Hastad.SourceQueryOrder.tupleBits`, `OAI.MinUncutGames.Foundations.Hastad.SourceRuntimeSpace.prefixAndFinishInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceTupleBody.Ready`, `OAI.MinUncutGames.Foundations.Hastad.SourceTupleBody.baseSnapshot` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_UniformCube`, `MinUncut_Encoding_Decoder`, `MinUncut_Encoding_FormulaEncoding`, `MinUncut_Encoding_GameDecoder`, `MinUncut_Encoding_ThreeBitTest`, `MinUncut_Estimates_ExpressionEffectivity`, `MinUncut_Estimates_ExpressionOutput`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Estimates_UniformAlgebra`, `MinUncut_Estimates_UniformEquation`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_UniformGrid`, `MinUncut_Estimates_UniformProduct`, `MinUncut_Estimates_UniformSets`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_Reindexing`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_DemandExpressions`, `MinUncut_Graphs_DemandQueryEffectivity`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineTupleOdometer`, `MinUncut_Machines_OuterAlphabets`, `MinUncut_Machines_RuntimeFinish`, `MinUncut_Machines_RuntimeSpace`, `MinUncut_PCP_AddressArithmetic`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ClauseVerifier`, `MinUncut_PCP_ContextClear`, `MinUncut_PCP_ContextLoad`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_Folding`, `MinUncut_PCP_FourierResponse`, `MinUncut_PCP_Game`, `MinUncut_PCP_Gap`, `MinUncut_PCP_Generator`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTableComplexity`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_LoopOrder`, `MinUncut_PCP_Overlay`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PoweringOpinionTables`, `MinUncut_PCP_PoweringReturn`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_ProfileBridge`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_TupleBody`, `MinUncut_PCP_TupleBound`, `MinUncut_PCP_Walsh`, `MinUncut_Search_RawRationalArithmetic`, `MinUncut_Search_UniformRational`.
--
--   **Imports.** It imports the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M009`, `OAIQ076M010`, `OAIQ076M011` and `OAIQ076M012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M026` and `OAIQ076M027`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M008
import Definitions.Def_OAIQ076M009
import Definitions.Def_OAIQ076M010
import Definitions.Def_OAIQ076M011
import Definitions.Def_OAIQ076M012

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_OuterAlphabets
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

variable {Name : Type*}

instance directionFintype (E : Equation Name) : Fintype (alphabet E).direction := Fintype.ofFinite _

end MinUncut.Outer

end
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
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def responseTableLaw (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    FiniteDistribution (Strategy Q₁ Q₂ A₁ A₂) := by
  classical
  exact (FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)

def stochasticSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.questions.expectation (fun q =>
    (responses₁ q.1).expectation (fun a =>
      (responses₂ q.2).expectation (fun b =>
        if G.accepts q.1 q.2 a b then 1 else 0)))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_eq_question_expectation (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    G.success strategy = G.questions.expectation
      (fun q => if G.wins strategy q then 1 else 0) := by
  simp [success, FiniteDistribution.probability,
    FiniteDistribution.expectation, mul_ite]

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

namespace MinUncutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end MinUncutGames.Foundations.Games.FiniteDistribution

end OAI
end

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

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

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

def testBias (ε : ℝ) (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ * A f *
    (𝔼 g, B g * B (thirdQuery π f g μ))

theorem testAcceptance_eq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    testAcceptance ε π A B =
      (1 + testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g))) / 2 := by
  unfold testAcceptance testBias
  simp_rw [threeBit_indicator, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp only [Fintype.expect_const]
  have hterm (f : Cube I) (μ : Cube J) :
      noiseWeight ε μ * ((1 + 𝔼 g,
        bitSign (A f) * bitSign (B g) * bitSign (B (thirdQuery π f g μ))) * 2⁻¹) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (A f) *
        (𝔼 g, bitSign (B g) * bitSign (B (thirdQuery π f g μ)))) * 2⁻¹ := by
    simp_rw [mul_assoc (bitSign (A f)), ← Finset.mul_expect]
    ring
  simp_rw [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp

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

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

end MinUncutGames.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseVerifier
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP

open Target

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

end MinUncutGames.Foundations.PCP

end
section
namespace MinUncutGames.Foundations.Hastad.SourceContexts

open Target PCP

theorem baseAccepts_implies_sampled (F : Formula) (c : Fin F.clauses.length)
    (s : Slot) (i : Bool) (j : ClauseAnswer)
    (h : baseAccepts F (nameAt (clauseAt F c) s) c i j = true) :
    (localSatisfies (clauseAt F c) j && decide (answerAt j s = i)) = true := by
  obtain ⟨hsat, hcons, heq⟩ := (baseAccepts_eq_true_iff F _ _ _ _).mp h
  have hname := canonicalSlot_name (clauseAt F c) (nameAt (clauseAt F c) s) ⟨s, rfl⟩
  have hans := (localConsistent_eq_true_iff _ _).mp hcons s
    (canonicalSlot (clauseAt F c) (nameAt (clauseAt F c) s)) hname.symm
  simp [hsat, hans.trans heq]

end MinUncutGames.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RawRationalArithmetic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
namespace RawRat

instance instDecidableLt (q r : RawRat) : Decidable (lt q r) := inferInstanceAs (Decidable (_<_))

end RawRat

end MinUncut.Preprocess

section
attribute [fun_prop] Computable ComputablePred

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

open _root_.Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

theorem cleared_frame (clearKeys : List K) (base : Tapes K) (tape : K)
    (h : tape ∉ clearKeys) : MachineDrainMany.finalTapes clearKeys base tape = base tape :=
  MachineDrainMany.finalTapes_not_mem clearKeys base tape h

variable [Fintype K]
open scoped BigOperators

theorem cleared_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    totalLength (MachineDrainMany.finalTapes clearKeys base) = (base accumulator).length := by
  have point (k : K) : (MachineDrainMany.finalTapes clearKeys base k).length =
      if k = accumulator then (base accumulator).length else 0 := by
    by_cases ha : k = accumulator
    · subst k
      simp [cleared_frame clearKeys base accumulator keepAccumulator]
    · by_cases ho : k = output
      · subst k
        simp [ha, cleared_frame clearKeys base output keepOutput, outputEmpty]
      · rw [MachineDrainMany.finalTapes_mem clearKeys base k (covers k ha ho)]
        simp [ha]
  simp only [totalLength, point]
  simp

theorem finishCost_eq_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    finishCost clearKeys accumulator base = totalLength base + clearKeys.length + 2 := by
  have h := drain_conservation clearKeys base
  rw [cleared_totalLength clearKeys accumulator output keepAccumulator keepOutput covers
    base outputEmpty] at h
  unfold finishCost
  omega

end MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

open _root_.Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

theorem spacePolynomial_eval (tm : FinTM2) (time : Polynomial Nat) (N : Nat) :
    (spacePolynomial tm time).eval N = N +
      time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simp [spacePolynomial]

theorem finishCost_le_of_prefix (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget)
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.finishCost clearKeys accumulator base ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) + clearKeys.length + 2 := by
  rw [SourceRuntimeFinish.finishCost_eq_totalLength clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty,
    totalLength_eq_configurationLength tm finish base sameLengths]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (prefix_configurationLength tm input run) clearKeys.length) 2

theorem completedTime_eval (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) (N : Nat) :
    (completedTime tm clearKeyCount time).eval N = time.eval N +
      (N + time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm)) +
      (clearKeyCount + 2) := by
  simp [completedTime, spacePolynomial_eval]

def prefixAndFinishInTime (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {middle finish : tm.Cfg}
    (prefixRun : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some middle) (time.eval input.length))
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (middle.stk k).length)
    (finishRun : StateTransition.EvalsToInTime tm.step middle (some finish)
      (SourceRuntimeFinish.finishCost clearKeys accumulator base)) :
    StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      ((completedTime tm clearKeys.length time).eval input.length) := by
  have joined := StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ prefixRun finishRun
  have hc := finishCost_le_of_prefix tm input prefixRun clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty sameLengths
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  rw [completedTime_eval]
  omega

end MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Decoder
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

def parityProjection (π : J → I) (s : Cube J) : Cube I := fun i =>
  decide (Odd ((support s).filter fun y => π y = i).card)

theorem walsh_support (s x : Cube I) :
    walsh s x = ∏ i ∈ support s, bitSign (x i) := by
  unfold walsh support
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [bitSign]

omit [DecidableEq J] in
theorem projection_has_preimage (π : J → I) (s : Cube J) (i : I)
    (hi : i ∈ support (parityProjection π s)) :
    ∃ y ∈ support s, π y = i := by
  have hodd : Odd ((support s).filter fun y => π y = i).card := by
    have hbit := (Finset.mem_filter.mp hi).2
    simpa only [parityProjection, decide_eq_true_eq] using hbit
  have hp : 0 < ((support s).filter fun y => π y = i).card := by
    obtain ⟨n, hn⟩ := hodd
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩

omit [DecidableEq I] in
theorem support_eq_empty_iff (s : Cube I) : support s = ∅ ↔ s = zeroMask := by
  constructor
  · intro h
    funext i
    have hi : i ∉ support s := by rw [h]; simp
    have : s i ≠ true := by simpa [support] using hi
    cases hs : s i <;> simp_all [zeroMask]
  · intro h
    subst s
    simp [zeroMask, support]

omit [Fintype I] [DecidableEq J] in
theorem parityProjection_zero (π : J → I) :
    parityProjection π (zeroMask : Cube J) = zeroMask := by
  funext i
  simp [parityProjection, support, zeroMask]

def agreementProbability (π : J → I) (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a, (((support b).filter fun y => π y = i).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem agreementProbability_nonneg (π : J → I) (a : Cube I) (b : Cube J) :
    0 ≤ agreementProbability π a b := by
  unfold agreementProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq J] in
theorem agreementProbability_projection (π : J → I) (b : Cube J)
    (ha : (support (parityProjection π b)).Nonempty) :
    1 / ((support b).card : ℝ) ≤ agreementProbability π (parityProjection π b) b := by
  have hca : (0 : ℝ) < (support (parityProjection π b)).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ha)
  have hb : (support b).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    obtain ⟨y, hy, _⟩ := projection_has_preimage π b i hi
    exact ⟨y, hy⟩
  have hcb : (0 : ℝ) < (support b).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hb)
  have hsum : ((support (parityProjection π b)).card : ℝ) ≤
      ∑ i ∈ support (parityProjection π b),
        (((support b).filter fun y => π y = i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ support (parityProjection π b), (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨y, hy, hπ⟩ := projection_has_preimage π b i hi
        have hp : 0 < ((support b).filter fun y => π y = i).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hπ⟩⟩
        exact_mod_cast hp
  unfold agreementProbability
  apply (div_le_div_iff₀ hcb (mul_pos hca hcb)).mpr
  nlinarith

def decoderSuccess (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)

def decodingEnergy (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  ∑ b, projectedCoefficient π A b ^ 2 * coefficient B b ^ 2 / (support b).card

def validAgreementProbability (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a,
    (((support b).filter fun y => π y = i ∧ valid y = true).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem validAgreementProbability_eq (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) (hb : ∀ y ∈ support b, valid y = true) :
    validAgreementProbability valid π a b = agreementProbability π a b := by
  unfold validAgreementProbability agreementProbability
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro y hy
  simp [hb y hy]

def validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 *
      validAgreementProbability valid π a b)

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FourierResponse
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
open MinUncutGames.Foundations.Games

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def supportResponse (fallback : I) (s : Cube I) : FiniteDistribution I where
  weight i := if (support s).Nonempty then
    if i ∈ support s then 1 / ((support s).card : ℝ) else 0
    else if i = fallback then 1 else 0
  nonnegative i := by
    split_ifs <;> positivity
  normalized := by
    by_cases hs : (support s).Nonempty
    · have hc : ((support s).card : ℝ) ≠ 0 :=
        ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
      simp [hs, hc]
    · simp [hs]

theorem supportResponse_expectation (fallback : I) (s : Cube I) (H : I → ℝ)
    (hs : (support s).Nonempty) :
    (supportResponse fallback s).expectation H =
      (∑ i ∈ support s, H i) / ((support s).card : ℝ) := by
  simp only [FiniteDistribution.expectation, supportResponse, hs, ite_true]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  simp only [div_eq_mul_inv, one_mul, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

theorem response_expectation_nonnegative {K : Type*} [Fintype K]
    (law : FiniteDistribution K) (H : K → ℝ) (hH : ∀ k, 0 ≤ H k) :
    0 ≤ law.expectation H :=
  Finset.sum_nonneg fun k _ => mul_nonneg (law.nonnegative k) (hH k)

theorem supportResponse_validAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J)
    (ha : (support a).Nonempty) (hb : (support b).Nonempty) :
    (supportResponse fallbackI a).expectation (fun i =>
      (supportResponse fallbackJ b).expectation (fun j =>
        if π j = i ∧ valid j = true then 1 else 0)) =
      validAgreementProbability valid π a b := by
  rw [supportResponse_expectation fallbackI a _ ha]
  simp_rw [supportResponse_expectation fallbackJ b _ hb, Finset.sum_boole]
  unfold validAgreementProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem validAgreement_le_supportResponses (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J) :
    validAgreementProbability valid π a b ≤
      (supportResponse fallbackI a).expectation (fun i =>
        (supportResponse fallbackJ b).expectation (fun j =>
          if π j = i ∧ valid j = true then 1 else 0)) := by
  by_cases ha : (support a).Nonempty
  · by_cases hb : (support b).Nonempty
    · exact le_of_eq (supportResponse_validAgreement valid π fallbackI fallbackJ a b ha hb).symm
    · have he : support b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [validAgreementProbability, he, Finset.card_empty, Nat.cast_zero,
        mul_zero, div_zero]
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  · have he : support a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    simp only [validAgreementProbability, he, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_mul, div_zero]
    apply response_expectation_nonnegative
    intro i
    apply response_expectation_nonnegative
    intro j
    split_ifs <;> norm_num

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_GameDecoder
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
open MinUncutGames.Foundations.Games

theorem distribution_sq_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (F : Ω → ℝ) :
    law.expectation F ^ 2 ≤ law.expectation (fun x => F x ^ 2) := by
  let m := law.expectation F
  have h := response_expectation_nonnegative law (fun x => (F x - m) ^ 2)
    (fun x => sq_nonneg _)
  have he : law.expectation (fun x => (F x - m) ^ 2) =
      law.expectation (fun x => F x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * F x ^ 2 - 2 * m * (law.weight x * F x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => F x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

def questionBias (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testBias ε (π q.1 q.2) (fun f => bitSign (A q.1 f)) (fun g => bitSign (B q.2 g))

def questionAcceptance (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testAcceptance ε (π q.1 q.2) (A q.1) (B q.2)

omit [DecidableEq Q₁] [DecidableEq Q₂] [Nonempty I] [Nonempty J] in
theorem questionAcceptance_eq (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) :
    questions.expectation (questionAcceptance ε π A B) =
      (1 + questions.expectation (questionBias ε π A B)) / 2 := by
  unfold questionAcceptance
  simp_rw [testAcceptance_eq]
  unfold questionBias FiniteDistribution.expectation
  simp only [div_eq_mul_inv, mul_add, mul_one, ← mul_assoc,
    Finset.sum_add_distrib, ← Finset.sum_mul, questions.normalized]

omit [Nonempty I] [Nonempty J] in
theorem testBias_constant_right (ε : ℝ) (π : J → I) (A : Cube I → ℝ) :
    testBias ε π A (fun _ => 1) = 𝔼 f, A f := by
  unfold testBias
  simp only [mul_one, Fintype.expect_const]
  simp_rw [← Finset.sum_mul, noiseWeight_sum, one_mul]

omit [Nonempty I] [Nonempty J] in
theorem empty_conditioned_bias (ε : ℝ) (π : J → I)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) :
    testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun _ => bitSign false) = 0 := by
  simp only [bitSign, Bool.false_eq_true, ite_false]
  rw [testBias_constant_right]
  have hz := foldedAnswer_zero_coefficient i₀ tableA
  simpa [coefficient, walsh, bitSign] using hz

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Reindexing
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

end FiniteDistribution

end MinUncutGames.Foundations.Games

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Game
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem failureCount_eq_sum_map (F : Formula) (bob : BobStrategy F)
    (cs : List (Fin F.clauses.length)) :
    failureCount F bob cs =
      (cs.map (fun c => clauseFailure (clauseAt F c) bob)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [failureCount, List.map_cons, List.sum_cons, ih]

theorem failureCount_allIndices (F : Formula) (bob : BobStrategy F) :
    failureCount F bob (allIndices F) =
      ∑ c : Fin F.clauses.length, clauseFailure (clauseAt F c) bob := by
  rw [failureCount_eq_sum_map]
  unfold allIndices
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem base_success_le_verifier (F : Formula) (hne : F.clauses ≠ [])
    (strategy : Strategy (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer) :
    (baseGame F hne).success strategy ≤
      (eventLaw F hne).probability (accepts F strategy.2 strategy.1) := by
  unfold Game.success baseGame
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro e he
  exact baseAccepts_implies_sampled F e.1 e.2 _ _ he

theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μ : FiniteDistribution X) (f : X → Y) (g : Y → Z) :
    (μ.pushforward f).pushforward g = μ.pushforward (g ∘ f) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward]
  calc
    _ = ∑ y : Y, ∑ x : X, if f x = y then
        (if g y = z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y = z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem expectation_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (f : X → Y) (H : Y → ℝ) :
    (μ.pushforward f).expectation H = μ.expectation (H ∘ f) := by
  classical
  simp only [FiniteDistribution.expectation, FiniteDistribution.pushforward,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem repeated_questions (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    ((baseGame F hne).repetition u).questions =
      ((eventLaw F hne).iid u).pushforward (repeatedVisible F u) := by
  change (((eventLaw F hne).pushforward (visibleQuestion F)).iid u).transport
    (Game.tupleQuestionEquiv u) = _
  rw [FiniteDistribution.iid_pushforward, ← FiniteDistribution.pushforward_equiv,
    pushforward_comp]
  rfl

theorem repeated_expectation (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 events : Fin u → RandomEvent F, H (repeatedVisible F u events) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  rw [repeated_questions, expectation_pushforward]
  change ((FiniteDistribution.uniform (RandomEvent F)).iid u).expectation _ = _
  rw [FiniteDistribution.iid_uniform, FiniteDistribution.expectation_uniform,
    Fintype.expect_eq_sum_div_card]
  rfl

theorem repeated_expectation_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        H (sampledVariables F c s, c) := by
  rw [repeated_expectation]
  calc
    _ = 𝔼 p : ClauseContext F u × SlotContext u,
        H (sampledVariables F p.1 p.2, p.1) :=
      Fintype.expect_equiv
        (Game.tupleQuestionEquiv (Q₁ := Fin F.clauses.length) (Q₂ := Slot) u)
        _ _ (fun _ => rfl)
    _ = _ := SourceTape.expect_prod _

end MinUncutGames.Foundations.Hastad.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextLoad
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextLoad

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) (s : Fin 6) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((clauseWords F.clauses[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

omit [DecidableEq Extra] in
theorem output_variable (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (variableField j s) =
      encodeWord (F.clauses[(tuple j).val][s.val].variableIndex.val) ++ base (variableField j s) := by
  rw [variableField, stageTapes_field, ite_eq_left j.isLt, clauseWords_variable]

omit [DecidableEq Extra] in
theorem output_polarity (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (polarityField j s) =
      encodeWord (if F.clauses[(tuple j).val][s.val].positive then 1 else 0) ++
        base (polarityField j s) := by
  rw [polarityField, stageTapes_field, ite_eq_left j.isLt, clauseWords_polarity]

end MinUncutGames.Foundations.Hastad.SourceContextLoad

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ProfileBridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

theorem nameWords_length_le_input (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (i : Fin (positionEncoding u).size) :
    (nameWords F c i).length ≤ (formulaBits F).length := by
  rw [nameWords, encodeWord_length]
  exact (Nat.succ_le_of_lt
    (occurrenceName F c ((positionEncoding u).code.symm i)).isLt).trans
      (SourceBounds.formulaBits_length_ge_variables F)

end MinUncutGames.Foundations.Hastad.SourceProfileBridge

namespace MinUncutGames.Foundations.Hastad.SourceSignaturePrepare

open _root_.Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open MinUncutGames.Foundations.Complexity

variable {u : ℕ} {Extra τ : Type}

theorem place_injective : Function.Injective (place (u := u) (Extra := Extra)) := by
  intro a b h
  have h' := congrArg unplace h
  simpa only [unplace_place, Option.some.injEq] using h'

variable [DecidableEq Extra]

theorem fill_update (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) (value : List Bool) :
    fill base (Function.update localTapes k value) =
      Function.update (fill base localTapes) (place k) value := by
  funext a
  cases hu : unplace a with
  | none =>
    have hne : a ≠ place k := by
      intro h
      rw [h, unplace_place] at hu
      contradiction
    simp only [fill, hu, Function.update_of_ne hne]
  | some j =>
    have ha := place_unplace a j hu
    rw [← ha]
    by_cases h : j = k
    · subst j
      simp only [fill_place]
      simp [Function.update]
    · have hne : place (Extra := Extra) j ≠ place k := fun h' => h (place_injective h')
      simp only [fill_place, Function.update_of_ne h, Function.update_of_ne hne]

omit [DecidableEq Extra] in

theorem loaded_name_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (i : Fin (Width u)) :
    SourceContextLoad.stageTapes F c base u (place (.inl i)) = nameWords F c i := by
  obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
  simp only [place, Equiv.symm_apply_apply]
  have ho := SourceContextLoad.output_variable F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (variableField p) =
    encodeWord (F.clauses[(c p.1).val][(slotEncoding.code p.2).val].variableIndex.val) ++
      base (variableField p) at ho
  rw [ho, hbase p, List.append_nil]
  simp only [nameWords, names, Equiv.symm_apply_apply]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

end MinUncutGames.Foundations.Hastad.SourceSignaturePrepare

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_AddressArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRankPhase

open _root_.Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

variable {u : Nat} {Extra : Type}

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  rw [variableSlots_digit]
  erw [SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, slotEncoding, hs] <;> rfl

end MinUncutGames.Foundations.Hastad.SourceRankPhase

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderAccumulate
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceStartup

open _root_.Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceStartup.instDecidableEqExtra
theorem ready_sharedFrame (F : Target.Formula) (k : Tape u D)
    (hk : k = .index ∨ k = .scratch ∨ k = .copyScratch) : readyTapes F k = [] := by
  rcases hk with rfl | rfl | rfl <;>
    simp only [readyTapes, initializedTapes]
  all_goals
    rw [SourceLoopInit.output_frame F (initialTapes F) _
      (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
      (by simp) (by simp)]
    simp [initialTapes]

end

end MinUncutGames.Foundations.Hastad.SourceStartup

end
section
namespace MinUncutGames.Foundations.Hastad.SourceBasePhase

open _root_.Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open MinUncutGames.Reduction.MachineSubstitution

def operandLength (rank offset : Nat) : Nat :=
  (encodeWord rank).length + (encodeWord offset).length

theorem steps_le_timePolynomial (coefficient rank offset : Nat) :
    steps coefficient rank offset ≤ (timePolynomial coefficient).eval (operandLength rank offset) := by
  have hr : rank ≤ operandLength rank offset + coefficient := by
    simp only [operandLength, encodeWord_length]
    omega
  have hd : ∀ i, i < 2 → digits coefficient offset i ≤ operandLength rank offset + coefficient := by
    intro i _
    simp only [digits, operandLength, encodeWord_length]
    split <;> omega
  have h := MachineHorner.steps_le_timePolynomial rank (digits coefficient offset) 2
    (operandLength rank offset + coefficient) hr hd
  rw [timePolynomial_eval]
  unfold steps
  omega

end MinUncutGames.Foundations.Hastad.SourceBasePhase

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTupleOdometer
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineTupleOdometer

open _root_.Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_increment_succ (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix) =
      ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord, List.replicate_succ, update_current, update_remaining]

theorem stepAux_increment_zero (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d 0 currentSuffix remainingSuffix) =
      ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord]

theorem incrementStep_succ (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix⟩ =
      some ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_succ current remaining distinct]

theorem incrementStep_zero (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ =
      some ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_zero current remaining distinct]

theorem resetTrace (current remaining : K) (distinct : current ≠ remaining)
    (resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 1]
      (some ⟨some resetLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 (d + r) currentSuffix remainingSuffix⟩ :=
  MachineUnaryAddAt.addTrace current remaining distinct resetLabel (some carryLabel)
    program atReset base d r currentSuffix remainingSuffix ambient register

theorem carryTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 2]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 d currentSuffix remainingSuffix⟩ := by
  rw [show d + 2 = (d + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[d + 1]
    (TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) = _
  rw [incrementStep_zero current remaining distinct checkLabel doneLabel resetLabel
    program atCheck]
  simpa only [Nat.add_zero] using resetTrace current remaining distinct resetLabel carryLabel
    program atReset base d 0 currentSuffix remainingSuffix ambient none

section AscendingCycle

open scoped BigOperators

def bodyConfiguration (current remaining : K) (bodyLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (remainder + 1), none),
    digitTapes current remaining (base (remainder + 1)) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def checkConfiguration (current remaining : K) (checkLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some checkLabel, (ambient remainder, register remainder),
    digitTapes current remaining (base remainder) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def cycleExit (current remaining : K) (exitLabel : Λ)
    (maximum : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none),
    digitTapes current remaining (base 0) 0 maximum currentSuffix remainingSuffix⟩

def VisitTraces (current remaining : K) (bodyLabel checkLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (maximum count : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) : Prop :=
  ∀ r, r ≤ count → (MachineComposition.advance (TM2.step program))^[cost r]
    (some (bodyConfiguration current remaining bodyLabel maximum r
      currentSuffix remainingSuffix ambient base)) =
    some (checkConfiguration current remaining checkLabel maximum r
      currentSuffix remainingSuffix ambient register base)

theorem cycleTrace (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (maximum count : ℕ) (hcount : count ≤ maximum)
    (currentSuffix remainingSuffix : List Bool) (ambient : ℕ → σ)
    (register : ℕ → Option Bool) (base : ℕ → K → List Bool) (cost : ℕ → ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program maximum count
      currentSuffix remainingSuffix ambient register base cost) :
    (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (some (bodyConfiguration current remaining bodyLabel maximum count
        currentSuffix remainingSuffix ambient base)) =
      some (cycleExit current remaining exitLabel maximum
        currentSuffix remainingSuffix ambient base) := by
  induction count with
  | zero =>
    rw [cycleSteps_zero, Function.iterate_add_apply, visits 0 (Nat.le_refl 0)]
    simpa only [checkConfiguration, cycleExit, Nat.sub_zero] using
      carryTrace current remaining distinct checkLabel bodyLabel resetLabel exitLabel
        program atCheck atReset (base 0) maximum currentSuffix remainingSuffix
        (ambient 0) (register 0)
  | succ count ih =>
    rw [cycleSteps_succ, Function.iterate_add_apply, visits (count + 1) (Nat.le_refl _),
      Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (TM2.step program ⟨some checkLabel, (ambient (count + 1), register (count + 1)),
        digitTapes current remaining (base (count + 1)) (maximum - (count + 1))
          (count + 1) currentSuffix remainingSuffix⟩) = _
    rw [incrementStep_succ current remaining distinct checkLabel bodyLabel resetLabel
      program atCheck]
    have hnext : maximum - (count + 1) + 1 = maximum - count := by omega
    rw [hnext]
    exact ih (by omega) (fun r hr => visits r (by omega))

def ascendingCycleInTime (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (n : ℕ) (hn : 0 < n) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) (B : ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program (n - 1) (n - 1)
      currentSuffix remainingSuffix ambient register base cost)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (bodyConfiguration current remaining bodyLabel (n - 1) (n - 1)
        currentSuffix remainingSuffix ambient base)
      (some (cycleExit current remaining exitLabel (n - 1)
        currentSuffix remainingSuffix ambient base)) (n * (B + 2)) where
  steps := cycleSteps cost (n - 1) (n - 1)
  evals_in_steps := cycleTrace current remaining distinct bodyLabel checkLabel resetLabel exitLabel
    program atCheck atReset (n - 1) (n - 1) (Nat.le_refl _) currentSuffix remainingSuffix
    ambient register base cost visits
  steps_le_m := by
    have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
      calc
        _ ≤ ∑ _r ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
        _ = _ := by simp
    have hn' : n - 1 + 1 = n := by omega
    simp only [cycleSteps, hn', Nat.mul_add] at *
    omega

end AscendingCycle

section Nested

open scoped BigOperators

inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

end NestedCycle

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested

end MinUncutGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextClear
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextClear

open _root_.Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

theorem fieldAt_injective : Function.Injective (fieldAt (u := u) (Extra := Extra)) := by
  intro i j h
  have hpair := SourceContextLoad.Tape.field.inj h
  have hp : finProdFinEquiv.symm i = finProdFinEquiv.symm j :=
    Prod.ext hpair.1 hpair.2
  exact finProdFinEquiv.symm.injective hp

theorem fields_nodup : (fields (u := u) (Extra := Extra)).Nodup := by
  exact List.nodup_ofFn.mpr fieldAt_injective

theorem field_mem (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.Tape.field j s : Tape u Extra) ∈ fields := by
  apply List.mem_ofFn.mpr
  exact ⟨finProdFinEquiv (j, s), by simp [fieldAt]⟩

theorem mem_fields_iff (p : Tape u Extra) : p ∈ fields ↔ ∃ j s, p = .field j s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, hi.symm⟩
  · rintro ⟨j, s, rfl⟩
    exact field_mem j s

variable [DecidableEq Extra]

theorem finalTapes_eq (base : Tape u Extra → List Bool) :
    MachineDrainMany.finalTapes fields base = outputTapes base := by
  funext p
  rw [MachineDrainMany.finalTapes_apply]
  cases p <;> simp [mem_fields_iff, outputTapes]

theorem lengthSum_update {K : Type} [DecidableEq K] (chosen : List K)
    (base : K → List Bool) (source : K) (h : source ∉ chosen) :
    MachineDrainMany.lengthSum chosen (Function.update base source []) =
      MachineDrainMany.lengthSum chosen base := by
  unfold MachineDrainMany.lengthSum
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [Function.update_of_ne (by intro he; subst k; exact h hk)]

theorem steps_eq_of_nodup {K : Type} [DecidableEq K] (chosen : List K)
    (h : chosen.Nodup) (base : K → List Bool) :
    MachineDrainMany.steps chosen base =
      MachineDrainMany.lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => rfl
  | cons source chosen ih =>
      obtain ⟨hn, hd⟩ := List.nodup_cons.mp h
      rw [MachineDrainMany.steps, ih hd, lengthSum_update chosen base source hn]
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem lengthSum_le_selected {K : Type} (chosen : List K)
    (base : K → List Bool) (B : Nat) (h : ∀ k ∈ chosen, (base k).length ≤ B) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length * B := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons source chosen ih =>
      have hs := h source (by simp)
      have ht := ih (by intro k hk; exact h k (by simp [hk]))
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
        List.length_cons, Nat.add_mul, Nat.one_mul] at ht ⊢
      omega

omit [DecidableEq Extra] in
theorem loaded_field_length_le (F : Target.Formula)
    (tuple : Fin u → Fin F.clauses.length) (base : Tape u Extra → List Bool)
    (hfields : ∀ j s, base (.field j s) = []) (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.stageTapes F tuple base u (.field j s)).length ≤
      (formulaBits F).length := by
  rw [SourceContextLoad.stageTapes_field, ite_eq_left j.isLt, hfields, List.append_nil]
  exact (clauseField_length_le _ s).trans (variables_add_two_le_input F)

omit [DecidableEq Extra] in
theorem loaded_cost_le (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = []) :
    MachineDrainMany.lengthSum fields (SourceContextLoad.stageTapes F tuple base u) + 6 * u + 1 ≤
      6 * u * ((formulaBits F).length + 1) + 1 := by
  have h := lengthSum_le_selected fields (SourceContextLoad.stageTapes F tuple base u)
    (formulaBits F).length (by
      intro p hp
      obtain ⟨j, s, rfl⟩ := (mem_fields_iff p).mp hp
      exact loaded_field_length_le F tuple base hfields j s)
  rw [fields_length] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

omit [DecidableEq Extra] in
theorem output_loaded_eq_base (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) :
    outputTapes (SourceContextLoad.stageTapes F tuple base u) = base := by
  funext p
  cases p with
  | field j s => exact (hfields j s).symm
  | index => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).1.trans hindex.symm
  | work => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).2.trans hwork.symm
  | _ => exact SourceContextLoad.stageTapes_frame F tuple base u _ (by simp) (by simp) (by simp)

end MinUncutGames.Foundations.Hastad.SourceContextClear

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_LoopOrder
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open MinUncutGames.Reduction

theorem inputBits_eq_header_records (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++
        input.equations.flatMap (fun e => encodeWords (SourceEncoding.equationWords e)) := by
  unfold SourceEncoding.inputBits SourceEncoding.inputWords
  rw [encodeWords_append]
  congr 1
  induction input.equations with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, encodeWords_append, ih]

end MinUncutGames.Foundations.Hastad.SourceLoopOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceQueryOrder

open _root_.Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder

def occurrenceBits (F : Formula) (u D : Nat) (p : SourceIndex F u D) : List Bool :=
  encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))

def slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u) (s : SlotContext u) :
    List Bool :=
  (testTapeEncoding u D).enumerate.flatMap (fun t => occurrenceBits F u D ((c, s), t))

def tupleBits (F : Formula) (u D : Nat) (c : ClauseContext F u) : List Bool :=
  (slotContextEncoding u).enumerate.flatMap (slotBits F u D c)

end MinUncutGames.Foundations.Hastad.SourceQueryOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceTupleTape

open _root_.Turing Complexity SourceContexts SourceRuntimeModel

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem update_rank (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rank) value = tapes base {s with rank := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rightBase) value = tapes base {s with rightBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .leftBase) value = tapes base {s with leftBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_zero (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .zero) value = tapes base {s with zero := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_emitted (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .accumulator)
      (value.reverse ++ base (workTape .accumulator)) = tapes base {s with emitted := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

structure WorkClean (base : Arena u Extra → List Bool) : Prop where
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  scratch : base (workTape .arithScratch) = []

omit [DecidableEq Extra] in
theorem tapes_coordinateOutput {numVariables : ℕ} (j : Fin u) (clause : Target.Clause numVariables)
    (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes (SourceContextLoad.coordinateOutput j clause base) s =
      SourceContextLoad.coordinateOutput j clause (tapes base s) := by
  funext k
  cases k <;> simp [tapes, SourceContextLoad.coordinateOutput, workTape]
  rename_i extra
  cases extra with
  | inl header => rfl
  | inr role => cases role <;> rfl

omit [DecidableEq Extra] in

theorem tapes_stageTapes (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot) (r : Nat) :
    tapes (SourceContextLoad.stageTapes F c base r) s =
      SourceContextLoad.stageTapes F c (tapes base s) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [SourceContextLoad.stageTapes]
    split
    · rw [tapes_coordinateOutput, ih]
    · exact ih

theorem final_tapes (base : Arena u Extra → List Bool) (emitted : List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {emitted := emitted} =
      Function.update base (workTape .accumulator) (emitted.reverse ++ base (workTape .accumulator)) := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role =>
    cases role <;> simp_all [tapes, workTape]

theorem empty_tapes (base : Arena u Extra → List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {} = base := by
  simpa using final_tapes base [] hrank hright hleft hzero

end MinUncutGames.Foundations.Hastad.SourceTupleTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TupleBody
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleBody

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape

variable {u D : Nat} {Extra : Type}

variable [DecidableEq Extra]

structure Ready (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) : Prop where
  formula : base .formula = formulaBits F
  current : ∀ j, base (.current j) = encodeWord (c j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copyScratch : base .copyScratch = []
  fields : ∀ j s, base (.field j s) = []
  variableCount : base variableHeader = encodeWord F.«variables»
  clauseCount : base clauseHeader = encodeWord F.clauses.length
  leftBlock : base (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
  dummy : base (workTape .dummy) =
    encodeWord (F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u))
  rank : base (workTape .rank) = []
  rightBase : base (workTape .rightBase) = []
  leftBase : base (workTape .leftBase) = []
  zero : base (workTape .zero) = []
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  arithScratch : base (workTape .arithScratch) = []
  coefficient : base (workTape .coefficient) = []
  queryTemporary : base (workTape .queryTemporary) = []
  queryScratch : base (workTape .queryScratch) = []

def rightValue (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1

def variableRank (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  ((variableEncoding F u).code (sampledVariables F c (selected index))).val

def leftValue (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0

noncomputable def slotBudget (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) : Nat :=
  1 + (MachineHorner.timePolynomial u).eval F.«variables» +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
      (SourceBasePhase.operandLength (variableRank F c index) 0) +
    (QueryCount u D * (9 * nBits F u + 21) + 1) +
    (variableRank F c index + 2) + (leftValue F c index + 2)

omit [DecidableEq Extra] in
theorem Ready.loadedClean {F : Target.Formula} {c : ClauseContext F u}
    {base : Arena u Extra → List Bool} (h : Ready F c base) :
    WorkClean (SourceContextLoad.stageTapes F c base u) where
  accA := (loaded_extra F c base _).trans h.accA
  accB := (loaded_extra F c base _).trans h.accB
  counter := (loaded_extra F c base _).trans h.counter
  scratch := (loaded_extra F c base _).trans h.arithScratch

def loopSnapshot (F : Target.Formula) (c : ClauseContext F u) (bits : List Bool) : Snapshot :=
  { rightBase := encodeWord (rightValue F c), zero := encodeWord 0, emitted := bits }

def rankSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { loopSnapshot F c bits with rank := encodeWord (variableRank F c index) }

def baseSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { rankSnapshot F c index bits with leftBase := encodeWord (leftValue F c index) }

def slotAt (u : Nat) (i : Nat) : SlotContext u :=
  if h : i < SlotCount u then selected ⟨i, h⟩ else fun _ => .first

def prefixBits (F : Target.Formula) (c : ClauseContext F u) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits F c r ++ SourceQueryOrder.slotBits F u D c (slotAt u r)

noncomputable def prefixBudget (F : Target.Formula) (c : ClauseContext F u) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixBudget F c r + if h : r < SlotCount u then slotBudget (D := D) F c ⟨r, h⟩ else 0

theorem prefixBits_eq_ofFn (F : Target.Formula) (c : ClauseContext F u) (n : Nat) :
    prefixBits (D := D) F c n =
      (List.ofFn (fun i : Fin n => slotAt u i.val)).flatMap (SourceQueryOrder.slotBits F u D c) := by
  induction n with
  | zero => simp [prefixBits]
  | succ n ih =>
    rw [prefixBits, List.ofFn_succ', List.concat_eq_append, List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using congrArg
        (fun bits => bits ++ SourceQueryOrder.slotBits F u D c (slotAt u n)) ih

theorem prefixBits_eq_tupleBits (F : Target.Formula) (c : ClauseContext F u) :
    prefixBits (D := D) F c (SlotCount u) = SourceQueryOrder.tupleBits F u D c := by
  rw [prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (SlotCount u) => slotAt u i.val) =
      (slotContextEncoding u).enumerate := by
    apply congrArg List.ofFn
    funext i
    simp only [slotAt, i.isLt, ↓reduceDIte, selected]
  rw [hlist]
  rfl

noncomputable def setupBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  ((u * (10 * (formulaBits F).length + 20) + 1) +
    (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
      (5 * (formulaBits F).length + 6) + 2)) + 1 +
    (MachineHorner.timePolynomial u).eval F.clauses.length +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
      (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
        (2 ^ (2 ^ u) * F.«variables» ^ u)) +
    (((clauseEncoding F u).code c).val + 2)

def finishBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  1 + (rightValue F c + 2) + 2 + (6 * u * ((formulaBits F).length + 1) + 1) + 1

noncomputable def bodyBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  setupBudget F c + prefixBudget (D := D) F c (SlotCount u) + finishBudget F c

end MinUncutGames.Foundations.Hastad.SourceTupleBody

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Gap
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open MinUncutGames.Integration.SourceParameters
open MinUncutGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

end MinUncutGames.Foundations.Hastad.SourceGap

namespace MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

open _root_.Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def currentAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .current ⟨i, h⟩ else .extra accumulator

def remainingAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .remaining ⟨i, h⟩ else .extra accumulator

theorem setDigits_setAcc (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc a base bits) = setAcc a (setDigits m digits base) bits := by
  funext k
  cases k <;> simp [setDigits, setAcc, Function.update_apply]

theorem putDigit_setAcc (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) (bits : List Bool) :
    putDigit i (setAcc a base bits) d r = setAcc a (putDigit i base d r) bits := by
  funext k
  cases k <;> simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
    setAcc, Function.update_apply]

theorem setDigits_putDigit (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (d r : ℕ) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d r := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | remaining i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m (Fin.snoc digits d) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d (m - 1 - d) := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | remaining i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc_base (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d (m - 1 - d)) =
      setDigits m (Fin.snoc digits d) base := by
  rw [setDigits_putDigit, setDigits_snoc]

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ) (accumulator : Extra)
    {q : ℕ} (base : Tape u Extra → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc accumulator base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc accumulator base ((bits c).reverse ++ output))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ u)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical accumulator base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (.extra accumulator))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical accumulator base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt accumulator)
      (remaining := remainingAt accumulator) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical accumulator base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    dsimp only [tree]
    erw [NestedCycle.LeafBound]
    exact hcount
  | succ q ih =>
    have hqu : q < u := by omega
    let s : CycleSchedule (Tape u Extra) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (.extra accumulator))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base)
            (checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
              s.ambient s.register s.base), tree.LeafBound B := by
      let d : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c d)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (.extra accumulator)))
        d.val (m - 1 - d.val)
      have hrem : m - 1 - d.val = r.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = d.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = d.val + 1 := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, d.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical accumulator
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c d) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical accumulator childBase childBits =
          checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
            s.ambient s.register s.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_extra, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) s children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
        bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, s,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt accumulator q) (remainingAt accumulator q)
        (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        finalConfiguration (next (q + 1)) canonical accumulator base bits := by
      simp only [cycleExit, finalConfiguration, configuration, s, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt accumulator) (remainingAt accumulator)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
          bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (currentAt accumulator q) (remainingAt accumulator q)
          (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B : ℕ) (base : Tape u Extra → List Bool)
    (bits : (Fin u → Fin m) → List Bool)
    (atCheck : ∀ i, i < u → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < u → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) u bodyLabel canonical base)
      (some (finalConfiguration (next u) canonical accumulator base bits))
      ((B + 2 * u) * m ^ u)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical accumulator
    positive B u (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

end MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TupleBound
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

theorem clauseRank_le_power (F : Target.Formula) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val ≤ (formulaBits F).length ^ u := by
  have hr := ((clauseEncoding F u).code c).isLt
  change _ < F.clauses.length ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

theorem variableRank_le_power (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    variableRank F c index ≤ (formulaBits F).length ^ u := by
  have hr := ((variableEncoding F u).code (sampledVariables F c (selected index))).isLt
  change variableRank F c index < F.«variables» ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_variables F) u)

theorem leftValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    leftValue F c index ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (selected index)) 0).le.trans
    (SourceBounds.nBits_le_input F u)

theorem rightValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u) :
    rightValue F c ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (fun _ => .first)) 1).le.trans
    (SourceBounds.nBits_le_input F u)

theorem leftBlock_le_numberBound (F : Target.Formula) :
    2 ^ (2 ^ u) * F.«variables» ^ u ≤
      SourceBounds.bitCoefficient u * (formulaBits F).length ^ u := by
  apply Nat.le_trans (m := nBits F u)
  · rw [Nat.mul_comm (2 ^ (2 ^ u)) (F.«variables» ^ u), nBits_eq]
    omega
  · exact SourceBounds.nBits_le_input F u

theorem slotBudget_le (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    slotBudget (D := D) F c index ≤ (slotPolynomial u D).eval (formulaBits F).length := by
  have hr := variableRank_le_power F c index
  have hl := leftValue_le_numberBound F c index
  have hb := SourceBounds.nBits_le_input F u
  have hn := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_variables F)
  have ho : SourceBasePhase.operandLength (variableRank F c index) 0 ≤
      (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))) ho
  have hq := Nat.mul_le_mul_left (QueryCount u D)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb) 21)
  rw [slotPolynomial_eval]
  unfold slotBudget
  omega

theorem prefixBudget_le (F : Target.Formula) (c : ClauseContext F u) (r : Nat) :
    prefixBudget (D := D) F c r ≤ r * (slotPolynomial u D).eval (formulaBits F).length := by
  induction r with
  | zero => simp [prefixBudget]
  | succ r ih =>
    rw [prefixBudget]
    split
    next h =>
      have hs := slotBudget_le (D := D) F c ⟨r, h⟩
      simpa only [Nat.succ_mul] using Nat.add_le_add ih hs
    next _ =>
      simpa only [Nat.add_zero] using ih.trans
        (Nat.mul_le_mul_right ((slotPolynomial u D).eval (formulaBits F).length) (Nat.le_succ r))

theorem finishBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    finishBudget F c ≤ (finishPolynomial u).eval (formulaBits F).length := by
  have hr := rightValue_le_numberBound F c
  rw [finishPolynomial_eval]
  unfold finishBudget
  omega

end MinUncutGames.Foundations.Hastad.SourceTupleBound

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal.tupleBoundExtraDecidableEq
theorem resetDigits_ready (F : Target.Formula) :
    setDigits F.clauses.length (fun _ : Fin u => 0)
      (SourceStartup.readyTapes (u := u) (D := D) F) = SourceStartup.readyTapes F := by
  funext k
  cases k <;> simp [setDigits]

theorem allBits_eq_records (F : Target.Formula) (hne : F.clauses ≠ []) :
    allBits (SourceQueryOrder.tupleBits F u D) =
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords e)) := by
  rw [sourceList_nonempty F u D hne]
  unfold allBits SourceQueryOrder.tupleBits SourceQueryOrder.slotBits
    SourceQueryOrder.occurrenceBits
  simp only [rawSourceList, occurrenceList,
    sourceIndexEncoding, Encoding.enumerate_prod, List.flatMap_map, List.flatMap_assoc,
    clauseEncoding, Encoding.enumerate_fin_function]

theorem accumulated_eq_input (F : Target.Formula) (hD : 0 < D) (hne : F.clauses ≠ []) :
    (allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
        SourceStartup.readyTapes F (accumulatorTape u D) =
      (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MinUncutGames.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

end

end MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

end

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

end MinUncutGames.Foundations.PCP

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

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type,
    padded_satisfied_inl, padded_satisfied_inr, Bool.true_eq_false,
    ite_false, Finset.sum_const_zero, Nat.add_zero]
  rfl

end MinUncutGames.Foundations.PCP.DegreeReplacement

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

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

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

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

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

end Profiles

section ReturnSums

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end ReturnSums

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

namespace MinUncutGames.Foundations.PCP.ZigzagGraphs

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

end MinUncutGames.Foundations.PCP.ZigzagGraphs

namespace MinUncutGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

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
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
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
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
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

end MinUncutGames.Foundations.PCP.ZigzagSpectral

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

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

end MinUncutGames.Foundations.PCP.ExpanderFamily

namespace MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlay
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

section Averages

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

end Averages

end MinUncutGames.Foundations.PCP.Overlay

end
section

namespace MinUncutGames.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem operator_binomialMean [Fintype D] (G : PortGraph V D)
    (n : Nat) (g : Nat → V → ℝ) (v : V) :
    averagingOperator G (fun w => LazySmoothing.binomialMean n (fun k => g k w)) v =
      LazySmoothing.binomialMean n (fun k => averagingOperator G (g k) v) := by
  unfold averagingOperator LazySmoothing.binomialMean
  exact Finset.expect_comm Finset.univ Finset.univ
    (fun d tape => g (LazySmoothing.bitCount tape) (G.rot (v, d)).1)

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

theorem iterate_lazy_eq_binomialMean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (f : V → ℝ) :
    iterateOperator (lazyGraph G) n f =
      fun v => LazySmoothing.binomialMean n (fun k => iterateOperator G k f v) := by
  induction n with
  | zero =>
    funext v
    simp [iterateOperator]
  | succ n ih =>
    funext v
    change averagingOperator (lazyGraph G) (iterateOperator (lazyGraph G) n f) v = _
    rw [ih, averagingOperator_lazy, operator_binomialMean, LazySmoothing.mean_succ]
    rfl

theorem iterate_mem_Icc [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (n : Nat) (v : V) : iterateOperator G n f v ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    change mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact mean_nonnegative _ (fun d => (ih ((G.rot (v, d)).1)).1)
    · calc
        mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ≤
            mean (fun _ : D => (1 : ℝ)) :=
          mean_mono (fun d => (ih ((G.rot (v, d)).1)).2)
        _ = 1 := mean_const _

theorem lazy_endpoint_modal_transfer [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M m : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1) (v : V)
    (hmodal : 1 / (q : ℝ) ≤ iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) f v) :
    1 / (2 * (q : ℝ)) ≤ iterateOperator (lazyGraph G) m f v := by
  rw [iterate_lazy_eq_binomialMean] at hmodal ⊢
  exact LazySmoothing.modal_transfer q M m hq hM hlo hhi
    (fun k => iterateOperator G k f v) (fun k => iterate_mem_Icc G f hf k v) hmodal

end MinUncutGames.Foundations.PCP.PoweringLazy

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.CloudRounding

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

end MinUncutGames.Foundations.PCP.CloudRounding

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

namespace MinUncutGames.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

theorem rejectionCount_eq_sum {U E : Type*} [Fintype E]
    (G : ConstraintGraph U E A) (labeling : U → A) :
    G.rejectionCount labeling = ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]

theorem pad_rejectionCount [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) :
    (pad G extra).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [edgeSatisfied_inl G htail, edgeSatisfied_inr]
  simp

end MinUncutGames.Foundations.PCP.VertexPadding

namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  classical
  calc
    (baseGraph (pad table h)).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      unfold ConstraintGraph.rejectionCount
      symm
      apply Finset.card_equiv (dartEquiv h)
      intro e
      simp only [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_pad_equiv]
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

end MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

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
namespace MinUncutGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]
  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

end Nonempty

theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end MinUncutGames.Foundations.PCP.SpectralCut


end
namespace MinUncutGames.Foundations.PCP.LazySpectral

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

end MinUncutGames.Foundations.PCP.LazySpectral

noncomputable section

namespace MinUncutGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

end MinUncutGames.Foundations.PCP.Preprocessing

end
namespace MinUncutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

end MinUncutGames.Foundations.PCP.PreprocessingTables

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

end MinUncutGames.Foundations.PCP.PreprocessingRegularSoundness

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
namespace MinUncutGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

theorem portGraph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

end MinUncutGames.Foundations.PCP.PreprocessingTableSpectral

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringReturn
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem iterateOperator_succ_right [Fintype D] (G : PortGraph V D)
    (n : Nat) (f : V → ℝ) :
    iterateOperator G n (averagingOperator G f) = iterateOperator G (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (averagingOperator G) ih

theorem mean_wordEnd [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (f : V → ℝ),
      mean (fun r : Fin n → D => f (wordEnd G n v r)) = iterateOperator G n f v := by
  intro n
  induction n with
  | zero =>
    intro v f
    change mean (fun _ : Fin 0 → D => f v) = f v
    exact mean_const _
  | succ n ih =>
    intro v f
    rw [mean_word_cons_head]
    change mean (fun d : D => mean (fun r : Fin n → D =>
      f (wordEnd G n (next G v d) r))) = _
    calc
      _ = mean (fun d : D => iterateOperator G n f (next G v d)) := by
        congr 1
        funext d
        exact ih (next G v d) f
      _ = iterateOperator G (n + 1) f v := rfl

theorem mean_pivot_endpoints [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (e : Edge V D) (φ ψ : V → ℝ),
      mean (fun r : Fin n → D =>
        φ (leftFromPivot G n k e.1 r) * ψ (rightFromPivot G n k e r)) =
        iterateOperator G k.val φ e.1 *
          iterateOperator G (n - k.val) ψ (next G e.1 e.2) := by
  intro n
  induction n with
  | zero =>
    intro k e φ ψ
    have hk : k = 0 := Fin.eq_zero k
    subst k
    change mean (fun _ : Fin 0 → D => φ e.1 * ψ (next G e.1 e.2)) =
      φ e.1 * ψ (next G e.1 e.2)
    exact mean_const _
  | succ n ih =>
    intro k e φ ψ
    refine Fin.cases ?_ (fun j => ?_) k
    · change mean (fun r : Fin (n + 1) → D =>
        φ e.1 * ψ (wordEnd G (n + 1) (next G e.1 e.2) r)) =
          φ e.1 * iterateOperator G (n + 1) ψ (next G e.1 e.2)
      rw [mean_mul_left, mean_wordEnd]
    · simp only [Fin.val_succ, Nat.add_sub_add_right]
      rw [mean_word_cons_tail]
      change mean (fun r : Fin n → D => mean (fun d : D =>
        φ (next G (leftFromPivot G n j e.1 r) d) *
          ψ (rightFromPivot G n j e r))) =
        iterateOperator G (j.val + 1) φ e.1 *
          iterateOperator G (n - j.val) ψ (next G e.1 e.2)
      calc
        _ = mean (fun r : Fin n → D =>
            averagingOperator G φ (leftFromPivot G n j e.1 r) *
              ψ (rightFromPivot G n j e r)) := by
          congr 1
          funext r
          rw [mean_mul_right]
          rfl
        _ = iterateOperator G j.val (averagingOperator G φ) e.1 *
            iterateOperator G (n - j.val) ψ (next G e.1 e.2) :=
          ih j e (averagingOperator G φ) ψ
        _ = _ := by rw [iterateOperator_succ_right]

theorem mean_edge_endpoints [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (φ ψ : Edge V D → V → ℝ) :
    mean (fun w : Walk V D (n + 1) =>
      φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)) =
      mean (fun e : Edge V D =>
        iterateOperator G k.val (φ e) e.1 *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
  let F : Edge V D × (Fin n → D) → ℝ := fun z =>
    φ z.1 (leftFromPivot G n k z.1.1 z.2) *
      ψ z.1 (rightFromPivot G n k z.1 z.2)
  calc
    _ = mean (fun w => F (pivotEquiv G n k w)) := by
      congr 1
      funext w
      dsimp [F]
      rw [leftFromPivot_actual, rightFromPivot_actual, pivotEquiv_fst]
    _ = mean F := mean_equiv (pivotEquiv G n k) F
    _ = mean (fun e : Edge V D => mean (fun r : Fin n → D =>
        φ e (leftFromPivot G n k e.1 r) * ψ e (rightFromPivot G n k e r))) := mean_prod F
    _ = _ := by
      congr 1
      funext e
      exact mean_pivot_endpoints G n k e (φ e) (ψ e)

theorem mean_marked_bit [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
      markedStep G bad f v := by
  change mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
    mean (fun d : D => if bad (v, d) then f (next G v d) else 0)
  congr 1
  funext d
  cases bad (v, d) <;> simp [bit]

theorem edgeAt_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    edgeAt G n w 0 = (w.1, w.2 0) := by
  cases n <;> rfl

theorem word_first_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (v : V) :
    mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) 0) = true)) =
      edgeProfile bad v := by
  rw [mean_word_cons_head]
  simp_rw [edgeAt_zero]
  change mean (fun d : D => mean (fun _ : Fin n → D => bit (bad (v, d) = true))) = _
  calc
    _ = mean (fun d : D => bit (bad (v, d) = true)) := by simp only [mean_const]
    _ = edgeProfile bad v := mean_edge_bit bad v

theorem word_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (k : Fin (n + 1)),
      mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) k) = true)) =
        iterateOperator G k.val (edgeProfile bad) v := by
  intro n
  induction n with
  | zero =>
    intro v k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact word_first_hit_mean G bad 0 v
  | succ n ih =>
    intro v k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact word_first_hit_mean G bad (n + 1) v
    · rw [mean_word_cons_head]
      change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (next G v d, p) j) = true))) =
          averagingOperator G (iterateOperator G j.val (edgeProfile bad)) v
      calc
        _ = mean (fun d : D => iterateOperator G j.val (edgeProfile bad) (next G v d)) := by
          congr 1
          funext d
          exact ih (next G v d) j
        _ = _ := rfl

theorem word_pair_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (i j : Fin (n + 1)), i < j →
      mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true)) =
        iterateOperator G i.val (markedStep G bad
          (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) v := by
  intro n
  induction n with
  | zero =>
    intro v i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact ((lt_irrefl _) hij).elim
  | succ n ih =>
    intro v i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact ((lt_irrefl _) hij).elim
      · intro _hij
        simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (v, d) = true) * bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          markedStep G bad (iterateOperator G b.val (edgeProfile bad)) v
        calc
          _ = mean (fun d : D => bit (bad (v, d) = true) *
              iterateOperator G b.val (edgeProfile bad) (next G v d)) := by
            congr 1
            funext d
            rw [mean_mul_left, word_hit_mean]
          _ = _ := mean_marked_bit G bad _ v
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (Nat.not_lt_zero _ hij).elim
      · intro hij
        have hab : a < b := Nat.lt_of_succ_lt_succ hij
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (edgeAt G n (next G v d, p) a) = true) *
            bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          averagingOperator G (iterateOperator G a.val (markedStep G bad
            (iterateOperator G (b.val - a.val - 1) (edgeProfile bad)))) v
        calc
          _ = mean (fun d : D => iterateOperator G a.val (markedStep G bad
              (iterateOperator G (b.val - a.val - 1) (edgeProfile bad))) (next G v d)) := by
            congr 1
            funext d
            exact ih (next G v d) a b hab
          _ = _ := rfl

theorem hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (k : Fin (n + 1)) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w k) = true)) =
      edgeDensity bad := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) k) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w k) = true))
    _ = mean (iterateOperator G k.val (edgeProfile bad)) := by
      congr 1
      funext v
      exact word_hit_mean G bad n v k
    _ = mean (edgeProfile bad) := mean_iterate G k.val _
    _ = _ := rfl

theorem pair_hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w i) = true) *
      bit (bad (edgeAt G n w j) = true)) = returnMass G bad (j.val - i.val - 1) := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w i) = true) *
          bit (bad (edgeAt G n w j) = true))
    _ = mean (iterateOperator G i.val (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad)))) := by
      congr 1
      funext v
      exact word_pair_hit_mean G bad n v i j hij
    _ = mean (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) := mean_iterate G i.val _
    _ = _ := rfl

theorem pair_event_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) =>
      bit (bad (edgeAt G n w i) = true ∧ bad (edgeAt G n w j) = true)) =
        returnMass G bad (j.val - i.val - 1) := by
  simpa only [PoweringMoment.bit_mul] using pair_hit_mean G bad n i j hij

end MinUncutGames.Foundations.PCP.PoweringReturn

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

end MinUncutGames.Foundations.PCP.PoweringOpinions

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

end MinUncutGames.Foundations.PCP.PoweringTest

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

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
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

end MinUncutGames.Foundations.PCP.PoweringCounting

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

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

end MinUncutGames.Foundations.PCP.QueryIncidence

noncomputable section

namespace MinUncutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MinUncutGames.Foundations.Hastad

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

end MinUncutGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.AlphabetGraph

open MinUncutGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

end MinUncutGames.Foundations.PCP.AlphabetGraph

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

theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_FormulaEncoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.NameCompaction

open MinUncutGames.Foundations.Target

theorem failureCount_evaluations (F : Formula) (A : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

end MinUncutGames.Foundations.PCP.NameCompaction

end

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

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

end MinUncutGames.Foundations.PCP.FinalConstants

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

theorem walkParameter_eq : walkParameter = 2 * FinalConstants.endpointLength :=
  fixedWalkParameter.property

end MinUncutGames.Foundations.PCP.RoundTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTableComplexity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end MinUncutGames.Foundations.PCP.AmplificationRound

end
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
namespace MinUncutGames.Foundations.PCP.PoweringFinalConstants

theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

end MinUncutGames.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec

def C {P : Type} [Primcodable P] (f : P → AExpr) : Prop :=
  Computable (fun p=>(f p).program.code)
variable {P : Type} [Primcodable P]
lemma C.fixed (a : AExpr) : C (fun _ : P=>a) := Computable.const _
lemma cond_code (e a b : AExpr) :
    (.cond e a b : AExpr).program.code = branch e.program.code a.program.code b.program.code := rfl
attribute [local irreducible] PolyProgram.add PolyProgram.sub PolyProgram.mul
lemma eqOf_code {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    (PolyProgram.eqOf F G).code =
      branch (bin PolyProgram.add.code (bin PolyProgram.sub.code F.code G.code)
        (bin PolyProgram.sub.code G.code F.code)) (constCode 1) (constCode 0) := rfl
lemma eq_code (a b : AExpr) :
    (.eq a b : AExpr).program.code =
      branch (bin PolyProgram.add.code (bin PolyProgram.sub.code a.program.code b.program.code)
        (bin PolyProgram.sub.code b.program.code a.program.code)) (constCode 1) (constCode 0) :=
  eqOf_code a.program b.program
lemma at_code (a : AExpr) : (.at a : AExpr).program.code =
    Code.comp PolyProgram.dynamic.code (Code.cons a.program.code Code.id) := rfl
lemma powCode_eq (a : AExpr) (n : ℕ) :
    Nat.rec (AExpr.const 1).program.code (fun _ ih=>bin PolyProgram.mul.code ih a.program.code) n =
      (a.pow n).program.code := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bin _ (Nat.rec _ _ n) _ = _
    rw [ih]; rfl

def sumCode (cs : List Code) : Code := cs.foldr (bin PolyProgram.add.code) (AExpr.const 0).program.code
lemma p_sumCode : Primrec sumCode :=
  Primrec.list_foldr Primrec.id (Primrec.const _) ((p_bin _).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
lemma sumCode_eq (as : List AExpr) : sumCode (as.map (fun a=>a.program.code))=(AExpr.sum as).program.code := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [sumCode,List.map_cons,List.foldr_cons] at *; rw [ih]; rfl
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type}
def O (c : UEncoding P A) (f : ∀p,A p → AExpr) : Prop := c.Out (fun p x=>(f p x).program.code)
variable {c : UEncoding P A}
lemma O.fixed (e : AExpr) : O c (fun _ _=>e) := out_const c (Computable.const _)
lemma O.const {f : ∀p,A p → ℕ} (hf : c.Out f) : O c (fun p x=>.const (f p x)) := hf.map p_constCode.to_comp
lemma O.add {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.add (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.add.code).to_comp
lemma O.sub {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.sub (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.sub.code).to_comp
lemma O.mul {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.mul (a p x) (b p x)) :=
  ha.map₂ hb (p_bin PolyProgram.mul.code).to_comp
lemma O.div {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.div (a p x) (b p x)) :=
  ha.map₂ hb (p_bin Division.quotient.code).to_comp
lemma O.mod {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.mod (a p x) (b p x)) :=
  ha.map₂ hb (p_bin Division.remainder.code).to_comp
lemma O.cond {e a b : ∀p,A p → AExpr} (he : O c e) (ha : O c a) (hb : O c b) :
    O c (fun p x=>.cond (e p x) (a p x) (b p x)) := by
  have hh := (he.pair (ha.pair hb)).map p_branch.to_comp
  exact hh.ofEq (fun p x=>(cond_code (e p x) (a p x) (b p x)).symm)
lemma O.eq {a b : ∀p,A p → AExpr} (ha : O c a) (hb : O c b) : O c (fun p x=>.eq (a p x) (b p x)) := by
  have hh := ((ha.sub hb).add (hb.sub ha)).cond (O.fixed (.const 1)) (O.fixed (.const 0))
  exact hh.ofEq (fun p x=>(eq_code (a p x) (b p x)).symm)
lemma O.at {a : ∀p,A p → AExpr} (ha : O c a) : O c (fun p x=>.at (a p x)) := by
  have hh := ha.map (computable_comp.comp (Computable.const PolyProgram.dynamic.code)
    (computable_cons.comp Computable.id (Computable.const Code.id)))
  exact hh.ofEq (fun p x=>(at_code (a p x)).symm)
lemma O.choose {q : ∀p,A p → Bool} {a b : ∀p,A p → AExpr}
    (hq : c.Map bool q) (ha : O c a) (hb : O c b) : O c (fun p x=>if q p x then a p x else b p x) := by
  apply (Out.cond hq ha hb).ofEq
  intro p x
  change (if q p x = true then (a p x).program.code else (b p x).program.code) =
    (if q p x = true then a p x else b p x).program.code
  by_cases h : q p x = true
  · rw [ite_eq_left h]
    exact (congrArg (fun e : AExpr=>e.program.code) (ite_eq_left h : (if q p x = true then a p x else b p x)=a p x)).symm
  · rw [ite_eq_right h]
    exact (congrArg (fun e : AExpr=>e.program.code) (ite_eq_right h : (if q p x = true then a p x else b p x)=b p x)).symm

def powCode (a : Code) (n : ℕ) : Code := Nat.rec (AExpr.const 1).program.code (fun _ ih=>bin PolyProgram.mul.code ih a) n
lemma c_powCode : Computable₂ powCode := by
  exact Computable.nat_rec Computable.snd (Computable.const _)
    ((p_bin PolyProgram.mul.code).to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)).to₂
lemma O.pow {a : ∀p,A p → AExpr} {n : ∀p,A p → ℕ} (ha : O c a) (hn : c.Out n) :
    O c (fun p x=>(a p x).pow (n p x)) :=
  (ha.map₂ hn c_powCode).ofEq (fun p x=>powCode_eq (a p x) (n p x))
lemma O.sum {as : ∀p,A p → List AExpr} (hs : c.Out (fun p x=>(as p x).map (fun a=>a.program.code))) :
    O c (fun p x=>AExpr.sum (as p x)) :=
  (hs.map p_sumCode.to_comp).ofEq (fun p x=>sumCode_eq (as p x))
lemma O.fromC {a : P → AExpr} (ha : C a) : O c (fun p _=>a p) := out_const c ha
lemma O.toC {a : P → AExpr} (ha : O (UEncoding.fixed (P:=P) Encoding.unit) (fun p _=>a p)) : C a := by
  obtain ⟨f,hf,he⟩:=ha
  exact (hf.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())

end MinUncut.Preprocess.Syntax

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TemplateExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.FiniteProof MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type} {c : UEncoding P A}
lemma O.ofEq {f g : ∀p,A p → AExpr} (hf : O c f) (h : ∀p x,f p x=g p x) : O c g :=
  Out.ofEq hf (fun p x=>congrArg (fun a:AExpr=>a.program.code) (h p x))

lemma lookupCode_eq (a : AExpr) (xs : List (ℕ × ℕ)) :
    lookupCode a.program.code xs=(a.lookup xs).program.code := by
  induction xs with
  | nil => rfl
  | cons ix xs ih =>
    simp only [lookupCode,List.foldr_cons] at *
    rw [ih]
    rw [AExpr.lookup,cond_code,eq_code]
    rfl
lemma O.lookup {a : ∀p,A p → AExpr} {xs : ∀p,A p → List (ℕ × ℕ)}
    (ha : O c a) (hx : c.Out xs) : O c (fun p x=>(a p x).lookup (xs p x)) :=
  (ha.map₂ hx p_lookupCode.to_comp).ofEq (fun p x=>lookupCode_eq (a p x) (xs p x))
lemma O.sum_enum {b : UEncoding P B} {f : ∀p,A p × B p → AExpr}
    (hf : O (c.prod b) f) : O c (fun p x=>AExpr.sum ((b.enc p).enumerate.map (fun y=>f p (x,y)))) := by
  apply O.sum
  apply (out_list hf).ofEq
  intro p x
  simp only [List.map_map,Function.comp_def]
lemma O.sum_fin {n : P → ℕ} (hn : Computable n) {f : ∀p,A p × Fin (n p) → AExpr}
    (hf : O (c.prod (fin n hn)) f) : O c (fun p x=>AExpr.sum (List.ofFn (fun i=>f p (x,i)))) := by
  apply hf.sum_enum.ofEq
  intro p x
  simp only [fin,Encoding.fin,Encoding.enumerate,List.map_ofFn,Function.comp_def,Equiv.refl_symm]
  rfl
end MinUncut.Preprocess.Syntax

end
end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def answers : UEncoding ℕ (fun _=>ClauseAnswer) := fixed clauseAnswerEncoding
def lefts : UEncoding ℕ I := positions.function bool
def rights : UEncoding ℕ J := positions.function answers

end MinUncut.Preprocess.Source

end
section

namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad
variable {P : Type} [Primcodable P] {A Γ : P → Type}

lemma map_representative {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p → A p → Bool} {i : ∀p,Γ p → A p}
    (hf : g.Map (a.function bool) f) (hi : g.Map a i) :
    g.Map (a.function bool) (fun p x=>representative (i p x) (f p x)) := by
  apply (map_lambda (map_xor (map_apply hf.first (map_snd g a)) (map_apply hf hi).first)).ofEq
  intro p x
  funext y
  change (f p x y ^^ f p x (i p x))=(if f p x (i p x) then cubeFlip (f p x) else f p x) y
  cases f p x (i p x) <;> simp [cubeFlip]
end MinUncut.Preprocess.UEncoding

end
section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

def paddedRep {u : ℕ} (valid : J u → Bool) (j₀ : J u) (g : Cube (J u)) : Cube (J u) :=
  fun j=>if valid j then representative j₀ g j else false

lemma extend_representative {u : ℕ} (valid : J u → Bool)
    (j₀ : {j : J u // valid j=true}) (g : Cube (J u)) :
    extendRestricted valid (representative j₀ (restrictQuery valid g))=paddedRep valid j₀ g := by
  funext j
  unfold extendRestricted paddedRep
  by_cases h:valid j=true
  · simp only [h,↓reduceDIte,ite_true]
    cases h₀:g j₀ <;> simp [representative,restrictQuery,cubeFlip,h₀]
  · simp [h]

def rawLocal {u : ℕ} (valid : J u → Bool) (π : J u → I u)
    (f : Cube (I u)) (g μ : Cube (J u)) : Equation (LocalKey u) :=
  ((jEncoding u).enumerate.find? valid).elim
    ⟨.inl (representative (leftAnchor u) f),.inr (.inr ()),.inr (.inr ()),f (leftAnchor u)⟩
    (fun j₀=>⟨.inl (representative (leftAnchor u) f),
      .inr (.inl (paddedRep valid j₀ g)),
      .inr (.inl (paddedRep valid j₀ (thirdQuery π f g μ))),
      f (leftAnchor u) ^^ f (π j₀) ^^ μ j₀⟩)

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_UniformCube
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def equationEquiv (X : Type) : Equation X ≃ X × X × X × Bool where
  toFun e := (e.first,e.second,e.third,e.rhs)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def equation (a : UEncoding P A) : UEncoding P (fun p=>Equation (A p)) :=
  (a.prod (a.prod (a.prod bool))).ofEquiv (fun p=>equationEquiv (A p))

lemma map_equation {g : UEncoding P Γ} {a : UEncoding P A}
    {f h j : ∀p,Γ p → A p} {b : ∀p,Γ p → Bool}
    (hf : g.Map a f) (hh : g.Map a h) (hj : g.Map a j) (hb : g.Map bool b) :
    g.Map a.equation (fun p x=>⟨f p x,h p x,j p x,b p x⟩) :=
  map_comp (map_pair hf (map_pair hh (map_pair hj hb)))
    (map_from (a.prod (a.prod (a.prod bool))) (fun p=>equationEquiv (A p)))

end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformAlgebra
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]

namespace UEncoding
variable {A B Γ : P → Type}

lemma out_sum {g : UEncoding P Γ} {a : UEncoding P A}
    [∀p,Fintype (A p)] {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f)
    (hadd : Computable₂ (fun x y : X=>x+y)) :
    g.Out (fun p s=>∑x,f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).sum,
    (c_rangeSum hr hadd).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  have he : ((a.enc p).enumerate.map (fun x=>f p (s,x))).sum=∑x,f p (s,x) := by
    classical
    have ht : (a.enc p).enumerate.toFinset=Finset.univ := by ext x; simp [(a.enc p).mem_enumerate x]
    rw [← List.sum_toFinset _ (a.enc p).nodup_enumerate,ht]
  rw [←he,Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquation
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.SourceTemplate UEncoding

def ls : UEncoding Par (fun p=>I p.1) := up lefts
def rs : UEncoding Par (fun p=>J p.1) := up rights
def fc := ls.function bool
def gc := rs.function bool
def keys : UEncoding Par (fun p=>LocalKey p.1) := fc.sum (gc.sum (fixed Encoding.unit))

variable {Γ : Par → Type} {e : UEncoding Par Γ}
def tapes : UEncoding Par (fun p=>SourceTape.TestTape (I p.1) (J p.1) p.2) :=
  fc.prod ((rs.function ds).prod gc)
end MinUncut.Preprocess.Source

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type} {c : UEncoding P A}
lemma C.precomp {a : Q → AExpr} (ha : C a) {f : P → Q} (hf : Computable f) : C (fun p=>a (f p)) :=
  Computable.comp ha hf
end MinUncut.Preprocess.Syntax

namespace MinUncut.Preprocess.Face
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)

def rowEquiv (p : P) : Row (m p) (n p) ≃
    {x:Fin (m p) × Point (m p) (n p) // rowGood m n hnpos p x=true} where
  toFun r := ⟨(r.1,fun j=>if h:j=r.1 then ⟨0,hnpos p⟩ else r.2 ⟨j,h⟩),by simp [rowGood]⟩
  invFun r := ⟨r.val.1,fun j=>r.val.2 j.val⟩
  left_inv r := by
    dsimp only
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    funext j
    exact dite_eq_right j.property
  right_inv r := by
    apply Subtype.ext
    dsimp only
    refine Prod.ext (by rfl) ?_
    funext j
    by_cases h:j=r.val.1
    · subst j
      dsimp only
      split
      · exact ((of_decide_eq_true r.property) : r.val.2 r.val.1=⟨0,hnpos p⟩).symm
      · rename_i hh; exact False.elim (hh rfl)
    · exact dite_eq_right h

def rows : UEncoding P (fun p=>Row (m p) (n p)) :=
  ((rowPairs m n hm hn).restrict (rowGood m n hnpos) (map_rowGood m n hm hn hnpos)).ofEquiv
    (rowEquiv m n hnpos)

lemma map_faceRow : ((points m n hm hn).prod (axes m hm)).Map (rows m n hm hn hnpos)
    (fun _ x=>⟨x.2,face x.1 x.2⟩) := by
  let pt:=points m n hm hn
  let ax:=axes m hm
  let rs:=rowPairs m n hm hn
  let c:=pt.prod ax
  have hi : c.Map ax (fun _ x=>x.2) := map_snd _ _
  have hx : c.Map pt (fun _ x=>x.1) := map_fst _ _
  have hy : (c.prod ax).Map ax (fun _ x=>x.2) := map_snd _ _
  have hz : (c.prod ax).Map (values n hn) (fun p _=>⟨0,hnpos p⟩) := map_const (Computable.const 0)
  have hw : (c.prod ax).Map (values n hn)
      (fun p x=>if x.2=x.1.2 then ⟨0,hnpos p⟩ else x.1.1 x.2) := by
    apply (map_cond (map_bool_eq hy hi.first) hz
      (map_apply hx.first hy)).ofEq
    intro p x
    simp only [decide_eq_true_eq]
  have hp := map_pair hi (map_lambda hw)
  have hg : ∀p (x : Point (m p) (n p) × Fin (m p)),rowGood m n hnpos p (x.2,fun j=>if j=x.2 then ⟨0,hnpos p⟩ else x.1 j)=true := by
    intro p x
    simp [rowGood]
  have hmk:=map_restrict_mk (map_rowGood m n hm hn hnpos) hp hg
  apply (map_comp hmk (map_from _ (rowEquiv m n hnpos))).ofEq
  intro p x
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext j
  exact ite_eq_right j.property

end MinUncut.Preprocess.Face

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformProduct
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [CommMonoid X]

namespace UEncoding
variable {A B Γ : P → Type}
lemma out_prod {g : UEncoding P Γ} {a : UEncoding P A}
    [∀p,Fintype (A p)] {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f)
    (hmul : Computable₂ (fun x y : X=>x*y)) :
    g.Out (fun p s=>∏x,f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).prod,
    (c_rangeProd hr hmul).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  have he : ((a.enc p).enumerate.map (fun x=>f p (s,x))).prod=∏x,f p (s,x) := by
    classical
    have ht : (a.enc p).enumerate.toFinset=Finset.univ := by ext x; simp [(a.enc p).mem_enumerate x]
    rw [← List.prod_toFinset _ (a.enc p).nodup_enumerate,ht]
  rw [←he,Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformRational
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian
lemma c_algebraicNonneg : Computable (fun p : ℚ × ℚ × ℕ=>algebraicNonneg p.1 p.2.1 p.2.2) := by
  have ha : Computable (fun p : ℚ × ℚ × ℕ=>p.1) := Computable.fst
  have hb : Computable (fun p : ℚ × ℚ × ℕ=>p.2.1) := Computable.fst.comp Computable.snd
  have hn : Computable (fun p : ℚ × ℚ × ℕ=>p.2.2) := Computable.snd.comp Computable.snd
  exact (Computable.cond (ca_ratLe (ca_const 0) hb).decide
    (Computable.cond (ca_ratLe (ca_const 0) ha).decide (ca_const true)
      (ca_ratLe (ca_ratPow ha (ca_const 2)) (ca_ratMul (ca_ratCast hn) (ca_ratPow hb (ca_const 2)))).decide)
    (Computable.cond (ca_ratLt ha (ca_const 0)).decide (ca_const false)
      (ca_ratLe (ca_ratMul (ca_ratCast hn) (ca_ratPow hb (ca_const 2))) (ca_ratPow ha (ca_const 2))).decide)).of_eq
    (by intro p; simp only [algebraicNonneg,Bool.cond_decide])
namespace UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {a : UEncoding P A}
variable {f g : ∀p,A p → ℚ}
lemma Out.ratAdd (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x+g p x) :=
  hf.map₂ hg computable_ratAdd
lemma Out.ratSub (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x-g p x) :=
  hf.map₂ hg computable_ratSub
lemma Out.ratMul (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x*g p x) :=
  hf.map₂ hg computable_ratMul
lemma Out.ratDiv (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x/g p x) :=
  hf.map₂ hg computable_ratDiv
lemma Out.ratInv (hf : a.Out f) : a.Out (fun p x=>(f p x)⁻¹) := hf.map computable_ratInv
lemma Out.algebraicNonneg (hf : a.Out f) (hg : a.Out g) {n : ∀p,A p → ℕ} (hn : a.Out n) :
    a.Map bool (fun p x=>algebraicNonneg (f p x) (g p x) (n p x)) :=
  ((hf.pair (hg.pair hn)).map c_algebraicNonneg).toBool
end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformGrid
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian
open scoped BigOperators
lemma c_coefficient : Computable coefficient :=
  ca_ratDiv (ca_ratPow (ca_const (-1)) Computable.id)
    (ca_ratMul (ca_ratPow (ca_const 2) Computable.id) (ca_ratCast (ca_factorial Computable.id)))
lemma c_primitive : Computable₂ primitive := by
  have hc : Computable₂ (fun (p : ℕ × ℚ) (j : ℕ)=>coefficient j*p.2^(2*j+1)/(2*j+1)) := by
    apply ca_ratDiv
    · exact ca_ratMul (c_coefficient.comp Computable.snd)
        (ca_ratPow (Computable.snd.comp Computable.fst) (ca_add (ca_mul (ca_const 2) Computable.snd) (ca_const 1)))
    · exact ca_ratAdd (ca_ratMul (ca_const 2) (ca_ratCast Computable.snd)) (ca_const 1)
  exact ((c_rangeSum hc computable_ratAdd).comp Computable.id
    (ca_add (ca_mul (ca_const 2) Computable.fst) (ca_const 1))).of_eq
      (by
        intro p
        dsimp only [primitive]
        rw [←List.sum_toFinset _ List.nodup_range,List.toFinset_range]
        rfl)
lemma c_qIntegral : Computable (fun p : ℕ × ℚ × ℚ=>qIntegral p.1 p.2.1 p.2.2) :=
  ca_ratSub (c_primitive.comp Computable.fst (Computable.snd.comp Computable.snd))
    (c_primitive.comp Computable.fst (Computable.fst.comp Computable.snd))
lemma c_endpoint : Computable (fun p : ℚ × ℕ × ℕ=>endpoint p.1 p.2.1 p.2.2) := by
  unfold endpoint
  exact ca_ratAdd (computable_ratNeg.comp Computable.fst)
    (ca_ratDiv (ca_ratMul (ca_ratMul (ca_const 2) Computable.fst)
      (ca_ratCast (Computable.snd.comp Computable.snd)))
      (ca_ratCast (Computable.fst.comp Computable.snd)))
attribute [local irreducible] endpoint qIntegral primitive
lemma ca_endpoint {X : Type} [Primcodable X] {t : X → ℚ} {l i : X → ℕ}
    (ht : Computable t) (hl : Computable l) (hi : Computable i) :
    Computable (fun x=>endpoint (t x) (l x) (i x)) := by
  have hh := @Computable.comp X (ℚ × ℕ × ℕ) ℚ _ _ _ _ _ c_endpoint (ht.pair (hl.pair hi))
  exact hh.of_eq (by intro x; rfl)
lemma ca_qIntegral {X : Type} [Primcodable X] {r : X → ℕ} {a b : X → ℚ}
    (hr : Computable r) (ha : Computable a) (hb : Computable b) :
    Computable (fun x=>qIntegral (r x) (a x) (b x)) := by
  have hh := @Computable.comp X (ℕ × ℚ × ℚ) ℚ _ _ _ _ _ c_qIntegral (hr.pair (ha.pair hb))
  exact hh.of_eq (by intro x; rfl)
lemma c_midpoint : Computable (fun p : ℚ × ℕ × ℕ=>midpoint p.1 p.2.1 p.2.2) := by
  unfold FiniteGaussian.midpoint
  exact ca_ratDiv (ca_ratAdd c_endpoint
    (ca_endpoint Computable.fst (Computable.fst.comp Computable.snd)
      (ca_add (Computable.snd.comp Computable.snd) (ca_const 1)))) (ca_const 2)
end MinUncut.Preprocess

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian MinUncut.Outer
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
attribute [local irreducible] gridWeight
namespace UEncoding
variable {P X : Type} [Primcodable P] [Primcodable X] {A : P → Type}
lemma computable_prod [CommMonoid X] (a : UEncoding P A) [∀p,Fintype (A p)]
    {f : ∀p,A p → X} (hf : a.Out f) (hmul : Computable₂ (fun x y : X=>x*y)) :
    Computable (fun p=>∏x,f p x) := (out_prod hf.second hmul).unit
end UEncoding
namespace Denominator
variable {P : Type} [Primcodable P]
variable (t m n : P → ℕ) (ht : Computable t) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
include ht hm hn hnpos in
lemma c_faceCardBound : Computable (fun p=>faceCardBound (t p) (m p) (n p)) :=
  ca_pow (ca_pow (ca_const 2) (ca_pow (ca_const 2) (ca_mul (ca_const 3) ht)))
    (computableCard (Face.rows m n hm hn hnpos))
end Denominator

open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
end MinUncut.Preprocess

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
lemma O.demandDigit {i : ∀p,A p → ℕ} (hi : c.Out i) :
    O c (fun p x=>MinUncut.Costed.SourceWords.tupleDigit (i p x)) :=
  ((O.fixed (.reg 0)).div ((O.fixed (.reg 2)).pow hi)).mod (O.fixed (.reg 2))
lemma O.slotExpr {i j : ∀p,A p → ℕ} (hi : c.Out i) (hj : c.Out j) :
    O c (fun p x=>MinUncut.Costed.SourceWords.slotExpr (i p x) (j p x)) :=
  ((O.fixed (.const 3)).add ((O.fixed (.const 4)).mul (O.demandDigit hi))).add (O.const hj) |>.at
lemma O.equationExpr {i : ∀p,A p → ℕ} (hi : c.Out i) :
    O c (fun p x=>MinUncut.Costed.SourceWords.equationExpr (i p x)) := by
  have hp : (c.prod (fin (fun _ : P=>3) (Computable.const 3))).Out (fun _ x=>x.2.val) :=
    (out_code (fin (P:=P) (fun _=>3) (Computable.const 3))).second
  have hw := (O.slotExpr hi.first hp).mul ((O.fixed (.reg 1)).pow hp)
  exact (O.slotExpr hi (out_const c (Computable.const 3))).add
    ((O.fixed (.const 2)).mul (hw.sum_fin (Computable.const 3)))
lemma c_firstExpr : C MinUncut.Costed.SourceWords.firstExpr := by
  let c := unitN.prod (fin id Computable.id)
  have hi : c.Out (fun _ x=>x.2.val) := (out_code (fin id Computable.id)).second
  have hbase : O c (fun _ _=>.mul ((AExpr.reg 1).pow 3) (.const 2)) := O.fixed _
  exact ((O.equationExpr hi).mul (hbase.pow hi) |>.sum_fin Computable.id).toC
lemma O.secondExpr {t : P → ℕ} (ht : Computable t) {h : ∀p,A p → Fin (t p) → Bool}
    {pos : ∀p,A p → Fin (t p) → Fin 3}
    (hh : c.Map ((fin t ht).function bool) h)
    (hp : c.Map (Alphabet.positionsList t ht) pos) :
    O c (fun p x=>MinUncut.Costed.SourceWords.secondExpr (h p x) (pos p x)) := by
  let d:=c.prod (fin t ht)
  have hi : d.Out (fun _ x=>x.2.val) := (out_code (fin t ht)).second
  have hj := map_apply hp.first (map_snd c (fin t ht))
  have hjn := (out_code (fin (fun _ : P=>3) (Computable.const 3))).comp hj
  have hb:=map_apply hh.first (map_snd c (fin t ht))
  have left:=O.slotExpr hi hjn
  have right:=(O.fixed (.reg 1)).add (O.equationExpr hi)
  have base : O d (fun _ _=>.add (.reg 1) (.mul ((AExpr.reg 1).pow 3) (.const 2))) := O.fixed _
  exact ((O.choose hb left right).mul (base.pow hi)).sum_fin ht

lemma c_demandSignatureExpr : C MinUncut.Costed.SourceWords.signatureExpr := by
  let axes:=fin (P:=ℕ) id Computable.id
  let pos:=fin (P:=ℕ) (fun _=>3) (Computable.const 3)
  let c:=unitN.prod axes
  let d:=c.prod pos
  let e:=d.prod pos
  have hi : e.Out (fun _ x=>x.1.1.2.val) := (out_code axes).second.first.first
  have hp : e.Out (fun _ x=>x.1.2.val) := (out_code pos).second.first
  have hq : e.Out (fun _ x=>x.2.val) := (out_code pos).second
  have eqs := (O.slotExpr hi hp).eq (O.slotExpr hi hq)
  have powq := hq.map (ca_pow (Computable.const 2) Computable.id)
  have inner := (eqs.mul (O.const powq)).sum_fin (Computable.const 3)
  have pcode : d.Out (fun _ x=>x.2.val) := (out_code pos).second
  have powp := pcode.map (ca_pow (Computable.const (2^3)) Computable.id)
  have mid := (inner.mul (O.const powp)).sum_fin (Computable.const 3)
  have ii : c.Out (fun _ x=>x.2.val) := (out_code axes).second
  have outer := (mid.mul (O.const (ii.map (ca_pow (Computable.const ((2^3)^3)) Computable.id)))).sum_fin Computable.id
  have rhs := ((O.slotExpr ii (out_const c (Computable.const 3))).mul
    (O.const (ii.map (ca_pow (Computable.const 2) Computable.id)))).sum_fin Computable.id
  have co := O.const (out_const unitN (ca_pow (Computable.const ((2^3)^3)) Computable.id))
  exact (outer.add (co.mul rhs)).toC
end MinUncut.Preprocess.Syntax

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncut.SourceTemplate UEncoding
lemma out_keyTag : keys.Out (fun _ x=>keyTag x) := by
  apply (out_elimSum (out_const fc (Computable.const 0))
    (out_elimSum (out_const gc (Computable.const 1)) (out_const (fixed Encoding.unit) (Computable.const 2)))).ofEq
  intro p x
  cases x with
  | inl _=> rfl
  | inr x=>cases x <;> rfl
lemma out_keyTable : keys.Out (fun _ x=>keyTable x) := by
  apply (out_elimSum (out_code fc)
    (out_elimSum (out_code gc) (out_const (fixed Encoding.unit) (Computable.const 0)))).ofEq
  intro p x
  cases x with
  | inl _=> rfl
  | inr x=>cases x <;> rfl
end MinUncut.Preprocess.Source

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformSets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open MinUncut.Outer MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
lemma out_setCard (t : P → ℕ) (ht : Computable t) :
    (sets t ht).Out (fun _ S=>S.card) := by
  have hmask:=map_hidden t ht
  have hi := map_apply hmask.first (map_snd (sets t ht) (fin t ht))
  apply (out_sum (out_boolNat hi) Primrec.nat_add.to_comp).ofEq
  intro p S
  have he : ∀i:Fin (t p), (hiddenSet S i).toNat=if i∈S then 1 else 0 := by
    intro i
    by_cases hi:i∈S <;> simp [hiddenSet,hi]
  simp only [he]
  simp
end MinUncut.Preprocess

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandQueryEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable {pos : ∀p,A p → Fin (t p) → Fin 3}
variable (hp : c.Map (Alphabet.positionsList t ht) pos)
include hp hc in
lemma O.secondAddress : O c (fun p x=>secondAddress (h p) (pos p x)) := by
  have hh : c.Map ((fin t ht).function bool) (fun p _=>h p) := map_const hc
  exact ((O.fixed (.mul ((AExpr.reg 1).pow 3) (.const 2))).pow (out_const c ht)).add
    (O.secondExpr ht hh hp)
end MinUncut.Preprocess.Syntax

end
end

end OAI
end


