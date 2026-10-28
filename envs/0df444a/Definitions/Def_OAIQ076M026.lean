-- Prove2me | Definitions.Def_OAIQ076M026
-- name    : OAIQ076M026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:17.843818+00:00
-- url     : https://prove2.me/theorems/ff4f0331-cfc2-4f01-9b3f-a26f392fab41
-- title:
--   Definitions bundle OAIQ076M026 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 315 declarations of OpenAI's Lean: 135 definitions and 180 theorems. The definitions and types are `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.prefixInTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.profileInTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.profileInTime_bounded`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.profileMachine`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.stageInTime`, `OAI.MinUncutGames.Foundations.Complexity.PoweringMachineFinish.afterD`, `OAI.MinUncutGames.Foundations.Complexity.PoweringMachineFinish.steps`, `OAI.MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop.prefixRows`, `OAI.MinUncutGames.Foundations.Complexity.PoweringMachineRowBody.rowWords`, `OAI.MinUncutGames.Foundations.Complexity.PoweringMachineVertex.rowBits`, `OAI.MinUncutGames.Foundations.Complexity.PoweringPolynomialBudget.finishBudget`, `OAI.MinUncutGames.Foundations.Complexity.PoweringRuntimeBudget.tapeCount`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.affineInPolynomialTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.coefficientTapes`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.leftBaseInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.program`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.rightBaseInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceBasePhase.statement`, `OAI.MinUncutGames.Foundations.Hastad.SourceClauseLookup.lookupInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceClauseLookup.lookupWithSplitInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextClear.clearLoadedInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextClear.clearLoadedToBaseInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextLoad.coordinateInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextLoad.loadInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextLoad.loadUnaryInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextLoad.placedLookupInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextLoad.prefixInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextPrepare.loadInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextPrepare.preparationConfiguration`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextPrepare.prepareInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceContextPrepare.signatureInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.beforeFinish`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.computableInPolyTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.enterFinishInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.forErrorComputableInPolyTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.outputInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.prefixInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.startupInTime`, `OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.timePolynomial`, `OAI.MinUncutGames.Foundations.Hastad.SourceGeneratorContract.sourceMap` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Encoding_Decoder`, `MinUncut_Encoding_FormulaEncoding`, `MinUncut_Encoding_GameDecoder`, `MinUncut_Encoding_ThreeBitTest`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_PoweringPolynomialBudget`, `MinUncut_Machines_Addresses`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_Driver`, `MinUncut_Machines_LoopInitialization`, `MinUncut_Machines_MachineCanonicalOutput`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineLookup`, `MinUncut_Machines_MachineRegisterEmit`, `MinUncut_Machines_PoweringMachineField`, `MinUncut_Machines_PoweringMachineRow`, `MinUncut_Machines_PoweringMachineRowHeaders`, `MinUncut_Machines_PoweringMachineVertex`, `MinUncut_Machines_PoweringRuntimeBudget`, `MinUncut_Machines_Relations`, `MinUncut_Machines_RuntimeFinish`, `MinUncut_Machines_RuntimeModel2`, `MinUncut_PCP_AddressArithmetic`, `MinUncut_PCP_ClauseLookup`, `MinUncut_PCP_ClauseVerifier`, `MinUncut_PCP_ContextClear`, `MinUncut_PCP_ContextLoad`, `MinUncut_PCP_ContextPrepare`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_DescriptorEmission`, `MinUncut_PCP_EquationEmit`, `MinUncut_PCP_Folding`, `MinUncut_PCP_FourierResponse`, `MinUncut_PCP_Game`, `MinUncut_PCP_Gap`, `MinUncut_PCP_Generator`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_Hastad`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_HeaderCounts`, `MinUncut_PCP_LoopOrder`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PoweringOpinionTables`, `MinUncut_PCP_PoweringRowData`, `MinUncut_PCP_PoweringRowHeaderSemantics`, `MinUncut_PCP_PoweringTableLayout`, `MinUncut_PCP_ProfileBridge`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_TableIteration`, `MinUncut_PCP_TupleBody`, `MinUncut_PCP_TupleBound`, `MinUncut_PCP_Walsh`.
--
--   **Imports.** It imports the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M018`, `OAIQ076M019` and `OAIQ076M020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M029` and `OAIQ076M030`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M014
import Definitions.Def_OAIQ076M015
import Definitions.Def_OAIQ076M018
import Definitions.Def_OAIQ076M019
import Definitions.Def_OAIQ076M020

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

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

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

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

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

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

end MinUncutGames.Foundations.Hastad

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

theorem walsh_pullback (π : J → I) (s : Cube J) (f : Cube I) :
    walsh s (fun y => f (π y)) = walsh (parityProjection π s) f := by
  rw [walsh_support]
  rw [← Finset.prod_fiberwise' (support s) π (fun i => bitSign (f i))]
  unfold walsh parityProjection
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const]
  exact sign_power_parity (f i) _

theorem projectedCoefficient_eq (π : J → I) (A : Cube I → ℝ) (s : Cube J) :
    projectedCoefficient π A s = coefficient A (parityProjection π s) := by
  simp only [projectedCoefficient, coefficient, walsh_pullback]

theorem decodingEnergy_le_success (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    decodingEnergy π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ≤
      decoderSuccess π A B := by
  unfold decodingEnergy decoderSuccess
  apply Finset.sum_le_sum
  intro b _
  rw [projectedCoefficient_eq]
  have hsum :
      coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        agreementProbability π (parityProjection π b) b ≤
      ∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun a => coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)
    · intro a _
      exact mul_nonneg (sq_nonneg _) (agreementProbability_nonneg π a b)
    · exact Finset.mem_univ _
  have hm := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (coefficient (fun g => bitSign (B g)) b))
  by_cases ha : (support (parityProjection π b)).Nonempty
  · have hagree := agreementProbability_projection π b ha
    have ht := mul_le_mul_of_nonneg_left hagree
      (mul_nonneg (sq_nonneg (coefficient (fun f => bitSign (A f))
        (parityProjection π b))) (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    have heq : coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2 / (support b).card =
      (coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2) * (1 / (support b).card) := by ring
    rw [heq]
    exact ht.trans (by convert hm using 1; ring)
  · have hempty : support (parityProjection π b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hz := (support_eq_empty_iff _).mp hempty
    simpa [hz, hzero] using hm

theorem bias_sq_le_weighted_energy (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → Bool) :
    testBias ε π A (fun g => bitSign (B g)) ^ 2 ≤
      ∑ b, (projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
        (1 - 2 * ε) ^ (support b).card) ^ 2 := by
  rw [testBias_fourier]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
      (1 - 2 * ε) ^ (support b).card)
    (fun b => coefficient (fun g => bitSign (B g)) b)
  rw [sign_parseval, mul_one] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem decoder_four_epsilon_bias_sq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    4 * ε * testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ^ 2 ≤
      decoderSuccess π A B := by
  apply le_trans _ (decodingEnergy_le_success π A B hzero)
  have hcs := mul_le_mul_of_nonneg_left
    (bias_sq_le_weighted_energy ε π (fun f => bitSign (A f)) B)
    (by linarith : 0 ≤ 4 * ε)
  apply hcs.trans
  rw [Finset.mul_sum]
  unfold decodingEnergy
  apply Finset.sum_le_sum
  intro b _
  by_cases hk : 0 < (support b).card
  · have hd := noise_decay_bound hε hε' hk
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg (projectedCoefficient π (fun f => bitSign (A f)) b))
        (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    convert hm using 1 <;> ring
  · have hb : support b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbzero := (support_eq_empty_iff b).mp hb
    subst b
    simp [projectedCoefficient_eq, parityProjection_zero, hzero, support, zeroMask]

theorem folded_decoder_bound (ε : ℝ) (π : J → I)
    (i₀ : I) (table : HalfCube i₀ → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ table f))
      (fun g => bitSign (B g)) ^ 2 ≤ decoderSuccess π (foldedAnswer i₀ table) B := by
  exact decoder_four_epsilon_bias_sq ε π (foldedAnswer i₀ table) B hε hε'
    (foldedAnswer_zero_coefficient i₀ table)

theorem conditioned_validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (j₀ : {j : J // valid j = true})
    (table : HalfCube j₀ → Bool) :
    validDecoderSuccess valid π A (conditionedFoldedAnswer valid j₀ table) =
      decoderSuccess π A (conditionedFoldedAnswer valid j₀ table) := by
  unfold validDecoderSuccess decoderSuccess
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : coefficient (fun g => bitSign (conditionedFoldedAnswer valid j₀ table g)) b = 0
  · simp [hc]
  · have hb : ∀ y ∈ support b, valid y = true := by
      apply conditioned_coefficient_support valid (fun g => bitSign (foldedAnswer j₀ table g)) b
      exact hc
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [validAgreementProbability_eq valid π a b hb]

theorem conditioned_folded_decoder_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validDecoderSuccess valid π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  rw [conditioned_validDecoderSuccess]
  exact folded_decoder_bound ε π i₀ tableA
    (conditionedFoldedAnswer valid j₀ tableB) hε hε'

end MinUncutGames.Foundations.Hastad

end
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

theorem local_rejection_bound {n : Nat} (clause : Clause n) (alice : ClauseAnswer)
    (bob : Fin n → Bool) :
    acceptedSlots clause alice (honestAnswer clause bob) + clauseFailure clause bob ≤ 3 := by
  have hle := matchingSlots_le alice (honestAnswer clause bob)
  by_cases hb : clause.eval bob = true
  · simp only [clauseFailure, hb, ↓reduceIte, Nat.add_zero]
    unfold acceptedSlots
    split <;> omega
  · have hfailure : clauseFailure clause bob = 1 := by simp [clauseFailure, hb]
    rw [hfailure]
    by_cases ha : localSatisfies clause alice = true
    · have hne : alice ≠ honestAnswer clause bob := by
        intro h
        subst alice
        exact hb ((honest_satisfies clause bob).symm.trans ha)
      have hlt : matchingSlots alice (honestAnswer clause bob) ≠ 3 := by
        intro h
        exact hne ((matchingSlots_eq_three _ _).mp h)
      simp only [acceptedSlots, ha, ↓reduceIte]
      omega
    · simp [acceptedSlots, ha]

end MinUncutGames.Foundations.PCP

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

theorem evaluations_allIndices (F : Formula) (A : Fin F.«variables» → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun c => c.eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

theorem verifier_failureCount (F : Formula) (A : Fin F.«variables» → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end MinUncutGames.Foundations.PCP.NameCompaction

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

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem randomized_success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    {Seed : Type*} [Fintype Seed] (seedLaw : FiniteDistribution Seed)
    (strategies : Seed → Strategy Q₁ Q₂ A₁ A₂) :
    seedLaw.expectation (fun seed => G.success (strategies seed)) ≤ G.value := by
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * G.value := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (G.success_le_value _) (seedLaw.nonnegative seed)
    _ = G.value := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end Game

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

theorem table_success_eq_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    (responseTableLaw responses₁ responses₂).expectation G.success =
      G.stochasticSuccess responses₁ responses₂ := by
  classical
  unfold stochasticSuccess
  calc
    _ = (responseTableLaw responses₁ responses₂).expectation
        (fun strategy => G.questions.expectation
          (fun q => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_congr _ (G.success_eq_question_expectation)
    _ = G.questions.expectation (fun q =>
        (responseTableLaw responses₁ responses₂).expectation
          (fun strategy => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro q
      rw [responseTableLaw, FiniteDistribution.expectation_product]
      change (FiniteDistribution.table responses₁).expectation
        (fun answers₁ => (FiniteDistribution.table responses₂).expectation
          (fun answers₂ =>
            if G.accepts q.1 q.2 (answers₁ q.1) (answers₂ q.2) then 1 else 0)) = _
      calc
        _ = (FiniteDistribution.table responses₁).expectation
            (fun answers₁ => (responses₂ q.2).expectation
              (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then 1 else 0)) := by
          apply FiniteDistribution.expectation_congr
          intro answers₁
          exact FiniteDistribution.expectation_table_eval responses₂ q.2
            (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then (1 : ℝ) else 0)
        _ = _ := FiniteDistribution.expectation_table_eval responses₁ q.1
          (fun a => (responses₂ q.2).expectation
            (fun b => if G.accepts q.1 q.2 a b then (1 : ℝ) else 0))

variable [Nonempty A₁] [Nonempty A₂]

theorem stochasticSuccess_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    G.stochasticSuccess responses₁ responses₂ ≤ G.value := by
  classical
  rw [← G.table_success_eq_stochastic]
  exact G.randomized_success_le_value (responseTableLaw responses₁ responses₂) id

end Game
end
end MinUncutGames.Foundations.Games

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

def fourierResponse (fallback : I) (F : Cube I → Bool) : FiniteDistribution I where
  weight i := ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
    (supportResponse fallback s).weight i
  nonnegative i := Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) ((supportResponse fallback s).nonnegative i)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact sign_parseval F

theorem fourierResponse_expectation (fallback : I) (F : Cube I → Bool)
    (H : I → ℝ) :
    (fourierResponse fallback F).expectation H =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
        (supportResponse fallback s).expectation H := by
  unfold FiniteDistribution.expectation fourierResponse
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def validResponseAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  (fourierResponse fallbackI A).expectation fun i =>
    (fourierResponse fallbackJ B).expectation fun j =>
      if π j = i ∧ valid j = true then 1 else 0

theorem validDecoderSuccess_le_response (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (A : Cube I → Bool) (B : Cube J → Bool) :
    validDecoderSuccess valid π A B ≤
      validResponseAgreement valid π fallbackI fallbackJ A B := by
  unfold validDecoderSuccess validResponseAgreement
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackJ B]
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackI A]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact validAgreement_le_supportResponses valid π fallbackI fallbackJ a b

theorem conditioned_folded_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validResponseAgreement valid π i₀ j₀.val (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) :=
  (conditioned_folded_decoder_bound ε π valid i₀ tableA j₀ tableB hε hε').trans
    (validDecoderSuccess_le_response valid π i₀ j₀.val _ _)

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

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

omit [Nonempty I] [Nonempty J] in
theorem conditionedOracle_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) (default : J)
    (right : ConditionedOracle valid) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (right.answer g)) ^ 2 ≤
      validResponseAgreement valid π i₀ (right.fallback default)
        (foldedAnswer i₀ tableA) right.answer := by
  cases right with
  | empty noLegal =>
      simp only [ConditionedOracle.answer, ConditionedOracle.fallback,
        empty_conditioned_bias, pow_two, mul_zero]
      unfold validResponseAgreement
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  | stored j₀ table =>
      exact conditioned_folded_response_bound ε π valid i₀ tableA j₀ table hε hε'

theorem conditionedOracle_game_decoder_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * questions.expectation (questionBias ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ^ 2 ≤
      (projectionGame questions π valid).value := by
  let A := fun q => foldedAnswer (i₀ q) (tableA q)
  let B := fun q => (right q).answer
  let bias := questionBias ε π A B
  calc
    _ ≤ 4 * ε * questions.expectation (fun q => bias q ^ 2) :=
      mul_le_mul_of_nonneg_left (distribution_sq_expectation_le questions bias) (by linarith)
    _ = questions.expectation (fun q => 4 * ε * bias q ^ 2) := by
      unfold FiniteDistribution.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ questions.expectation (fun q =>
        validResponseAgreement (valid q.2) (π q.1 q.2) (i₀ q.1)
          ((right q.2).fallback default) (A q.1) (B q.2)) := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (questions.nonnegative q)
      exact conditionedOracle_response_bound ε (π q.1 q.2) (valid q.2)
        (i₀ q.1) (tableA q.1) default (right q.2) hε hε'
    _ = (projectionGame questions π valid).stochasticSuccess
        (fun q => fourierResponse (i₀ q) (A q))
        (fun q => fourierResponse ((right q).fallback default) (B q)) := by
      simp [Game.stochasticSuccess, projectionGame, validResponseAgreement]
    _ ≤ _ := Game.stochasticSuccess_le_value _ _ _

theorem conditionedOracle_acceptance_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε δ : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : (projectionGame questions π valid).value ≤ 4 * ε * δ ^ 2) :
    questions.expectation (questionAcceptance ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ≤
      (1 + δ) / 2 := by
  have hd := conditionedOracle_game_decoder_bound questions ε π valid i₀ tableA
    default right hε hε'
  have hpos : 0 < 4 * ε := by positivity
  have hs := le_of_mul_le_mul_left (hd.trans hvalue) hpos
  rw [questionAcceptance_eq]
  nlinarith

end MinUncutGames.Foundations.Hastad

end
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

def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

open scoped BigOperators

end MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

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

theorem verifier_probability_plus_failure (F : Formula) (hne : F.clauses ≠ [])
    (alice : AliceStrategy F) (bob : BobStrategy F) :
    (eventLaw F hne).probability (accepts F alice bob) +
      (failureCount F bob (allIndices F) : ℝ) / (3 * F.clauses.length : ℕ) ≤ 1 := by
  have hm : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
  have hlocal (c : Fin F.clauses.length) :
      (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) +
        (clauseFailure (clauseAt F c) bob : ℝ) ≤ 3 := by
    rw [sum_slot_accepts]
    exact_mod_cast local_rejection_bound (clauseAt F c) (alice c) bob
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset _)) => hlocal c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [eventLaw_probability, failureCount_allIndices]
  push_cast
  push_cast at hm
  rw [Fintype.sum_prod_type, ← add_div]
  apply (div_le_one hm).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

theorem base_value_le_of_clause_gap (F : Formula) (hne : F.clauses ≠ [])
    (δ : ℝ) (hgap : ∀ bob : BobStrategy F,
      δ * F.clauses.length ≤ (failureCount F bob (allIndices F) : ℝ)) :
    (baseGame F hne).value ≤ 1 - δ / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have hbase := base_success_le_verifier F hne strategy
  have hprob := verifier_probability_plus_failure F hne strategy.2 strategy.1
  have hm : (0 : ℝ) < F.clauses.length :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)
  have hg : δ / 3 ≤ (failureCount F strategy.1 (allIndices F) : ℝ) /
      (3 * F.clauses.length : ℕ) := by
    have hden : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
      exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
    apply (le_div_iff₀ hden).mpr
    calc
      δ / 3 * (3 * F.clauses.length : ℕ) = δ * F.clauses.length := by push_cast; ring
      _ ≤ _ := hgap strategy.1
  linarith

theorem projection_value_le_repetition (F : Formula) (hne : F.clauses ≠ [])
    (u : ℕ) :
    (sourceProjectionGame F hne u).value ≤ ((baseGame F hne).repetition u).value := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have h : (sourceProjectionGame F hne u).success strategy ≤
      ((baseGame F hne).repetition u).success strategy := by
    apply FiniteDistribution.probability_mono
    intro q hq
    have hlegal : pi F q.2 q.1 (strategy.2 q.2) = strategy.1 q.1 ∧
        validJ F q.2 (strategy.2 q.2) = true := by
      simpa only [Game.wins, sourceProjectionGame, projectionGame,
        decide_eq_true_eq] using hq
    apply (Game.repetition_accepts_iff _ _ _ _ _ _).mpr
    intro t
    exact projection_implies_coordinate_accepts F q.2 q.1
      (strategy.1 q.1) (strategy.2 q.2) hlegal.2 hlegal.1 t
  exact h.trans (Game.success_le_value _ strategy)

theorem source_acceptance_le_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
      testAcceptance ε (pi F c (sampledVariables F c s))
        (foldedAnswer (i₀ (sampledVariables F c s)) (tableA (sampledVariables F c s)))
        (right c).answer) ≤ (1 + δ) / 2 := by
  have h := conditionedOracle_acceptance_bound
    ((baseGame F hne).repetition u).questions ε δ (fun v c => pi F c v)
    (validJ F) i₀ tableA (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)
  rw [repeated_expectation_split] at h
  exact h

end MinUncutGames.Foundations.Hastad.SourceGame

namespace MinUncutGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MinUncutGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MinUncutGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end MinUncutGames.Foundations.Hastad.SourceSoundness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCompare
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFieldProfile

open _root_.Turing

def stageInTime {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length)
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (profile : Profile q) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells r 0), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile cells[r]), base⟩)
      (pairTime (fun i => base (.inl i)) cells[r]) := by
  let pair := cells[r]
  have copied := nonDestructiveCompareInTime (.inl pair.1) (.inl pair.2)
    (.inr 0 : Tape q) (.inr 1) (.inr 2) (by simp) (by simp) (by simp)
    (labelAt cells r 0) (labelAt cells r 1) (labelAt cells r 2) (labelAt cells r 3)
    (labelAt cells r 4) (some (labelAt cells r 5)) (some (labelAt cells r 6))
    (profileProgram cells)
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr])
    base (hwork 0) (hwork 1) (hwork 2) profile
  have stored : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
        else some (labelAt cells r 6), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile pair), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
          else some (labelAt cells r 6), normalState profile, base⟩ = _
      by_cases heq : base (.inl pair.1) = base (.inl pair.2)
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  dsimp only [pair] at h
  dsimp only [pairTime]
  omega

def prefixInTime {q : Nat} (cells : List (Fin q × Fin q))
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (r : Nat) (hr : r ≤ cells.length) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells 0 0), normalState initial, base⟩
      (some ⟨some (labelAt cells r 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells r), base⟩)
      (prefixTime (fun i => base (.inl i)) cells r) := by
  induction r with
  | zero =>
    exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  | succ r ih =>
    have hrl : r < cells.length := by omega
    let first := ih (by omega)
    let second := stageInTime cells r hrl base hwork
      (prefixProfile (fun i => base (.inl i)) initial cells r)
    let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
    rw [prefixProfile_succ _ _ _ _ hrl, prefixTime_succ _ _ _ hrl]
    exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def profileMachine (q : Nat) : FinTM2 where
  K := Tape q
  k₀ := .inr 0
  k₁ := .inr 0
  Γ _ := Bool
  Λ := Label (allPairs q)
  main := labelAt (allPairs q) 0 0
  σ := MachineCompare.State (Profile q)
  initialState := normalState (fun _ _ => false)
  m := profileProgram (allPairs q)

def profileInTime (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (((allPairs q).map (pairTime (fun i => base (.inl i)))).sum + 1) := by
  let cells := allPairs q
  have first := prefixInTime cells base hwork initial cells.length (Nat.le_refl _)
  have last : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells cells.length 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨some (labelAt cells cells.length 0),
          normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩ = _
      simp [TM2.step, profileProgram, labelAt, TM2.stepAux,
        prefixProfile, cells, foldProfile_allPairs]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simpa [prefixTime, cells, Nat.add_comm] using h

def profileInTime_bounded (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (L : Nat) (hL : ∀ i, (base (.inl i)).length ≤ L) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (q * q * (5 * L + 6) + 1) := by
  let run := profileInTime q base hwork initial
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  apply Nat.add_le_add_right
  simpa only [length_allPairs] using totalTime_le (fun i => base (.inl i)) L hL (allPairs q)

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseLookup
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceClauseLookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition SourceMachine

theorem lookupWithSplitTrace (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior clause]
      (some ⟨some .copyOut, ((), register), base⟩) =
      some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩ := by
  have hbits : formulaBits F = encodeWords [F.«variables», F.clauses.length] ++
      (encodeWords (prior.flatMap clauseWords) ++
        (encodeWords (clauseWords clause) ++ encodeWords (after.flatMap clauseWords))) := by
    simp only [formulaBits, formulaWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .formula .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch () register
  have htapes : Function.update base .work (base .formula ++ base .work) =
      scanTapes base prior.length indexSuffix (formulaBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hformula, hindex, hwork]
  rw [htapes, hformula] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.«variables» F.clauses.length prior clause indexSuffix
    (encodeWords (after.flatMap clauseWords))

def lookupWithSplitInTime (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) where
  steps := lookupSteps F prior clause
  evals_in_steps := lookupWithSplitTrace F prior clause after hsplit base indexSuffix
    hformula hindex hwork hscratch register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior clause after hsplit

def lookupInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  have hp : (F.clauses.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.clauses = F.clauses.take i.val ++ F.clauses[i.val] :: F.clauses.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.clauses.take i.val) F.clauses[i.val]
    (F.clauses.drop (i.val + 1)) hs base indexSuffix hformula
    (by simpa only [hp] using hindex) hwork hscratch register

end MinUncutGames.Foundations.Hastad.SourceClauseLookup

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

noncomputable def placedLookupInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((), register), base⟩
      (some ⟨some (.clearWork j), ((), none), lookupOutput j F i base suffix⟩)
      (4 * (formulaBits F).length + 10) := by
  have h := SourceClauseLookup.lookupInTime F i (base ∘ place j) suffix
    hformula hindex hwork hscratch register
  have lifted := liftExecutionInTime (TM2.step SourceClauseLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceClauseLookup.timePolynomial_eval, lookupOutput] using lifted

noncomputable def coordinateInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : base (.current j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((), register), base⟩
      (some ⟨some (nextLabel j), ((), none), coordinateOutput j F.clauses[i.val] base⟩)
      (6 * (formulaBits F).length + 4 * (base (.current j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.current j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy () register
  have copied_eq : Function.update base .index (base (.current j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hformula)
    (by simpa [copied, copiedTapes] using hcurrent)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded () none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) () none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords) := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_index]
  have hc : suffix.length ≤ (base (.current j)).length := by
    rw [hcurrent, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

noncomputable def prefixInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes F tuple base r⟩)
      (r * (6 * (formulaBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape u Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.current j) = base (.current j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hformula)
      (by rw [hc]; exact hcurrent j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (formulaBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j, stageTapes, before] using
          one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (6 * (formulaBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hformula hcurrent hsize
    hindex hwork hscratch hcopy u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

noncomputable def loadUnaryInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (formulaBits F).length hformula
    (by simpa only [List.append_nil] using hcurrent)
    (by
      intro j
      rw [hcurrent j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := clauses_length_le_input F
      omega)
    hindex hwork hscratch hcopy
  have he : 6 * (formulaBits F).length + 4 * (formulaBits F).length + 20 =
      10 * (formulaBits F).length + 20 := by omega
  simpa only [he] using run

end MinUncutGames.Foundations.Hastad.SourceContextLoad

namespace MinUncutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end MinUncutGames.Foundations.Hastad.SourceLocalEquation

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

theorem computed_profile_eq (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)) =
      contextNameProfile F c := by
  funext p q
  unfold reindexProfile nameWords
  rw [MachineFieldProfile.equalityProfile_encodeWord]
  simp only [names, Equiv.symm_apply_apply, contextNameProfile, Fin.ext_iff]

theorem prepared_signature_eq (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (⟨fun p => positiveAt (PCP.clauseAt F (c p.1)) p.2,
      reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)), s⟩ :
        Signature u) = ofContext F c s := by
  rw [computed_profile_eq]
  rfl

end MinUncutGames.Foundations.Hastad.SourceProfileBridge

namespace MinUncutGames.Foundations.Hastad.SourceSignaturePrepare

open _root_.Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open MinUncutGames.Foundations.Complexity

variable {u : ℕ} {Extra τ : Type}

variable [DecidableEq Extra]

def placedLabel : Option (ProfileLabel u) → Option (Label u)
  | none => some .commit
  | some l => some (.profile l)

def placedConfiguration (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (c : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  ⟨placedLabel c.l, (c.var, metadata), fill base c.stk⟩

theorem placed_stepAux (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (q : TM2.Stmt (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (state : ProfileState u) (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) :
    TM2.stepAux (placedStatement q) (state, metadata) (fill base localTapes) =
      placedConfiguration base metadata (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using
      ih (f state (localTapes k).head?) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state (localTapes k).head?) _
  | load f next ih =>
    simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

theorem placed_step (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (a b : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (h : (MachineFieldProfile.profileMachine (Width u)).step a = some b) :
    TM2.step program (placedConfiguration base metadata a) =
      some (placedConfiguration base metadata b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some label =>
    change some (TM2.stepAux
      (MachineFieldProfile.profileProgram (MachineFieldProfile.allPairs (Width u)) label)
      state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (placedStatement _) (state, metadata) (fill base tapes)) = _
    rw [placed_stepAux]

theorem stepAux_commit (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    TM2.stepAux commitStatement (work, (initial, ambient)) tapes =
      ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩ := by
  change TM2.stepAux (MachineControl.statement id (signStateEquiv u τ)
    (SourceSignLoad.statement polarityField none))
      ((signStateEquiv u τ)
        ({initial with sameName := reindexProfile u work.1}, (work, ambient))) tapes = _
  rw [MachineControl.stepAux_simulation, SourceSignLoad.stepAux_statement]
  rfl

def profileInTime (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (ambient : τ) (L : ℕ)
    (hL : ∀ i, (tapes (place (.inl i))).length ≤ L) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨some .commit,
        (MachineFieldProfile.normalState
          (MachineFieldProfile.equalityProfile (fun i => tapes (place (.inl i)))),
          (initial, ambient)), tapes⟩)
      (Width u * Width u * (5 * L + 6) + 1) := by
  let run := MachineFieldProfile.profileInTime_bounded (Width u) (tapes ∘ place)
    hwork initialProfile L hL
  have lifted := MachineComposition.liftExecutionInTime _ _
    (placedConfiguration tapes (initial, ambient))
    (placed_step tapes (initial, ambient)) run
  simpa only [placedConfiguration, placedLabel, fill_self, Function.comp_apply] using lifted

def commitInTime (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .commit, (work, (initial, ambient)), tapes⟩
      (some ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step program ⟨some .commit, (work, (initial, ambient)), tapes⟩ = _
    change some (TM2.stepAux commitStatement (work, (initial, ambient)) tapes) = _
    rw [stepAux_commit]
  steps_le_m := Nat.le_refl _

def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (hnames : ∀ i, tapes (place (.inl i)) = nameWords F c i)
    (suffix : Position u → List Bool)
    (hsigns : ∀ p, tapes (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++ suffix p)
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), tapes⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  have hfields : (fun i => tapes (place (.inl i))) = nameWords F c := funext hnames
  have hsign : SourceSignLoad.readSigns polarityField tapes =
      fun p => positiveAt (clauseAt F (c p.1)) p.2 :=
    SourceSignLoad.readSigns_of_unary polarityField tapes _ suffix hsigns
  have hL : ∀ i, (tapes (place (.inl i))).length ≤ (formulaBits F).length := by
    intro i
    rw [hnames]
    exact nameWords_length_le_input F c i
  have first := profileInTime tapes hwork initialProfile initial ambient
    (formulaBits F).length hL
  rw [hfields] at first
  have last := commitInTime
    (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)))
    initial ambient tapes
  dsimp only [MachineFieldProfile.normalState] at last
  rw [hsign, hselected, prepared_signature_eq F c selected] at last
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  omega

omit [DecidableEq Extra] in

theorem loaded_sign_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (p : Position u) :
    SourceContextLoad.stageTapes F c base u (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++
        base (polarityField p) := by
  have ho := SourceContextLoad.output_polarity F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (polarityField p) =
    encodeWord (if F.clauses[(c p.1).val][(slotEncoding.code p.2).val].positive then 1 else 0) ++
      base (polarityField p) at ho
  rw [ho]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

def loadedPrepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)),
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), SourceContextLoad.stageTapes F c base u⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  apply prepareInTime F c selected (SourceContextLoad.stageTapes F c base u) _
    (loaded_name_field F c base hbase) (fun p => base (polarityField p))
    (loaded_sign_field F c base) initialProfile initial hselected ambient
  intro w
  have hc := SourceContextLoad.stageTapes_clean F c base u hindex hwork
  have hs : SourceContextLoad.stageTapes F c base u .scratch = [] := by
    rw [SourceContextLoad.stageTapes_frame F c base u .scratch
      (by simp) (by simp) (by intros; simp)]
    exact hscratch
  obtain ⟨w, hw⟩ := w
  have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact hc.1
  · exact hc.2
  · exact hs

end MinUncutGames.Foundations.Hastad.SourceSignaturePrepare

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextPrepare
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceContextPrepare

open _root_.Turing MinUncutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

def preparationConfiguration (loaderState : LoadState)
    (c : TM2.Cfg (fun _ : Arena u Extra => Bool) (SourceSignaturePrepare.Label u) (PrepareState u τ)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  MachineControl.configuration id (stateSwap u τ)
    (MachineStateFrame.configuration Sum.inr none loaderState c)

variable [DecidableEq Extra]

theorem preparation_step (loaderState : LoadState)
    (a b : TM2.Cfg (fun _ : Arena u Extra => Bool)
      (SourceSignaturePrepare.Label u) (PrepareState u τ))
    (h : TM2.step SourceSignaturePrepare.program a = some b) :
    TM2.step program (preparationConfiguration loaderState a) =
      some (preparationConfiguration loaderState b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (SourceSignaturePrepare.program l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (stateSwap u τ)
        (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l)))
      ((stateSwap u τ) (state, loaderState)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

noncomputable def loadInTime (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := SourceContextLoad.loadUnaryInTime F c base hformula hcurrent
    hindex hwork hscratch hcopy
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (prepareEntry u)))
    (MachineFieldProfile.normalState initialProfile, (initial, ambient))
    SourceContextLoad.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, initialState] using lifted

def signatureInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
        (5 * (formulaBits F).length + 6) + 2) := by
  have run := SourceSignaturePrepare.loadedPrepareInTime F c selected base
    hindex hwork hscratch hfields initialProfile initial hselected ambient
  have lifted := MachineComposition.liftExecutionInTime
    (TM2.step SourceSignaturePrepare.program) (TM2.step program)
    (preparationConfiguration ((), none)) (preparation_step ((), none)) run
  simpa only [preparationConfiguration, MachineControl.configuration, MachineStateFrame.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.configuration,
    MachineSubroutine.label, Option.map_some, Option.map_none, id_eq, stateSwap,
    Equiv.prodComm_apply, Prod.swap, initialState, finalState, prepareEntry] using lifted

noncomputable def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  have firstRun := loadInTime F c base hformula hcurrent hindex hwork hscratch hcopy
    initialProfile initial ambient
  have secondRun := signatureInTime F c selected base hindex hwork hscratch hfields
    initialProfile initial hselected ambient
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun

end MinUncutGames.Foundations.Hastad.SourceContextPrepare

end
section

namespace MinUncutGames.Foundations.Hastad.SourceLoopInit

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def headerInTime (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F) (hwork : base .work = [])
    (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), register), base⟩
      (some ⟨some (labelAt 0), ((), none), headerOutput F base⟩)
      (3 * (formulaBits F).length + 6) := by
  have copying := MachineCopy.copyInTime .formula .work .scratch
    (by simp) (by simp) (by simp) false .inputCopyOut .inputCopyBack (some (readStart 0))
    program rfl rfl base hscratch () register
  have hc : Function.update base .work (base .formula ++ base .work) = copiedInput base := by
    simp [copiedInput, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime .work headerDestination readStart readLoop
    (some .clearWork) program (copiedInput base) 0 [F.«variables», F.clauses.length]
    (encodeWords (F.clauses.flatMap clauseWords))
    (by intro r hr; simp [headerDestination, variableHeader, clauseHeader]; split <;> simp)
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart (u := u) (Extra := Extra) r (by simpa using hr))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop (u := u) (Extra := Extra) r (by simpa using hr))
    (by simpa using (atReadDone (u := u) (Extra := Extra)))
    (by simp [copiedInput, hformula, formulaBits, formulaWords, encodeWords, List.append_assoc]) () none
  have draining := MachineDrain.drainInTime .work .clearWork (some (labelAt 0))
    program rfl (readOutput F base) () none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readOutput] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readOutput_work, hformula]
    have he : (formulaBits F).length = F.«variables» + F.clauses.length + 2 +
        (encodeWords (F.clauses.flatMap clauseWords)).length := by
      simp [formulaBits, formulaWords, encodeWords, Nat.add_assoc]
      omega
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega

def digitInTime (j : Fin u) (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : base (.current j) = []) (hremaining : base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩)
      (2 * m + 6) := by
  let seeded := Function.update base (.current j) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (.digitCopyOut j), ((), none), seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.seed j), ((), none), base⟩ = _
    simp [program, TM2.step, TM2.stepAux, seeded, hcurrent, encodeWord]
  have copying := MachineCopy.copyInTime clauseHeader (.remaining j) .copyScratch
    (by simp [clauseHeader]) (by simp [clauseHeader]) (by simp)
    false (.digitCopyOut j) (.digitCopyBack j) (some (.trim j)) program rfl rfl seeded
    (by simpa [seeded] using hscratch) () none
  let copied := Function.update seeded (.remaining j) (encodeWord m)
  have he : Function.update seeded (.remaining j)
      (seeded clauseHeader ++ seeded (.remaining j)) = copied := by
    have hcount' : base (.extra (.inl .clauseCount)) = encodeWord m := hcount
    simp [copied, seeded, clauseHeader, hremaining, hcount']
  rw [he] at copying
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.trim j), ((), none), copied⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.trim j), ((), none), copied⟩ = _
    have hn : m = (m - 1) + 1 := by omega
    have htail : (encodeWord m).tail = encodeWord (m - 1) := by
      conv_lhs => rw [hn]
      simp [encodeWord, List.replicate_succ]
    simp [program, TM2.step, TM2.stepAux, copied, seeded, digitOutput, htail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copying) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded clauseHeader = encodeWord m := by simpa [seeded, clauseHeader] using hcount
  rw [hs, encodeWord_length]
  omega

def prefixInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes m base r⟩)
      (r * (2 * m + 6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes m base r
    have one := digitInTime j m hm before
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]; exact hcount)
      (by simp [before, stageTapes_current, j, hcurrent])
      (by simp [before, stageTapes_remaining, j, hremaining])
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp) (by simp)]; exact hscratch)
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes m base (r + 1)⟩)
        (2 * m + 6) := by
      simpa only [labelAt, dite_eq_left hru, j, stageTapes, before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

def digitsInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes m base u⟩)
      (u * (2 * m + 6) + 1) := by
  have initialRun := prefixInTime m hm base hcount hcurrent hremaining hscratch u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes m base u⟩
      (some ⟨none, ((), none), stageTapes m base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes m base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initialRun doneRun

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length)
    (base : Tape u Extra → List Bool) (hformula : base .formula = formulaBits F)
    (hwork : base .work = []) (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hclauseHeader : base clauseHeader = [])
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), none), base⟩
      (some ⟨none, ((), none), outputTapes F base⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have firstRun := headerInTime F base hformula hwork hscratch none
  have hcount : headerOutput F base clauseHeader = encodeWord F.clauses.length := by
    simp [headerOutput, hclauseHeader]
  have secondRun := digitsInTime F.clauses.length hm (headerOutput F base) hcount
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcurrent j)
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hremaining j)
    (by rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcopy)
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hL := SourceContextLoad.clauses_length_le_input F
  have hb : u * (2 * F.clauses.length + 6) ≤ u * (2 * (formulaBits F).length + 6) :=
    Nat.mul_le_mul_left u (by omega)
  have he : (2 * u + 3) * (formulaBits F).length + 6 * u + 7 =
      u * (2 * (formulaBits F).length + 6) + 3 * (formulaBits F).length + 7 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [he]
  omega

end MinUncutGames.Foundations.Hastad.SourceLoopInit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegisterEmit
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegisterEmit

open _root_.Turing
open MinUncutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem registerEmitTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 5]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩ := by
  have copied := MachineCopy.copyTrace source destination scratch sourceDestination
    sourceScratch destinationScratch false firstLabel secondLabel (some emitLabel)
    program atFirst atSecond base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at copied
  rw [show 2 * n + 5 = 1 + 2 * (n + 1 + 1) by omega,
    Function.iterate_add_apply, copied, Function.iterate_one]
  change TM2.step program
    ⟨some emitLabel, (ambient, none),
      Function.update base destination (encodeWord n ++ base destination)⟩ = _
  rw [emitStep destination offset emitLabel exit program atEmit]
  simp only [Function.update_self, Function.update_idem]
  rw [← List.append_assoc, prefix_encodeWord]

end MinUncutGames.Foundations.Complexity.MachineRegisterEmit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_AddressArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

theorem rankTrace (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      MachineHorner.steps radix (reverseDigits digits) width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩ := by
  have h := MachineHorner.hornerTrace (reverseSlots slots) labels exit p atLabels base radix
    (reverseDigits digits) operandRadix
    (fun i => by simpa only [reverseSlots_digit, reverseDigits_apply] using operandDigits i.rev)
    (clean_reverseSlots slots base clean) ambient register
  rw [horner_reverse_eq_rank] at h
  simpa only [MachineHorner.resultTapes, reverseSlots_control] using h

def rankInPolynomialTime (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool)
    (magnitude : Nat) (radixBound : radix ≤ magnitude) (digitBound : ∀ i, digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      ((MachineHorner.timePolynomial width).eval magnitude) where
  steps := MachineHorner.steps radix (reverseDigits digits) width
  evals_in_steps := rankTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient register
  steps_le_m := MachineHorner.steps_le_timePolynomial radix (reverseDigits digits) width magnitude
    radixBound (fun i hi => by simpa only [reverseDigits, dite_eq_left hi] using digitBound (Fin.rev ⟨i, hi⟩))

def variableRankInTime (F : Formula) (u : Nat) (v : VariableContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.«variables»)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (v i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((variableEncoding F u).code v).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.«variables» (fun i => (v i).val)
    operandRadix operandDigits clean ambient register F.«variables» (Nat.le_refl _) (fun i => (v i).isLt.le)
  simpa only [rank, ← variable_rank F u v] using h

def clauseRankInTime (F : Formula) (u : Nat) (c : ClauseContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.clauses.length)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (c i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.clauses.length (fun i => (c i).val)
    operandRadix operandDigits clean ambient register F.clauses.length (Nat.le_refl _) (fun i => (c i).isLt.le)
  simpa only [rank, ← clause_rank F u c] using h

end MinUncutGames.Foundations.Hastad.SourceRankPhase

namespace MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open MinUncutGames.Reduction.CloneGap

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [MinUncutGames.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

end MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_EquationEmit
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceEquationEmit

open _root_.Turing Complexity
open SourceAddressDescriptors
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]

end MinUncutGames.Foundations.Hastad.SourceEquationEmit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DescriptorEmission
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceTestAppend

open _root_.Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

def equationBits (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : List Bool :=
  encodeWords (words values (localEquation u D state))

def steps (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : Nat :=
  SourceEquationEmit.steps values (localEquation u D state) + 1 +
    (equationBits u D values state).length + 1

variable {K Λ : Type} [DecidableEq K]

theorem emitTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨some (labels .append), (state, none),
        prefixTapes layout.temporary base (words values (localEquation u D state))⟩ := by
  have select : TM2.step p
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩ =
      some ⟨some (bodyLabel u D labels state .seed), (state, register), base⟩ := by
    change some (TM2.stepAux (p (labels (.test (.inl ())))) (state, register) base) = _
    rw [atLabels]
    rfl
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (TM2.step p ⟨some (labels (.test (.inl ()))), (state, register), base⟩) = _
  rw [select]
  exact SourceEquationEmit.equationTrace layout.sources layout.temporary layout.scratch
    layout.sourceTemporary layout.sourceScratch layout.temporaryScratch (localEquation u D state)
    (bodyLabel u D labels state) (some (labels .append)) p
    (fun label => atLabels (.test (SourceTestEmit.bodyLabel u D state label)))
    base values sourceWords scratchEmpty state register

theorem appendTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps u D values state]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩ := by
  let emitted := prefixTapes layout.temporary base (words values (localEquation u D state))
  have hemit := emitTrace u D layout labels exit p atLabels state base values sourceWords
    scratchEmpty register
  have htemp : emitted layout.temporary = equationBits u D values state := by
    simp [emitted, prefixTapes, equationBits, temporaryEmpty]
  have hacc : emitted layout.accumulator = base layout.accumulator :=
    prefixTapes_other _ _ _ _ (Ne.symm layout.temporaryAccumulator)
  have hfinal : Reduction.MachineTransfer.tapesAt layout.temporary layout.accumulator emitted []
      ((equationBits u D values state).reverse ++ base layout.accumulator) =
      resultTapes layout base (equationBits u D values state) := by
    funext k
    by_cases hka : k = layout.accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, resultTapes]
    · by_cases hkt : k = layout.temporary
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, layout.temporaryAccumulator,
          temporaryEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, emitted, prefixTapes, hka, hkt]
  have transferred := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := LocalInput u D)
    layout.temporary layout.accumulator layout.temporaryAccumulator id false (labels .append)
    exit p (by simpa only [statement] using atLabels .append) emitted state none
  change (MachineComposition.advance (TM2.step p))^[(emitted layout.temporary).length + 1]
    (some ⟨some (labels .append), (state, none), emitted⟩) = _ at transferred
  rw [htemp, hacc] at transferred
  simp only [List.map_id] at transferred
  rw [hfinal] at transferred
  rw [show steps u D values state = ((equationBits u D values state).length + 1) +
      (SourceEquationEmit.steps values (localEquation u D state) + 1) by unfold steps; omega,
    Function.iterate_add_apply, hemit]
  exact transferred

def sourceAppendInTime (F : Formula) (u D : Nat) (occurrence : SourceIndex F u D)
    (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2) side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))),
        ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), register), base⟩
      (some ⟨exit, ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), none),
        resultTapes layout base (encodeWords
          (MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D occurrence)))⟩)
      (9 * nBits F u + 20) where
  steps := steps u D
    (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
    (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2)
  evals_in_steps := by
    rw [sourceEquation_words]
    exact appendTrace u D layout labels exit p atLabels
      (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2) base
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
      sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := by
    have he := equation_emit_steps_le F u occurrence.1.1
      (sampledVariables F occurrence.1.1 occurrence.1.2)
      (localEquation u D (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2))
    have hl := MinUncutGames.Reduction.SourceEncoding.equationBits_length_le
      (sourceEquation F u D occurrence)
    rw [sourceEquation_words] at hl
    unfold steps SourceEquationEmit.steps equationBits
    dsimp only [localEquation] at he hl ⊢
    omega

end MinUncutGames.Foundations.Hastad.SourceTestAppend

namespace MinUncutGames.Foundations.Hastad.SourceQueryLoop

open _root_.Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

variable {K Λ : Type} [DecidableEq K]

def prefixBits (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → List Bool
  | 0 => []
  | n + 1 => prefixBits u D queries values signature n ++
      SourceTestAppend.equationBits u D values (signature, queries n)

def prefixSteps (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps u D queries values signature n +
      (SourceTestAppend.steps u D values (signature, queries n) + 1)

theorem prefixTrace (u D n : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (r : Nat) (hr : r ≤ n) :
    ∃ lastQuery : Query u D,
      (MachineComposition.advance (TM2.step p))^[prefixSteps u D queries values signature r]
        (some ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩) =
        some ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature r)⟩ := by
  induction r with
  | zero =>
    refine ⟨initialQuery, ?_⟩
    simp [prefixSteps, prefixBits, SourceTestAppend.resultTapes]
  | succ r ih =>
    obtain ⟨lastQuery, hprevious⟩ := ih (by omega)
    have hlt : r < n := by omega
    let current := SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r)
    have hselect : TM2.step p
        ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none), current⟩ =
        some ⟨some (labels (.emit ⟨r, hlt⟩ (.test (.inl ())))),
          ((signature, queries r), none), current⟩ := by
      change some (TM2.stepAux (p (labels (.load ⟨r, by omega⟩))) _ _) = _
      rw [atLabels]
      simp only [statement, hlt, ↓reduceDIte, TM2.stepAux]
    have hbody := SourceTestAppend.appendTrace u D layout
      (fun l => labels (.emit ⟨r, hlt⟩ l))
      (some (labels (.load ⟨r + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨r, hlt⟩ l)) (signature, queries r) current values
      (fun side => (SourceTestAppend.resultTapes_source layout base _ side).trans
        (sourceWords side))
      ((SourceTestAppend.resultTapes_scratch layout base _).trans scratchEmpty)
      ((SourceTestAppend.resultTapes_temporary layout base _).trans temporaryEmpty) none
    refine ⟨queries r, ?_⟩
    rw [show prefixSteps u D queries values signature (r + 1) =
      (SourceTestAppend.steps u D values (signature, queries r) + 1) +
        prefixSteps u D queries values signature r by rw [prefixSteps]; omega,
      Function.iterate_add_apply, hprevious, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[
      SourceTestAppend.steps u D values (signature, queries r)]
      (TM2.step p ⟨some (labels (.load ⟨r, by omega⟩)),
        ((signature, lastQuery), none), current⟩) = _
    rw [hselect, hbody]
    rw [show current = SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r) from rfl, resultTapes_append]
    rfl

theorem prefixSteps_le (u D n B : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u)
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    prefixSteps u D queries values signature n ≤ n * (B + 1) := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hp := ih (fun i hi => hbound i (by omega))
    have hb := hbound n (by omega)
    rw [prefixSteps, Nat.succ_mul]
    omega

theorem loopInTime (u D n B : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    ∃ lastQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩
        (some ⟨exit, ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature n)⟩)
        (n * (B + 1) + 1)) := by
  obtain ⟨lastQuery, hprefix⟩ := prefixTrace u D n queries layout labels exit p atLabels
    signature initialQuery base values sourceWords scratchEmpty temporaryEmpty n (Nat.le_refl n)
  refine ⟨lastQuery, ⟨{
    steps := prefixSteps u D queries values signature n + 1
    evals_in_steps := ?_
    steps_le_m := ?_ }⟩⟩
  · change (MachineComposition.advance (TM2.step p))^[
      prefixSteps u D queries values signature n + 1] _ = _
    rw [Function.iterate_succ_apply', hprefix]
    rw [MachineComposition.advance_some]
    change some (TM2.stepAux (p (labels (.load ⟨n, by omega⟩))) _ _) = _
    rw [atLabels]
    simp only [statement, Nat.lt_irrefl, ↓reduceDIte]
    cases exit <;> rfl
  · exact Nat.add_le_add_right (prefixSteps_le u D n B queries values signature hbound) 1

end MinUncutGames.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderCounts
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceHeaderCounts

open _root_.Turing Complexity
open MachineComposition

noncomputable section

variable {u D : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem trace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps u D n m]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := Function.update base (control slots .leftBlockSize) (encodeWord (leftValue u n))
  let t2 := Function.update t1 (control slots .rightTemporary) (encodeWord (rightValue u m))
  let t3 := Function.update t2 (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m))
  let t4 := Function.update t3 (control slots .dummyIndex) (encodeWord (leftValue u n))
  let t5 := Function.update (Function.update t4 (control slots .rightTemporary) [false])
    (control slots .dummyIndex) (encodeWord (dummyValue u n m))
  let t6 := Function.update t5 (control slots .rightTemporary) []
  let t7 := Function.update t6 (control slots .bitCount) (encodeWord (dummyValue u n m))
  have h1 := evalPhaseTrace slots labels exit program atLabels .left base n hn clean.left
    clean.work ambient register
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .left) n]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .right)), ((ambient, ()), none), _⟩ at h1
  simp only [polynomial_left_eval] at h1
  have cw1 : WorkClean slots t1 := clean.work.update_output .left _
  have h2 := evalPhaseTrace slots labels exit program atLabels .right t1 m
    (by simpa [t1, inputControl] using hm)
    (by simpa [t1, outputControl] using clean.right) cw1 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .right) m]
      (some ⟨some (labels (evalStart .right)), ((ambient, ()), none), t1⟩) =
      some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), _⟩ at h2
  simp only [polynomial_right_eval] at h2
  have cw2 : WorkClean slots t2 := cw1.update_output .right _
  have h3 := evalPhaseTrace slots labels exit program atLabels .occurrences t2 m
    (by simpa [t2, t1, inputControl] using hm)
    (by simpa [t2, t1, outputControl] using clean.occurrences) cw2 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .occurrences) m]
      (some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), t2⟩) =
      some ⟨some (labels .copyLeftOut), ((ambient, ()), none), _⟩ at h3
  simp only [polynomial_occurrences_eval] at h3
  have cw3 : WorkClean slots t3 := cw2.update_output .occurrences _
  have copyingLeft := MachineCopy.copyTrace (control slots .leftBlockSize)
    (control slots .dummyIndex) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyLeftOut) (labels .copyLeftBack)
    (some (labels .addRight)) program (atLabels .copyLeftOut) (atLabels .copyLeftBack)
    t3 cw3.scratch (ambient, ()) none
  have hleft : t3 (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
    simp [t3, t2, t1]
  have hdummy : t3 (control slots .dummyIndex) = [] := by
    simpa [t3, t2, t1] using clean.dummy
  rw [hleft, hdummy, List.append_nil, encodeWord_length] at copyingLeft
  have adding := MachineUnaryAddAt.addFromTapes (control slots .rightTemporary)
    (control slots .dummyIndex) (by simp) (labels .addRight) (some (labels .clearTemporary))
    program (atLabels .addRight) t4 (rightValue u m) (leftValue u n) [] []
    (by simp [t4, t3, t2]) (by simp [t4]) (ambient, ()) none
  have ha : MachineUnaryAddAt.unaryTapes (control slots .rightTemporary)
      (control slots .dummyIndex) t4 0 (rightValue u m + leftValue u n) [] [] = t5 := by
    simp [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt, t5,
      encodeWord, dummyValue, Nat.add_comm]
  rw [ha] at adding
  have clearing : (advance (TM2.step program))^[1]
      (some ⟨some (labels .clearTemporary), ((ambient, ()), none), t5⟩) =
      some ⟨some (labels .copyDummyOut), ((ambient, ()), none), t6⟩ := by
    change some (TM2.stepAux (program (labels .clearTemporary)) _ _) = _
    rw [atLabels]
    simp [statement, TM2.stepAux, t6, t5]
  have copyingDummy := MachineCopy.copyTrace (control slots .dummyIndex)
    (control slots .bitCount) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyDummyOut) (labels .copyDummyBack)
    (some (labels .incrementBits)) program (atLabels .copyDummyOut) (atLabels .copyDummyBack)
    t6 (by simpa [t6, t5, t4] using cw3.scratch) (ambient, ()) none
  have hdi : t6 (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
    simp [t6, t5]
  have hbi : t6 (control slots .bitCount) = [] := by
    simpa [t6, t5, t4, t3, t2, t1] using clean.bits
  rw [hdi, hbi, List.append_nil, encodeWord_length] at copyingDummy
  have increment : (advance (TM2.step program))^[1]
      (some ⟨some (labels .incrementBits), ((ambient, ()), none), t7⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m))⟩ := by
    change some (TM2.stepAux (program (labels .incrementBits)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
      t7, bitValue, encodeWord, List.replicate_succ]
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) copyingLeft) adding) clearing)
      copyingDummy) increment
  have htime :
      Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
        Eval.steps (polynomial u D .occurrences) m + 2 * (leftValue u n + 1 + 1) +
        (rightValue u m + 1) + 1 + 2 * (dummyValue u n m + 1 + 1) + 1 =
      steps u D n m := by unfold steps; omega
  rw [htime] at total
  have frame : Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m)) =
      resultTapes slots base n m := by
    funext k
    by_cases hr : k = control slots .rightTemporary
    · subst k
      simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, clean.right]
    · simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, Function.update_apply, hr]
      split_ifs <;> rfl
  rw [frame] at total
  exact total

def inTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps u D n m) where
  steps := steps u D n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

end

end MinUncutGames.Foundations.Hastad.SourceHeaderCounts

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorModel

open _root_.Turing Complexity SourceRuntimeModel

theorem mem_coefficientKeys (u D : Nat) (i : SourceHeaderCounts.Coefficients u D) :
    i ∈ coefficientKeys u D := by
  cases i with
  | inl i => simp [coefficientKeys]
  | inr i => cases i <;> simp [coefficientKeys]

theorem mem_workKeys (u D : Nat) (i : BodyWork (Extra u D)) : i ∈ workKeys u D := by
  cases i
  case extra e =>
    cases e with
    | inl i =>
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, mem_coefficientKeys u D i, rfl⟩))
    | inr i => cases i; simp [workKeys]
  all_goals simp [workKeys]

theorem mem_allTapes (u D : Nat) (k : Tape u D) : k ∈ allTapes u D := by
  cases k with
  | formula => simp [allTapes]
  | index => simp [allTapes]
  | work => simp [allTapes]
  | scratch => simp [allTapes]
  | copyScratch => simp [allTapes]
  | current i => simp [allTapes]
  | remaining i => simp [allTapes]
  | field i j => simp [allTapes]
  | extra e =>
    cases e with
    | inl h => cases h <;> simp [allTapes, variableHeader, clauseHeader,
        SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader]
    | inr w =>
      have h : workTape (u := u) w ∈ (workKeys u D).map (workTape (u := u)) :=
        List.mem_map.mpr ⟨w, mem_workKeys u D w, rfl⟩
      simp only [allTapes, List.mem_append]
      tauto

theorem mem_clearKeys (u D : Nat) (k : Tape u D) :
    k ∈ clearKeys u D ↔ k ≠ accumulatorTape u D ∧ k ≠ outputTape u D := by
  classical
  simp [clearKeys, mem_allTapes]

end MinUncutGames.Foundations.Hastad.SourceGeneratorModel

end

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
theorem initial_arithmetic (hD : 0 < D) :
    arithmeticStateEquiv u D ((((), ()), none), initialArithmeticMetadata u D hD) =
      SourceGeneratorModel.initialState u D hD := rfl

theorem initial_loader (hD : 0 < D) :
    (((), none), (SourceGeneratorModel.initialState u D hD).2) =
      SourceGeneratorModel.initialState u D hD := rfl

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD,
        initializedTapes F⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have run := SourceLoopInit.initializeInTime F hm (initialTapes (u := u) (D := D) F)
    (by simp [initialTapes]) (by simp [initialTapes]) (by simp [initialTapes])
    (by simp [initialTapes]) (by simp [initialTapes, SourceLoopInit.clauseHeader])
    (by intro j; simp [initialTapes]) (by intro j; simp [initialTapes])
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (arithmeticEntry u D)))
    (SourceGeneratorModel.initialState u D hD).2 SourceLoopInit.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, initial_loader,
    initializedTapes] using lifted

def arithmeticInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step arithmeticProgram)
      ⟨some (arithmeticEntry u D), (((), ()), none), initializedTapes F⟩
      (some ⟨none, (((), ()), none), outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have countRun := SourceHeaderCounts.inTime (headerSlots u D) Sum.inl (some (.inr false))
    arithmeticProgram (fun _ => rfl) (initializedTapes F) F.«variables» F.clauses.length
    (initialized_variableHeader F) (initialized_clauseHeader F) (initialized_clean F) () none
  have appendRun := SourceHeaderAccumulate.inTime (headerLayout u D) Sum.inr none
    arithmeticProgram (fun _ => rfl) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.«variables» F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)
    (SourceHeaderCounts.result_bits (headerSlots u D) (initializedTapes F) _ _)
    (SourceHeaderCounts.result_occurrences (headerSlots u D) (initializedTapes F) _ _) ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step arithmeticProgram) _ _ _ _ _
    countRun appendRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  have ht := joined.steps_le_m
  omega

def arithmeticPlacedInTime (F : Target.Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD, initializedTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have lifted := liftExecutionInTime (TM2.step arithmeticProgram) (TM2.step program)
    (arithmeticConfiguration (initialArithmeticMetadata u D hD))
    (arithmetic_step (initialArithmeticMetadata u D hD)) (arithmeticInTime F)
  simpa only [arithmeticConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some, Option.map_none,
    id_eq, initial_arithmetic] using lifted

def phasesInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (phaseBound F u D) := by
  have run := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (initializeInTime (u := u) F hm hD) (arithmeticPlacedInTime (u := u) F hD)
  simpa only [phaseBound, Nat.add_comm] using run

def startupInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      (phaseBound F u D) := by
  have run := phasesInTime (u := u) F hm hD
  simpa only [output_eq_ready F hm] using run

def startupInPolynomialTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      ((timePolynomial u D).eval (formulaBits F).length) := by
  have run := startupInTime (u := u) F hm hD
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  exact Nat.le_trans run.steps_le_m (phaseBound_le_polynomial F u D)

end

end MinUncutGames.Foundations.Hastad.SourceStartup

end
section
namespace MinUncutGames.Foundations.Hastad.SourceBasePhase

open _root_.Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open MinUncutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .seed => pushWord (slots (.inr 0)) (encodeWord coefficient).reverse
      (.goto fun _ => labels (.horner .start))
  | .horner label => MachineHorner.statement slots (fun l => labels (.horner l))
      (some (labels .clear)) label
  | .clear => MachineHorner.drainLoop (slots (.inr 0)) (labels .clear) exit

def program (slots : Layout ↪ K) (coefficient : Nat) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (MachineHorner.State σ) :=
  statement slots coefficient id none

def coefficientTapes (slots : Layout ↪ K) (base : K → List Bool) (coefficient : Nat) : K → List Bool :=
  Function.update base (slots (.inr 0)) (encodeWord coefficient)

theorem affineTrace (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps coefficient rank offset]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩ := by
  have hc (i : Fin 6) : slots (.inl i) ≠ slots (.inr 0) := slots.injective.ne (by simp)
  have hd : slots (.inr 1) ≠ slots (.inr 0) := slots.injective.ne (by decide)
  let seeded := coefficientTapes slots base coefficient
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (.horner .start)), ((ambient, ()), register), seeded⟩ := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      coefficientEmpty, List.append_nil, seeded, coefficientTapes]
  have hradix : seeded (slots (.inl 0)) = encodeWord rank := by
    simp [seeded, coefficientTapes, hc, rankWord]
  have hdigits : ∀ i : Fin 2, seeded (slots (.inr i)) = encodeWord (digits coefficient offset i.val) := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp [seeded, coefficientTapes, digits]
    · simp [seeded, coefficientTapes, digits, hd, offsetWord]
  have hclean : MachineHorner.Clean slots seeded := {
    accA := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 1)] using clean.accA
    accB := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 2)] using clean.accB
    counter := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 4)] using clean.counter
    scratch := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 5)] using clean.scratch
  }
  have hhorner := MachineHorner.hornerTrace slots (fun l => labels (.horner l))
    (some (labels .clear)) p (fun l => atLabels (.horner l)) seeded rank
    (digits coefficient offset) hradix hdigits hclean ambient register
  rw [horner_value] at hhorner
  let after := MachineHorner.resultTapes slots seeded (coefficient * rank + offset)
  have hafter : after (slots (.inr 0)) = encodeWord coefficient := by
    simp [after, MachineHorner.resultTapes, Ne.symm (hc 3), seeded, coefficientTapes]
  have hstart : Function.update after (slots (.inr 0)) (encodeWord coefficient ++ []) = after := by
    rw [List.append_nil, ← hafter, Function.update_eq_self]
  have hfinish : Function.update after (slots (.inr 0)) [] =
      MachineHorner.resultTapes slots base (coefficient * rank + offset) := by
    funext k
    by_cases ho : k = slots (.inl 3)
    · subst k
      simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, hc 3]
    · by_cases hk : k = slots (.inr 0)
      · subst k
        simp [MachineHorner.resultTapes, Ne.symm (hc 3), coefficientEmpty]
      · simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, ho, hk]
  have hclear := MachineHorner.drainTrace (slots (.inr 0)) (labels .clear) exit p
    (atLabels .clear) after coefficient [] ambient none
  rw [hstart, hfinish] at hclear
  rw [show steps coefficient rank offset = (coefficient + 1) +
      (MachineHorner.steps rank (digits coefficient offset) 2 + 1) by unfold steps; omega,
    Function.iterate_add_apply, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[coefficient + 1]
    ((MachineComposition.advance (TM2.step p))^[MachineHorner.steps rank (digits coefficient offset) 2]
      ((MachineComposition.advance (TM2.step p))^[1]
        (some ⟨some (labels .seed), ((ambient, ()), register), base⟩))) = _
  rw [hseed, hhorner]
  exact hclear

def affineInPolynomialTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := steps_le_timePolynomial coefficient rank offset

def leftBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (2 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((variableEncoding F u).code v).val))
    (zeroWord : base (slots (.inr 1)) = encodeWord 0)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 0)⟩)
      ((timePolynomial (2 ^ (2 ^ u))).eval (operandLength (((variableEncoding F u).code v).val) 0)) := by
  have h := affineInPolynomialTime slots (2 ^ (2 ^ u)) labels exit p atLabels base
    (((variableEncoding F u).code v).val) 0 rankWord zeroWord coefficientEmpty clean ambient register
  have hv : 2 ^ (2 ^ u) * (((variableEncoding F u).code v).val) + 0 = baseValue F u c v 0 := by
    simp [baseValue]
  simpa only [hv] using h

def rightBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (8 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (leftBlockWord : base (slots (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u))
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 1)⟩)
      ((timePolynomial (2 ^ (8 ^ u))).eval
        (operandLength (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
  have h := affineInPolynomialTime slots (2 ^ (8 ^ u)) labels exit p atLabels base
    (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.«variables» ^ u)
    rankWord leftBlockWord coefficientEmpty clean ambient register
  have hv : 2 ^ (8 ^ u) * (((clauseEncoding F u).code c).val) + 2 ^ (2 ^ u) * F.«variables» ^ u =
      baseValue F u c v 1 := by
    simp [baseValue, Nat.mul_comm, Nat.add_comm]
  simpa only [hv] using h

end MinUncutGames.Foundations.Hastad.SourceBasePhase

end

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

variable [DecidableEq Extra]

omit [DecidableEq Extra] in
theorem entry_eq :
    MachineDrainMany.entry (fields (u := u) (Extra := Extra)) Sum.inl (some (.inr ())) =
      some (main (u := u) (Extra := Extra)) := entryLabel_eq fields

theorem clearTrace (base : Tape u Extra → List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDrainMany.lengthSum fields base + 6 * u + 1]
      (some ⟨some main, ((), register), base⟩) =
      some ⟨none, ((), none), outputTapes base⟩ := by
  have drain := MachineDrainMany.trace fields Sum.inl (some (.inr ()))
    program (fun _ => rfl) base () register
  rw [entry_eq, finalTapes_eq, steps_eq_of_nodup fields fields_nodup, fields_length] at drain
  have last : (advance (TM2.step program))^[1]
      (some ⟨some (.inr ()), ((), MachineDrainMany.finalRegister (fields (u := u) (Extra := Extra)) register), outputTapes base⟩) =
      some ⟨none, ((), none), outputTapes base⟩ := rfl
  exact trace_trans _ drain last

def clearLoadedInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), outputTapes (SourceContextLoad.stageTapes F tuple base u)⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) where
  steps := MachineDrainMany.lengthSum fields (SourceContextLoad.stageTapes F tuple base u) + 6 * u + 1
  evals_in_steps := clearTrace _ register
  steps_le_m := loaded_cost_le F tuple base hfields

def clearLoadedToBaseInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), base⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  simpa only [output_loaded_eq_base F tuple base hfields hindex hwork] using
    clearLoadedInTime F tuple base hfields register

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

theorem rankedQuery_at (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : Fin (testTapeEncoding u D).size) :
    rankedQuery u D fallback i.val = (testTapeEncoding u D).code.symm i := by
  simp only [rankedQuery, i.isLt, ↓reduceDIte]

theorem query_prefixBits_eq_ofFn (u D n : ℕ) (queries : ℕ → SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D queries values signature n =
      (List.ofFn (fun i : Fin n => queries i.val)).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  induction n with
  | zero => simp [SourceQueryLoop.prefixBits]
  | succ n ih =>
    rw [SourceQueryLoop.prefixBits, List.ofFn_succ', List.concat_eq_append,
      List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using
      congrArg (fun bits => bits ++
        SourceTestAppend.equationBits u D values (signature, queries n)) ih

theorem query_prefixBits_eq_enumerate (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (testTapeEncoding u D).enumerate.flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (testTapeEncoding u D).size =>
      rankedQuery u D fallback i.val) = (testTapeEncoding u D).enumerate := by
    apply congrArg List.ofFn
    funext i
    exact rankedQuery_at u D fallback i
  rw [hlist]

end MinUncutGames.Foundations.Hastad.SourceLoopOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceQueryOrder

open _root_.Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder

theorem equationBits_eq (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceQueryLoop.Query u D) :
    SourceTestAppend.equationBits u D (baseValue F u c (sampledVariables F c s))
      (ofContext F c s, t) = occurrenceBits F u D ((c, s), t) := by
  rw [occurrenceBits, sourceEquation_words]
  rfl

theorem prefixBits_eq_slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback : SourceQueryLoop.Query u D) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback)
      (baseValue F u c (sampledVariables F c s)) (ofContext F c s)
      (testTapeEncoding u D).size = slotBits F u D c s := by
  rw [query_prefixBits_eq_enumerate]
  unfold slotBits
  congr 1
  funext t
  exact equationBits_eq F u D c s t

variable {K Λ : Type} [DecidableEq K]

theorem sourceLoopInTime (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback initialQuery : SourceQueryLoop.Query u D)
    (layout : SourceTestAppend.Layout K)
    (labels : SourceQueryLoop.Label u D (testTapeEncoding u D).size → Λ)
    (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (SourceQueryLoop.State u D))
    (atLabels : ∀ l, p (labels l) = SourceQueryLoop.statement u D
      (testTapeEncoding u D).size (rankedQuery u D fallback) layout labels exit l)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) =
      encodeWord (baseValue F u c (sampledVariables F c s) side))
    (scratchEmpty : base layout.scratch = [])
    (temporaryEmpty : base layout.temporary = []) :
    ∃ lastQuery : SourceQueryLoop.Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, Nat.zero_lt_succ _⟩)),
          ((ofContext F c s, initialQuery), none), base⟩
        (some ⟨exit, ((ofContext F c s, lastQuery), none),
          SourceTestAppend.resultTapes layout base (slotBits F u D c s)⟩)
        ((testTapeEncoding u D).size * (9 * nBits F u + 21) + 1)) := by
  have hbound : ∀ i, i < (testTapeEncoding u D).size →
      SourceTestAppend.steps u D (baseValue F u c (sampledVariables F c s))
        (ofContext F c s, rankedQuery u D fallback i) ≤ 9 * nBits F u + 20 := by
    intro i hi
    let run := SourceTestAppend.sourceAppendInTime F u D
      ((c, s), rankedQuery u D fallback i) layout
      (fun l => labels (.emit ⟨i, hi⟩ l))
      (some (labels (.load ⟨i + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨i, hi⟩ l)) base sourceWords
      scratchEmpty temporaryEmpty none
    exact run.steps_le_m
  have h := SourceQueryLoop.loopInTime u D (testTapeEncoding u D).size
    (9 * nBits F u + 20) (rankedQuery u D fallback) layout labels exit p atLabels
    (ofContext F c s) initialQuery base (baseValue F u c (sampledVariables F c s))
    sourceWords scratchEmpty temporaryEmpty hbound
  rw [prefixBits_eq_slotBits] at h
  exact h

end MinUncutGames.Foundations.Hastad.SourceQueryOrder

end
section
namespace MinUncutGames.Foundations.Hastad.SourceTupleTape

open _root_.Turing Complexity SourceContexts SourceRuntimeModel

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem query_result (base : Arena u Extra → List Bool) (s : Snapshot) (bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (tapes base s) bits =
      tapes base {s with emitted := s.emitted ++ bits} := by
  change Function.update (tapes base s) (workTape .accumulator)
    (bits.reverse ++ tapes base s (workTape .accumulator)) = _
  rw [tapes_accumulator]
  have h := update_emitted base s (s.emitted ++ bits)
  simpa only [List.reverse_append, List.append_assoc] using h

theorem horner_clause_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes clauseRankSlots (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_variable_result (base : Arena u Extra → List Bool) (s : Snapshot)
    (selected : SlotContext u) (value : Nat) :
    MachineHorner.resultTapes (variableRankSlots selected) (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_right_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots true) (tapes base s) value =
      tapes base {s with rightBase := encodeWord value ++ s.rightBase} := by
  change Function.update (tapes base s) (workTape .rightBase)
    (encodeWord value ++ tapes base s (workTape .rightBase)) = _
  rw [tapes_rightBase, update_rightBase]

theorem horner_left_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots false) (tapes base s) value =
      tapes base {s with leftBase := encodeWord value ++ s.leftBase} := by
  change Function.update (tapes base s) (workTape .leftBase)
    (encodeWord value ++ tapes base s (workTape .leftBase)) = _
  rw [tapes_leftBase, update_leftBase]

omit [DecidableEq Extra] in
theorem clean_clause (base : Arena u Extra → List Bool) (s : Snapshot) (clean : WorkClean base) :
    MachineHorner.Clean clauseRankSlots (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_variable (base : Arena u Extra → List Bool) (s : Snapshot) (selected : SlotContext u)
    (clean : WorkClean base) : MachineHorner.Clean (variableRankSlots selected) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_base (base : Arena u Extra → List Bool) (s : Snapshot) (right : Bool)
    (clean : WorkClean base) : MachineHorner.Clean (baseSlots right) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

def clearLoadedSnapshotInTime (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step SourceContextClear.program)
      ⟨some SourceContextClear.main, ((), register), tapes (SourceContextLoad.stageTapes F c base u) s⟩
      (some ⟨none, ((), none), tapes base s⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  rw [tapes_stageTapes]
  exact SourceContextClear.clearLoadedToBaseInTime F c (tapes base s) hfields hindex hwork register

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

def framedConfiguration {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' S :=
  MachineControl.configuration id e (MachineStateFrame.configuration labels exit ambient c)

section Frame

variable {K Λ Λ' σ τ S : Type} {Γ : K → Type} [DecidableEq K]

theorem framed_stepAux (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (framed e labels exit q) (e (state, ambient)) tapes =
      framedConfiguration e labels exit ambient (TM2.stepAux q state tapes) := by
  rw [framed, MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
  rfl

theorem framed_step (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (framedConfiguration e labels exit ambient a) =
      some (framedConfiguration e labels exit ambient b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (source l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (target (labels l)) (e (state, ambient)) tapes) = _
    rw [atLabels, framed_stepAux]

def framedExecution (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (framedConfiguration e labels exit ambient a)
      (some (framedConfiguration e labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime _ _ (framedConfiguration e labels exit ambient)
    (framed_step e labels exit ambient source target atLabels) run

end Frame

variable [DecidableEq Extra]

def program (initialQuery : Query u D) (exit : Option (Label u D Extra)) :
    Label u D Extra → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D)
  | .prepare label => MachineSubroutine.statement .prepare (some .seedZero)
      (SourceContextPrepare.program label)
  | .seedZero => .push (workTape .zero) (fun _ => false) (.goto fun _ => .clauseRank .start)
  | .clauseRank label => framed (arithmeticStateEquiv u D) .clauseRank
      (some (.rightBase .seed)) (SourceRankPhase.program clauseRankSlots label)
  | .rightBase label => framed (arithmeticStateEquiv u D) .rightBase
      (some .clearClauseRank) (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)) label)
  | .clearClauseRank => drainStatement (workTape .rank) .clearClauseRank
      (some (.select ⟨0, by omega⟩))
  | .select index =>
    if h : index.val < SlotCount u then
      .load (selectState initialQuery ⟨index.val, h⟩)
        (.goto fun _ => .variableRank ⟨index.val, h⟩ .start)
    else .goto fun _ => .clearRight
  | .variableRank index label => framed (arithmeticStateEquiv u D) (.variableRank index)
      (some (.leftBase index .seed))
      (SourceRankPhase.program (variableRankSlots (selected index)) label)
  | .leftBase index label => framed (arithmeticStateEquiv u D) (.leftBase index)
      (some (.query index (.load ⟨0, by omega⟩)))
      (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)) label)
  | .query index label => framed (queryStateEquiv u D) (.query index)
      (some (.clearSlotRank index))
      (SourceQueryLoop.statement u D (QueryCount u D)
        (SourceLoopOrder.rankedQuery u D initialQuery) queryLayout id none label)
  | .clearSlotRank index => drainStatement (workTape .rank) (.clearSlotRank index)
      (some (.clearLeft index))
  | .clearLeft index => drainStatement (workTape .leftBase) (.clearLeft index)
      (some (.select ⟨index.val + 1, by omega⟩))
  | .clearRight => drainStatement (workTape .rightBase) .clearRight (some .clearZero)
  | .clearZero => drainStatement (workTape .zero) .clearZero
      (some (.clearContext SourceContextClear.main))
  | .clearContext label => MachineStateFrame.statement .clearContext (some .reset)
      (SourceContextClear.program label)
  | .reset => .load (fun _ => canonicalState initialQuery) (finish exit)

theorem reset_step (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    TM2.step (program initialQuery exit) ⟨some .reset, state, tapes⟩ =
      some ⟨exit, canonicalState initialQuery, tapes⟩ := by
  cases exit <;> rfl

def resetInTime (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .reset, state, tapes⟩ (some ⟨exit, canonicalState initialQuery, tapes⟩) 1 where
  steps := 1
  evals_in_steps := reset_step initialQuery exit state tapes
  steps_le_m := Nat.le_refl _

noncomputable def preparePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some .seedZero,
        SourceContextPrepare.finalState F c (fun _ => .first)
          ((((canonicalSignature u, initialQuery), none), (((), ()), none))),
        SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  let run := SourceContextPrepare.prepareInTime (τ := QueryState u D × ArithmeticState) F c (fun _ => .first) base hformula hcurrent
    hindex hwork hscratch hcopy hfields (fun _ _ => false) (canonicalSignature u) rfl
    ((((canonicalSignature u, initialQuery), none), (((), ()), none)))
  exact MachineSubroutine.execution .prepare (some .seedZero) SourceContextPrepare.program
    (program initialQuery exit) (fun _ => rfl) run

def seedZeroPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (base : Arena u Extra → List Bool) (hzero : base (workTape .zero) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .seedZero, state, base⟩
      (some ⟨some (.clauseRank .start), state,
        Function.update base (workTape .zero) (encodeWord 0)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit .seedZero) state base) = _
    simp only [program, TM2.stepAux, hzero]
    rfl
  steps_le_m := Nat.le_refl _

def drainPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (source : Arena u Extra) (entry : Label u D Extra) (next : Option (Label u D Extra))
    (atEntry : program initialQuery exit entry = drainStatement source entry next)
    (base : Arena u Extra → List Bool)
    (metadata : SourceSignaturePrepare.State u (QueryState u D × ArithmeticState))
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some entry, (((), register), metadata), base⟩
      (some ⟨next, (((), none), metadata), Function.update base source []⟩)
      ((base source).length + 1) := by
  let run := MachineDrain.drainInTime source () none (drainProgram source) rfl base () register
  exact MachineStateFrame.execution (fun _ : Unit => entry) next metadata (drainProgram source)
    (program initialQuery exit) (fun _ => atEntry) run

noncomputable def clauseRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (clauseRankSlots (.inl 0)) = encodeWord F.clauses.length)
    (hdigits : ∀ i, base (clauseRankSlots (.inr i)) = encodeWord (c i).val)
    (hclean : MachineHorner.Clean clauseRankSlots base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes clauseRankSlots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  let run := SourceRankPhase.clauseRankInTime F u c clauseRankSlots id none
    (SourceRankPhase.program clauseRankSlots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .clauseRank (some (.rightBase .seed))
    metadata (SourceRankPhase.program clauseRankSlots) (program initialQuery exit)
    (fun _ => rfl) run

noncomputable def variableRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (variableRankSlots (selected index) (.inl 0)) = encodeWord F.«variables»)
    (hdigits : ∀ i, base (variableRankSlots (selected index) (.inr i)) =
      encodeWord (sampledVariables F c (selected index) i).val)
    (hclean : MachineHorner.Clean (variableRankSlots (selected index)) base)
    (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (variableRankSlots (selected index)) base
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
  let slots := variableRankSlots (u := u) (Extra := Extra) (selected index)
  let run := SourceRankPhase.variableRankInTime F u (sampledVariables F c (selected index))
    slots id none (SourceRankPhase.program slots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.variableRank index)
    (some (.leftBase index .seed)) metadata (SourceRankPhase.program slots)
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def rightBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots true (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (hleftBlock : base (baseSlots true (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u))
    (hcoefficient : base (baseSlots true (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots true) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some .clearClauseRank, arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots true) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
  let run := SourceBasePhase.rightBaseInTime F u c (sampledVariables F c (fun _ => .first))
    (baseSlots true) id none (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (fun _ => rfl) base hrank hleftBlock hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .rightBase (some .clearClauseRank) metadata
    (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def leftBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots false (.inl 0)) =
      encodeWord (((variableEncoding F u).code (sampledVariables F c (selected index))).val))
    (hzero : base (baseSlots false (.inr 1)) = encodeWord 0)
    (hcoefficient : base (baseSlots false (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots false) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)),
        arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots false) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val) 0)) := by
  let run := SourceBasePhase.leftBaseInTime F u c (sampledVariables F c (selected index))
    (baseSlots false) id none (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (fun _ => rfl) base hrank hzero hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.leftBase index)
    (some (.query index (.load ⟨0, by omega⟩))) metadata
    (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

theorem queryPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery beforeQuery : Query u D)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool)
    (metadata : QueryMetadata u)
    (hsource : ∀ side, base (queryLayout.sources side) = encodeWord
      (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) side))
    (hscratch : base queryLayout.scratch = []) (htemporary : base queryLayout.temporary = []) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.query index (.load ⟨0, by omega⟩)),
          queryStateEquiv u D (((ofContext F c (selected index), beforeQuery), none), metadata), base⟩
        (some ⟨some (.clearSlotRank index),
          queryStateEquiv u D (((ofContext F c (selected index), afterQuery), none), metadata),
          SourceTestAppend.resultTapes queryLayout base
            (SourceQueryOrder.slotBits F u D c (selected index))⟩)
        (QueryCount u D * (9 * nBits F u + 21) + 1)) := by
  let localProgram := SourceQueryLoop.statement u D (QueryCount u D)
    (SourceLoopOrder.rankedQuery u D initialQuery) (queryLayout (u := u) (Extra := Extra)) id none
  obtain ⟨lastQuery, ⟨run⟩⟩ := SourceQueryOrder.sourceLoopInTime F u D c (selected index)
    initialQuery beforeQuery queryLayout id none localProgram (fun _ => rfl) base
    hsource hscratch htemporary
  refine ⟨lastQuery, ⟨?_⟩⟩
  exact framedExecution (queryStateEquiv u D) (.query index) (some (.clearSlotRank index))
    metadata localProgram (program initialQuery exit) (fun _ => rfl) run

def selectPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (index : Fin (SlotCount u)) (state : State u D) (base : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select index.castSucc), state, base⟩
      (some ⟨some (.variableRank index .start), selectState initialQuery index state, base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit (.select index.castSucc)) state base) = _
    simp only [program, Fin.val_castSucc, index.isLt, ↓reduceDIte, TM2.stepAux]
  steps_le_m := Nat.le_refl _

theorem slotInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (index : Fin (SlotCount u)) (bits : List Bool) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select index.castSucc), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
        (some ⟨some (.select ⟨index.val + 1, by omega⟩),
          workingState F c (ofContext F c (selected index)) afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (bits ++ SourceQueryOrder.slotBits F u D c (selected index)))⟩)
        (slotBudget (D := D) F c index)) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let sig := ofContext F c (selected index)
  let startTapes := tapes loaded (loopSnapshot F c bits)
  let rankedTapes := tapes loaded (rankSnapshot F c index bits)
  let basedTapes := tapes loaded (baseSnapshot F c index bits)
  have hs := selectPhase initialQuery exit index (workingState F c beforeSignature beforeQuery) startTapes
  rw [select_workingState] at hs
  have hr := variableRankPhase F c index initialQuery exit startTapes
    (by change loaded variableHeader = encodeWord F.«variables»
        exact (loaded_extra F c base _).trans h.variableCount)
    (by intro i
        exact SourceRankPhase.selectedDigits_loaded F c (selected index)
          (rankControls .variableCount) base (fun j => h.fields j _) i)
    (clean_variable loaded (loopSnapshot F c bits) (selected index) h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), workingState F c sig initialQuery, startTapes⟩
      (some ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
    simpa only [arithmeticState_working, startTapes, rankedTapes, rankSnapshot,
      horner_variable_result, loopSnapshot, List.append_nil, variableRank] using hr
  have hb := leftBasePhase F c index initialQuery exit rankedTapes
    (by rfl) (by rfl)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded (rankSnapshot F c index bits) false h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength (variableRank F c index) 0)) := by
    simpa only [arithmeticState_working, rankedTapes, basedTapes, baseSnapshot,
      horner_left_result, rankSnapshot, loopSnapshot, List.append_nil, leftValue, variableRank] using hb
  obtain ⟨lastQuery, ⟨hq⟩⟩ := queryPhase F c index initialQuery initialQuery exit basedTapes
    (queryMetadata F c)
    (by intro side
        fin_cases side
        · rfl
        · rfl
        · change loaded (workTape .dummy) = _
          exact (loaded_extra F c base _).trans h.dummy)
    (by change loaded (workTape .queryScratch) = []
        exact (loaded_extra F c base _).trans h.queryScratch)
    (by change loaded (workTape .queryTemporary) = []
        exact (loaded_extra F c base _).trans h.queryTemporary)
  let emitted := bits ++ SourceQueryOrder.slotBits F u D c (selected index)
  let emittedSnapshot := {baseSnapshot F c index bits with emitted := emitted}
  let emittedTapes := tapes loaded emittedSnapshot
  have hq' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩
      (some ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩)
      (QueryCount u D * (9 * nBits F u + 21) + 1) := by
    simpa only [queryState_working, basedTapes, emittedTapes, emittedSnapshot, query_result,
      baseSnapshot, rankSnapshot, loopSnapshot, emitted, sig] using hq
  let afterRank := tapes loaded {emittedSnapshot with rank := []}
  have hdRank := drainPhase initialQuery exit (workTape .rank) (.clearSlotRank index)
    (some (.clearLeft index)) rfl emittedTapes (workingState F c sig lastQuery).2 none
  have hdRank' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩
      (some ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩)
      (variableRank F c index + 2) := by
    simpa only [workingState_loader, emittedTapes, afterRank, update_rank, tapes_rank, emittedSnapshot,
      baseSnapshot, rankSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdRank
  have hdLeft := drainPhase initialQuery exit (workTape .leftBase) (.clearLeft index)
    (some (.select ⟨index.val + 1, by omega⟩)) rfl afterRank
    (workingState F c sig lastQuery).2 none
  have hdLeft' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩
      (some ⟨some (.select ⟨index.val + 1, by omega⟩), workingState F c sig lastQuery,
        tapes loaded (loopSnapshot F c emitted)⟩)
      (leftValue F c index + 2) := by
    simpa only [workingState_loader, afterRank, update_leftBase, tapes_leftBase, emittedSnapshot,
      baseSnapshot, rankSnapshot, loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdLeft
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
          (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hs hr') hb') hq') hdRank') hdLeft'
  refine ⟨lastQuery, ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩⟩
  have hj := joined.steps_le_m
  dsimp only [slotBudget]
  omega

theorem prefixInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (r : Nat) (hr : r ≤ SlotCount u) :
    ∃ afterSignature : Signature u, ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select ⟨0, by omega⟩), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩
        (some ⟨some (.select ⟨r, by omega⟩), workingState F c afterSignature afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (prefixBits (D := D) F c r))⟩)
        (prefixBudget (D := D) F c r)) := by
  induction r with
  | zero =>
    refine ⟨beforeSignature, beforeQuery, ⟨{
      steps := 0
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl _ }⟩⟩
  | succ r ih =>
    obtain ⟨previousSignature, previousQuery, ⟨previous⟩⟩ := ih (by omega)
    have hlt : r < SlotCount u := by omega
    let index : Fin (SlotCount u) := ⟨r, hlt⟩
    obtain ⟨lastQuery, ⟨one⟩⟩ := slotInTime F c initialQuery previousQuery previousSignature
      exit base h index (prefixBits (D := D) F c r)
    let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ previous one
    refine ⟨ofContext F c (selected index), lastQuery,
      ⟨{ steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }⟩⟩
    · simpa only [prefixBits, slotAt, dite_eq_left hlt, index] using joined.evals_in_steps
    · have hj := joined.steps_le_m
      simp only [prefixBudget, dite_eq_left hlt]
      dsimp only [index] at hj
      omega

noncomputable def setupInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some (.select ⟨0, by omega⟩),
        workingState F c (canonicalSignature u) initialQuery,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩)
      (setupBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c (canonicalSignature u) initialQuery
  let s0 : Snapshot := {zero := encodeWord 0}
  let s1 : Snapshot := {s0 with rank := encodeWord (((clauseEncoding F u).code c).val)}
  let s2 : Snapshot := {s1 with rightBase := encodeWord (rightValue F c)}
  have hp := preparePhase F c initialQuery exit base h.formula h.current h.index h.work
    h.scratch h.copyScratch (fun p => h.fields p.1 _)
  have he : tapes loaded {} = loaded := empty_tapes loaded
    ((loaded_extra F c base _).trans h.rank) ((loaded_extra F c base _).trans h.rightBase)
    ((loaded_extra F c base _).trans h.leftBase) ((loaded_extra F c base _).trans h.zero)
  have hz := seedZeroPhase initialQuery exit state loaded ((loaded_extra F c base _).trans h.zero)
  have hupdate := update_zero loaded {} (encodeWord 0)
  rw [he] at hupdate
  rw [hupdate] at hz
  have hr := clauseRankPhase F c initialQuery exit (tapes loaded s0)
    (by change loaded clauseHeader = encodeWord F.clauses.length
        exact (loaded_extra F c base _).trans h.clauseCount)
    (by intro i
        change loaded (.current i) = encodeWord (c i).val
        exact (SourceContextLoad.stageTapes_frame F c base u (.current i)
          (by simp) (by simp) (by simp)).trans (h.current i))
    (clean_clause loaded s0 h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), state, tapes loaded s0⟩
      (some ⟨some (.rightBase .seed), state, tapes loaded s1⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
    simpa only [arithmeticState_working, horner_clause_result, state, s1, s0, List.append_nil] using hr
  have hb := rightBasePhase F c initialQuery exit (tapes loaded s1) (by rfl)
    (by change loaded (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
        exact (loaded_extra F c base _).trans h.leftBlock)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded s1 true h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), state, tapes loaded s1⟩
      (some ⟨some .clearClauseRank, state, tapes loaded s2⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
    simpa only [arithmeticState_working, horner_right_result, state, s2, s1, s0,
      List.append_nil, rightValue] using hb
  have hd := drainPhase initialQuery exit (workTape .rank) .clearClauseRank
    (some (.select ⟨0, by omega⟩)) rfl (tapes loaded s2) state.2 none
  have hd' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearClauseRank, state, tapes loaded s2⟩
      (some ⟨some (.select ⟨0, by omega⟩), state, tapes loaded (loopSnapshot F c [])⟩)
      (((clauseEncoding F u).code c).val + 2) := by
    simpa only [state, workingState_loader, update_rank, tapes_rank, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hd
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hp hz) hr') hb') hd'
  refine { toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }
  have hj := joined.steps_le_m
  dsimp only [setupBudget]
  omega

def finishInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery query : Query u D) (signature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (bits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), workingState F c signature query,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
      (some ⟨exit, canonicalState initialQuery, SourceTestAppend.resultTapes queryLayout base bits⟩)
      (finishBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c signature query
  let s0 := loopSnapshot F c bits
  let s1 : Snapshot := {s0 with rightBase := []}
  let s2 : Snapshot := {emitted := bits}
  have hd : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), state, tapes loaded s0⟩
      (some ⟨some .clearRight, state, tapes loaded s0⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program initialQuery exit (.select ⟨SlotCount u, by omega⟩))
        state (tapes loaded s0)) = _
      simp only [program, Nat.lt_irrefl, ↓reduceDIte, TM2.stepAux]
    steps_le_m := Nat.le_refl _ }
  have hr := drainPhase initialQuery exit (workTape .rightBase) .clearRight (some .clearZero)
    rfl (tapes loaded s0) state.2 none
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearRight, state, tapes loaded s0⟩
      (some ⟨some .clearZero, state, tapes loaded s1⟩) (rightValue F c + 2) := by
    simpa only [state, workingState_loader, update_rightBase, tapes_rightBase, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hr
  have hz := drainPhase initialQuery exit (workTape .zero) .clearZero
    (some (.clearContext SourceContextClear.main)) rfl (tapes loaded s1) state.2 none
  have hz' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearZero, state, tapes loaded s1⟩
      (some ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩) 2 := by
    simpa only [state, workingState_loader, update_zero, tapes_zero, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] using hz
  have cleanup := clearLoadedSnapshotInTime F c base s2 h.fields h.index h.work none
  have hc := MachineStateFrame.execution .clearContext (some .reset) state.2
    SourceContextClear.program (program initialQuery exit) (fun _ => rfl) cleanup
  have hc' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩
      (some ⟨some .reset, state, tapes base s2⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
    simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
      MachineSubroutine.configuration, MachineSubroutine.label, state, workingState_loader] using hc
  have reset := resetInTime initialQuery exit state (tapes base s2)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hd hr') hz') hc') reset
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · have hend : tapes base s2 = SourceTestAppend.resultTapes queryLayout base bits :=
      final_tapes base bits h.rank h.rightBase h.leftBase h.zero
    simpa only [hend] using joined.evals_in_steps
  · have hj := joined.steps_le_m
    dsimp only [finishBudget]
    omega

theorem bodyInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨exit, canonicalState initialQuery,
        SourceTestAppend.resultTapes queryLayout base (SourceQueryOrder.tupleBits F u D c)⟩)
      (bodyBudget (D := D) F c)) := by
  have setup := setupInTime F c initialQuery exit base h
  obtain ⟨signature, lastQuery, ⟨loopRun⟩⟩ := prefixInTime F c initialQuery initialQuery
    (canonicalSignature u) exit base h (SlotCount u) (Nat.le_refl _)
  rw [prefixBits_eq_tupleBits] at loopRun
  have finishRun := finishInTime F c initialQuery lastQuery signature exit base h
    (SourceQueryOrder.tupleBits F u D c)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ setup loopRun) finishRun
  refine ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩
  have hj := joined.steps_le_m
  dsimp only [bodyBudget]
  omega

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

namespace MinUncutGames.Foundations.Hastad.SourceGeneratorContract

open Target Complexity

def sourceMap (u D : Nat) (hD : 0 < D) (F : NonemptyFormula) :
    MinUncutGames.Reduction.SourceEncoding.Input :=
  SourceOccurrences.sourceInput F.val u D hD

end MinUncutGames.Foundations.Hastad.SourceGeneratorContract

namespace MinUncutGames.Foundations.Hastad.SourceGeneratorProgram

open _root_.Turing Complexity SourceGeneratorModel

noncomputable section

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceGeneratorProgram.sourceGeneratorProgramExtraDecidableEq
def program (u D : Nat) (hD : 0 < D) :
    Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .startup l => SourceTupleBody.framed (sourceStateEquiv u D) Label.startup
      (some (bodyEntry u D)) (SourceStartup.program l)
  | .body l => SourceTupleBody.framed (sourceStateEquiv u D) Label.body
      (some (next u D 0))
      (SourceTupleBody.program (initialQuery u D hD) none l)
  | .check i => MachineTupleOdometer.increment
      (.current i) (.remaining i) (bodyEntry u D) (.reset i)
  | .reset i => MachineTupleOdometer.reset
      (.current i) (.remaining i) (.reset i) (next u D (i.val + 1))
  | .finishEnter => Reduction.MachineTransfer.exitAt (accumulatorTape u D)
      (SourceRuntimeFinish.entry (clearKeys u D) Label.finish)
  | .finish l => SourceRuntimeFinish.statement (clearKeys u D)
      (accumulatorTape u D) (outputTape u D) (initialAmbient u D hD)
      Label.finish none l

def machine (u D : Nat) (hD : 0 < D) : FinTM2 where
  K := Tape u D
  k₀ := .formula
  k₁ := outputTape u D
  Γ _ := Bool
  Λ := Label u D
  main := main u D
  σ := State u D
  initialState := (initialAmbient u D hD, none)
  m := program u D hD

end

end MinUncutGames.Foundations.Hastad.SourceGeneratorProgram

namespace MinUncutGames.Foundations.Hastad.SourceGenerator
open _root_.Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract
noncomputable section
variable {u D : Nat}

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.sourceGeneratorExtraDecidableEq
theorem initial_configuration (F : Formula) (hD : 0 < D) :
    initList (SourceGeneratorProgram.machine u D hD) (formulaBits F) =
      (⟨some (SourceGeneratorProgram.main u D), (initialAmbient u D hD, none),
        SourceStartup.initialTapes F⟩ : (SourceGeneratorProgram.machine u D hD).Cfg) := by
  simp only [initList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = SourceContextLoad.Tape.formula
  · subst k
    simp [SourceStartup.initialTapes]
    rfl
  · simp [SourceStartup.initialTapes, hk]

def startupInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩)
      ((SourceStartup.timePolynomial u D).eval (formulaBits F).length) := by
  have run := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.startup (some (bodyEntry u D)) ()
    SourceStartup.program (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceStartup.startupInPolynomialTime (u := u) F hm hD)
  rw [initial_configuration F hD]
  simpa only [SourceTupleBody.framedConfiguration, MachineStateFrame.configuration,
    MachineControl.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, source_initial,
    Option.map_some, Option.map_none, id_eq, SourceGeneratorProgram.main,
    FinTM2.step, FinTM2.Cfg, SourceGeneratorProgram.machine] using! run

end
end MinUncutGames.Foundations.Hastad.SourceGenerator

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TupleBound
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

theorem preparePolynomial_eval (u L : Nat) :
    (preparePolynomial u).eval L =
      (u * (10 * L + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u * (5 * L + 6) + 2) := by
  simp only [preparePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem setupPolynomial_eval (u L : Nat) :
    (setupPolynomial u).eval L =
      (preparePolynomial u).eval L + 1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
          (L ^ u + SourceBounds.bitCoefficient u * L ^ u + 2) + (L ^ u + 2) := by
  simp only [setupPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

theorem setupBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    setupBudget F c ≤ (setupPolynomial u).eval (formulaBits F).length := by
  have hr := clauseRank_le_power F c
  have hl := leftBlock_le_numberBound (u := u) F
  have hm := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_clauses F)
  have ho : SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
      (2 ^ (2 ^ u) * F.«variables» ^ u) ≤
      (formulaBits F).length ^ u +
        SourceBounds.bitCoefficient u * (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))) ho
  rw [setupPolynomial_eval, preparePolynomial_eval]
  unfold setupBudget
  omega

theorem bodyBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    bodyBudget (D := D) F c ≤ (bodyPolynomial u D).eval (formulaBits F).length := by
  have hs := setupBudget_le F c
  have hp := prefixBudget_le (D := D) F c (SlotCount u)
  have hf := finishBudget_le F c
  simp only [bodyPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  unfold bodyBudget
  omega

theorem bodyInPolynomialTime {Extra : Type} [DecidableEq Extra]
    (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : SourceRuntimeModel.Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (program initialQuery exit))
      ⟨some main, SourceRuntimeModel.canonicalState initialQuery, base⟩
      (some ⟨exit, SourceRuntimeModel.canonicalState initialQuery,
        SourceTestAppend.resultTapes SourceRuntimeModel.queryLayout base
          (SourceQueryOrder.tupleBits F u D c)⟩)
      ((bodyPolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := bodyInTime F c initialQuery exit base h
  exact ⟨{
    toEvalsTo := run.toEvalsTo
    steps_le_m := run.steps_le_m.trans (bodyBudget_le F c)
  }⟩

end MinUncutGames.Foundations.Hastad.SourceTupleBound

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal.tupleBoundExtraDecidableEq
theorem leaf_work_blank (F : Target.Formula) (c : ClauseContext F u) (output : List Bool)
    (role : BodyWork (SourceGeneratorModel.Extra u D))
    (hl : role ≠ .leftBlock) (hd : role ≠ .dummy) (ha : role ≠ .accumulator) :
    leafTapes F c output (workTape role) = [] := by
  change (Function.update (SourceStartup.readyTapes F) (accumulatorTape u D) output)
    (workTape role) = []
  rw [Function.update_of_ne (by simpa [workTape, accumulatorTape] using ha)]
  exact SourceStartup.ready_work_blank F role hl hd ha

theorem leaf_ready (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceTupleBody.Ready F c (leafTapes (D := D) F c output) := by
  constructor
  · simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · intro i
    simp [leafTapes, setDigits]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .index = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inl rfl)
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .work = []
    exact SourceStartup.ready_sharedWork F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .scratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inl rfl))
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .copyScratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inr rfl))
  · intro i s
    simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) variableHeader = encodeWord F.«variables»
    exact SourceStartup.ready_variableHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) clauseHeader = encodeWord F.clauses.length
    exact SourceStartup.ready_clauseHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .leftBlock) = _
    exact SourceStartup.ready_leftBlock F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .dummy) = _
    simpa only [SourceHeaderCounts.dummyValue, SourceHeaderCounts.leftValue,
      SourceHeaderCounts.rightValue, Nat.mul_comm] using SourceStartup.ready_dummy (u := u) (D := D) F
  all_goals apply leaf_work_blank F c output _ <;> simp

theorem body_result_leaf (F : Target.Formula) (c : ClauseContext F u)
    (output bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (leafTapes (D := D) F c output) bits =
      leafTapes F c (bits.reverse ++ output) := by
  change setAcc (accumulatorRole u D) (leafTapes F c output)
    (bits.reverse ++ leafTapes F c output (accumulatorTape u D)) = _
  rw [leaf_accumulator]
  unfold leafTapes
  rw [setDigits_setAcc, setAcc_setAcc, ← setDigits_setAcc]

theorem actual_bodies (F : Target.Formula) (hD : 0 < D) :
    BodyTrace (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D 0)
      (initialAmbient u D hD) (accumulatorRole u D) (SourceStartup.readyTapes F)
      (SourceQueryOrder.tupleBits F u D)
      ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length) := by
  intro c output
  obtain ⟨run⟩ := SourceTupleBound.bodyInPolynomialTime F c (initialQuery u D hD) none
    (leafTapes (D := D) F c output) (leaf_ready F c output)
  have lifted := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.body (some (next u D 0)) ()
    (SourceTupleBody.program (initialQuery u D hD) none)
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl) run
  refine ⟨lifted.steps, lifted.steps_le_m, ?_⟩
  have ht := lifted.evals_in_steps
  change (MachineComposition.advance (TM2.step (SourceGeneratorProgram.program u D hD)))^[lifted.steps]
    _ = _ at ht
  simp only [body_result_leaf] at ht
  simpa only [SourceTupleBody.framedConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some,
    Option.map_none, id_eq, source_initial, configuration,
    bodyEntry, leafTapes] using ht

def resetLabel (u D : Nat) (i : Nat) : SourceGeneratorProgram.Label u D :=
  if h : i < u then .reset ⟨i, h⟩ else .finishEnter

theorem traversalInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      (((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length + 2 * u) *
        F.clauses.length ^ u)) := by
  have hne : F.clauses ≠ [] := List.length_pos_iff.mp hm
  obtain ⟨run⟩ := SourceOdometerSchedule.traversalInTime
    (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D) (resetLabel u D)
    (initialAmbient u D hD) (accumulatorRole u D) hm
    ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length)
    (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D)
    (by intro i hi
        simp only [next, resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (by intro i hi
        simp only [resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (actual_bodies F hD)
  refine ⟨?_⟩
  have hs : initialConfiguration (m := F.clauses.length) u (bodyEntry u D)
      (initialAmbient u D hD) (SourceStartup.readyTapes F) =
      (⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    rw [initialConfiguration, configuration, resetDigits_ready]
  have hf : finalConfiguration (next u D u) (initialAmbient u D hD) (accumulatorRole u D)
      (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D) =
      (⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    unfold finalConfiguration configuration
    rw [setDigits_setAcc, resetDigits_ready]
    change (⟨some (next u D u), (initialAmbient u D hD, none),
      setAcc (accumulatorRole u D) (SourceStartup.readyTapes F)
        ((allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
          SourceStartup.readyTapes F (accumulatorTape u D))⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) = _
    rw [accumulated_eq_input F hD hne]
    simp only [next, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [hs, hf] using run

theorem traversalInPolynomialTime (F : Target.Formula)
    (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      ((timePolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := traversalInTime F hm hD
  refine ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩
  apply run.steps_le_m.trans
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

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

namespace MinUncutGames.Foundations.Hastad.SourceGenerator

open _root_.Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MinUncutGames.Foundations.Hastad.SourceGenerator.generatorExtraDecidableEq
def timePolynomial (u D : Nat) (hD : 0 < D) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (SourceGeneratorProgram.machine u D hD)
    (clearKeys u D).length (prefixPolynomial u D)

def beforeFinish (F : Formula) (hD : 0 < D) : (SourceGeneratorProgram.machine u D hD).Cfg :=
  ⟨SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish,
    (initialAmbient u D hD, none), SourceGeneratorTraversal.traversalOutput F hD⟩

def enterFinishInTime (F : Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      ⟨some .finishEnter, (initialAmbient u D hD, none),
        SourceGeneratorTraversal.traversalOutput F hD⟩
      (some (beforeFinish F hD)) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux
      (Reduction.MachineTransfer.exitAt (accumulatorTape u D)
        (SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish))
      _ _) = _
    cases h : SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish <;>
      simp only [Reduction.MachineTransfer.exitAt, beforeFinish, TM2.stepAux] <;>
      erw [h] <;> rfl
  steps_le_m := Nat.le_refl _

def prefixInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some (beforeFinish F hD)) ((prefixPolynomial u D).eval (formulaBits F).length) := by
  have start := startupInTime (u := u) F hm hD
  let traversal := Classical.choice (SourceGeneratorTraversal.traversalInPolynomialTime
    (u := u) F hm hD)
  have first := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ start traversal
  have joined := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ first (enterFinishInTime F hD)
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply joined.steps_le_m.trans
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem halted_configuration (F : Formula) (hD : 0 < D) :
    (⟨none, (initialAmbient u D hD, none),
      SourceRuntimeFinish.canonicalTapes (outputTape u D)
        (SourceGeneratorTraversal.traversalOutput F hD (accumulatorTape u D)).reverse⟩ :
      (SourceGeneratorProgram.machine u D hD).Cfg) =
      haltList (SourceGeneratorProgram.machine u D hD)
        (MinUncutGames.Reduction.SourceEncoding.inputBits (SourceOccurrences.sourceInput F u D hD)) := by
  rw [SourceGeneratorTraversal.traversalOutput_accumulator, List.reverse_reverse]
  simp only [haltList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = outputTape u D
  · subst k
    simp [SourceRuntimeFinish.canonicalTapes]
    erw [Function.update_self]
    rfl
  · simp [SourceRuntimeFinish.canonicalTapes, hk]
    erw [Function.update_of_ne hk]

def outputInTime (F : NonemptyFormula) (hD : 0 < D) :
    TM2OutputsInTime (SourceGeneratorProgram.machine u D hD) (inputEncoding F)
      (some (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)))
      ((timePolynomial u D hD).eval (inputEncoding F).length) := by
  have hm : 0 < F.val.clauses.length := List.length_pos_iff.mpr F.property
  have prefixRun := prefixInTime (u := u) F.val hm hD
  have keepAcc : accumulatorTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have keepOut : outputTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have covers : ∀ k, k ≠ accumulatorTape u D → k ≠ outputTape u D → k ∈ clearKeys u D :=
    fun k ha ho => (mem_clearKeys u D k).mpr ⟨ha, ho⟩
  have finish := SourceRuntimeFinish.finishInTime (clearKeys u D)
    (accumulatorTape u D) (outputTape u D) (accumulator_ne_output u D)
    keepAcc keepOut covers (initialAmbient u D hD) SourceGeneratorProgram.Label.finish none
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceGeneratorTraversal.traversalOutput F.val hD) (output_empty F.val hD)
    (initialAmbient u D hD) none
  erw [halted_configuration F.val hD] at finish
  have joined := SourceRuntimeSpace.prefixAndFinishInTime
    (SourceGeneratorProgram.machine u D hD) (formulaBits F.val) (prefixPolynomial u D)
    prefixRun (clearKeys u D) (accumulatorTape u D) (outputTape u D)
    keepAcc keepOut covers (SourceGeneratorTraversal.traversalOutput F.val hD)
    (output_empty F.val hD) (fun _ => rfl) finish
  exact joined

def computableInPolyTime (u D : Nat) (hD : 0 < D) :
    TM2ComputableInPolyTime inputEncoding MinUncutGames.Reduction.SourceEncoding.inputBits
      (sourceMap u D hD) where
  tm := SourceGeneratorProgram.machine u D hD
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial u D hD
  outputsFun F := by
    change TM2OutputsInTime (machine u D hD) ((inputEncoding F).map id)
      (some ((MinUncutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)).map id)) _
    have input_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₀)
        ((machine u D hD).Γ (machine u D hD).k₀) id (inputEncoding F) =
        inputEncoding F := List.map_id _
    have output_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₁)
        ((machine u D hD).Γ (machine u D hD).k₁) id
        (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)) =
        MinUncutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F) := List.map_id _
    simpa only [input_eq, output_eq] using outputInTime (u := u) F hD

def forErrorComputableInPolyTime (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    TM2ComputableInPolyTime inputEncoding MinUncutGames.Reduction.SourceEncoding.inputBits
      (errorMap η ξ hη hη1 hξ) := by
  let D := SourceNoiseParameter.noiseDenominator ξ
  let hD := SourceNoiseParameter.noiseDenominator_pos ξ
  let u := SourceGap.repetitionCount η ξ hη hη1 hξ D hD
  exact computableInPolyTime u D hD

theorem forError_finite_work_alphabets (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (k : (forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.K) :
    Finite ((forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.Γ k) := by
  change Finite Bool
  infer_instance

end

end MinUncutGames.Foundations.Hastad.SourceGenerator

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
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

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

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

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

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

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

end Minimum

end MinUncutGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

variable {vertices d : Nat}

def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end MinUncutGames.Foundations.PCP.PoweringOpinionTables

end
section
namespace MinUncutGames.Foundations.PCP.GenericGraphTables

open MinUncutGames.Foundations.Complexity

variable {q : Nat}

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MinUncutGames.Foundations.PCP.GenericGraphTables

end
section
namespace MinUncutGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, PoweringOpinionTables.rowsAccepts_walkRows]

def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end MinUncutGames.Foundations.PCP.PoweringTables

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

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

end MinUncutGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Relations
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

end MinUncutGames.Foundations.PCP.AlphabetTable.Table

namespace MinUncutGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

end MinUncutGames.Foundations.PCP.AlphabetGraphBounds

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel2
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

def rowLoop (table : GenericGraphTables.Table q) (e : Fin table.darts) : Bool :=
  decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val)

def rowState (table : GenericGraphTables.Table q) (e : Fin table.darts) : State q :=
  normal table.rows[e].relation (rowLoop table e)

def compareRowInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (table : GenericGraphTables.Table q) (e : Fin table.darts)
    (base : Tape → List Bool)
    (hTail : base .tail = encodeWord table.rows[e].tail.val)
    (hHead : base .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = []) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal table.rows[e].relation oldLoop, base⟩
      (some ⟨some next, rowState table e, base⟩) (5 * table.vertices + 6) := by
  let run := compareInTime labels next program atLabel base _ _ hTail hHead
    hLeft hRight hScratch table.rows[e].relation oldLoop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (comparisonTime_le_of_lt _ _ _
    table.rows[e].tail.isLt table.rows[table.rows[e].reverseIndex].tail.isLt)

end MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K : Type}

variable {Λ σ : Type} {h bound : Nat} [DecidableEq K]

theorem bitCommands_bits (bits : List (σ → Bool)) (values : Fin h → Nat) (ambient : σ) :
    (bitCommands (h := h) (bound := bound) bits).flatMap (commandBits values ambient) =
      encodeWords (bits.map (fun bit => if bit ambient then 1 else 0)) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [bitCommands, List.map_cons, List.flatMap_cons, commandBits, encodeWords]
      using congrArg (encodeWord (if bit ambient then 1 else 0) ++ ·) ih

end MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Addresses
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

open MinUncutGames.Foundations.Hastad
open Enumeration

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

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

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> rfl

def fieldForQueryEvent (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨queryEventTerms q event slot, queryEventOffset q event slot P⟩

theorem fieldForQueryEvent_eq_rawQueryField (q : Nat)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    fieldForQueryEvent q event slot P = rawQueryField q (Queries.query P event slot) := by
  unfold fieldForQueryEvent queryEventOffset rawQueryField
  rw [rawQueryTerms_query]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

def fieldForDartTail (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨dartTailTerms q event slot orientation, dartTailOffset q event slot orientation P⟩

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

theorem rawQueryTerms_length_le (q : Nat) (query : Queries.RawQuery q) :
    (rawQueryTerms q query).length ≤ 3 := by
  cases query with
  | inl query => rcases query with ⟨side, tape⟩; simp [rawQueryTerms, vertexQueryTerms]
  | inr tape => simp [rawQueryTerms, edgeQueryTerms]

theorem queryEventTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : (queryEventTerms q event slot).length ≤ 3 :=
  rawQueryTerms_length_le q _

theorem dartTailTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (dartTailTerms q event slot orientation).length ≤ 3 := by
  cases orientation with
  | false => simp [dartTailTerms]
  | true => exact queryEventTerms_length_le q event slot

end MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

namespace MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open Emitter

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

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

theorem rowCommands_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : (rowCommands q event slot orientation).length ≤ 4104 := by
  have htail := Addresses.dartTailTerms_length_le q event slot orientation
  simp only [rowCommands, List.length_append, affineCommands_length,
    Addresses.reverseDartField, List.length_cons, List.length_nil,
    bitCommands, List.length_map, relationBits, List.length_ofFn]
  omega

theorem blockCommands_length_le (q : Nat) :
    (blockCommands q).length ≤ Enumeration.localCount q * (6 * (2 * 4104)) := by
  unfold blockCommands
  apply le_trans (flatMap_length_le _ _ (6 * (2 * 4104)) ?_) (by simp)
  intro event _
  apply le_trans (flatMap_length_le _ _ (2 * 4104) ?_) (by simp)
  intro slot _
  apply le_trans (flatMap_length_le _ _ 4104 ?_) (by simp)
  intro orientation _
  exact rowCommands_length_le q event slot orientation

end MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLookup
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

end MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Driver
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Driver

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MinUncutGames.Foundations.Hastad
open RuntimeModel

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

end MinUncutGames.Foundations.PCP.AlphabetTable.Driver

namespace MinUncutGames.Foundations.PCP.AlphabetTable.LoopState

open MinUncutGames.Foundations.Complexity
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

end MinUncutGames.Foundations.PCP.AlphabetTable.LoopState

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Initialization

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

end MinUncutGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_LoopInitialization
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Finish

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel
open scoped BigOperators

noncomputable def completedPolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  prefixTime + Polynomial.C 16 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound (Driver.machine q)) * prefixTime) +
    Polynomial.C 17

end MinUncutGames.Foundations.PCP.AlphabetTable.Finish

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Runtime

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

end MinUncutGames.Foundations.PCP.AlphabetTable.Runtime

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
namespace MinUncutGames.Foundations.PCP.AlphabetTable

open MinUncutGames.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

end MinUncutGames.Foundations.PCP.AlphabetTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRow
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRow

open _root_.Turing
open MachineFixedBlockMap
open MinUncutGames.Foundations.PCP

theorem rowAccept_eq_true {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt bits a b = true ↔ ∀ k, edgeAccept labelAt bits k a b = true := by
  simp [rowAccept, List.all_eq_true, List.mem_ofFn]

end MinUncutGames.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringRowData
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.Complexity.PoweringMachineField.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringRowData

open MinUncutGames.Foundations.Complexity
open _root_.Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

theorem firstMatch_endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    firstMatch (endpointMask G t center u.val) = some (addressIndex G t center u) := by
  unfold endpointMask addressIndex
  exact firstMatch_firstIndex
    (fun w : PortWords (Fin d) t => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem fixedLabelAt_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (center : Fin vertices) (u : Ball G (n + 1) center)
    (a : Fin (PoweringTables.labelCount d n)) :
    fixedLabelAt d n a (addressIndex G (n + 1) center u) =
      decode (finitePortSelector G (n + 1) center) (decodeLabel d (n + 1) 64 a) u := by
  simpa only [fixedLabelAt, labelTable_get] using
    labelTable_addressIndex G (n + 1) center u (decodeLabel d (n + 1) 64 a)

theorem firstMatch_walkBits_left (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (leftMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1) w.1
        (tailFromStart (PortTables.portGraph input) n w k)) := by
  rw [leftMatches_walkBits]
  simpa only [tailFromStart_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1) w.1
      (tailFromStart (PortTables.portGraph input) n w k)

theorem firstMatch_walkBits_right (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (rightMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1)
        (endpoint (PortTables.portGraph input) w)
        (headFromEnd (PortTables.portGraph input) n w k)) := by
  rw [rightMatches_walkBits]
  simpa only [headFromEnd_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w) (headFromEnd (PortTables.portGraph input) n w k)

theorem edgeAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    edgeAccept (fixedLabelAt d n) (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k)
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1) w.1)
          (decodeLabel d (n + 1) 64 a) (tailFromStart (PortTables.portGraph input) n w k))
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1)
          (endpoint (PortTables.portGraph input) w))
          (decodeLabel d (n + 1) 64 b) (headFromEnd (PortTables.portGraph input) n w k)) := by
  simp only [edgeAccept, firstMatch_walkBits_left, firstMatch_walkBits_right,
    basePredicate_walkBits, fixedLabelAt_addressIndex]

theorem rowAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (walkBits input n w) a b =
      rowsAccepts (PortTables.accepts input) (walkRows (PortTables.portGraph input) n w)
        (labelTable (decodeLabel d (n + 1) 64 a))
        (labelTable (decodeLabel d (n + 1) 64 b)) := by
  rw [rowsAccepts_walkRows]
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, PoweringTest.pathAccepts_eq_true_iff, edgeAccept_walkBits]

theorem edgeAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) :
    edgeAccept labelAt (transposeBits bits) k a b = edgeAccept labelAt bits k b a := by
  simp only [edgeAccept, leftMatches_transposeBits, rightMatches_transposeBits]
  cases firstMatch (leftMatches bits k) <;>
    cases firstMatch (rightMatches bits k) <;>
    simp

theorem rowAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt (transposeBits bits) a b = rowAccept labelAt bits b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, edgeAccept_transposeBits]

theorem rowAccept_rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (rowBits input n e) a b =
      PoweringTables.rowAccepts input n e a b := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowBits, Bool.false_eq_true, ite_false, ite_true,
      rowAccept_transposeBits, rowAccept_walkBits, PoweringTables.rowAccepts]

def dataWords (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Nat :=
  (List.ofFn (rowBits input n e)).map GraphTables.bitWord

def dataTape (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Bool :=
  encodeWords (dataWords input n e)

def emittedRelation (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    GenericGraphTables.RelationTable (PoweringTables.labelCount d n) :=
  Vector.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))

end MinUncutGames.Foundations.PCP.PoweringRowData

end
section
namespace MinUncutGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open MinUncutGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

theorem walkEnd_tailPorts (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
      walkEnd G v (tailPorts n p k) = (edgeAt G n (v, p) k).1 := by
  intro n
  induction n with
  | zero => intro v p k; rfl
  | succ n ih =>
      intro v p k
      refine Fin.cases rfl (fun j => ?_) k
      exact ih (next G v (p 0)) (fun i => p i.succ) j

theorem walkEnd_headPorts (G : PortGraph V D) (n : Nat) (v : V)
    (p : Fin (n + 1) → D) (k : Fin (n + 1)) :
    walkEnd G v (headPorts n p k) = (G.rot (edgeAt G n (v, p) k)).1 := by
  rw [headPorts, walkEnd_append, walkEnd_tailPorts]
  change (G.rot ((edgeAt G n (v, p) k).1, p k)).1 = _
  have hp : (edgeAt G n (v, p) k).2 = p k := edgeAt_port G n (v, p) k
  rw [← hp]

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

def evaluate {vertices d : Nat} (input : PortTables.Table vertices d)
    (start : Fin vertices) : Instruction d → Bool
  | .relation ports port a b => PortTables.accepts input
      (walkEnd (PortTables.portGraph input) start ports, port) a b
  | .equal left right => decide
      (walkEnd (PortTables.portGraph input) start left =
        walkEnd (PortTables.portGraph input) start right)

theorem evaluate_fieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (fieldPlan n ports k field) = walkData input n (start, ports) k field := by
  rcases field with ⟨a,b⟩ | i | i
  · simp only [evaluate, fieldPlan, walkData, walkEnd_tailPorts]
    have hp : (edgeAt (PortTables.portGraph input) n (start, ports) k).2 = ports k :=
      edgeAt_port (PortTables.portGraph input) n (start, ports) k
    rw [← hp]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_tailPorts]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input) start i
    rw [ha]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_append,
      walkEnd_headPorts]
    rw [← wordEnd_eq_walkEnd_ofFn]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input)
      (wordEnd (PortTables.portGraph input) (n + 1) start ports) i
    rw [ha]
    rfl

theorem evaluate_directedFieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (directedFieldPlan n ports direction k field) =
      rowData input n (direction, start, ports) k field :=
  evaluate_fieldPlan input n start ports k _

def rowPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Instruction d) :=
  List.ofFn fun i : Fin (inputSize (n + 1) (slotCount d n)) =>
    let pair := (inputEquiv (n + 1) (slotCount d n)).symm i
    directedFieldPlan n ports direction pair.1 pair.2

theorem evaluate_rowPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (rowPlan n ports direction).map (evaluate input start) =
      List.ofFn (rowBits input n (direction, start, ports)) := by
  rw [rowPlan, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [evaluate_directedFieldPlan, rowBits_packData]
  rfl

end MinUncutGames.Foundations.PCP.PoweringFieldPlan

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineField
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachinePlan

open _root_.Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

theorem boundedRowPlan_values (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (boundedRowPlan n ports direction).map Subtype.val = rowPlan n ports direction := by
  rw [boundedRowPlan, rowPlan, List.map_ofFn]
  rfl

end MinUncutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringRowHeaderSemantics
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open MinUncutGames.Foundations.Complexity

variable {vertices d : Nat}

def tailVertex (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Fin vertices :=
  if direction then wordEnd (PortTables.portGraph input) (n + 1) vertex ports else vertex

def headerWords (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  [(tailVertex input n vertex ports direction).val, reverseValue d n vertex ports direction]

end MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRowHeaders
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

open _root_.Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

theorem plan_entry_eq {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E)
    (labels : PoweringMachinePlan.Label ops ⊕ E → Λ) :
    PoweringMachinePlan.entry ops (fun l => labels (.inl l))
      (some (labels (.inr fallback))) = some (labels (planMain ops fallback)) := by
  cases ops <;> rfl

def rowWords (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  GenericGraphTables.rowWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)]

end MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableLayout
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringTableLayout

open MinUncutGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  erw [blockIndex_val]

def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)

theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  erw [List.flatMap_assoc]
  rfl

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap]
  rfl

end MinUncutGames.Foundations.PCP.PoweringTableLayout

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineVertex

open _root_.Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

def rowBits (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) : List Bool :=
  encodeWords (PoweringMachineRowBody.rowWords graph n vertex (ports j) (direction j))

theorem blockIndex_eq_encodeDart (n : Nat) (vertex : Fin vertices) (j : Command d n) :
    PoweringTableLayout.blockIndex d n vertex j =
      PoweringEnumeration.encodeDart vertices d n (direction j, vertex, ports j) := by
  have h := PoweringTableLayout.blockIndex_eq_encodeDart d n vertex (ports j) (direction j)
  simp only [ports, direction, Prod.mk.eta] at h
  erw [Equiv.apply_symm_apply] at h
  exact h

theorem rowBits_eq (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) :
    rowBits graph n vertex j = encodeWords (GenericGraphTables.rowWords
      (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
  rw [blockIndex_eq_encodeDart]
  rfl

theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rows_eq_vertexRowBits (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) :
    (List.ofFn id : List (Command d n)).flatMap (rowBits graph n vertex) =
      PoweringTableLayout.vertexRowBits graph n vertex := by
  have hrows : (List.ofFn id : List (Command d n)).map
      (fun j => (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) =
      List.ofFn (fun j : Command d n =>
        (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
    simp only [List.map_ofFn, Function.comp_id]
  calc
    _ = (List.ofFn id : List (Command d n)).flatMap (fun j => encodeWords
        (GenericGraphTables.rowWords
          (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j])) := by
      apply congrArg (List.flatMap · (List.ofFn id))
      funext j
      exact rowBits_eq graph n vertex j
    _ = PoweringTableLayout.vertexRowBits graph n vertex := by
      unfold PoweringTableLayout.vertexRowBits PoweringTableLayout.vertexRowWords
        PoweringTableLayout.vertexRows
      rw [encodeWords_flatMap]
      erw [← hrows, List.flatMap_map]
      rfl

end MinUncutGames.Foundations.Complexity.PoweringMachineVertex

namespace MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

open _root_.Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

def prefixRows (graph : PortTables.Table vertices d) (n : Nat) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixRows graph n r ++
      if h : r < vertices then PoweringTableLayout.vertexRowBits graph n ⟨r, h⟩ else []

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

end MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

namespace MinUncutGames.Foundations.Complexity.PoweringMachineFinish

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

end MinUncutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringPolynomialBudget
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

def finishBudget (d n pushBound tapeCount vertices inputLength prior : Nat) : Nat :=
  2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
    tapeCount * (inputLength + prior * pushBound + vertices +
      PoweringTableLayout.blockSize d n * vertices + 3)

theorem finishBudget_mono (d n pushBound tapeCount inputLength : Nat)
    {v w prior later : Nat} (hvertices : v ≤ w) (hprior : prior ≤ later) :
    finishBudget d n pushBound tapeCount v inputLength prior ≤
      finishBudget d n pushBound tapeCount w inputLength later := by
  have hdarts := Nat.mul_le_mul_left (PoweringTableLayout.blockSize d n) hvertices
  have hheader := Nat.mul_le_mul_left 2 (Nat.add_le_add hvertices hdarts)
  have hgrowth := Nat.mul_le_mul_right pushBound hprior
  have hinside : inputLength + prior * pushBound + v +
      PoweringTableLayout.blockSize d n * v + 3 ≤
      inputLength + later * pushBound + w + PoweringTableLayout.blockSize d n * w + 3 := by
    omega
  have hclear := Nat.mul_le_mul_left tapeCount hinside
  unfold finishBudget
  omega

end MinUncutGames.Foundations.Complexity.PoweringPolynomialBudget

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCanonicalOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCanonicalOutput

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end MinUncutGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringRuntimeBudget
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringRuntimeBudget

open _root_.Turing

abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

end MinUncutGames.Foundations.Complexity.PoweringRuntimeBudget

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

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator

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

end MinUncutGames.Foundations.PCP.FinalConstants

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

namespace MinUncutGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

end MinUncutGames.Foundations.PCP.RoundGap

end
end
section
namespace MinUncutGames.Foundations.Hastad.SourceNonempty

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

end MinUncutGames.Foundations.Hastad.SourceNonempty

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

noncomputable section
namespace MinUncutGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

end MinUncutGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Hastad
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Outer.HastadSource

open MinUncutGames.Foundations Target Complexity PCP
open MinUncutGames.Reduction
open MachineFiniteAlphabet


noncomputable def sourceMachine (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime Hastad.SourceGeneratorContract.inputEncoding
      SourceEncoding.inputBits (sourceMap ξ hξ) :=
  Hastad.SourceGenerator.forErrorComputableInPolyTime PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

end MinUncutGames.Outer.HastadSource

end

end OAI
end


