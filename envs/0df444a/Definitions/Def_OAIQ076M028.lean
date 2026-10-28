-- Prove2me | Definitions.Def_OAIQ076M028
-- name    : OAIQ076M028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:27:21.874005+00:00
-- url     : https://prove2.me/theorems/f4bd5991-cee2-441c-95f3-24c661f809a7
-- title:
--   Definitions bundle OAIQ076M028 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 207 declarations of OpenAI's Lean: 64 definitions, 5 inductive types or structures, 3 instances and 135 theorems. The definitions and types are `OAI.MinUncut.Outer.ProofFamily.assignment`, `OAI.MinUncut.SourceBridge.binaryReduction`, `OAI.MinUncutGames.BinaryRenameMachine.computableInPolyTime`, `OAI.MinUncutGames.BinaryRenameMachine.tokenComputation`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program.computableInPolyTime`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program.formulaHeader`, `OAI.MinUncutGames.Foundations.Complexity.FinalCNFPattern.tableVerifier`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.count`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.countedBits`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.inputBits`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.lengthPolynomial`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.runtimePolynomial`, `OAI.MinUncutGames.Foundations.Complexity.GraphIterationBounds.words`, `OAI.MinUncutGames.Foundations.Complexity.MachineCloudSelect.queryWord`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderFamily.multiplySizeInTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderFamily.returnFrame`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.rowSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.TableRun`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.VertexLoopRun`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.VertexRun`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.VertexSuffixRun`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.completeBudget`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.finalTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.reverseOutputHaltInTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.vertexLoopBudget`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderTable.vertexLoopTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.Alphabet`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.Tape`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.clearTape`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.copyExit`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.copySource`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.copyTarget`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.coreTape`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.dummyFuel`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.frame`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.headerAux`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.headerTape`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.machine`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.oldFuel`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.ownerFuel` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianDistance`, `MinUncut_Encoding_Binary`, `MinUncut_Estimates_AnalyticOuter`, `MinUncut_Estimates_Basic2`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_InnerUniform`, `MinUncut_Estimates_InputData`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_OuterRemainder`, `MinUncut_Estimates_OuterSampling`, `MinUncut_Games_FinalCNFOutput`, `MinUncut_Games_FinalCNFPattern`, `MinUncut_Games_FinalCNFStream`, `MinUncut_Games_GraphIterationBounds`, `MinUncut_Games_HintSections`, `MinUncut_Games_HintSoundness`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_GeneratedGraph`, `MinUncut_Graphs_HonestBudgets`, `MinUncut_Machines_MachineBinaryRenameMachine`, `MinUncut_Machines_MachineCloudPrefix`, `MinUncut_Machines_MachineCloudSelect`, `MinUncut_Machines_MachineExpanderFamilyAffine`, `MinUncut_Machines_MachineExpanderFamilyCycle`, `MinUncut_Machines_MachineExpanderRowFrames`, `MinUncut_Machines_MachineExpanderTableProgram`, `MinUncut_Machines_MachineExpanderTableRows`, `MinUncut_Machines_MachinePaddedExpanderFamilyBounds`, `MinUncut_Machines_MachineRegularOwnerProgram`, `MinUncut_Machines_MachineRegularTableRuntime`, `MinUncut_Machines_MachineRegularTableTrace`, `MinUncut_Machines_MachineTableIteration`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_Hastad`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SelectionSequence`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_TableIteration`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_InnerParameters`, `MinUncut_Search_RationalBasics`, `MinUncut_Search_RationalInner`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M022`, `OAIQ076M023`, `OAIQ076M024` and `OAIQ076M025` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ076M031`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M022
import Definitions.Def_OAIQ076M023
import Definitions.Def_OAIQ076M024
import Definitions.Def_OAIQ076M025

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*}

variable [Fintype S] [Nonempty S]

variable [Fintype Name]

lemma ordinary_success_le (equations : S → Equation Name)
    (strategy : Strategy (Equation Name) Name Triple F₂) :
    (ordinaryGame equations).success strategy ≤
      (2+equationFraction equations strategy.2)/3 := by
  have hc : (0 : ℝ)<Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  rw [ordinary_success_formula]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun i _ => ordinary_coordinate_bound (equations i) (strategy.1 (equations i)) strategy.2)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  unfold equationFraction
  apply (div_le_iff₀ (mul_pos hc (by norm_num : (0 : ℝ)<3))).2
  calc
    _ ≤ (Fintype.card S : ℝ)*2 +
        ∑ i, if Satisfied strategy.2 (equations i) then (1 : ℝ) else 0 := hsum
    _ = _ := by field_simp

theorem ordinary_value_le (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4) :
    (ordinaryGame equations).value ≤ 11/12 := by
  apply (Game.value_le_iff _ _).2
  intro strategy
  have h := ordinary_success_le equations strategy
  have hs := hsound strategy.2
  linarith

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectionSequence
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games MinUncutGames.Foundations.Repetition

variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

theorem ordinary_repetition_success (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4) (r : ℕ)
    (strategy : Strategy (Fin r → Equation Name) (Fin r → Name)
      (Fin r → Triple) (Fin r → F₂)) :
    ((ordinaryGame equations).repetition r).success strategy ≤ repetitionRate^r := by
  classical
  have h := holenstein_repetition_success (ordinaryGame equations) r strategy
    (ordinary_value_le equations hsound) (by norm_num : (11/12 : ℝ)<1)
    (by norm_num : (1 : ℝ)≤4) ordinary_alphabet_log
  refine h.trans ?_
  have hb : 0 ≤ 1-(1-(11/12 : ℝ))^3/6000 := by norm_num
  have hp : 0 ≤ (r : ℝ)/4 := by positivity
  calc
    (1-(1-(11/12 : ℝ))^3/6000)^((r : ℝ)/4) ≤
        (repetitionRate^4)^((r : ℝ)/4) :=
      Real.rpow_le_rpow hb repetitionRate_fourth hp
    _ = repetitionRate^r := by
      rw [← Real.rpow_natCast,← Real.rpow_mul repetitionRate_pos.le]
      have he : (4 : ℝ)*((r : ℝ)/4)=(r : ℝ) := by ring
      norm_num only [Nat.cast_ofNat]
      rw [he,Real.rpow_natCast]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterSampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

theorem ordinary_repetition_on (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {J : Type*} [Fintype J]
    (a : (J → Equation Name) → J → Triple) (b : (J → Name) → J → F₂) :
    (𝔼 w : J → S × Fin 3,
      if (∀ j, ordinaryAccepts (equations (w j).1)
        ((equations (w j).1).names (w j).2)
        (a (fun i => equations (w i).1) j)
        (b (fun i => (equations (w i).1).names (w i).2) j)=true)
      then (1 : ℝ) else 0) ≤ repetitionRate ^ Fintype.card J := by
  classical
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let strategy : Strategy (Fin (Fintype.card J) → Equation Name)
      (Fin (Fintype.card J) → Name) (Fin (Fintype.card J) → Triple)
      (Fin (Fintype.card J) → F₂) :=
    (fun x i => a (fun j => x (e.symm j)) (e i),
     fun y i => b (fun j => y (e.symm j)) (e i))
  have h := ordinary_repetition_success equations hsound (Fintype.card J) strategy
  rw [ordinary_repetition_formula] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  let ew : (J → S × Fin 3) ≃ (Fin (Fintype.card J) → S × Fin 3) :=
    Equiv.arrowCongr e.symm (Equiv.refl _)
  apply Fintype.expect_equiv ew
  intro w
  simp only [ew,Equiv.arrowCongr_apply,Equiv.coe_refl,Equiv.symm_symm,
    strategy,Function.comp_apply,id_eq,Equiv.apply_symm_apply]
  congr 1
  exact propext e.forall_congr_right.symm

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSections
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem hint_section_bound (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0)
    (bg : I → S × Fin 3) :
    (𝔼 w : {i // A i} → S × Fin 3,
      if hintedWins strategy (sampledEquations equations (patch A bg w)) hidden
        (sampledPositions (patch A bg w)) c then (1 : ℝ) else 0) ≤
      repetitionRate ^ Fintype.card {i // A i} := by
  classical
  obtain ⟨a,b,hsim⟩ := active_simulation strategy A hidden hA c hzero
    (sampledEquations equations bg) (sampledPositions bg)
  have hrep := ordinary_repetition_on equations hsound a b
  apply le_trans (b := (𝔼 w : {i // A i} → S × Fin 3,
    if (∀ j, ordinaryAccepts (equations (w j).1)
      ((equations (w j).1).names (w j).2)
      (a (fun i => equations (w i).1) j)
      (b (fun i => (equations (w i).1).names (w i).2) j)=true)
    then (1 : ℝ) else 0)) ?_ (by
    convert hrep using 1; congr 1
    first | rfl | congr!)
  refine Finset.expect_le_expect (fun w _ => ?_)
  split_ifs with hw hr hr
  · rfl
  · exfalso
    apply hr
    have hwin := hw
    rw [sampledEquations_patch,sampledPositions_patch] at hwin
    exact hsim (sampledEquations equations w) (sampledPositions w) hwin
  · norm_num
  · rfl

theorem hint_fixed_coefficients_bound (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0) :
    (𝔼 w : I → S × Fin 3,
      if hintedWins strategy (sampledEquations equations w) hidden
        (sampledPositions w) c then (1 : ℝ) else 0) ≤
      repetitionRate ^ Fintype.card {i // A i} :=
  expect_le_of_active_sections A _ _
    (hint_section_bound equations hsound strategy A hidden hA c hzero)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

theorem shared_hint_soundness (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 L : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        if hintedAcceptance strategy (sampledEquations equations w) hidden
          (sampledPositions w) L then (1 : ℝ) else 0) ≤
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  classical
  have hsample (w : I → S × Fin 3) :
      (𝔼 L : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        if hintedAcceptance strategy (sampledEquations equations w) hidden
          (sampledPositions w) L then (1 : ℝ) else 0) =
      (𝔼 c : HintCoefficients I q,
        if hintedWins strategy (sampledEquations equations w) hidden
          (sampledPositions w) c then (1 : ℝ) else 0) := by
    exact (uniform_hintTupleGenerator _ q
      (fun L => if hintedAcceptance strategy (sampledEquations equations w) hidden
        (sampledPositions w) L then (1 : ℝ) else 0)).symm
  simp_rw [hsample]
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 c : HintCoefficients I q,
        repetitionRate ^ Fintype.card {i // Active hidden (coefficientVectors q c) i} := by
      apply Finset.expect_le_expect
      intro c _
      apply hint_fixed_coefficients_bound equations hsound strategy
        (Active hidden (coefficientVectors q c)) hidden (fun _ hi => hi.1) c
      intro k i hi
      exact congrFun hi.2 k
    _ = _ := coefficient_active_expect q hidden

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ListDecoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable {Name I : Type*} [Fintype I]

theorem HintLists.shared_soundness [Fintype Name]
    {S : Type*} [Fintype S] [Nonempty S] (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q L R : ℕ} (lists : HintLists Name I q)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 B : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
      if lists.matches (sampledEquations equations w) hidden (sampledPositions w) B
        then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate q ^ Fintype.card {i // hidden i=true} := by
  calc
    _ ≤ 𝔼 w : I → S × Fin 3,
        𝔼 B : Fin q → Forms (SecondAlphabet
          (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        ∑ z : Fin L × Fin R,
          if hintedAcceptance (lists.strategy z) (sampledEquations equations w) hidden
            (sampledPositions w) B then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro w _
      exact Finset.expect_le_expect (fun B _ => lists.matching_le_sum hL hR _ hidden _ B)
    _ = ∑ z : Fin L × Fin R, 𝔼 w : I → S × Fin 3,
        𝔼 B : Fin q → Forms (SecondAlphabet
          (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
          if hintedAcceptance (lists.strategy z) (sampledEquations equations w) hidden
            (sampledPositions w) B then (1 : ℝ) else 0 := by
      simp_rw [Finset.expect_sum_comm]
    _ ≤ ∑ _z : Fin L × Fin R, hintRate q ^ Fintype.card {i // hidden i=true} := by
      apply Finset.sum_le_sum
      intro z _
      exact shared_hint_soundness equations hsound (lists.strategy z) hidden
    _ = _ := by simp [mul_assoc]


open scoped BigOperators
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IndexedLists
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem IndexedLists.shared_soundness [Fintype Name]
    {S : Type*} [Fintype S] [Nonempty S] (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {L R : ℕ} (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 B : J → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
      if lists.matches (sampledEquations equations w) hidden (sampledPositions w) B
        then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J) ^ Fintype.card {i // hidden i=true} := by
  have h := lists.numbered.shared_soundness equations hsound
    (fun U B => hL U _) (fun V B => hR V _) hidden
  simpa only [lists.numbered_matches] using h

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

lemma IndexedLists.shared_soundness_split [Fintype Name]
    (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {L R : ℕ} (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 a : I → S, 𝔼 pos : I → Fin 3,
      𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) hidden pos)),
      if lists.matches (fun i => equations (a i)) hidden pos B then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J) ^ Fintype.card {i // hidden i=true} := by
  have h := lists.shared_soundness equations hsound hL hR hidden
  rw [← expect_split_tuple (fun a pos =>
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) hidden pos)),
      if lists.matches (fun i => equations (a i)) hidden pos B then (1 : ℝ) else 0)]
  exact h

lemma IndexedLists.full_soundness [Fintype Name]
    (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {k L R : ℕ} (hk : k≤Fintype.card I) (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) :
    backgroundMean equations k (fun U h pos B => if lists.matches U h pos B then 1 else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J)^k := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  unfold backgroundMean
  calc
    _ ≤ 𝔼 H : FixedSets I k,
        (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J)^k := by
      apply Finset.expect_le_expect
      intro H _
      have h := lists.shared_soundness_split equations hsound hL hR (hiddenSet H.val)
      simpa only [hiddenSet_card,H.property] using h
    _ = _ := Fintype.expect_const _

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterRemainder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [DecidableEq J]


open scoped BigOperators
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

theorem LocalRows.atom_bound [Fintype Name] [Nonempty I]
    (rows : LocalRows Name I J) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {k : ℕ} (hk : k≤Fintype.card I) {M u θ : ℝ} (hM : 0≤M) (hu : 0<u) (hθ : 0<θ)
    (hf : ∀ U D z, |rows.first U D z|≤M) (hg : ∀ V D z, |rows.second V D z|≤M) :
    backgroundMean equations k (rows.atom θ) ≤
      (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)*hintRate (Fintype.card J)^k +
      (16/θ^2)*backgroundMean equations k rows.distance +
      (256/θ^4)*(u^2*M^2+
        Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*(M+M^2/u)^4) := by
  have hp := backgroundMean_mono equations k (F := rows.atom θ)
    (G := fun U hidden pos B =>
      (if (rows.lists u θ).matches U hidden pos B then 1 else 0) +
      (16/θ^2)*rows.distance U hidden pos B + (256/θ^4)*rows.fourth u U hidden pos B)
    (fun U hidden pos B => atom_le_matching_charge (projection U hidden pos)
      (rows.first U (fun j => formPullback (projection U hidden pos) (B j)))
      (rows.second (secondQuestion U hidden pos) B) u hθ)
  rw [backgroundMean_add,backgroundMean_add,backgroundMean_mul,backgroundMean_mul] at hp
  have hm := (rows.lists u θ).full_soundness equations hsound hk
    (rows.card_first hM hu hf) (rows.card_second hM hθ hg)
  have hr := rows.mean_fourth equations hk hM hu hf
  have hx := mul_le_mul_of_nonneg_left hr (by positivity : 0≤256/θ^4)
  linarith

end MinUncut.Outer

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDistance
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

theorem ProofFamily.row_soundness [Fintype Name] [Nonempty I] [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s≤3/4)
    {k : ℕ} (hk : k≤Fintype.card I) {σ u θ : ℝ} (hσ : 0<σ) (hu : 0<u) (hθ : 0<θ)
    (η : ℝ) (x : Point m n) (i : Fin m) :
    edgeMean equations k (f.atomAt σ η θ x i) ≤
      listTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k +
      (16/θ^2)*edgeMean equations k (f.distanceAt σ η x i) +
      remainderTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k (Fintype.card I) := by
  let M : ℝ := Real.sqrt (n^m:ℕ)/σ
  let L := listTerm M u θ (Fintype.card (Row m n)-1) k
  let R := remainderTerm M u θ (Fintype.card (Row m n)-1) k (Fintype.card I)
  have hpoint (c : Point m n → ℝ) :
      backgroundMean equations k ((f.rows σ η c x ⟨i,face x i⟩).atom θ) ≤
        L+(16/θ^2)*backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance+R := by
    have h := (f.rows σ η c x ⟨i,face x i⟩).atom_bound equations hsound hk
      (by positivity : 0≤M) hu hθ (f.rows_first_bound hσ η c x _) (f.rows_second_bound hσ η c x _)
    simpa only [rest_card,L,R,listTerm,remainderTerm] using h
  have hiA := backgroundMean_integrable equations k _ (f.rows_atom_integrable hσ.ne' hθ η x i)
  have hiD := backgroundMean_integrable equations k _ (f.rows_distance_integrable hσ.ne' η x ⟨i,face x i⟩)
  have h := integral_mono hiA (((integrable_const L).add (hiD.const_mul (16/θ^2))).add (integrable_const R)) hpoint
  rw [f.atomAt_integral equations k hσ.ne' hθ η x i] at h
  simp only [Pi.add_apply] at h
  have hiL : Integrable (fun c => L+(16/θ^2)*backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance) (gauss (Point m n)) :=
    (integrable_const L).add (hiD.const_mul _)
  rw [integral_add hiL (integrable_const R),
    integral_add (integrable_const L) (hiD.const_mul (16/θ^2)),integral_const_mul,
    f.distanceAt_integral equations k hσ.ne' η x i] at h
  simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using h
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AnalyticOuter
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

theorem ProofFamily.atomTotal_bound [Fintype Name] [Nonempty I] [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s≤3/4)
    {k : ℕ} (hk : k≤Fintype.card I) (hm : 0 < m) (hn : 0 < n)
    {σ u θ : ℝ} (hσ : 0<σ) (hu : 0<u) (hθ : 0<θ) (η : ℝ) :
    edgeMean equations k (f.atomTotal (m := m) (n := n) σ η θ) ≤
      listTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k +
      (64/(θ^2*σ^2))*edgeMean equations k (f.fourthTotal (m := m) (n := n) σ η) +
      remainderTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k (Fintype.card I) := by
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero n := ⟨hn.ne'⟩
  have h := Finset.expect_le_expect (s := Finset.univ) (fun (x : Point m n) _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun i _ => f.row_soundness equations hsound hk hσ hu hθ η x i))
  rw [f.atomTotal_mean] at h
  simp only [Finset.expect_add_distrib,Fintype.expect_const,← Finset.mul_expect] at h
  have hd := f.distanceTotal_bound equations k hm hn hσ.ne' η
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : 0≤16/θ^2)
  have hc : (16/θ^2)*(4*σ⁻¹^2) = 64/(θ^2*σ^2) := by ring
  rw [← mul_assoc,hc] at hd'
  linarith
end MinUncut.Outer

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_InnerParameters
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox

theorem InnerParameters.decode {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ))
    (h1 : (∑ ξ, w ξ*firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := P.m) (n := P.n) (f ξ)
      ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ ∑ ξ, w ξ*atomProbability (m := P.m) (n := P.n) (f ξ)
      (sourceSigma J) (sourceEta J) (P.θ:ℝ) := by
  apply inner_atom_of_errors V A w hw hw1 f hJ P.hm (by have := P.hn; omega)
    (by have := P.hn; omega) P.hs P.hroom (by exact_mod_cast P.hH) P.hγ
    (by exact_mod_cast P.hA) P.hθ.le P.hloc P.henergy P.hclip P.hcollision P.hfourth P.hatom
    h1 h2 h3
end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerUniform
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner

attribute [local irreducible] firstError secondError thirdError atomProbability

theorem InnerParameters.decode_expect {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    {Ξ : Type*} [Fintype Ξ] [Nonempty Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (f : ∀ ξ, FoldedProof (A ξ))
    (h1 : (𝔼 ξ,firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J))
    (h2 : (𝔼 ξ,secondError (m := P.m) (n := P.n) (f ξ)
      ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (𝔼 ξ,thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ 𝔼 ξ,atomProbability (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J) P.θ := by
  let w := fun _ : Ξ => (Fintype.card Ξ:ℝ)⁻¹
  have hw (ξ : Ξ) : 0≤w ξ := by dsimp [w]; positivity
  have hw1 : ∑ ξ,w ξ=1 := by
    simpa only [mul_one,Fintype.expect_const] using (uniformWeight_sum (fun _ : Ξ => (1:ℝ)))
  have hh1 : (∑ ξ,w ξ*firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J) := by
    simpa only [w,uniformWeight_sum] using h1
  have hh2 : (∑ ξ,w ξ*secondError (m := P.m) (n := P.n) (f ξ) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)) := by
    simpa only [w,uniformWeight_sum] using h2
  have hh3 : (∑ ξ,w ξ*thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J/(Fintype.card (Code P.m P.n):ℝ) := by
    simpa only [w,uniformWeight_sum] using h3
  simpa only [w,uniformWeight_sum] using P.decode hJ V A w hw hw1 f hh1 hh2 hh3
end MinUncut.Inner

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S]

theorem ProofFamily.atomTotal_lower [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name) {J : ℝ} (hJ : 1≤J)
    (P : InnerParameters J) {k : ℕ} (hk : k≤Fintype.card I)
    (h1 : edgeMean equations k (fun U h pos => firstError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J))
    (h2 : edgeMean equations k (fun U h pos => secondError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤
        J*(10*(sourceEta J+sourceEta J)))
    (h3 : edgeMean equations k (fun U h pos => thirdError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J)) ≤
        J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ edgeMean equations k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  let A := fun e : EdgeSamples I S k => SecondAlphabet (edgeSampleSecond equations e)
  rw [← edgeSample_expect equations k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ)]
  change (P.p:ℝ) ≤ 𝔼 e : EdgeSamples I S k,atomProbability (m := P.m) (n := P.n)
    (f.second (edgeSampleSecond equations e)) (sourceSigma J) (sourceEta J) P.θ
  apply P.decode_expect hJ A A (fun e => f.second (edgeSampleSecond equations e))
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => firstError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))]
    exact h1
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => secondError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J))]
    exact h2
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => thirdError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))]
    exact h3
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError fourthError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

attribute [local irreducible] edgeMean

omit [Nonempty S] in
lemma ProofFamily.error_le_of_cost {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) (hcost : f.cost P O equations ≤ J)
    (j : Test) : f.testErrors P O equations j ≤ J*budgets P O j := by
  apply (div_le_iff₀ (budgets_pos hJ P O j)).mp
  exact (Finset.single_le_sum (fun i _ => div_nonneg (f.testErrors_nonneg hJ P O equations i)
    (budgets_pos hJ P O i).le) (Finset.mem_univ j)).trans hcost

attribute [local irreducible] ProofFamily.fourthTotal ProofFamily.atomTotal

lemma ProofFamily.cost_atom_lower {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k ≤ Fintype.card I) (hc : f.cost P O equations ≤ J) :
    (P.p:ℝ) ≤ edgeMean equations O.k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) := by
  have h1 := f.error_le_of_cost hJ P O equations hc .first
  have h2 := f.error_le_of_cost hJ P O equations hc .second
  have h3 := f.error_le_of_cost hJ P O equations hc .third
  simp only [ProofFamily.testErrors,budgets] at h1 h2 h3
  rw [← div_eq_mul_inv] at h3
  exact f.atomTotal_lower equations hJ P hk h1 h2 h3

lemma ProofFamily.cost_atom_upper [Fintype Name] [Nonempty I] {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    (hcard : Fintype.card I=O.t) (hc : f.cost P O equations ≤ J) :
    edgeMean equations O.k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) < (P.p:ℝ) := by
  have hk : O.k ≤ Fintype.card I := by simpa only [hcard] using O.hk
  have hm : 0 < P.m := by have := P.hm; omega
  have hn : 0 < P.n := by have := P.hn; omega
  have h4 := f.error_le_of_cost hJ P O equations hc .fourth
  simp only [ProofFamily.testErrors,budgets] at h4
  have hu := f.atomTotal_bound equations hsound hk hm hn (sourceSigma_pos hJ) O.hu P.hθ (sourceEta J)
  have hx := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 64/(P.θ^2*(sourceSigma J)^2))
  have hg := O.hgap
  simp only [hcard] at hu
  linarith

theorem ProofFamily.cost_gt [Fintype Name] [Nonempty I] {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4) (hcard : Fintype.card I=O.t) :
    J < f.cost P O equations := by
  by_contra! hc
  exact (not_lt_of_ge (f.cost_atom_lower hJ P O equations (by simpa only [hcard] using O.hk) hc)) (f.cost_atom_upper hJ P O equations hsound hcard hc)
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteQueryFamily
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma ProofFamily.queryAnswer_folded (f : ProofFamily Name I) : Folded f.queryAnswer := by
  intro q P
  cases q with
  | inl U => exact (f.first U).folded P
  | inr Q => exact (f.second Q).folded P

def ProofFamily.assignment (f : ProofFamily Name I) : FamilyVariable Name I → Bool :=
  fun p => f.queryAnswer p.1 p.2.val

lemma ProofFamily.answer_assignment (f : ProofFamily Name I) :
    answer familyBase f.assignment=f.queryAnswer :=
  answer_of_folded familyBase f.queryAnswer f.queryAnswer_folded

lemma ProofFamily.variableProof_assignment (f : ProofFamily Name I) : variableProof f.assignment=f := by
  apply proofFamily_ext
  · funext U
    apply foldedProof_ext
    exact (congrFun f.answer_assignment (.inl U))
  · funext Q
    apply foldedProof_ext
    exact (congrFun f.answer_assignment (.inr Q))

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestBudgets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma failure_fraction (equations : S → Equation Name) (s : Name → F₂) :
    (𝔼 a : S, if Satisfied s (equations a) then (0:ℝ) else 1)=1-equationFraction equations s := by
  have he (a : S) : (if Satisfied s (equations a) then (0:ℝ) else 1)=
      1-(if Satisfied s (equations a) then (1:ℝ) else 0) := by split <;> norm_num
  simp_rw [he,Finset.expect_sub_distrib,Fintype.expect_const,Fintype.expect_eq_sum_div_card]
  rfl

lemma honest_fourth_mean (equations : S → Equation Name) (s : Name → F₂) {k : ℕ}
    (hk : k ≤ Fintype.card I) (m n : ℕ) (σ η : ℝ) :
    edgeMean equations k ((honestProof (I := I) s).fourthTotal (m := m) (n := n) σ η) ≤
      (Fintype.card I:ℝ)*(1-equationFraction equations s) := by
  apply (edgeMean_mono equations k (fun U h p => honest_fourth_point s U h p m n σ η)).trans_eq
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have hcoord (i : I) : (𝔼 a : I → S, if Satisfied s (equations (a i)) then (0:ℝ) else 1)=
      1-equationFraction equations s :=
    (Subbox.expect_coordinate (B := fun _ : I => S) i
      (fun b => if Satisfied s (equations b) then (0:ℝ) else 1)).trans (failure_fraction equations s)
  simp only [edgeMean,Fintype.expect_const,Finset.expect_sum_comm,hcoord,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]

attribute [local irreducible] firstError secondError thirdError fourthError edgeMean

lemma honest_errors_le {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (equations : S → Equation Name) (s : Name → F₂) (hcard : Fintype.card I=O.t)
    (hs : (O.t:ℝ)*(1-equationFraction equations s) ≤ O.b4) (j : Test) :
    (honestProof (I := I) s).testErrors P O equations j ≤ budgets P O j := by
  have hk : O.k ≤ Fintype.card I := by simpa only [hcard] using O.hk
  have hn : 0 < P.n := by have := P.hn; omega
  have hm : 0 < P.m := by have := P.hm; omega
  cases j <;> simp only [ProofFamily.testErrors,budgets,honestProof]
  · apply (edgeMean_mono equations O.k (fun U h pos => honest_first_budget (V := SecondAlphabet (secondQuestion U h pos)) (secondLabel s (secondQuestion U h pos)) hn hJ)).trans_eq
    exact edgeMean_const equations hk _
  · apply (edgeMean_mono equations O.k (fun U h pos => honest_second_budget (V := SecondAlphabet (secondQuestion U h pos)) (secondLabel s (secondQuestion U h pos)) hn hm hJ)).trans_eq
    exact edgeMean_const equations hk _
  · apply le_of_eq
    simp only [thirdError_evaluation]
    exact edgeMean_const equations hk _
  · exact (honest_fourth_mean equations s hk P.m P.n (sourceSigma J) (sourceEta J)).trans
      (by simpa only [hcard] using hs)

lemma honest_cost_le {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (equations : S → Equation Name) (s : Name → F₂) (hcard : Fintype.card I=O.t)
    (hs : (O.t:ℝ)*(1-equationFraction equations s) ≤ O.b4) :
    (honestProof (I := I) s).cost P O equations ≤ 4 := by
  have hh : (honestProof (I := I) s).cost P O equations ≤ ∑ _ : Test, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact (div_le_one (budgets_pos hJ P O j)).mpr (honest_errors_le hJ P O equations s hcard hs j)
  have hc : (∑ _ : Test, (1:ℝ))=4 := by
    have hc : Fintype.card Test=4 := by decide
    simp [hc]
  exact hh.trans_eq hc
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

attribute [local irreducible] edgeMean
lemma ProofFamily.finiteErrors_difference {J : ℕ} (hJ : 1≤J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k≤Fintype.card I) {ε : ℚ} (hε : 0<ε) (j : Test) :
    |f.testErrors P O equations j-
      f.finiteErrors P O (tableGrid P.m P.n ε hε) equations j|≤ε := by
  have hn : 0<P.n := by have := P.hn; omega
  have hm : 0<P.m := by have := P.hm; omega
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  obtain ⟨hs,hs1,he,he1⟩ := rational_source_bounds hJ
  have ha := source_row_rate hJ' hm
  cases j <;> rw [ProofFamily.testErrors,ProofFamily.finiteErrors] <;>
    apply edgeMean_abs_difference equations hk <;> intro U hidden pos
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteFirst_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteSecond_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε ha.1 ha.2.1
  · simpa only [rationalSigma_cast,rationalEta_cast] using
      finiteThird_difference (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε
  · simpa only [rationalSigma_cast,rationalEta_cast,ProofFamily.fourthTotal] using
      finiteFourth_difference (projection U hidden pos) (f.first U)
        (f.second (secondQuestion U hidden pos)) hn hs hs1 he he1 hε

lemma ProofFamily.finiteCost_difference {J : ℕ} (hJ : 1≤J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k≤Fintype.card I) {ε : ℚ} (hε : 0<ε) :
    |f.cost P O equations-f.finiteCost P O (tableGrid P.m P.n ε hε) equations|≤
      (ε:ℝ)*budgetWeight P O := by
  have hJ' : (1:ℝ)≤J := by exact_mod_cast hJ
  unfold ProofFamily.cost ProofFamily.finiteCost
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |f.testErrors P O equations j / budgets P O j-
          f.finiteErrors P O (tableGrid P.m P.n ε hε) equations j / budgets P O j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (ε:ℝ) / budgets P O j := Finset.sum_le_sum (fun j _ => by
      rw [← sub_div,abs_div,abs_of_pos (budgets_pos hJ' P O j)]
      exact div_le_div_of_nonneg_right (f.finiteErrors_difference hJ P O equations hk hε j)
        (budgets_pos hJ' P O j).le)
    _ = _ := by simp only [budgetWeight,Finset.mul_sum,div_eq_mul_inv]
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalInner
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian

variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma ProofFamily.finiteCost_close {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : o.k≤Fintype.card I) :
    |f.cost (d.realize hJ hd) (o.realize hJ d hd ho) equations-
      f.finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
        (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations|<1/2 := by
  have hh := f.finiteCost_difference hJ (d.realize hJ hd) (o.realize hJ d hd ho)
    equations hk (tableAccuracy_pos hJ d hd o ho)
  apply hh.trans_lt
  rw [← rationalWeight_cast hJ d hd o ho]
  have he := (Rat.cast_lt (K := ℝ)).mpr (tableAccuracy_error hJ d hd o ho)
  simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he

lemma finite_honest_cost {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (equations : S → Equation Name) (s : Name → F₂)
    (hcard : Fintype.card I=o.t) (hs : (o.t:ℝ)*(1-equationFraction equations s)≤o.b4) :
    (honestProof (I := I) s).finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
      (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations < 9/2 := by
  have hk : o.k≤Fintype.card I := by rw [hcard]; exact ho.2.2.2.2.1
  have hc := (honestProof (I := I) s).finiteCost_close hJ d hd o ho equations hk
  have hb := honest_cost_le (I := I) (by exact_mod_cast hJ : (1:ℝ)≤J) (d.realize hJ hd)
    (o.realize hJ d hd ho) equations s hcard hs
  have := (abs_lt.mp hc).1
  linarith

lemma finite_unsound_cost [Fintype Name] [Nonempty I] {J : ℕ} (hJ : 1≤J)
    (d : InnerData) (hd : d.Check J) (o : OuterData) (ho : o.Check J d)
    (f : ProofFamily Name I) (equations : S → Equation Name) (hcard : Fintype.card I=o.t)
    (hs : ∀ s : Name → F₂, equationFraction equations s≤3/4) :
    (J:ℝ)-1/2 < f.finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
      (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations := by
  have hk : o.k≤Fintype.card I := by rw [hcard]; exact ho.2.2.2.2.1
  have hc := f.finiteCost_close hJ d hd o ho equations hk
  have hb := f.cost_gt (by exact_mod_cast hJ : (1:ℝ)≤J) (d.realize hJ hd)
    (o.realize hJ d hd ho) equations hs hcard
  have := (abs_lt.mp hc).2
  linarith
end MinUncut.Outer

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

variable {W D B : Type*}

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

end MinUncutGames.Foundations.PCP.ConstraintGraph

end

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

namespace MinUncutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

end MinUncutGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

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
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
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
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (preprocess H t)).Satisfiable := by
  have hp : (PortTables.baseGraph (padded H t)).Satisfiable :=
    (PreprocessingPaddingTables.pad_satisfiable_iff _ _).mpr
      (PreprocessingRegularSoundness.completeness H t h)
  obtain ⟨labels, hlabels⟩ := hp
  refine ⟨labels, ?_⟩
  apply (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mp
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mpr hlabels

end MinUncutGames.Foundations.PCP.PreprocessingGuarantees

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPrefix
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

open _root_.Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

end MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudSelect
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudSelect

open _root_.Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

abbrev queryWord := MachineCloudRank.queryWord

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudSelect

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ]

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyAffine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ] {d : Nat}

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

variable {ρ : Type} [Fintype ρ] {d : Nat}

section Embedded

variable {K Λ : Type} [DecidableEq K]

theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

end Embedded

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

variable {v d : Nat}

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

open _root_.Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.finalTapes current oldWord newWord [])
    (extraFrame remaining current suffix)

theorem returnFrame_eq_cycleTapes (remaining current : Nat)
    (oldWord newWord suffix : List Bool) :
    returnFrame remaining current oldWord newWord suffix =
      cycleTapes remaining oldWord (encodeWord current) (encodeWord current)
        (encodeWord 0) newWord suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [returnFrame, MachineEmbedding.tapes,
        MachineExpanderTable.finalTapes, MachineExpanderTable.boundaryTapes,
        MachineExpanderTable.extraTapes, cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem multipliedFrame_eq_update (d remaining current : Nat) (word suffix : List Bool) :
    Function.update (installedFrame remaining current word suffix)
      (.inr .currentSize) (encodeWord (cloudSize d * current)) =
      multipliedFrame d remaining current word suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyCycle
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePaddedExpanderFamilyBounds
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

open _root_.Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

instance instDecidableEqTape : DecidableEq Tape := MachineRegularOwnerCleanup.tapeDecidableEq

open _root_.Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic2
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP


namespace Top

abbrev Tape := Body ⊕ (Header.Tape ⊕ Fin 4)
abbrev Alphabet (_ : Tape) := Bool

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (sumDecidableEq
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineCloudPrefix.Tape))
        (inferInstanceAs (DecidableEq Header.Extra)))
      (inferInstanceAs (DecidableEq (Fin 4))))

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def coreTape (i : Fin 27) : Tape := .inl (.inl i)
def oldFuel : Tape := .inr (.inr 0)
def ownerFuel : Tape := .inr (.inr 1)
def dummyFuel : Tape := .inr (.inr 2)
def scratch : Tape := .inr (.inr 3)

def headerTape (k : Header.Tape) : Tape :=
  if k = Header.tableTape then coreTape 0
  else if k = Header.mTape then coreTape 6
  else if k = Header.outputTape then coreTape 8
  else .inr (.inl k)

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

def ownerView : Tape → Option MachineRegularOwnerBody.Tape
  | .inl k => some (.inl k)
  | .inr (.inl _) => none
  | .inr (.inr i) => match i.val with
    | 2 => some (.inr 0)
    | 3 => some (.inr 1)
    | _ => none

def copySource : CopyPhase → Tape
  | .old => coreTape 6
  | .owner => headerTape Header.nTape
def copyTarget : CopyPhase → Tape
  | .old => oldFuel
  | .owner => ownerFuel

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

def frame (data : Data) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr (.inl k) => header k
  | .inr (.inr i) => counters i

@[simp] theorem frame_core (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (i : Fin 27) :
    frame data header counters (coreTape i) = MachineRegularMetadata.frame data (.inl i) := rfl

def headerAux (n N R : List Bool) : Header.Tape → List Bool := fun k =>
  if k = Header.nTape then n
  else if k = Header.verticesTape then N
  else if k = Header.dartsTape then R
  else []

@[simp] theorem headerAux_empty : headerAux [] [] [] = (fun _ => []) := by
  funext k
  simp [headerAux]

end Top
end MinUncutGames.Foundations.Complexity.MachineRegularTable
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InputData
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable
open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP
namespace Top

@[simp] theorem frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) oldFuel = old := rfl

@[simp] theorem frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) ownerFuel = owners := rfl

@[simp] theorem update_frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) oldFuel replacement =
      frame data header (counterStacks replacement owners dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) ownerFuel replacement =
      frame data header (counterStacks old replacement dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_global (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 1) replacement =
      frame { data with globalIndex := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_owner (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 2) replacement =
      frame { data with owner := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

@[simp] theorem frame_scratch (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) scratch = work := rfl

@[simp] theorem frame_darts (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) : frame data header counters (coreTape 6) = data.darts := rfl

@[simp] theorem frame_header_n (data : Data) (n N R : List Bool)
    (counters : Fin 4 → List Bool) :
    frame data (headerAux n N R) counters (headerTape Header.nTape) = n := rfl

@[simp] theorem update_frame_offset (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 5) replacement =
      frame { data with offset := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

end Top

end MinUncutGames.Foundations.Complexity.MachineRegularTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

end MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTableRuntime

open _root_.Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)


def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

end MinUncutGames.Foundations.Complexity.MachineRegularTableRuntime

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
namespace MinUncutGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end MinUncutGames.Foundations.PCP.RawInitialTables

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

def sizeFactor : Nat := AlphabetGraphBounds.sizeFactor alphabet *
  (ExpanderFamily.growth ^ 2 * (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)))

theorem sizeFactor_positive : 0 < sizeFactor := by
  unfold sizeFactor
  apply Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive alphabet)
  apply Nat.mul_pos
  · exact Nat.pow_pos (Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one)
  · omega

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

theorem build_completeness (H : BaseTable) (table : GraphTables.Table)
    (sat : (GraphTables.semantics table).Satisfiable) :
    (GraphTables.semantics (build H table)).Satisfiable := by
  let : Nonempty (Fin alphabet) := ⟨⟨0, alphabet_positive⟩⟩
  exact AlphabetTable.Table.perfect_completeness (powered H table)
    (PoweringTableSemantics.preserves_satisfiability
      (PreprocessingTables.preprocess H table) walkParameter
      (PreprocessingGuarantees.completeness H table sat))

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

theorem step_completeness (H : BaseTable) (input : Input) :
    Satisfiable input → Satisfiable (step H input) := build_completeness H input.val

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end MinUncutGames.Foundations.PCP.RoundTables

end
section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

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

theorem query_tail (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.castAdd 6 j) =
      bitIndex vertices (G.tail (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_left]

theorem query_head (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.natAdd 6 j) =
      bitIndex vertices (G.head (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_right]

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

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

end MinUncutGames.Foundations.Complexity.FinalCNFPattern

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFStream
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

end MinUncutGames.Foundations.Complexity.FinalCNFTemplate

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

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
namespace MinUncutGames.Foundations.PCP.FinalTableFormula

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

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).«variables» ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).«variables» + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end MinUncutGames.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).«variables»,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

open PCP

theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open _root_.Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have input_eq : @List.map
        ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
          (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
        ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
          (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
        id (GraphTables.tableBits table) = GraphTables.tableBits table := List.map_id _
    have output_eq : @List.map
        ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
          (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
        ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
          (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
        id (formulaBits (FinalTableFormula.output table)) =
          formulaBits (FinalTableFormula.output table) := List.map_id _
    rw [input_eq, output_eq, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

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

namespace MinUncutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

end MinUncutGames.Foundations.PCP.TableIteration

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_GraphIterationBounds
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end MinUncutGames.Foundations.Complexity.GraphIterationBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTableIteration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineTableIteration

open _root_.Turing PCP RoundTables GraphIterationBounds

def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input := by
    let budgets := fun i => body.time.eval (words H input i).length
    have runs (i : Nat) (_hi : i < count input) :
        TM2OutputsInTime body.tm ((words H input i).map body.inputAlphabet.symm)
          (some ((words H input (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      exact body.outputsFun (TableIteration.runTables H i input.val)
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count input) (words H input) budgets runs
    have start : encodeWord (count input) ++ words H input 0 = countedBits input := rfl
    have finish : words H input (count input) = GraphTables.tableBits (finalTable H input) := rfl
    rw [start, finish] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (countedBits input).length
    let L := lengthPolynomial.eval N
    let B := body.time.eval L
    have hl (i : Nat) (hi : i ≤ count input) : (words H input i).length ≤ L :=
      intermediate_bits H input i hi
    have hb (i : Nat) (hi : i < count input) : budgets i ≤ B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count input) (words H input) budgets B L hb hl
    have hc : count input ≤ N + 1 := count_le input
    rw [runtimePolynomial_eval]
    calc
      run.steps ≤ count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets :=
        run.steps_le_m
      _ ≤ count input + 1 + (count input * (B + 2 * L + 3) + 2 * L + 3) :=
        Nat.add_le_add_left hloop _
      _ = count input * (B + 2 * L + 4) + 2 * L + 4 := by ring
      _ ≤ (N + 1) * (B + 2 * L + 4) + 2 * L + 4 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _) _

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end MinUncutGames.Foundations.Complexity.MachineTableIteration

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


def gapInput (H : RoundTables.BaseTable) (F : Formula) :
    Hastad.SourceGeneratorContract.NonemptyFormula :=
  ⟨TableIteration.gapMap H F, TableIteration.gapMap_nonempty H F⟩

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  sourceMap ξ hξ (gapInput H F)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits, 1 - ξ ≤ success (output H ξ hξ F) bits := by
  exact Hastad.SourceGap.forError_complete PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableIteration.gapMap_completeness H F hF)

structure Reduction (ξ : ℚ) where
  reduce : Formula → SourceEncoding.Input
  completeness : ∀ F, F.Satisfiable → ∃ bits, 1 - ξ ≤ success (reduce F) bits
  soundness : ∀ F, ¬ F.Satisfiable → ∀ bits, success (reduce F) bits ≤ (1 + ξ) / 2
  computation : Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

end MinUncutGames.Outer.HastadSource

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryRenameMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryRenameMachine


open _root_.Turing MinUncutGames.Foundations
open Complexity Complexity.MachineComposition
open MinUncutGames.Reduction.MachineTransfer

noncomputable def tokenComputation :
    TM2ComputableInPolyTime (fun formula : BinaryFormula.Formula =>
      BinaryTokenMachine.tokens formula.clauses) formulaBits BinaryOccurrenceRename.renamed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((BinaryTokenMachine.tokens formula.clauses).map id)
      (some ((formulaBits (BinaryOccurrenceRename.renamed formula)).map id))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits formulaBits
      BinaryOccurrenceRename.renamed :=
  MachineSequential.composeBits preprocessing tokenComputation

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  MachineFiniteAlphabet.composeBits preprocessing tokenComputation
    BinaryTokenMachine.machine_finiteAlphabet machine_finiteAlphabet

end MinUncutGames.BinaryRenameMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Binary
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.SourceBridge
open MinUncutGames MinUncutGames.Reduction MinUncutGames.Foundations
open MinUncutGames.Foundations.Complexity
open Outer MinUncut.Inner

def binaryReduction {ξ : ℚ} (R : Outer.HastadSource.Reduction ξ) : BinaryReduction ξ where
  reduce F := R.reduce (BinaryOccurrenceRename.renamed F)
  complete F hF := R.completeness _ ((BinaryOccurrenceRename.renamed_satisfiable_iff F).mpr hF)
  sound F hF := R.soundness _ (fun h => hF ((BinaryOccurrenceRename.renamed_satisfiable_iff F).mp h))
  computation := MachineSequential.composeBits BinaryRenameMachine.computableInPolyTime R.computation
  finiteAlphabet := MachineFiniteAlphabet.composeBits _ _
    BinaryRenameMachine.computation_finiteAlphabet R.finiteAlphabet

end MinUncut.SourceBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GeneratedGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable
variable {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
  [Nonempty (Fin input.equations.length)]
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

lemma generatedGraph_yes (s : Fin input.«variables» → F₂)
    (hs : (P.o.t:ℝ)*(1-equationFraction (equations input) s)≤P.o.b4) :
    (generatedGraph P input E).opt≤(generatedGraph P input E).threshold := by
  let y := (honestProof (I:=Fin P.o.t) s).assignment
  have hy : ∑e,(P.weight (equations input) e:ℝ)*(failure (P.demand (equations input) e) y:ℝ)≤9/2 := by
    rw [P.failure_eq,ProofFamily.variableProof_assignment]
    exact (finite_honest_cost P.hJ P.d P.hd P.o P.ho (equations input) s (Fintype.card_fin _) hs).le
  apply listOutput_yes _ _ _ (extendAssignment variableCode y)
  rw [generated_failure_eq]
  have hh := listFailure_weight (P.denominator (Fin input.equations.length)) (P.weight (equations input))
    (P.weight_nonneg _) (P.weight_den _) (P.demand (equations input))
    (SampleEnumeration.all (equations input) P.o.k P.d.m P.d.n P.grid).encoding y
  have he : listFailure (P.canonicalDemands (equations input)) (extendAssignment variableCode y)=
      listFailure (demandList (P.denominator (Fin input.equations.length)) (P.weight (equations input))
        (P.demand (equations input))
        (SampleEnumeration.all (equations input) P.o.k P.d.m P.d.n P.grid).encoding) y :=
    listFailure_extend variableCode variableCode_injective _ y
  have hD : (0:ℝ)<P.denominator (Fin input.equations.length) := by exact_mod_cast P.denominator_pos
  have h : (listFailure (P.canonicalDemands (equations input)) (extendAssignment variableCode y):ℝ)≤
      5*P.denominator (Fin input.equations.length) := by
    rw [he,hh]
    have h' := mul_le_mul_of_nonneg_left (hy.trans (by norm_num : (9/2:ℝ)≤5)) hD.le
    simpa only [mul_comm] using h'
  exact_mod_cast h

lemma generatedGraph_no {K : ℕ} (hK : 2≤K) (hKJ : 8*K≤J)
    (hs : ∀ s : Fin input.«variables» → F₂,equationFraction (equations input) s≤3/4) :
    K*(generatedGraph P input E).threshold<(generatedGraph P input E).opt := by
  let : NeZero P.o.t := ⟨ne_of_gt P.t_pos⟩
  apply listOutput_no
  intro y
  rw [generated_failure_eq]
  have hh := P.canonicalGraph_failure (equations input) y
  have hK' : (2:ℝ)≤K := by exact_mod_cast hK
  have hJ' : 8*(K:ℝ)≤J := by exact_mod_cast hKJ
  have hD : (0:ℝ)<P.denominator (Fin input.equations.length) := by exact_mod_cast P.denominator_pos
  have hg : 5*(K:ℝ)<∑e,(P.weight (equations input) e:ℝ)*
      (failure (P.demand (equations input) e) (y ∘ variableCode):ℝ) := by
    rw [P.failure_eq]
    have h := finite_unsound_cost P.hJ P.d P.hd P.o P.ho (variableProof (y ∘ variableCode))
      (equations input) (Fintype.card_fin _) hs
    change (J:ℝ)-1/2 < (variableProof (y ∘ variableCode)).finiteCost _ _ P.grid (equations input) at h
    linarith
  have h : (K:ℝ)*(5*P.denominator (Fin input.equations.length))<
      (listFailure (P.canonicalDemands (equations input)) y:ℝ) := by
    rw [hh]
    have h' := mul_lt_mul_of_pos_left hg hD
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h'
  exact_mod_cast h
end MinUncut.Costed.SourceWords

end
end

end OAI
end


