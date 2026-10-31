-- Prove2me | Definitions.Def_OAIQ028V008
-- name    : OAIQ028V008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:19:13.570209+00:00
-- url     : https://prove2.me/theorems/13717ad9-282e-497e-a011-8be0197fd9a8
-- title:
--   Definitions bundle OAIQ028V008 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 240 declarations of OpenAI's Lean: 124 definitions and 116 theorems. The definitions and types are `OAI.UniqueGames.Foundations.Repetition.partialLeftFactor`, `OAI.UniqueGames.Foundations.Repetition.partialRightFactor`, `OAI.UniqueGames.Foundations.Repetition.revealLeftFactor`, `OAI.UniqueGames.Foundations.Repetition.revealRightFactor`, `OAI.UniqueGames.Foundations.Repetition.selectedCompletionScale`, `OAI.UniqueGames.Foundations.Repetition.selectedFullCompletionMixture`, `OAI.UniqueGames.Foundations.Repetition.selectedFullLeftCompletion`, `OAI.UniqueGames.Foundations.Repetition.selectedFullRightCompletion`, `OAI.UniqueGames.Foundations.Repetition.selectedLeftCompletion`, `OAI.UniqueGames.Foundations.Repetition.selectedLeftRaw`, `OAI.UniqueGames.Foundations.Repetition.selectedRightCompletion`, `OAI.UniqueGames.Foundations.Repetition.selectedRightRaw`, `OAI.UniqueGames.Foundations.Repetition.selectedSamplingTarget`, `OAI.UniqueGames.Foundations.Repetition.updatedTableFallback`, `OAI.VertexCover.ClauseProjection.baseReduction`, `OAI.VertexCover.ClauseProjection.binaryReduction`, `OAI.VertexCover.ClauseProjection.reduction`, `OAI.VertexCover.ClauseProjection.repetitionLength`, `OAI.VertexCover.LabelCover.asGame`, `OAI.VertexCover.LabelCover.asGameValue`, `OAI.VertexCover.LabelCover.occurrenceLaw`, `OAI.VertexCover.Machine.AlphabetMachine.State`, `OAI.VertexCover.Machine.AlphabetMachine.addressesPoly`, `OAI.VertexCover.Machine.AlphabetMachine.code`, `OAI.VertexCover.Machine.AlphabetMachine.dartsPoly`, `OAI.VertexCover.Machine.AlphabetMachine.eventsPoly`, `OAI.VertexCover.Machine.AlphabetMachine.head`, `OAI.VertexCover.Machine.AlphabetMachine.headPoly`, `OAI.VertexCover.Machine.AlphabetMachine.indexPoly`, `OAI.VertexCover.Machine.AlphabetMachine.localPoly`, `OAI.VertexCover.Machine.AlphabetMachine.localRelationPoly`, `OAI.VertexCover.Machine.AlphabetMachine.localReversePoly`, `OAI.VertexCover.Machine.AlphabetMachine.localRow`, `OAI.VertexCover.Machine.AlphabetMachine.localTailPoly`, `OAI.VertexCover.Machine.AlphabetMachine.loopPoly`, `OAI.VertexCover.Machine.AlphabetMachine.old`, `OAI.VertexCover.Machine.AlphabetMachine.oldPoly`, `OAI.VertexCover.Machine.AlphabetMachine.poly`, `OAI.VertexCover.Machine.AlphabetMachine.queryPoly`, `OAI.VertexCover.Machine.AlphabetMachine.queryRank` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Analysis_BaseReductionCoherent`, `VertexCover_Analysis_PowerValueRepetition`, `VertexCover_Machines_Alphabet`, `VertexCover_Machines_AlphabetCorrect`, `VertexCover_Machines_AlphabetFrame`, `VertexCover_Machines_AlphabetRow`, `VertexCover_Machines_CloudFamily`, `VertexCover_Machines_FinalCNF`, `VertexCover_Machines_FinalCNFCorrect`, `VertexCover_Machines_Generic`, `VertexCover_Machines_InitialCorrect`, `VertexCover_Machines_InitialTable`, `VertexCover_Machines_Iteration`, `VertexCover_Machines_NatPath`, `VertexCover_Machines_Power`, `VertexCover_Machines_PowerRow`, `VertexCover_Machines_Preprocess`, `VertexCover_Machines_Regular`, `VertexCover_Machines_RegularRow`, `VertexCover_Machines_Round`, `VertexCover_Machines_SimpleLC`, `VertexCover_Main`, `VertexCover_Reduction_ReductionSound`, `VertexCover_Reduction_Soundness`, `VertexCover_Repetition_Holenstein`, `VertexCover_Repetition_MaskedVariation`, `VertexCover_Repetition_PartialReveal`, `VertexCover_Repetition_Reveal`, `VertexCover_Repetition_RevealFactorization`, `VertexCover_Repetition_RightProfileBounds`, `VertexCover_Repetition_SelectedCompletion`, `VertexCover_Repetition_SelectedCompletionGame`, `VertexCover_Repetition_SelectedInformation`, `VertexCover_Repetition_SelectedLikelihood`, `VertexCover_Repetition_SelectedMarginal`, `VertexCover_Repetition_SelectedProfileBudget`, `VertexCover_Repetition_SelectedProfiles`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`; the bundles `OAIQ028V006` and `OAIQ028V007` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.VertexCover.every_fixed_factor_below_two` and `OAI.VertexCover.explicit_cover_gap`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover
import Definitions.Def_OAIQ028V006
import Definitions.Def_OAIQ028V007

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Reveal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealInputLaw_inr (μ : FiniteDistribution (X × Y)) (y : Y) :
    (revealInputLaw μ).weight (Sum.inr y) = (∑ x, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight, div_eq_mul_inv, ← Finset.sum_mul]

theorem revealProfile_inr_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inr y)).weight (x,y) =
      conditionalKernel (μ.transport (Equiv.prodComm X Y)).weight
        (μ.pushforward Prod.fst).weight y x := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inr y) =
      firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inr]
    rfl
  have hf : (revealFallback μ (Sum.inr y)).weight (x,y) =
      (μ.pushforward Prod.fst).weight x := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1 = x <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y = 0
  · simpa [h] using hf
  · have hh : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 ≠ 0 :=
      div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, Sum.inr_ne_inl, ite_false, zero_add]
    change (μ.weight (x,y) / 2) / (firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2) =
      μ.weight (x,y) / firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y
    field_simp

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_MaskedVariation
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

theorem masked_totalVariation_identity (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) =
      Information.totalVariation p (leftRevealModel μ p) +
        Information.totalVariation p (rightRevealModel μ p) := by
  have hleft (s : S) :
      (∑ u : X, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) =
      (∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 := by
    simp_rw [Fintype.sum_prod_type, abs_masked_inl]
    simp [Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]
  have hright (s : S) :
      (∑ v : Y, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
      (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2 := by
    have hcollapse :
        (∑ v : Y, ∑ q : X × Y,
          |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
        ∑ v : Y, ∑ x : X, |p (s, (x, v)) - rightRevealModel μ p (s, (x, v))| / 2 := by
      simp [Fintype.sum_prod_type, abs_masked_inr]
    rw [hcollapse, Finset.sum_comm]
    simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul]
  have hmass :
      (∑ z : (S × (X ⊕ Y)) × (X × Y), |maskedJoint p z - maskedModel μ p z|) =
      ((∑ z : S × (X × Y), |p z - leftRevealModel μ p z|) +
       (∑ z : S × (X × Y), |p z - rightRevealModel μ p z|)) / 2 := by
    calc
      _ = ∑ s : S,
          ((∑ u : X, ∑ q : X × Y, |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) +
           (∑ v : Y, ∑ q : X × Y, |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
      _ = ∑ s : S,
          ((∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 +
           (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2) := by
        simp_rw [hleft, hright]
      _ = _ := by
        simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  unfold Information.totalVariation
  rw [hmass]
  ring

theorem leftRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (leftRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (rightRevealModel μ p)]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_PartialReveal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem leftReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (leftRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact leftRevealModel_totalVariation_le μ _

theorem rightReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (rightRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact rightRevealModel_totalVariation_le μ _

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedInformation
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) ≤ 1 := by
  rw [selectedLikelihood_sum]
  split <;> norm_num

theorem selected_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected}, totalVariation
      (fun tva : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) × (Q₁ × Q₂) =>
        selectedSideWeight G strategy selected tva.1 * coordinateMarginal
          (posteriorOrOriginal
            (independentProduct (fun j => (selectedInputProfile G selected tva.1.1 j).weight))
            (selectedLikelihood G strategy selected tva.1.1.1 tva.1.2)
            (selectedSideMass G strategy selected tva.1)) i tva.2)
      (fun tva => selectedSideWeight G strategy selected tva.1 *
        (selectedInputProfile G selected tva.1.1 i).weight tva.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  exact finite_side_information_bound (selectedInputLaw G selected).weight
    (fun t i => (selectedInputProfile G selected t i).weight)
    (fun tv => selectedLikelihood G strategy selected tv.1.1 tv.2)
    (selectedSideMass G strategy selected) (selectedSideWeight G strategy selected)
    (gameLaw_isProbability _) (fun t i => gameLaw_isProbability _)
    (fun tv => selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (fun t => selectedLikelihood_sum_le_one G strategy selected t.1)
    (fun _ => rfl) positive (selectedSideMass_total G strategy selected) (fun _ => rfl)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedMarginal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedPosterior_eq_raw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) (q) :
    selectedSideWeight G strategy selected tv * coordinateMarginal
      (posteriorOrOriginal
        (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
        (selectedLikelihood G strategy selected tv.1.1 tv.2)
        (selectedSideMass G strategy selected tv)) j q =
      selectedRawMarginal G strategy selected j (tv,q) := by
  classical
  rw [selectedSideWeight]
  have h := weighted_coordinate_posterior_recombine
    (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
    (selectedLikelihood G strategy selected tv.1.1 tv.2)
    (independentProduct_isProbability _
      (fun i => gameLaw_isProbability (selectedInputProfile G selected tv.1 i)))
    (selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    («c» := selectedSideMass G strategy selected tv) rfl
    ((selectedInputLaw G selected).weight tv.1) (G.selectedSuccess strategy selected) j q
  rw [h]
  simp only [Finset.mul_sum, selectedRawMarginal, selectedJointWeight]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = q
  · simp only [ite_eq_left hu]
    ring
  · simp [hu]

theorem selected_raw_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, totalVariation
      (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_information_bound G strategy selected positive
  simp_rw [selectedPosterior_eq_raw] at h
  exact h

theorem selectedRawReference_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    (fun w => selectedSideWeight G strategy selected w.1 *
      (selectedInputProfile G selected w.1.1 j).weight w.2)
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  change selectedSideWeight G strategy selected ((z.1.1.1,z.1.2),z.1.1.2) *
    (revealProfile G.questions (z.1.2 j)).weight z.2 = _
  rw [← selectedRawMarginal_firstMarginal G strategy selected j]
  unfold firstMarginal fullRevealModel
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact selectedRawMarginal_fullReveal G strategy selected j (z.1,q)

theorem selected_raw_error_eq_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2) =
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
  rw [← totalVariation_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm]
  congr 1 <;> funext z
  · exact selectedRawMarginal_fullReveal G strategy selected j z
  · exact selectedRawReference_fullReveal G strategy selected j z

theorem selected_fullReveal_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected))) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_raw_information_bound G strategy selected positive
  simp_rw [selected_raw_error_eq_fullReveal] at h
  exact h

theorem selected_leftReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact leftReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

theorem selected_rightReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rightReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_RevealFactorization
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

theorem revealLaw_factorization (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) (y : Y) :
    (revealLaw μ).weight ((x,y),r) =
      revealLeftFactor μ r x * revealRightFactor μ r y := by
  rw [revealLaw_weight]
  cases r with
  | inl u =>
    by_cases h : x = u
    · subst x; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]
  | inr v =>
    by_cases h : y = v
    · subst y; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

theorem partialRevealWeight_factorization (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    partialRevealWeight μ j rest u =
      μ.weight (u j) * partialLeftFactor μ j rest (fun i => (u i).1) *
        partialRightFactor μ j rest (fun i => (u i).2) := by
  have hpoint (i : {i : I // i ≠ j}) :
      (revealLaw μ).weight (u i.1,rest i) =
        revealLeftFactor μ (rest i) (u i.1).1 * revealRightFactor μ (rest i) (u i.1).2 :=
    revealLaw_factorization μ (rest i) (u i.1).1 (u i.1).2
  simp only [partialRevealWeight, partialLeftFactor, partialRightFactor,
    hpoint, Finset.prod_mul_distrib]
  ring

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedLikelihood
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
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

namespace UniqueGames.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedWins_of_answerLabel (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂)
    (hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label) :
    G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining) =
      selectedLabelAccepts G selected fixed label := by
  classical
  have hleft (i : selected) := congrArg (fun l => l.1 i) hlabel
  have hright (i : selected) := congrArg (fun l => l.2 i) hlabel
  apply Bool.eq_iff_iff.mpr
  simp only [Game.selectedWins, selectedLabelAccepts, decide_eq_true_eq]
  constructor
  · intro h i
    have hi := h i.1 i.property
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, i.property,
      ← hleft i, ← hright i, selectedAnswerLabel] using hi
  · intro h i hi
    have hv := h ⟨i,hi⟩
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, hi,
      ← hleft ⟨i,hi⟩, ← hright ⟨i,hi⟩, selectedAnswerLabel] using hv

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    selectedLikelihood G strategy selected fixed label remaining =
      (if selectedLabelAccepts G selected fixed label then 1 else 0) *
        selectedLocalTest strategy.1 selected (fun i => (fixed i).1) label.1 (fun i => (remaining i).1) *
        selectedLocalTest strategy.2 selected (fun i => (fixed i).2) label.2 (fun i => (remaining i).2) := by
  classical
  have he : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) =
      (selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1) (fun i => (remaining i).1),
       selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2) (fun i => (remaining i).2)) := by
    simp only [selectedAnswerLabel,
      selectedQuestionTuple_left, selectedQuestionTuple_right]
    rfl
  by_cases hl : selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1)
      (fun i => (remaining i).1) = label.1
  · by_cases hr : selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2)
        (fun i => (remaining i).2) = label.2
    · have hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label := by
        rw [he, hl, hr]
      simp only [selectedLikelihood, ite_eq_left hlabel,
        selectedWins_of_answerLabel G strategy selected fixed label remaining hlabel,
        selectedLocalTest, ite_eq_left hl, ite_eq_left hr, mul_one]
    · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
        intro h
        rw [he] at h
        exact hr (congrArg Prod.snd h)
      simp [selectedLikelihood, hn, selectedLocalTest, hl, hr]
  · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
      intro h
      rw [he] at h
      exact hl (congrArg Prod.fst h)
    simp [selectedLikelihood, hn, selectedLocalTest, hl]

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCompletion
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
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

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def updatedTableFallback (μ : FiniteDistribution X) (j : I) (x : X) :
    FiniteDistribution (I → X) :=
  (FiniteDistribution.table (fun _ : I => μ)).pushforward
    (fun l => Function.update l j x)

theorem updatedTableFallback_zero (μ : FiniteDistribution X) (j : I) (x : X)
    (l : I → X) (hne : l j ≠ x) :
    (updatedTableFallback μ j x).weight l = 0 := by
  classical
  simp only [updatedTableFallback, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro h
  have he := congrFun h j
  exact hne (by simpa only [Function.update_self] using he.symm)

theorem normalizeOr_weight_eq_zero_of_zero
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (fallback : FiniteDistribution X)
    (x : X) (hraw : w x = 0) (hdefault : fallback.weight x = 0) :
    (normalizeOr w hw fallback).weight x = 0 := by
  classical
  unfold normalizeOr
  split
  · change normalizedWeight w x = 0
    simp only [normalizedWeight, hraw, zero_div]
  · exact hdefault

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLeftRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) : ℝ :=
  (if l j = x then 1 else 0) * partialLeftFactor G.questions j s.2 l *
    selectedLocalTest strategy.1 selected (fun i => (s.1.1 i).1) s.1.2.1 l

def selectedRightRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) : ℝ :=
  (if r j = y then 1 else 0) * partialRightFactor G.questions j s.2 r *
    selectedLocalTest strategy.2 selected (fun i => (s.1.1 i).2) s.1.2.2 r

omit [DecidableEq Q₂] in
theorem selectedLeftRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) :
    0 ≤ selectedLeftRaw G strategy selected j s x l := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealLeftFactor_nonnegative G.questions (s.2 i) (l i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

omit [DecidableEq Q₁] in
theorem selectedRightRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) :
    0 ≤ selectedRightRaw G strategy selected j s y r := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealRightFactor_nonnegative G.questions (s.2 i) (r i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

def selectedLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₁) :=
  normalizeOr (selectedLeftRaw G strategy selected j s x)
    (selectedLeftRaw_nonnegative G strategy selected j s x)
    (updatedTableFallback (G.questions.pushforward Prod.fst) j x)

def selectedRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₂) :=
  normalizeOr (selectedRightRaw G strategy selected j s y)
    (selectedRightRaw_nonnegative G strategy selected j s y)
    (updatedTableFallback (G.questions.pushforward Prod.snd) j y)

omit [DecidableEq Q₂] in
theorem selectedLeftCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) (hne : l j ≠ x) :
    (selectedLeftCompletion G strategy selected j s x).weight l = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedLeftRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j x l hne

omit [DecidableEq Q₁] in
theorem selectedRightCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) (hne : r j ≠ y) :
    (selectedRightCompletion G strategy selected j s y).weight r = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedRightRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j y r hne

def selectedCompletionScale (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) : ℝ :=
  G.questions.weight xy * (∏ i : selected, G.questions.weight (s.1.1 i)) *
    (if selectedLabelAccepts G selected s.1.1 s.1.2 then 1 else 0) /
      G.selectedSuccess strategy selected

theorem selected_completion_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r =
      if (l j, r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rcases xy with ⟨x,y⟩
  by_cases hl : l j = x <;> by_cases hr : r j = y
  · rw [ite_eq_left (Prod.ext hl hr), partialRevealWeight_factorization]
    cases hacc : selectedLabelAccepts G selected s.1.1 s.1.2 <;>
      simp [selectedOutsideLikelihood, selectedLikelihood_factorization,
        selectedCompletionScale, selectedLeftRaw, selectedRightRaw, hl, hr, hacc] ; ring
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]

theorem selectedCommonLaw_completion_row_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) =
      ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) ×
          ({i : Fin n // i ∉ selected} → Q₂),
        selectedCompletionScale G strategy selected j s xy *
          selectedLeftRaw G strategy selected j s xy.1 lr.1 *
          selectedRightRaw G strategy selected j s xy.2 lr.2 := by
  classical
  change (∑ u, if u j = xy then partialRevealWeight G.questions j s.2 u *
    selectedOutsideLikelihood G strategy selected s.1 u else 0) = _
  rw [← (completionTupleEquiv (I := {i : Fin n // i ∉ selected})
    (X := Q₁) (Y := Q₂)).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  exact (selected_completion_factorization G strategy selected j s xy
    (fun i => (u i).1) (fun i => (u i).2)).symm

theorem selected_completion_row_recombine (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight (l,r) =
      if (l j,r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rw [selectedCommonLaw_completion_row_mass]
  calc
    _ = selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r :=
      factorized_completion_row
        (selectedLeftRaw G strategy selected j s xy.1)
        (selectedRightRaw G strategy selected j s xy.2)
        (selectedLeftRaw_nonnegative G strategy selected j s xy.1)
        (selectedRightRaw_nonnegative G strategy selected j s xy.2)
        (updatedTableFallback (G.questions.pushforward Prod.fst) j xy.1)
        (updatedTableFallback (G.questions.pushforward Prod.snd) j xy.2)
        (selectedCompletionScale G strategy selected j s xy) (l,r)
    _ = _ := selected_completion_factorization G strategy selected j s xy l r

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCompletionGame
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

theorem partialRevealWeight_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (u : I → X × Y) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y, partialRevealWeight μ j rest u) =
      ∏ i, μ.weight (u i) := by
  have h := reveal_product_forget μ (fun i : {i : I // i ≠ j} => u i.1)
  simp_rw [reveal_product_factorization] at h
  simp only [partialRevealWeight, ← Finset.mul_sum]
  rw [h]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ.weight (u i)) j).symm

theorem partialReveal_event_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (f : (I → X × Y) → ℝ) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y,
      ∑ u : I → X × Y, partialRevealWeight μ j rest u * f u) =
      ∑ u, (∏ i, μ.weight (u i)) * f u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, partialRevealWeight_forget]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedOutsideLikelihood_event_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (∏ i, G.questions.weight (u i)) * selectedOutsideLikelihood G strategy selected t u *
          (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  classical
  have hlabel (fixed : selected → Q₁ × Q₂)
      (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
      (∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (∏ i, G.questions.weight (u i)) *
          selectedOutsideLikelihood G strategy selected (fixed,label) u *
            (if event (selectedQuestionTuple selected fixed u) then 1 else 0)) =
      ((∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
            G.selectedSuccess strategy selected := by
    calc
      _ = (∏ i, G.questions.weight (u i)) *
          (∏ i : selected, G.questions.weight (fixed i)) *
          (∑ label, selectedLikelihood G strategy selected fixed label u) *
          (if event (selectedQuestionTuple selected fixed u) then 1 else 0) /
            G.selectedSuccess strategy selected := by
        simp only [selectedOutsideLikelihood, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label _
        ring
      _ = _ := by
        rw [selectedLikelihood_sum]
        cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) <;>
          cases he : event (selectedQuestionTuple selected fixed u) <;> simp [] ; ring
  calc
    _ = ∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          ∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
            (∏ i, G.questions.weight (u i)) *
              selectedOutsideLikelihood G strategy selected (fixed,label) u *
                (if event (selectedQuestionTuple selected fixed u) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.sum_comm]
    _ = (∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          (∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
            (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
              event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
                G.selectedSuccess strategy selected := by
      simp_rw [hlabel]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      congr 1
      have h := selectedSplit_question_probability G selected
        (fun q => G.selectedWins strategy selected q && event q)
      simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
        FiniteDistribution.table, Fintype.sum_prod_type, mul_ite] using h

theorem selected_partial_event_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  have hrest (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) :=
    partialReveal_event_forget G.questions j
      (fun u => selectedOutsideLikelihood G strategy selected t u *
        (if event (selectedQuestionTuple selected t.1 u) then 1 else 0))
  simp only [← mul_assoc] at hrest
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  exact selectedOutsideLikelihood_event_sum G strategy selected event

def selectedFullLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₁) :=
  (selectedLeftCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).1))

def selectedFullRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₂) :=
  (selectedRightCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).2))

omit [DecidableEq Q₂] in
theorem selectedFullLeftCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (l : Fin n → Q₁) (h : (selectedFullLeftCompletion G strategy selected j q).weight l ≠ 0) :
    l j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullLeftCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedLeftCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

omit [DecidableEq Q₁] in
theorem selectedFullRightCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (r : Fin n → Q₂) (h : (selectedFullRightCompletion G strategy selected j q).weight r ≠ 0) :
    r j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullRightCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedRightCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

theorem selected_full_completion_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
      (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event =
    ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight lr *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)))
            then 1 else 0) := by
  rw [selectedFullLeftCompletion, selectedFullRightCompletion,
    ← FiniteDistribution.product_pushforward, FiniteDistribution.probability_pushforward]
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro lr _
  have he : selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)) =
      (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
       mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) :=
    Prod.ext (selectedQuestionTuple_left selected s.1.1 _)
      (selectedQuestionTuple_right selected s.1.1 _)
  rw [he]
  cases hevent : event (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
    mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) <;> simp [hevent]

theorem selected_completion_event_row (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ xy : Q₁ × Q₂, (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
        (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event) =
    ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
      partialRevealWeight G.questions j s.2 u *
        selectedOutsideLikelihood G strategy selected s.1 u *
          (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
  classical
  have hpoint (xy : Q₁ × Q₂)
      (lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂)) :
      (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
        ((selectedLeftCompletion G strategy selected j s xy.1).product
          (selectedRightCompletion G strategy selected j s xy.2)).weight lr =
      if (lr.1 j,lr.2 j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0 :=
    selected_completion_row_recombine G strategy selected positive j s xy lr.1 lr.2
  simp_rw [selected_full_completion_probability, Finset.mul_sum, ← mul_assoc,
    hpoint]
  have hsum (xy : Q₁ × Q₂) :
      (∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
        (if (lr.1 j,lr.2 j) = xy then
          partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
            selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0) *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i))) then 1 else 0)) =
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (if u j = xy then partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u else 0) *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
    exact ((completionTupleEquiv (I := {i : Fin n // i ∉ selected})
      (X := Q₁) (Y := Q₂)).sum_comp _).symm
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul]
  simp

def selectedFullCompletionMixture (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)) :=
  ((selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)).mixture
    (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
      (selectedFullRightCompletion G strategy selected j (z.1.2,z.2)))

theorem selectedFullCompletionMixture_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedFullCompletionMixture G strategy selected positive j).probability event =
      ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability event := by
  erw [FiniteDistribution.probability_condition]
  rw [selectedFullCompletionMixture, FiniteDistribution.probability_mixture]
  simp only [FiniteDistribution.transport]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          partialRevealWeight G.questions j s.2 u *
            selectedOutsideLikelihood G strategy selected s.1 u *
              (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      exact selected_completion_event_row G strategy selected positive j s event
    _ = _ := selected_partial_event_total G strategy selected j event

theorem selectedFullCompletionMixture_eq_conditionedQuestions (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedFullCompletionMixture G strategy selected positive j =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  exact selectedFullCompletionMixture_probability G strategy selected positive j _

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_RightProfileBounds
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedProfiles
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedProfileBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

theorem selectedLeftProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedLeftProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedLeftProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hleft := selected_leftReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Holenstein
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

theorem holenstein_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).value ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  apply ((G.repetition n).value_le_iff _).2
  intro strategy
  exact holenstein_repetition_success G n strategy hvalue hv hell halphabet

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BaseReductionCoherent
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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
open Target

theorem failureCount_eq_sum (F : Formula) (a : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    PCP.failureCount F a indices =
      (indices.map (fun i => if (F.clauses.get i).eval a = false then 1 else 0)).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [PCP.failureCount, List.map_cons, List.sum_cons, ih]
      congr 1
      unfold PCP.clauseFailure PCP.clauseAt
      change (if (F.clauses.get i).eval a = true then 0 else 1) = _
      cases (F.clauses.get i).eval a <;> rfl

theorem failureCount_all (F : Formula) (a : Fin F.«variables» → Bool) :
    PCP.failureCount F a (PCP.allIndices F) = (unsatisfiedClauses F a).card := by
  rw [failureCount_eq_sum]
  simp only [PCP.allIndices, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  exact (Finset.card_filter _ _).symm

theorem simple_value_le (F : Formula) (η : ℚ) (hgap : Hastad.SourceGap.ClauseGap F η) :
    (simpleGame F hgap.1).value ≤ 1 - (η : ℝ) / 3 := by
  classical
  apply LabelCover.value_le_of_counts
  intro A
  have hbad := hgap.2 (assignmentOf F hgap.1 (decodedLabeling F hgap.1 A))
  rw [failureCount_all] at hbad
  have hreject := simple_rejection_count F hgap.1 A
  have hrejectR := Nat.cast_le (α := ℝ) |>.mpr hreject
  have hpart := Finset.card_filter_add_card_filter_not ((simpleGame F hgap.1).Satisfies A)
    (s := Finset.univ)
  have hpartR : ((simpleGame F hgap.1).satisfiedCount A : ℝ) +
      ((Finset.univ.filter (fun e => ¬(simpleGame F hgap.1).Satisfies A e)).card : ℝ) =
      (F.clauses.length : ℝ) * 3 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hpart
    change (simpleGame F hgap.1).satisfiedCount A + _ = F.clauses.length * 3 at hpart
    exact_mod_cast hpart
  change ((simpleGame F hgap.1).satisfiedCount A : ℝ) ≤
    (1 - (η : ℝ) / 3) * ((F.clauses.length * 3 : ℕ) : ℝ)
  push_cast
  nlinarith

noncomputable def baseReduction (F : Formula) : LabelCover :=
  simpleGame (PCP.TableIteration.gapMap fixedBaseTable F)
    (PCP.TableIteration.gapMap_nonempty fixedBaseTable F)

theorem baseReduction_complete (F : Formula) (hF : F.Satisfiable) :
    ∃ A : (baseReduction F).Labeling, ∀ e, (baseReduction F).Satisfies A e :=
  simple_perfect_complete _ _ (PCP.TableIteration.gapMap_completeness fixedBaseTable F hF)

theorem baseReduction_sound (F : Formula) (hF : ¬F.Satisfiable) :
    (baseReduction F).value ≤ 1 - (PCP.PCPIteration.finalClauseGap : ℝ) / 3 :=
  simple_value_le _ _ (PCP.TableGapReduction.gapMap_clauseGap fixedBaseTable
    fixedBaseTable_certificate F hF)

theorem baseReduction_coherent (F : Formula) : (baseReduction F).ParallelCoherent :=
  simple_parallel _ _

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

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PowerValueRepetition
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.encode_u _root_.OAI.VertexCover.LabelCover.Query.encode_v _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_profileLabels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.mem_privateFiber _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
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
namespace VertexCover.LabelCover
open UniqueGames.Foundations.Games
noncomputable section

def occurrenceLaw (Φ : LabelCover) : FiniteDistribution (Fin Φ.M) := by
  letI : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  exact FiniteDistribution.uniform (Fin Φ.M)

def asGame (Φ : LabelCover) : Game (Fin Φ.u) (Fin Φ.v) (Fin Φ.qU) (Fin Φ.qV) :=
  { questions := Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))
    accepts := fun x y a b => decide (Φ.questionProjection x y a = b) }

theorem asGame_success (Φ : LabelCover) (hc : Φ.ParallelCoherent) (A : Φ.Labeling) :
    Φ.asGame.success A = (Φ.satisfiedCount A : ℝ) / Φ.M := by
  classical
  change (Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Game.wins, asGame, questionProjection_at Φ hc,
    decide_eq_true_eq]
  simp only [occurrenceLaw, FiniteDistribution.uniform, Fintype.card_fin]
  change (∑ e, if Φ.Satisfies A e then 1 / (Φ.M : ℝ) else 0) = _
  calc
    _ = (∑ e, (if Φ.Satisfies A e then 1 else 0 : ℝ)) / Φ.M := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_boole]; rfl

def asGameValue (Φ : LabelCover) : ℝ := by
  letI : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  letI : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  exact Φ.asGame.value

theorem asGameValue_eq (Φ : LabelCover) (hc : Φ.ParallelCoherent) : Φ.asGameValue = Φ.value := by
  classical
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  change Φ.asGame.value = Φ.value
  apply le_antisymm
  · apply (Φ.asGame.value_le_iff _).mpr
    intro A
    rw [asGame_success Φ hc A]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Φ.satisfiedCount_le_max A)) (by positivity)
  · apply value_le_of_counts
    intro A
    have hs := Φ.asGame.success_le_value A
    rw [asGame_success Φ hc A] at hs
    exact (div_le_iff₀ (Nat.cast_pos.mpr Φ.M_pos)).mp hs

theorem repetition_success_probability (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ)
    (B : Strategy (Fin n → Fin Φ.u) (Fin n → Fin Φ.v)
      (Fin n → Fin Φ.qU) (Fin n → Fin Φ.qV)) :
    (Φ.asGame.repetition n).success B = (Φ.occurrenceLaw.iid n).probability
      (fun es => decide (∀ i, Φ.projection (es i)
        (B.1 (fun j => Φ.left (es j)) i) = B.2 (fun j => Φ.right (es j)) i)) := by
  classical
  unfold Game.success
  change (((Φ.occurrenceLaw.pushforward (fun e => (Φ.left e, Φ.right e))).iid n).transport
    (Game.tupleQuestionEquiv n)).probability _ = _
  rw [FiniteDistribution.probability_transport, FiniteDistribution.iid_pushforward,
    FiniteDistribution.probability_pushforward]
  congr 1
  funext es
  simp only [Game.wins, Game.repetition, Game.tupleQuestionEquiv, asGame,
    Equiv.coe_fn_mk, questionProjection_at Φ hc, decide_eq_true_eq]

theorem repetition_success (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ)
    (A : (Φ.parallelPower n).Labeling) :
    (Φ.asGame.repetition n).success (Φ.repeatedStrategy n A) =
      ((Φ.parallelPower n).satisfiedCount A : ℝ) / (Φ.M ^ n : ℕ) := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  rw [repetition_success_probability Φ hc]
  have hlaw : Φ.occurrenceLaw.iid n = FiniteDistribution.uniform (Fin n → Fin Φ.M) :=
    FiniteDistribution.iid_uniform n
  rw [hlaw]
  simp only [← power_satisfies_iff Φ n A, FiniteDistribution.probability,
    FiniteDistribution.uniform, Fintype.card_fun, Fintype.card_fin, decide_eq_true_eq]
  calc
    _ = ∑ e : Fin (Φ.M ^ n), if (Φ.parallelPower n).Satisfies A e then
        1 / ((Φ.M ^ n : ℕ) : ℝ) else 0 :=
      Fintype.sum_equiv (tupleEquiv Φ.M n) _ _ (fun _ => rfl)
    _ = (∑ e : Fin (Φ.M ^ n), (if (Φ.parallelPower n).Satisfies A e then 1 else 0 : ℝ)) /
        (Φ.M ^ n : ℕ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = _ := by
      have hsum : (∑ e : Fin (Φ.parallelPower n).M,
          (@ite ℝ ((Φ.parallelPower n).Satisfies A e) (Classical.propDecidable _) 1 0)) =
          ((Φ.parallelPower n).satisfiedCount A : ℝ) := by
        rw [satisfiedCount, Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : (Φ.parallelPower n).Satisfies A e <;> simp only [h, ite_true, ite_false, Nat.cast_zero, Nat.cast_one]
      exact congrArg (fun x : ℝ => x / ((Φ.M ^ n : ℕ) : ℝ)) hsum

theorem power_value_le_repetition (Φ : LabelCover) (hc : Φ.ParallelCoherent) (n : ℕ) :
    (Φ.parallelPower n).value ≤
      (letI : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩;
       letI : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩;
       (Φ.asGame.repetition n).value) := by
  classical
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  apply value_le_of_counts
  intro A
  have hs := (Φ.asGame.repetition n).success_le_value (Φ.repeatedStrategy n A)
  rw [repetition_success Φ hc] at hs
  exact (div_le_iff₀ (Nat.cast_pos.mpr (pow_pos Φ.M_pos n))).mp hs

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ReductionSound
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.encode_u _root_.OAI.VertexCover.LabelCover.Query.encode_v _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_profileLabels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.mem_privateFiber _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
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
open LabelCover
noncomputable section

theorem baseGap_le_third : baseGap ≤ 1/3 := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast PCP.TableGapReduction.finalClauseGap_le_one) (by norm_num)

theorem repetitionBase_mem : 0 < repetitionBase ∧ repetitionBase < 1 := by
  have hp := baseGap_pos
  have hu := baseGap_le_third
  have hc : baseGap ^ 3 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^3 := pow_le_pow_left₀ hp.le (by linarith) 3
      _ = 1 := by norm_num
  constructor
  · unfold repetitionBase; linarith
  · unfold repetitionBase; have : 0 < baseGap^3 / 6000 := by positivity
    linarith

theorem exists_repetition_length (σ : ℝ) (hσ : 0 < σ) :
    ∃ n : ℕ, repetitionBase ^ ((n : ℝ) / repetitionAlphabetBudget) < σ := by
  have hr := Real.rpow_lt_one repetitionBase_mem.1.le repetitionBase_mem.2
    (one_div_pos.mpr repetitionAlphabetBudget_pos)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hσ hr
  refine ⟨n, ?_⟩
  have he : (n : ℝ) / repetitionAlphabetBudget =
      (1 / repetitionAlphabetBudget) * (n : ℝ) := by ring
  rw [he, Real.rpow_mul repetitionBase_mem.1.le, Real.rpow_natCast]
  exact hn

def repetitionLength (σ : ℝ) (hσ : 0 < σ) : ℕ :=
  (exists_repetition_length σ hσ).choose

def reduction (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula) : LabelCover :=
  (baseReduction F).parallelPower (repetitionLength σ hσ)

theorem reduction_complete (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula)
    (hF : F.Satisfiable) :
    ∃ A : (reduction σ hσ F).Labeling, ∀ e, (reduction σ hσ F).Satisfies A e := by
  obtain ⟨A, hA⟩ := baseReduction_complete F hF
  exact ⟨_, LabelCover.repeat_perfect _ _ A hA⟩

theorem reduction_sound (σ : ℝ) (hσ : 0 < σ) (F : Target.Formula)
    (hF : ¬F.Satisfiable) : (reduction σ hσ F).value < σ := by
  let Φ := baseReduction F
  let n := repetitionLength σ hσ
  let : Nonempty (Fin Φ.qU) := ⟨⟨0, Φ.qU_pos⟩⟩
  let : Nonempty (Fin Φ.qV) := ⟨⟨0, Φ.qV_pos⟩⟩
  have hv : Φ.asGame.value ≤ 1 - baseGap := by
    change Φ.asGameValue ≤ 1 - baseGap
    rw [LabelCover.asGameValue_eq Φ (baseReduction_coherent F)]
    exact baseReduction_sound F hF
  have hb := Repetition.holenstein_repetition_value Φ.asGame n hv
    (by have := baseGap_pos; linarith : 1 - baseGap < 1)
    (le_max_left 1 (Repetition.logTwo 14))
    (show Repetition.logTwo ((Fintype.card (Fin Φ.qU) : ℝ) *
        (Fintype.card (Fin Φ.qV) : ℝ)) ≤ repetitionAlphabetBudget from by
      change Repetition.logTwo ((7 : ℝ) * 2) ≤ repetitionAlphabetBudget
      norm_num only [show (7 : ℝ) * 2 = 14 by norm_num]
      exact le_max_right _ _)
  have he : 1 - (1 - (1 - baseGap)) ^ 3 / 6000 = repetitionBase := by
    unfold repetitionBase; ring
  rw [he] at hb
  exact lt_of_le_of_lt ((LabelCover.power_value_le_repetition Φ
    (baseReduction_coherent F) n).trans hb)
    (exists_repetition_length σ hσ).choose_spec

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

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_Soundness
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
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
open UniqueGames
noncomputable section

def binaryReduction (σ : ℝ) (hσ : 0 < σ) (input : List Bool) : VertexCover.LabelCover :=
  reduction σ hσ (BinaryFormula.dense (inputFormula input))

theorem binaryReduction_complete (σ : ℝ) (hσ : 0 < σ) (input : List Bool)
    (h : InputSAT input) :
    ∃ A : (binaryReduction σ hσ input).Labeling,
      ∀ e, (binaryReduction σ hσ input).Satisfies A e :=
  reduction_complete σ hσ _ (BinaryFormula.dense_completeness _ ((inputFormula_sat input).mpr h))

theorem binaryReduction_sound (σ : ℝ) (hσ : 0 < σ) (input : List Bool)
    (h : ¬InputSAT input) : (binaryReduction σ hσ input).value < σ := by
  apply reduction_sound
  intro hs
  exact h ((inputFormula_sat input).mp (BinaryFormula.dense_reflects _ hs))

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

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Generic
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

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace GenericMachine
open GenericGraphTables
def erase {q : ℕ} (T : Table q) : Data q := (T.vertices,T.rows.toList.map rowData)
def code {q : ℕ} (T : Table q) : List Bool := dataCode (erase T)

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Table.vertices :=
  (Poly.fst natBits (listBits rowCode)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)
noncomputable def rowsPoly {q : ℕ} : Poly (code (q := q)) (listBits rowCode) (fun T => T.rows.toList.map rowData) :=
  (Poly.snd natBits (listBits rowCode)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)
noncomputable def dartsPoly {q : ℕ} : Poly (code (q := q)) natBits Table.darts :=
  ((rowsPoly (q := q)).comp (Poly.listLength rowCode (rowDefault q))).congr (fun T => by simp)
noncomputable def lookupPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) rowCode
    (fun p : Table q × ℕ => (erase p.1).2.getD p.2 (rowDefault q)) := by
  let rows := (Poly.fst code natBits).comp (rowsPoly (q := q))
  let idx := Poly.snd (code (q := q)) natBits
  exact ((idx.pair rows).comp (Poly.listGetD rowCode (rowDefault q))).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD]
    rfl)
 theorem lookup_valid {q : ℕ} (T : Table q) (i : Fin T.darts) :
    (erase T).2.getD i.val (rowDefault q) = rowData T.rows[i] := by
  simp only [erase,List.getD_eq_getElem?_getD,List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp)]
  rfl

 theorem materialize_source {α : Type} {q : ℕ} (Q : α → Table q) (r : α × ℕ → Row q)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) (a : α) :
    ((Q a).vertices,(List.range (Q a).darts).map (fun i => r (a,i))) = erase (Q a) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [erase]
  · intro i h₁ h₂
    simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
    exact hr a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α) {q : ℕ}
    (Q : α → Table q) {r : α × ℕ → Row q}
    (cn : Poly ea natBits (fun a => (Q a).vertices))
    (cm : Poly ea natBits (fun a => (Q a).darts))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) :
    Poly ea code Q := by
  let rows := Poly.tabulate ea rowCode a₀ (rowDefault q) cm cr
  exact (cn.pair rows).encodeCongr id (fun _ => rfl) (fun a => by
    exact congrArg dataCode (materialize_source Q r hr a))
end GenericMachine

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_AlphabetFrame
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

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable
open Enumeration

abbrev State (q : ℕ) := GenericGraphTables.Table q × ℕ
def code {q : ℕ} : State q → List Bool := prodBits GenericMachine.code natBits
def old {q : ℕ} (s : State q) : GenericMachine.Row q := (GenericMachine.erase s.1).2.getD s.2 (GenericMachine.rowDefault q)
def head {q : ℕ} (s : State q) : ℕ :=
  ((GenericMachine.erase s.1).2.getD (old s).1.2 (GenericMachine.rowDefault q)).1.1
noncomputable def tablePoly {q : ℕ} : Poly (code (q := q)) GenericMachine.code Prod.fst := Poly.fst _ _
noncomputable def indexPoly {q : ℕ} : Poly (code (q := q)) natBits Prod.snd := Poly.snd _ _
noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => s.1.vertices) :=
  tablePoly.comp GenericMachine.verticesPoly
noncomputable def dartsPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => s.1.darts) :=
  tablePoly.comp GenericMachine.dartsPoly
noncomputable def oldPoly {q : ℕ} : Poly (code (q := q)) GenericMachine.rowCode old := GenericMachine.lookupPoly
noncomputable def tailPoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => (old s).1.1) :=
  oldPoly.comp ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.fst natBits natBits))
noncomputable def reversePoly {q : ℕ} : Poly (code (q := q)) natBits (fun s => (old s).1.2) :=
  oldPoly.comp ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.snd natBits natBits))
noncomputable def relationPoly {q : ℕ} : Poly (code (q := q)) GenericMachine.relationCode (fun s => (old s).2) :=
  oldPoly.comp (Poly.snd (prodBits natBits natBits) GenericMachine.relationCode)
noncomputable def headPoly {q : ℕ} : Poly (code (q := q)) natBits head :=
  ((tablePoly.pair reversePoly).comp GenericMachine.lookupPoly).comp
    ((Poly.fst (prodBits natBits natBits) GenericMachine.relationCode).comp (Poly.fst natBits natBits))
noncomputable def loopPoly {q : ℕ} : Poly (code (q := q)) boolBits (fun s => decide ((old s).1.1=head s)) :=
  (tailPoly.pair headPoly).comp Poly.natEq

end VertexCover.Machine.AlphabetMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_AlphabetRow
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable Enumeration

def queryRank {q : ℕ} (s : State q) : Queries.RawQuery q → ℕ
  | .inl (side,tape) => (if side then head s else (old s).1.1)*tapeCount q+(cubeEquiv q tape).val
  | .inr tape => s.1.vertices*tapeCount q + (s.2*pairTapeCount q+(pairCubeEquiv q tape).val)
noncomputable def queryRankPoly {q : ℕ} (r : Queries.RawQuery q) :
    Poly (code (q := q)) natBits (fun s => queryRank s r) := by
  cases r with
  | inl p =>
    let endpoint : Poly (code (q := q)) natBits (fun s => if p.1 then head s else (old s).1.1) :=
      if h : p.1 then headPoly.congr (by intro s; simp [h])
      else tailPoly.congr (by intro s; simp [h])
    exact (((endpoint.pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul).pair
      (Poly.const _ natBits (cubeEquiv q p.2).val)).comp Poly.natAdd
  | inr tape =>
    let v := ((verticesPoly (q := q)).pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul
    let e := ((indexPoly (q := q)).pair (Poly.const _ natBits (pairTapeCount q))).comp Poly.natMul
    exact (v.pair ((e.pair (Poly.const _ natBits (pairCubeEquiv q tape).val)).comp Poly.natAdd)).comp Poly.natAdd
noncomputable def queryPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s =>
      queryRank s (Queries.query (GenericGraphTables.relationAt (old s).2) l.1.1 l.1.2)) := by
  letI := relationFintype q
  letI : Nonempty (GenericGraphTables.RelationTable q) := ⟨GenericMachine.relationDefault q⟩
  exact (((Poly.identity (code (q := q))).pair relationPoly).comp
    (Poly.finiteBranch code GenericMachine.relationCode natBits (relationCode_injective q)
      (fun s r => queryRank s (Queries.query (GenericGraphTables.relationAt r) l.1.1 l.1.2))
      (fun r => queryRankPoly _))).congr (fun _ => rfl)

def localRow {q : ℕ} (l : Local q) (s : State q) : TableMachine.Row :=
  ((if l.2 then s.1.darts*localCount q +
      queryRank s (Queries.query (GenericGraphTables.relationAt (old s).2) l.1.1 l.1.2)
    else s.2*localCount q+(localEventEquiv q l.1.1).val,
    s.2*blockCount q+(blockEquiv q (l.1,!l.2)).val),
    Relations.relationFromTable (old s).2 (decide ((old s).1.1=head s)) l.1.1 l.1.2 l.2)
noncomputable def localTailPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s => (localRow l s).1.1) := by
  if h : l.2 then
    let count := ((dartsPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
    exact ((count.pair (queryPoly l)).comp Poly.natAdd).congr (by intro s; simp [localRow,h])
  else
    let offset := ((indexPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
    exact ((offset.pair (Poly.const _ natBits (localEventEquiv q l.1.1).val)).comp Poly.natAdd).congr
      (by intro s; simp [localRow,h])
noncomputable def localReversePoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s => (localRow l s).1.2) :=
  ((((indexPoly (q := q)).pair (Poly.const _ natBits (blockCount q))).comp Poly.natMul).pair
    (Poly.const _ natBits (blockEquiv q (l.1,!l.2)).val)).comp Poly.natAdd
noncomputable def localRelationPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) TableMachine.relationCode (fun s => (localRow l s).2) := by
  letI := relationFintype q
  exact (relationPoly.pair loopPoly).comp (Poly.finite
    (prodBits GenericMachine.relationCode boolBits) TableMachine.relationCode
    (prodBits_injective (relationCode_injective q) boolBits_injective)
    (fun p => Relations.relationFromTable p.1 p.2 l.1.1 l.1.2 l.2))
noncomputable def localPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) TableMachine.rowCode (localRow l) :=
  ((localTailPoly l).pair (localReversePoly l)).pair (localRelationPoly l)

end VertexCover.Machine.AlphabetMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_AlphabetCorrect
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable Enumeration

 theorem old_valid {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) :
    old (T,e.val) = GenericMachine.rowData T.rows[e] := GenericMachine.lookup_valid T e
 theorem head_valid {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) :
    head (T,e.val) = T.rows[T.rows[e].reverseIndex].tail.val := by
  unfold head
  rw [old_valid]
  exact congrArg (fun r : GenericMachine.Row q => r.1.1)
    (GenericMachine.lookup_valid T T.rows[e].reverseIndex)

 theorem local_source {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) (l : Local q) :
    localRow l (T,e.val) = TableMachine.rowData (Table.rowFromDart T (((e,l.1.1),l.1.2),l.2)) := by
  rcases l with ⟨⟨event,slot⟩,b⟩
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [localRow,TableMachine.rowData,Table.rowFromDart]
      cases b with
      | false => simp only [Bool.false_eq_true,ite_false,vertexEquiv_event_val,eventEquiv_val]
      | true =>
        simp only [ite_true]
        unfold queryRank
        rw [old_valid]
        dsimp only [GenericMachine.rowData]
        cases h : Queries.query (GenericGraphTables.relationAt T.rows[e].relation) event slot with
        | inl z =>
          rcases z with ⟨side,tape⟩
          simp only [Queries.globalize,vertexEquiv_vertexAddress_val]
          cases side <;> simp [eventCount,head_valid]
        | inr tape =>
          simp only [Queries.globalize,vertexEquiv_edgeAddress_val,eventCount]
    · change e.val*blockCount q+(blockEquiv q ((event,slot),!b)).val =
        (dartEquiv T.darts q (((e,event),slot),!b)).val
      rw [dart_block_val e ((event,slot),!b)]
      ring
  · dsimp only [localRow,TableMachine.rowData,Table.rowFromDart]
    rw [old_valid,head_valid]
    simp only [GenericMachine.rowData,Fin.ext_iff]
    rfl

def row {q : ℕ} (s : State q) : TableMachine.Row :=
  localRow ((blockEquiv q).symm ⟨s.2%blockCount q,Nat.mod_lt _ (block_pos q)⟩)
    (s.1,s.2/blockCount q)
noncomputable def rowPoly {q : ℕ} : Poly (code (q := q)) TableMachine.rowCode row := by
  let t : Poly (code (q := q)) GenericMachine.code Prod.fst := tablePoly
  let i : Poly (code (q := q)) natBits Prod.snd := indexPoly
  let e := (i.pair (Poly.const _ natBits (blockCount q))).comp Poly.natDiv
  let j := i.comp (Poly.finMod (blockCount q) (block_pos q))
  letI : Nonempty (Fin (blockCount q)) := ⟨⟨0,block_pos q⟩⟩
  exact ((t.pair e).pair j).comp (Poly.finiteBranch code finCode TableMachine.rowCode
    (finCode_injective _) (fun s k => localRow ((blockEquiv q).symm k) s)
    (fun k => localPoly _))

 theorem row_source {q : ℕ} (T : GenericGraphTables.Table q) (i : Fin (Table.build T).darts) :
    row (T,i.val) = TableMachine.rowData (Table.build T).rows[i] := by
  obtain ⟨⟨⟨⟨e,event⟩,slot⟩,b⟩,rfl⟩ := (dartEquiv T.darts q).surjective i
  let l : Local q := ((event,slot),b)
  have he : (dartEquiv T.darts q (((e,event),slot),b)).val/blockCount q = e.val := by
    rw [dart_block_val e l,Nat.add_mul_div_left _ _ (block_pos q),Nat.div_eq_of_lt (blockEquiv q l).isLt,Nat.zero_add]
  have hj : (⟨(dartEquiv T.darts q (((e,event),slot),b)).val%blockCount q,Nat.mod_lt _ (block_pos q)⟩ : Fin (blockCount q)) = blockEquiv q l := by
    apply Fin.ext
    change (dartEquiv T.darts q (((e,event),slot),b)).val%blockCount q = (blockEquiv q l).val
    rw [dart_block_val e l,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (blockEquiv q l).isLt]
  unfold row
  conv_lhs => rw [he,hj,Equiv.symm_apply_apply]
  change localRow l (T,e.val) = TableMachine.rowData (Table.rows T)[dartEquiv T.darts q (((e,event),slot),b)]
  rw [Table.rows_at,Equiv.symm_apply_apply]
  exact local_source T e l

end VertexCover.Machine.AlphabetMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Alphabet
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

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace TableMachine
 theorem materialize_source {α : Type} (Q : α → GraphTables.Table) (r : α × ℕ → Row)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) (a : α) :
    ((Q a).vertices,(List.range (Q a).darts).map (fun i => r (a,i))) = tableData (Q a) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [tableData]
  · intro i h₁ h₂
    simp only [tableData,List.getElem_map,List.getElem_range,Vector.getElem_toList]
    exact hr a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α)
    (Q : α → GraphTables.Table) {r : α × ℕ → Row}
    (cn : Poly ea natBits (fun a => (Q a).vertices))
    (cm : Poly ea natBits (fun a => (Q a).darts))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) :
    Poly ea tableCode Q := by
  let rows := Poly.tabulate ea rowCode a₀ rowDefault cm cr
  exact (cn.pair rows).encodeCongr id (fun _ => rfl) (fun a => by
    exact congrArg dataCode (materialize_source Q r hr a))
end TableMachine

namespace AlphabetMachine
open AlphabetTable Enumeration
noncomputable def eventsPoly {q : ℕ} : Poly (GenericMachine.code (q := q)) natBits
    (fun T => eventCount T.darts q) :=
  ((GenericMachine.dartsPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
noncomputable def addressesPoly {q : ℕ} : Poly (GenericMachine.code (q := q)) natBits
    (fun T => addressCount T.vertices T.darts q) := by
  let v := ((GenericMachine.verticesPoly (q := q)).pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul
  let e := ((GenericMachine.dartsPoly (q := q)).pair (Poly.const _ natBits (pairTapeCount q))).comp Poly.natMul
  exact (v.pair e).comp Poly.natAdd
noncomputable def poly {q : ℕ} : Poly (GenericMachine.code (q := q)) TableMachine.tableCode Table.build := by
  let zero : GenericGraphTables.Table q := GenericGraphTables.ofGraph
    ({reverse := Equiv.refl (Fin 0),reverse_involutive := fun _ => rfl,
      tail := id,accepts := fun _ _ _ => true,reverse_accepts := fun _ _ _ => rfl} :
        ConstraintGraph (Fin 0) (Fin 0) (Fin q))
  exact TableMachine.materializePoly GenericMachine.code zero Table.build
    ((eventsPoly.pair addressesPoly).comp Poly.natAdd)
    ((eventsPoly.pair (Poly.const _ natBits 12)).comp Poly.natMul) rowPoly row_source
end AlphabetMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_CloudFamily
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGames.Foundations.PCP.RawInitialTables.table_vertices
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

namespace VertexCover.Machine.CloudMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables

 theorem cloudFamily_source (H : BaseTable) (T : GraphTables.Table) (v : Fin T.vertices) :
    cloudFamily H (cloud (T,v.val)).length =
      ExpandMachine.erase ⟨cloudSize T v + PreprocessingRegularTables.padding T v,familyCloudTable H T v⟩ := by
  rw [cloud_source,List.length_map]
  change cloudFamily H (cloudSize T v) = _
  by_cases hk : cloudSize T v = 0
  · simp only [cloudFamily,familyCloudTable,hk,↓reduceIte,↓reduceDIte]
    rw [erase_resize]
    simp [ExpandMachine.erase,PreprocessingRegularTables.emptyTable]
  · simp only [cloudFamily,familyCloudTable,hk,↓reduceIte,↓reduceDIte]
    exact (erase_resize _ _).symm

 theorem cloudLookup_source (H : BaseTable) (T : GraphTables.Table) (v : Fin T.vertices)
    (e : PaddedCloud T (PreprocessingRegularTables.padding T) v) (p : Fin internalDegree) :
    cloudLookup H (T,(v.val,((paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val,p.val))) =
      ((paddedCloudRank T (PreprocessingRegularTables.padding T) v
        ((cloudGraphs T (PreprocessingRegularTables.padding T) (familyCloudTable H T) v).rot (e,p)).1).val,
       ((cloudGraphs T (PreprocessingRegularTables.padding T) (familyCloudTable H T) v).rot (e,p)).2.val) := by
  dsimp only [cloudLookup]
  rw [cloudFamily_source]
  change ExpandMachine.lookup internalDegree
    ((familyCloudTable H T v).rows.toList.map Fin.val,
      ((paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val,p.val)) = _
  rw [ExpandMachine.lookup_erase (familyCloudTable H T v)
    (paddedCloudRank T (PreprocessingRegularTables.padding T) v e,p)]
  simp only [cloudGraphs,GraphTransport.reindex,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.prodCongr_symm,Equiv.symm_symm,Prod.map_apply,Prod.map_fst,Prod.map_snd,Equiv.refl_apply,Equiv.refl_symm,
    paddedCloudRank,Equiv.apply_symm_apply]
  rfl

end VertexCover.Machine.CloudMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_InitialTable
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP PCP.GraphTables
open FormulaParser TableMachine

namespace InitialTable

def relation (p : Signs × (Fin 3 × Bool)) : RelationTable :=
  relationOf (fun a b =>
    let x := AlphabetRetraction.decode64 (RawInitialTables.labelOrder.symm a)
    let y := AlphabetRetraction.decode64 (RawInitialTables.labelOrder.symm b)
    if p.2.2 then accepts p.1 p.2.1 y x else accepts p.1 p.2.1 x y)

def row (p : FormulaData × ℕ) : Row :=
  let F := p.1
  let i := p.2
  let cs := F.2.getD (i/6) clauseDefault
  let slot : Fin 3 := ⟨(i/2)%3,Nat.mod_lt _ (by decide)⟩
  let flip := decide (i%2=1)
  if i < 6*F.2.length then
    ((if flip then (lit cs slot).2 else F.1+i/6,
      if flip then i-1 else i+1),relation (signs cs,(slot,flip)))
  else ((F.1+F.2.length,6*F.2.length),relationOf (fun _ _ => true))

def output (F : FormulaData) : Data :=
  (F.1+F.2.length+1,(List.range (6*F.2.length+1)).map (fun i => row (F,i)))

noncomputable def relationPoly : Poly (prodBits signsCode (prodBits (finCode (n := 3)) boolBits))
    relationCode relation :=
  Poly.finite _ _ (prodBits_injective
    (prodBits_injective (prodBits_injective boolBits_injective boolBits_injective) boolBits_injective)
    (prodBits_injective (finCode_injective 3) boolBits_injective)) relation

noncomputable def rowPoly : Poly (prodBits FormulaParser.dataCode natBits) rowCode row := by
  let enc := prodBits FormulaParser.dataCode natBits
  let c (n : ℕ) := Poly.const enc natBits n
  let F := Poly.fst FormulaParser.dataCode natBits
  let i := Poly.snd FormulaParser.dataCode natBits
  let n := F.comp (Poly.fst natBits (listBits unaryClauseCode))
  let clauses := F.comp (Poly.snd natBits (listBits unaryClauseCode))
  let len := clauses.comp (Poly.listLength unaryClauseCode clauseDefault)
  let darts := ((c 6).pair len).comp Poly.natMul
  let j := (i.pair (c 6)).comp Poly.natDiv
  let cs := (j.pair clauses).comp (Poly.listGetD unaryClauseCode clauseDefault)
  let slot := ((i.pair (c 2)).comp Poly.natDiv).comp (Poly.finMod 3 (by decide))
  let flip := (((i.pair (c 2)).comp Poly.natMod).pair (c 1)).comp Poly.natBEq
  let v := ((cs.pair slot).comp litPoly).comp (Poly.snd boolBits natBits)
  let tail := flip.ite v ((n.pair j).comp Poly.natAdd)
  let rev := flip.ite ((i.pair (c 1)).comp Poly.natSub) (i.comp Poly.natSucc)
  let rel := ((cs.comp signsPoly).pair (slot.pair flip)).comp relationPoly
  let normal := (tail.pair rev).pair rel
  let dummy := (((n.pair len).comp Poly.natAdd).pair darts).pair
    (Poly.const enc relationCode (relationOf (fun _ _ => true)))
  let test := (i.pair darts).comp Poly.natLT
  refine (test.ite normal dummy).congr ?_
  intro p
  simp only [Function.comp_apply,row,List.headD_eq_head?_getD,List.head?_drop,
    List.getD_eq_getElem?_getD,decide_eq_true_eq]

noncomputable def outputPoly : Poly FormulaParser.dataCode TableMachine.dataCode output := by
  let n := Poly.fst natBits (listBits unaryClauseCode)
  let len := (Poly.snd natBits (listBits unaryClauseCode)).comp (Poly.listLength unaryClauseCode clauseDefault)
  let darts := (((Poly.const FormulaParser.dataCode natBits 6).pair len).comp Poly.natMul).comp Poly.natSucc
  let rows := Poly.tabulate FormulaParser.dataCode rowCode (0,[]) rowDefault darts rowPoly
  exact (((n.pair len).comp Poly.natAdd).comp Poly.natSucc).pair rows

end InitialTable
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNF
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.GraphTables FormulaParser TableMachine
abbrev enc := prodBits tableCode natBits
noncomputable def queryPoly : Poly (prodBits enc (finCode (n := 12))) natBits
    (fun p : (Table × ℕ) × Fin 12 => queryName p.1 p.2) := by
  apply Poly.finiteBranch enc finCode natBits (finCode_injective 12)
  intro i
  let c (n : ℕ) := Poly.const enc natBits n
  let first := TableMachine.tailPoly
  let second := ((Poly.fst tableCode natBits).pair TableMachine.reversePoly).comp TableMachine.tailPoly
  by_cases h : i.val<6
  · exact ((((c 6).pair first).comp Poly.natMul).pair (c i.val)).comp Poly.natAdd |>.congr
      (fun x => by simp only [Function.comp_apply,queryName,ite_eq_left h])
  · exact ((((c 6).pair second).comp Poly.natMul).pair (c (i.val-6))).comp Poly.natAdd |>.congr
      (fun x => by simp only [Function.comp_apply,queryName,ite_eq_right h])
abbrev renameEnc := prodBits enc natBits
noncomputable def renameFirst : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.1.vertices*6) :=
  ((((Poly.fst enc natBits).comp (Poly.fst tableCode natBits)).comp TableMachine.verticesPoly).pair
    (Poly.const renameEnc natBits 6)).comp Poly.natMul
noncomputable def renameOffset : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.2*36864) :=
  (((Poly.fst enc natBits).comp (Poly.snd tableCode natBits)).pair
    (Poly.const renameEnc natBits 36864)).comp Poly.natMul
noncomputable def renameRem : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.2-12) :=
  ((Poly.snd enc natBits).pair (Poly.const renameEnc natBits 12)).comp Poly.natSub
noncomputable def renameNo : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.1.vertices*6+p.1.2*36864+(p.2-12)) :=
  (((renameFirst.pair renameOffset).comp Poly.natAdd).pair renameRem).comp Poly.natAdd
noncomputable def renameYes : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => queryName p.1 ⟨p.2%12,Nat.mod_lt _ (by decide)⟩) :=
  ((Poly.fst enc natBits).pair ((Poly.snd enc natBits).comp (Poly.finMod 12 (by decide)))).comp queryPoly
noncomputable def renameTest : Poly renameEnc boolBits
    (fun p : (Table × ℕ) × ℕ => decide (p.2+1≤12)) :=
  ((((Poly.snd enc natBits).comp Poly.natSucc).pair (Poly.const renameEnc natBits 12))).comp Poly.natLE
noncomputable def renamePoly : Poly renameEnc natBits (fun p => rename p.1 p.2) := by
  exact (renameTest.ite renameYes renameNo).congr (fun p => by
    by_cases h : p.2<12
    · have h' : p.2+1≤12 := by omega
      simp only [h',decide_true,ite_true,rename,dite_eq_left h]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt h)
    · have h' : ¬p.2+1≤12 := by omega
      simp only [h',decide_false,Bool.false_eq_true,ite_false,rename,dite_eq_right h]
      rw [PCP.VerifierToCNF.patterns_length]
      rfl)
noncomputable def literalPoly : Poly (prodBits enc unaryLiteralCode) unaryLiteralCode renameLiteral := by
  let s := Poly.fst enc unaryLiteralCode
  let l := Poly.snd enc unaryLiteralCode
  let sign := l.comp (Poly.fst boolBits natBits)
  let idx := l.comp (Poly.snd boolBits natBits)
  exact (sign.pair ((s.pair idx).comp renamePoly)).congr (fun _ => rfl)
noncomputable def clausePoly : Poly (prodBits enc unaryClauseCode) unaryClauseCode renameClause := by
  let s := Poly.fst enc unaryClauseCode
  let cl := Poly.snd enc unaryClauseCode
  let ab := cl.comp (Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  let a := ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)
  let b := ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)
  let c := cl.comp (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  exact (((s.pair a).comp literalPoly).pair ((s.pair b).comp literalPoly)).pair
    ((s.pair c).comp literalPoly)
noncomputable def eventTemplatePoly : Poly enc (listBits unaryClauseCode)
    (fun p : Table × ℕ => skeleton (((tableData p.1).2.getD p.2 rowDefault).2)) := by
  refine (TableMachine.relationPoly.comp skeletonPoly).congr ?_
  intro p
  dsimp only [Function.comp_apply]
noncomputable def eventRenamePoly : Poly (prodBits enc (listBits unaryClauseCode)) (listBits unaryClauseCode)
    (fun p : (Table × ℕ) × List (Triple (Bool × ℕ)) => p.2.map (fun c => renameClause (p.1,c))) :=
  Poly.listMapWith enc unaryClauseCode unaryClauseCode (TableMachine.emptyTable,0)
    InitialTable.clauseDefault InitialTable.clauseDefault clausePoly
noncomputable def eventPoly : Poly enc (listBits unaryClauseCode) eventData :=
  by
  refine (((Poly.identity enc).pair eventTemplatePoly).comp eventRenamePoly).congr ?_
  intro p
  dsimp only [Function.comp_apply,id_eq,eventData]
noncomputable def clausesPoly : Poly tableCode (listBits unaryClauseCode) (fun T => (List.range T.darts).flatMap (fun e => eventData (T,e))) :=
  ((Poly.tabulate tableCode (listBits unaryClauseCode) TableMachine.emptyTable [] TableMachine.dartsPoly eventPoly).comp
    (Poly.listFlatten unaryClauseCode InitialTable.clauseDefault)).congr (fun _ => by simp only [Function.comp_apply,List.flatMap_def])
noncomputable def oldVarsPoly : Poly tableCode natBits (fun T : Table => T.vertices*6) :=
  (TableMachine.verticesPoly.pair (Poly.const tableCode natBits 6)).comp Poly.natMul
noncomputable def newVarsPoly : Poly tableCode natBits (fun T : Table => T.darts*36864) :=
  (TableMachine.dartsPoly.pair (Poly.const tableCode natBits 36864)).comp Poly.natMul
noncomputable def variablesPoly : Poly tableCode natBits (fun T : Table => T.vertices*6+T.darts*36864) :=
  (oldVarsPoly.pair newVarsPoly).comp Poly.natAdd
noncomputable def outputPoly : Poly tableCode FormulaParser.dataCode output := variablesPoly.pair clausesPoly
end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_InitialCorrect
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_graph _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_size _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true
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

namespace VertexCover.Machine.InitialTable
open UniqueGames.Foundations
open PCP PCP.GraphTables FormulaParser TableMachine
open RawInitialTables

@[simp] theorem vertexOrder_variable (F : Target.Formula) (v : Fin F.variables) :
    (vertexOrder F (InitialGraph.variableVertex F v)).val = v.val := rfl
@[simp] theorem vertexOrder_clause (F : Target.Formula) (v : Fin F.clauses.length) :
    (vertexOrder F (InitialGraph.clauseVertex F v)).val = F.variables+v.val := rfl
@[simp] theorem vertexOrder_dummy (F : Target.Formula) :
    (vertexOrder F (InitialGraph.dummyVertex F)).val = F.variables+F.clauses.length := by
  change F.variables+F.clauses.length+0 = _
  omega

@[simp] theorem dartOrder_real (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    (dartOrder F (.inl (e,b))).val = (if b then 1 else 0)+2*((slotOrder e.2).val+3*e.1.val) := by
  cases b <;> rfl
@[simp] theorem dartOrder_dummy (F : Target.Formula) :
    (dartOrder F (InitialGraph.dummyDart F)).val = 6*F.clauses.length := by
  change F.clauses.length*3*2+0 = _
  omega

 theorem clause_lookup (F : Target.Formula) (j : Fin F.clauses.length) :
    (targetData F).2.getD j.val clauseDefault = targetClauseData (PCP.clauseAt F j) := by
  rw [List.getD_eq_getElem _ _ (by simp [targetData])]
  simp only [targetData,List.getElem_map,PCP.clauseAt]

 theorem lit_target (F : Target.Formula) (e : PCP.RandomEvent F) :
    (lit (targetClauseData (PCP.clauseAt F e.1)) (slotOrder e.2)).2 =
      (PCP.nameAt (PCP.clauseAt F e.1) e.2).val := by
  rcases e with ⟨j,s⟩
  cases s <;> rfl

 theorem relation_target (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    relation (signs (targetClauseData (PCP.clauseAt F e.1)),(slotOrder e.2,b)) =
      relationOf (fun a c => (raw64 F).accepts (.inl (e,b))
        (labelOrder.symm a) (labelOrder.symm c)) := by
  apply congrArg relationOf
  funext a c
  rcases e with ⟨j,s⟩
  cases s <;> cases b <;> rfl

 theorem real_row (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    row (targetData F,(dartOrder F (.inl (e,b))).val) =
      (((vertexOrder F ((raw64 F).tail (.inl (e,b)))).val,
        (dartOrder F ((raw64 F).reverse (.inl (e,b)))).val),
        relationOf (fun a c => (raw64 F).accepts (.inl (e,b))
          (labelOrder.symm a) (labelOrder.symm c))) := by
  let idx := (dartOrder F (.inl (e,b))).val
  have hs : (slotOrder e.2).val < 3 := (slotOrder e.2).isLt
  have hi : idx < 6*F.clauses.length := by
    dsimp [idx]; rw [dartOrder_real]
    have hj := e.1.isLt
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hd : idx/6=e.1.val := by
    dsimp [idx]; rw [dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hp : (⟨(idx/2)%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=slotOrder e.2 := by
    apply Fin.ext
    dsimp [idx]; rw [dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hb : decide (idx%2=1)=b := by
    simp only [idx,dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,decide_eq_false_iff_not,decide_eq_true_eq] <;> omega
  change row (targetData F,idx) = _
  dsimp only [row]
  rw [show (targetData F).2.length=F.clauses.length by simp [targetData],ite_eq_left hi,hd,hp,hb,
    clause_lookup,lit_target,relation_target]
  apply Prod.ext
  · apply Prod.ext
    · cases b <;> rfl
    · cases b with
      | false =>
        change idx+1 = (dartOrder F (.inl (e,true))).val
        simp only [idx,dartOrder_real,Bool.false_eq_true,↓reduceIte]
        omega
      | true =>
        change idx-1 = (dartOrder F (.inl (e,false))).val
        simp only [idx,dartOrder_real,Bool.false_eq_true,↓reduceIte]
        omega
  · rfl

 theorem dummy_row (F : Target.Formula) :
    row (targetData F,(dartOrder F (InitialGraph.dummyDart F)).val) =
      (((vertexOrder F ((raw64 F).tail (InitialGraph.dummyDart F))).val,
        (dartOrder F ((raw64 F).reverse (InitialGraph.dummyDart F))).val),
        relationOf (fun a c => (raw64 F).accepts (InitialGraph.dummyDart F)
          (labelOrder.symm a) (labelOrder.symm c))) := by
  rw [dartOrder_dummy]
  simp only [row,targetData,List.length_map,lt_self_iff_false,↓reduceIte]
  change _ = ((F.variables+F.clauses.length+0,F.clauses.length*3*2+0),_)
  congr 2; omega

 theorem row_target (F : Target.Formula) (i : Fin (table F).darts) :
    row (targetData F,i.val) = rowData (table F).rows[i] := by
  obtain ⟨d,rfl⟩ := (dartOrder F).surjective i
  have he : rowData (table F).rows[dartOrder F d] =
      (((vertexOrder F ((raw64 F).tail d)).val,(dartOrder F ((raw64 F).reverse d)).val),
        relationOf (fun a c => (raw64 F).accepts d (labelOrder.symm a) (labelOrder.symm c))) := by
    have getrow {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m) Label) (j : Fin m) :
        rowData (graphRows G)[j] =
          ((G.tail j |>.val,G.reverse j |>.val),relationOf (G.accepts j)) := by
      change rowData (graphRows G)[j.val] = _
      simp only [graphRows,Vector.getElem_ofFn,rowData]
    change rowData (graphRows (enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder))[dartOrder F d] = _
    rw [getrow]
    simp only [enumeratedGraph,Equiv.trans_apply,Equiv.symm_apply_apply]
  apply Eq.trans _ he.symm
  cases d with
  | inl eb => exact real_row F eb.1 eb.2
  | inr u => cases u; exact dummy_row F

 theorem output_target (F : Target.Formula) : output (targetData F)=tableData (table F) := by
  apply Prod.ext
  · simp only [output,targetData,tableData,table_vertices,List.length_map]
  · apply List.ext_getElem
    · simp only [output,tableData,List.length_map,List.length_range,targetData]
      exact (table_darts F).symm.trans (Vector.length_toList (xs := (table F).rows)).symm
    · intro i h₁ h₂
      simp only [output,List.getElem_map,List.getElem_range,tableData] at *
      simpa only [Fin.getElem_fin,Vector.getElem_toList] using
        row_target F ⟨i,by simpa [output,targetData,table_darts] using h₁⟩

noncomputable def initialPoly : Poly targetCode tableCode table :=
  outputPoly.encodeCongr targetData (fun _ => rfl) (fun F => by
    change TableMachine.dataCode (output (targetData F)) = TableMachine.dataCode (tableData (table F))
    rw [output_target])

end VertexCover.Machine.InitialTable
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_RegularRow
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

 theorem reversePair_source (H : BaseTable) (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) (p : Fin internalDegree ⊕ Unit) :
    reversePair H (T,((vertexOrder T (PreprocessingRegularTables.padding T) e).val,
      (portOrder internalDegree p).val)) =
    ((vertexOrder T (PreprocessingRegularTables.padding T)
      ((sourcePortGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).rot (e,p)).1).val,
     (portOrder internalDegree
      ((sourcePortGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).rot (e,p)).2).val) := by
  cases p with
  | inl p =>
    dsimp only [reversePair]
    rw [portOrder_internal,ite_eq_left p.isLt,ownerRank_source,cloudLookup_source]
    rw [globalIndex_source]
    rfl
  | inr u =>
    cases u
    dsimp only [reversePair]
    rw [portOrder_inherited,ite_eq_right (Nat.lt_irrefl _)]
    cases e with
    | inl e =>
      rw [vertexOrder_original,ite_eq_left e.isLt,lookup_valid]
      rfl
    | inr z =>
      rw [vertexOrder_dummy,ite_eq_right (by omega)]
      rfl

 theorem relation_source (H : BaseTable) (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) (p : Fin internalDegree ⊕ Unit) :
    relation (T,((vertexOrder T (PreprocessingRegularTables.padding T) e).val,
      (portOrder internalDegree p).val)) =
      GraphTables.relationOf (fun a b =>
        (sourceGraph T (PreprocessingRegularTables.padding T) (familyCloudTable H T)).accepts (e,p) a b) := by
  cases p with
  | inl p =>
    dsimp only [relation]
    rw [portOrder_internal,ite_eq_left p.isLt]
    rfl
  | inr u =>
    cases u
    dsimp only [relation]
    rw [portOrder_inherited,ite_eq_right (Nat.lt_irrefl _)]
    cases e with
    | inl e =>
      rw [vertexOrder_original,ite_eq_left e.isLt,lookup_valid]
      change T.rows[e].relation = GraphTables.relationOf _
      apply Vector.ext
      intro i hi
      change T.rows[e].relation[i] = (GraphTables.relationOf
        (GraphTables.relationAt T.rows[e].relation))[i]
      simp only [GraphTables.relationOf,Vector.getElem_ofFn,GraphTables.relationAt,
        Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin]
    | inr z =>
      rw [vertexOrder_dummy,ite_eq_right (by omega)]
      rfl

end VertexCover.Machine.RegularMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatPath
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

namespace VertexCover.Machine.NatPathMachine
open UniqueGames.Foundations.PCP
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach NatWalkMachine

 theorem path_source {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (s : WalkMachine.State d) :
    path n p a b (forget s) = PoweringTest.pathAccepts (PortTables.portGraph s.1.2)
      (PortTables.accepts s.1.2) n (finitePortSelector (PortTables.portGraph s.1.2) (n+1)) (s.2,p) a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [path,decide_eq_true_iff,PoweringTest.pathAccepts_eq_true_iff,edgeTest_source]

end VertexCover.Machine.NatPathMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PowerRow
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
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

namespace VertexCover.Machine.PowerRowMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringEnumeration PoweringTables

def localRow {d : ℕ} (n : ℕ) (j : Block d n) (s : NatWalkMachine.State d) :
    GenericMachine.Row (labelCount d n) :=
  let w := (dartBlockEquiv d n).symm j
  ((if w.2 then (NatWalkMachine.word (n+1) w.1 s).2 else s.2,
    (2*d^(n+1))*s.2 + (dartBlockEquiv d n (w.1,!w.2)).val),
    GenericGraphTables.relationOf (fun a b =>
      if w.2 then NatPathMachine.path n w.1 ((paddedLabelEquiv d (n+1) 64).symm b)
        ((paddedLabelEquiv d (n+1) 64).symm a) s
      else NatPathMachine.path n w.1 ((paddedLabelEquiv d (n+1) 64).symm a)
        ((paddedLabelEquiv d (n+1) 64).symm b) s))

noncomputable def localTailPoly {d : ℕ} (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) natBits (fun s => (localRow n j s).1.1) := by
  let w := (dartBlockEquiv d n).symm j
  if h : w.2 then
    exact ((NatWalkMachine.wordPoly (n+1) w.1).comp
      (Poly.snd PortMachine.code natBits)).congr (fun _ => by simp [localRow,w,h])
  else
    exact (Poly.snd PortMachine.code natBits).congr (fun _ => by simp [localRow,w,h])
noncomputable def localReversePoly {d : ℕ} (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) natBits (fun s => (localRow n j s).1.2) := by
  let w := (dartBlockEquiv d n).symm j
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let c := Poly.const (NatWalkMachine.code (d := d)) natBits (2*d^(n+1))
  exact (((c.pair v).comp Poly.natMul).pair
    (Poly.const _ natBits (dartBlockEquiv d n (w.1,!w.2)).val)).comp Poly.natAdd
noncomputable def localRelationPoly {d : ℕ} (hd : 0<d) (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) GenericMachine.relationCode (fun s => (localRow n j s).2) := by
  let w := (dartBlockEquiv d n).symm j
  apply Poly.vectorOfFn
  intro i
  let a := (paddedLabelEquiv d (n+1) 64).symm ((GenericGraphTables.relationIndex (labelCount d n)).symm i).1
  let b := (paddedLabelEquiv d (n+1) 64).symm ((GenericGraphTables.relationIndex (labelCount d n)).symm i).2
  if h : w.2 then
    exact (NatPathMachine.pathPoly hd n w.1 b a).congr (fun _ => by simp [w,h,a,b])
  else
    exact (NatPathMachine.pathPoly hd n w.1 a b).congr (fun _ => by simp [w,h,a,b])
noncomputable def localPoly {d : ℕ} (hd : 0<d) (n : ℕ) (j : Block d n) :
    Poly (NatWalkMachine.code (d := d)) GenericMachine.rowCode (localRow n j) :=
  ((localTailPoly n j).pair (localReversePoly n j)).pair (localRelationPoly hd n j)
noncomputable def localVariablePoly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (prodBits (NatWalkMachine.code (d := d)) finCode) GenericMachine.rowCode
      (fun x => localRow n x.2 x.1) := by
  letI : Nonempty (Block d n) := ⟨⟨0,Nat.mul_pos (by decide) (Nat.pow_pos hd)⟩⟩
  exact Poly.finiteBranch NatWalkMachine.code finCode GenericMachine.rowCode (finCode_injective _)
    (fun s j => localRow n j s) (localPoly hd n)

def row {d : ℕ} (hd : 0<d) (n : ℕ) (x : PortTables.Input d × ℕ) : GenericMachine.Row (labelCount d n) :=
  localRow n ⟨x.2%(2*d^(n+1)),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.pow_pos hd))⟩
    (x.1,x.2/(2*d^(n+1)))
noncomputable def rowPoly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (prodBits (PortMachine.code (q := d)) natBits) GenericMachine.rowCode (row hd n) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let i := Poly.snd (PortMachine.code (q := d)) natBits
  let v := (i.pair (Poly.const _ natBits (2*d^(n+1)))).comp Poly.natDiv
  let j := i.comp (Poly.finMod (2*d^(n+1)) (Nat.mul_pos (by decide) (Nat.pow_pos hd)))
  exact ((t.pair v).pair j).comp (localVariablePoly hd n)

end VertexCover.Machine.PowerRowMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Power
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

namespace VertexCover.Machine.PowerMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringEnumeration PoweringTables PowerRowMachine

 theorem local_source {d : ℕ} (n : ℕ) (T : PortTables.Input d) (v : Fin T.1)
    (p : Fin (n+1) → Fin d) (b : Bool) :
    localRow n (dartBlockEquiv d n (p,b)) (T,v.val) =
      GenericMachine.rowData (table T.2 n).rows[dartEquiv T.1 d n (b,(v,p))] := by
  apply Prod.ext
  · apply Prod.ext
    · change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.1 =
        ((GenericGraphTables.semantics (table T.2 n)).tail (dartEquiv T.1 d n (b,(v,p)))).val
      rw [semantics_table]
      simp only [localRow,Equiv.symm_apply_apply,GenericGraphTables.enumeratedGraph,
        mathematicalGraph,PoweringTest.poweredGraph,Equiv.refl_apply]
      cases b with
      | false => rfl
      | true => exact congrArg Prod.snd (NatWalkMachine.word_forget (n+1) p (⟨T,v⟩ : WalkMachine.State d))
    · change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.2 =
        ((GenericGraphTables.semantics (table T.2 n)).reverse (dartEquiv T.1 d n (b,(v,p)))).val
      rw [semantics_table]
      change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.2 =
        (dartEquiv T.1 d n (PoweringTest.reverseDart (Fin T.1) (Fin d) n
          ((dartEquiv T.1 d n).symm (dartEquiv T.1 d n (b,(v,p)))))).val
      rw [Equiv.symm_apply_apply]
      simp only [localRow,Equiv.symm_apply_apply,PoweringTest.reverseDart]
      rw [dartEquiv_val,dartBlockEquiv_val,Nat.add_assoc]
      rfl
  · apply relation_ext
    intro a b'
    change GenericGraphTables.relationAt (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).2 a b' =
      (GenericGraphTables.semantics (table T.2 n)).accepts (dartEquiv T.1 d n (b,(v,p))) a b'
    rw [semantics_table]
    simp only [localRow,Equiv.symm_apply_apply,GenericGraphTables.relationAt_relationOf,
      GenericGraphTables.enumeratedGraph,mathematicalGraph,PoweringTest.poweredGraph]
    cases b <;> exact NatPathMachine.path_source n p _ _ (⟨T,v⟩ : WalkMachine.State d)

 theorem row_source {d : ℕ} (hd : 0<d) (n : ℕ) (T : PortTables.Input d)
    (i : Fin (table T.2 n).darts) :
    row hd n (T,i.val) = GenericMachine.rowData (table T.2 n).rows[i] := by
  obtain ⟨⟨b,v,p⟩,rfl⟩ := (dartEquiv T.1 d n).surjective i
  let j := dartBlockEquiv d n (p,b)
  have hval : (dartEquiv T.1 d n (b,(v,p))).val = j.val+(2*d^(n+1))*v.val := rfl
  have hB : 0<2*d^(n+1) := Nat.mul_pos (by decide) (Nat.pow_pos hd)
  have hv : (dartEquiv T.1 d n (b,(v,p))).val/(2*d^(n+1)) = v.val := by
    rw [hval,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have hj : (⟨(dartEquiv T.1 d n (b,(v,p))).val%(2*d^(n+1)),Nat.mod_lt _ hB⟩ : Block d n) = j := by
    apply Fin.ext
    change (dartEquiv T.1 d n (b,(v,p))).val%(2*d^(n+1)) = j.val
    rw [hval,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  unfold row
  conv_lhs => rw [hv,hj]
  exact local_source n T v p b

noncomputable def poly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (PortMachine.code (q := d)) GenericMachine.code (fun T => table T.2 n) := by
  let zero : PortTables.Input d := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  let size := ((Poly.const (PortMachine.code (q := d)) natBits 2).pair PortMachine.verticesPoly).comp Poly.natMul
  let darts := (size.pair (Poly.const _ natBits (d^(n+1)))).comp Poly.natMul
  exact GenericMachine.materializePoly PortMachine.code zero (fun T => table T.2 n)
    PortMachine.verticesPoly darts (rowPoly hd n) (row_source hd n)

end VertexCover.Machine.PowerMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Regular
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGames.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGames.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGames.Foundations.PCP.RawInitialTables.table_vertices
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

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

 theorem flatReverse_source (H : BaseTable) (T : GraphTables.Table)
    (i : Fin ((vertexCount T (PreprocessingRegularTables.padding T))*degree)) :
    flatReverse H (T,i.val) = (regularize H T).reverseIndex[i].val := by
  let V := vertexOrder T (PreprocessingRegularTables.padding T)
  let P := portOrder internalDegree
  let E := (Equiv.prodCongr V P).trans (PortTables.rowIndex _ degree)
  obtain ⟨⟨e,p⟩,rfl⟩ := E.surjective i
  have hc : ((E (e,p)).val/degree,(E (e,p)).val%degree) = ((V e).val,(P p).val) :=
    congrArg (fun z : Fin (vertexCount T (PreprocessingRegularTables.padding T)) × Fin degree =>
      (z.1.val,z.2.val)) ((PortTables.rowIndex _ degree).symm_apply_apply (V e,P p))
  dsimp only [flatReverse]
  rw [hc,reversePair_source]
  change _ = ((regularize H T).reverseIndex[PortTables.rowIndex _ degree (V e,P p)]).val
  rw [← PortTables.rowIndex_rotation]
  change _ = (PortTables.rowIndex _ degree
    (PortTables.rotation (ofCloudTables T (PreprocessingRegularTables.padding T) (familyCloudTable H T)) (V e,P p))).val
  rw [rotation_ofCloudTables]
  rfl

 theorem flatRelation_source (H : BaseTable) (T : GraphTables.Table)
    (i : Fin ((vertexCount T (PreprocessingRegularTables.padding T))*degree)) :
    flatRelation (T,i.val) = (regularize H T).relations[i] := by
  let V := vertexOrder T (PreprocessingRegularTables.padding T)
  let P := portOrder internalDegree
  let E := (Equiv.prodCongr V P).trans (PortTables.rowIndex _ degree)
  obtain ⟨⟨e,p⟩,rfl⟩ := E.surjective i
  have hc : ((E (e,p)).val/degree,(E (e,p)).val%degree) = ((V e).val,(P p).val) :=
    congrArg (fun z : Fin (vertexCount T (PreprocessingRegularTables.padding T)) × Fin degree =>
      (z.1.val,z.2.val)) ((PortTables.rowIndex _ degree).symm_apply_apply (V e,P p))
  dsimp only [flatRelation]
  rw [hc,relation_source H]
  apply relation_ext
  intro a b
  rw [GraphTables.relationAt_relationOf]
  exact (accepts_ofCloudTables T (PreprocessingRegularTables.padding T) (familyCloudTable H T) e p a b).symm

 theorem regularData_source (H : BaseTable) (T : GraphTables.Table) :
    regularData H T = PortMachine.erase (regularizeInput H T) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply List.ext_getElem
      · simp [regularData,PortMachine.erase,regularizeInput,PreprocessingTables.regularVertices]
      · intro i h₁ h₂
        simp only [regularData,PortMachine.erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact flatReverse_source H T ⟨i,by simpa [regularData,PreprocessingTables.regularVertices] using h₁⟩
    · apply List.ext_getElem
      · simp [regularData,PortMachine.erase,regularizeInput,PreprocessingTables.regularVertices]
      · intro i h₁ h₂
        simp only [regularData,PortMachine.erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact flatRelation_source H T ⟨i,by simpa [regularData,PreprocessingTables.regularVertices] using h₁⟩

noncomputable def regularPoly (H : BaseTable) :
    Poly tableCode PortMachine.code (regularizeInput H) := by
  exact (regularDataPoly H).encodeCongr id (fun _ => rfl) (fun T => by
    change PortMachine.dataCode (regularData H T) = PortMachine.dataCode _
    rw [regularData_source])

end VertexCover.Machine.RegularMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Preprocess
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
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

namespace VertexCover.Machine.PreprocessMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingTables

def overlayInput (H : BaseTable) (T : GraphTables.Table) :
    OverlayMachine.Input (PreprocessingRegularTables.internalDegree+1) PreprocessingRegularTables.internalDegree :=
  ⟨vertices T,padded H T,overlayFamily H T⟩

noncomputable def paddedPoly (H : BaseTable) : Poly tableCode PortMachine.code
    (fun T => (⟨vertices T,padded H T⟩ : PortTables.Input (PreprocessingRegularTables.internalDegree+1))) :=
  (RegularMachine.regularPoly H).comp PaddingMachine.poly

 theorem familyRows (H : BaseTable) (T : GraphTables.Table) :
    (overlayFamily H T).rows.toList.map Fin.val =
      (ExpandMachine.erase (ExpandMachine.paddedFamily H (regularVertices T))).2 := by
  exact congrArg Prod.snd (CloudMachine.erase_resize
    (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices T))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices T))))

noncomputable def familyRowsPoly (H : BaseTable) : Poly tableCode (listBits natBits)
    (fun T => (overlayFamily H T).rows.toList.map Fin.val) := by
  let r : Poly (ExpandMachine.code (q := PreprocessingRegularTables.internalDegree)) (listBits natBits)
      (fun T => (ExpandMachine.erase T).2) :=
    (Poly.snd natBits (listBits natBits)).encodeCongr ExpandMachine.erase (fun _ => rfl) (fun _ => rfl)
  let c := (CloudMachine.regularVerticesPoly.comp (ExpandMachine.paddedFamilyPoly H)).comp r
  exact c.congr (fun T => (familyRows H T).symm)

noncomputable def overlayInputPoly (H : BaseTable) : Poly tableCode OverlayMachine.code (overlayInput H) :=
  ((paddedPoly H).pair (familyRowsPoly H)).encodeCongr id (fun _ => rfl) (fun _ => rfl)

noncomputable def poly (H : BaseTable) : Poly tableCode PortMachine.code (output H) :=
  ((overlayInputPoly H).comp OverlayMachine.poly).comp LazyMachine.poly

end VertexCover.Machine.PreprocessMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Round
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

namespace VertexCover.Machine.RoundMachine
open UniqueGames.Foundations.PCP
open TableMachine
noncomputable def poweredPoly (H : RoundTables.BaseTable) : Poly tableCode GenericMachine.code (RoundTables.powered H) :=
  (PreprocessMachine.poly H).comp (PowerMachine.poly RoundTables.degree_positive RoundTables.walkParameter)
noncomputable def poly (H : RoundTables.BaseTable) : Poly tableCode tableCode (RoundTables.build H) :=
  (poweredPoly H).comp AlphabetMachine.poly
end VertexCover.Machine.RoundMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Iteration
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

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP
namespace IterationMachine
open TableMachine
abbrev State := ℕ × GraphTables.Table
abbrev enc : State → List Bool := prodBits natBits tableCode

def initial (F : Target.Formula) : State :=
  (TableIteration.iterationCount F,RawInitialTables.table F)
def result (H : RoundTables.BaseTable) (F : Target.Formula) : State :=
  (0,TableIteration.outputTable H F)

noncomputable def sizePolynomial : Polynomial ℕ :=
  let s := (2*Polynomial.X)^TableIteration.polynomialDegree*Polynomial.X
  2*Polynomial.X+1+TableMachine.lengthPolynomial.comp s

 theorem size_bound (H : RoundTables.BaseTable) (F : Target.Formula) (k l : ℕ)
    (h : k+l=TableIteration.iterationCount F) :
    (enc (l,Iterate.run (RoundTables.build H) k (RawInitialTables.table F))).length ≤
      sizePolynomial.eval (enc (initial F)).length := by
  let s := RoundTables.size (RoundTables.initial F)
  let N := (enc (initial F)).length
  have hsN : s ≤ N := by
    have hs := TableMachine.size_le_code (RawInitialTables.table F)
    simp only [N,initial,pairBits_length,natBits_length]
    exact hs.trans (Nat.le_add_left _ _)
  have hlN : l ≤ N := by
    simp only [N,initial,pairBits_length,natBits_length]
    omega
  have hk : k ≤ AmplificationIteration.rounds s := by
    change k ≤ TableIteration.iterationCount F
    omega
  have hp := (Nat.pow_le_pow_right RoundTables.sizeFactor_positive hk).trans
    (AmplificationIteration.blowup_rounds_le (RoundTables.size_positive (RoundTables.initial F))
      TableIteration.sizeFactor_le_power)
  have ht := (TableIteration.run_size H k (RoundTables.initial F)).trans (Nat.mul_le_mul_right s hp)
  have htN := ht.trans (Nat.mul_le_mul
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hsN) _) hsN)
  have hm : (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)).vertices+
      (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)).darts ≤
      (2*N)^TableIteration.polynomialDegree*N := by
    rw [Iterate.run_source]
    change (TableIteration.runTables H k (RawInitialTables.table F)).vertices+
      (TableIteration.runTables H k (RawInitialTables.table F)).darts ≤ _
    have hv : (TableIteration.run H k (RoundTables.initial F)).val =
        TableIteration.runTables H k (RawInitialTables.table F) := TableIteration.run_val H k _
    rw [← hv]
    exact htN
  have hb := (TableMachine.codeLength_le_eval _).trans
    (Complexity.MachineComposition.natPolynomial_eval_mono _ hm)
  calc
    _ = 2*l+1+(tableCode (Iterate.run (RoundTables.build H) k (RawInitialTables.table F))).length := by
      simpa only [natBits_length] using pairBits_length (natBits l) (tableCode (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)))
    _ ≤ 2*N+1+TableMachine.lengthPolynomial.eval ((2*N)^TableIteration.polynomialDegree*N) :=
      Nat.add_le_add (by omega) hb
    _ = sizePolynomial.eval N := by
      simp only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp,Polynomial.eval_pow]

noncomputable def initialPoly : Poly FormulaParser.targetCode enc initial := by
  let T := InitialTable.initialPoly
  let s := ((T.comp TableMachine.verticesPoly).pair (T.comp TableMachine.dartsPoly)).comp Poly.natAdd
  let n := (s.comp Poly.natLog2).comp Poly.natSucc
  exact (n.pair T).congr (fun _ => rfl)

noncomputable def loopPoly (H : RoundTables.BaseTable) :
    Poly (fun F => enc (initial F)) enc (result H) :=
  Poly.loopFrom (Iterate.bodyPoly (RoundTables.build H) tableCode (RoundMachine.poly H))
    initial (result H) sizePolynomial (Polynomial.X+1) (by
      intro F
      refine ⟨TableIteration.iterationCount F+1,?_,?_⟩
      · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,initial,
          prodBits,pairBits_length,natBits_length]
        omega
      · have h := Iterate.bounded (RoundTables.build H) tableCode (TableIteration.iterationCount F)
          (RawInitialTables.table F) _ (size_bound H F)
        simpa only [Iterate.run_source,initial,result,TableIteration.outputTable,TableIteration.runTables] using h)
noncomputable def poly (H : RoundTables.BaseTable) :
    Poly FormulaParser.targetCode tableCode (TableIteration.outputTable H) :=
  ((Poly.initializeLoop initialPoly (loopPoly H)).comp (Poly.snd natBits tableCode)).congr (fun _ => rfl)
end IterationMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNFCorrect
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

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.GraphTables PCP.VerifierToCNF FormulaParser TableMachine

 theorem rename_old (T : Table) (e : Fin T.darts) (r : RelationTable) (i : Fin 12) :
    rename (T,e.val) (oldIndex (localVerifier r) ((localVerifier r).query (0 : Fin 1) i)).val =
      (oldIndex (Complexity.FinalCNFPattern.tableVerifier T)
        ((Complexity.FinalCNFPattern.tableVerifier T).query e i)).val := by
  simp only [oldIndex_value]
  have hi : ((localVerifier r).query (0 : Fin 1) i).val = i.val := rfl
  rw [hi,rename,dite_eq_left i.isLt]
  exact queryName_correct T e i

 theorem rename_fresh (T : Table) (e : Fin T.darts) (r : RelationTable)
    (p : PatternIndex 12) (j : Fin (12-3)) :
    rename (T,e.val) (freshIndex (localVerifier r) (0 : Fin 1) p j).val =
      (freshIndex (Complexity.FinalCNFPattern.tableVerifier T) e p j).val := by
  have hleft := freshIndex_value (localVerifier r) (0 : Fin 1) p j
  rw [hleft, freshIndex_value]
  change rename (T,e.val) (12+((0*(patterns 12).length+p.val)*9+j.val)) =
    T.vertices*6+((e.val*(patterns 12).length+p.val)*9+j.val)
  have h : ¬12+((0*(patterns 12).length+p.val)*9+j.val)<12 := by omega
  rw [rename,dite_eq_right h]
  simp only [Nat.zero_mul,Nat.zero_add,Nat.add_sub_cancel_left]
  ring

 theorem event_correct (T : Table) (e : Fin T.darts) :
    eventData (T,e.val) =
      (eventBlock (Complexity.FinalCNFPattern.tableVerifier T) (by decide) e).map targetClauseData := by
  unfold eventData
  rw [lookup_valid]
  simp only [skeleton,List.map_map,Function.comp_def,rename_erase]
  exact erase_event (localVerifier T.rows[e].relation)
    (Complexity.FinalCNFPattern.tableVerifier T) (by decide) (0 : Fin 1) e
    (rename (T,e.val) ∘ Fin.val) Fin.val
    (rename_old T e T.rows[e].relation) (rename_fresh T e T.rows[e].relation) (fun _ => rfl)

 theorem output_correct (T : Table) : output T = targetData (FinalTableFormula.output T) := by
  apply Prod.ext
  · exact (FinalTableFormula.variable_count T).symm
  · change (List.range T.darts).flatMap (fun e => eventData (T,e)) =
      ((List.finRange T.darts).flatMap
        (eventBlock (Complexity.FinalCNFPattern.tableVerifier T) (by decide))).map targetClauseData
    rw [List.map_flatMap]
    have he : (List.finRange T.darts).map Fin.val = List.range T.darts := by
      apply List.ext_getElem
      · simp
      · intro i hi hj; simp
    rw [← he,List.flatMap_map]
    apply List.flatMap_congr
    intro e he
    exact event_correct T e
noncomputable def poly : Poly tableCode FormulaParser.targetCode FinalTableFormula.output :=
  outputPoly.encodeCongr id (fun _ => rfl) (fun T => by
    change FormulaParser.dataCode (output T) = FormulaParser.dataCode (targetData (FinalTableFormula.output T))
    rw [output_correct])
noncomputable def gapPoly (H : RoundTables.BaseTable) :
    Poly FormulaParser.targetCode FormulaParser.targetCode (TableIteration.gapMap H) :=
  (IterationMachine.poly H).comp poly
end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_SimpleLC
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count
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

namespace VertexCover.Machine.SimpleLC
open UniqueGames.Foundations
open FormulaParser InitialTable ClauseProjection

abbrev NEFormula := {F : Target.Formula // F.clauses ≠ []}
noncomputable def code (F : NEFormula) : List Bool := targetCode F.val
noncomputable def output (F : NEFormula) : FixedLC 7 2 where
  u := F.val.clauses.length
  v := F.val.variables
  M := F.val.clauses.length*3
  apos := by decide
  bpos := by decide
  Mpos := Nat.mul_pos (List.length_pos_iff.mpr F.property) (by decide)
  left := (simpleGame F.val F.property).left
  right := (simpleGame F.val F.property).right
  projection := (simpleGame F.val F.property).projection

 theorem lit_clause (F : Target.Formula) (j : Fin F.clauses.length) (k : Fin 3) :
    lit (targetClauseData (PCP.clauseAt F j)) k =
      ((literalAt F j k).positive,(literalAt F j k).variableIndex.val) := by
  fin_cases k <;> rfl
 theorem signature_clause (F : Target.Formula) (j : Fin F.clauses.length) :
    signature (targetClauseData (PCP.clauseAt F j)) =
      (fun k => (literalAt F j k).positive,
       fun kl => decide ((literalAt F j kl.1).variableIndex=(literalAt F j kl.2).variableIndex)) := by
  apply Prod.ext
  · funext k; exact congrArg Prod.fst (lit_clause F j k)
  · funext kl
    simp only [signature,lit_clause,Fin.val_inj]
 theorem relation_clause (F : Target.Formula) (j : Fin F.clauses.length) (k : Fin 3) :
    relation (signature (targetClauseData (PCP.clauseAt F j))) k =
      fun label => finTwoEquiv.symm (flipSign (literalAt F j k).positive
        ((normalizePattern F j (patternEquiv.symm label)).val k)) := by
  rw [signature_clause]
  funext label
  by_cases hg : Consistent F j (patternEquiv.symm label)
  · rw [normalizePattern,ite_eq_left hg]
    simp only [relation,decide_eq_true_eq]
    unfold Consistent at hg
    rw [ite_eq_left hg]
  · rw [normalizePattern,ite_eq_right hg]
    simp only [relation,decide_eq_true_eq]
    unfold Consistent at hg
    rw [ite_eq_right hg]
    change finTwoEquiv.symm (flipSign _ (flipSign _ (if _ then _ else _))) = _
    congr 2

 theorem row_correct (F : NEFormula) (e : Fin (output F).M) :
    row (targetData F.val,e.val) =
      (((output F).left e |>.val,(output F).right e |>.val),(output F).projection e) := by
  let j := (finProdFinEquiv.symm e).1
  let k := (finProdFinEquiv.symm e).2
  have hd : e.val/3=j.val := rfl
  have hm : (⟨e.val%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=k := rfl
  dsimp only [row]
  rw [hd,hm,InitialTable.clause_lookup,lit_clause,relation_clause]
  apply Prod.ext
  · rfl
  · funext label
    simp only [output,simpleGame,game,normalizeLabel,Equiv.symm_apply_apply]
    rfl

noncomputable def outputPoly : Poly code FixedLC.code output := by
  let enc := FormulaParser.dataCode
  let u := (Poly.snd natBits (listBits unaryClauseCode)).comp
    (Poly.listLength unaryClauseCode clauseDefault)
  let v := Poly.fst natBits (listBits unaryClauseCode)
  let M := (u.pair (Poly.const enc natBits 3)).comp Poly.natMul
  let erase := fun F : NEFormula => targetData F.val
  let cu : Poly code natBits (fun F => (output F).u) :=
    u.encodeCongr erase (fun _ => rfl) (fun F => by simp [output,erase,targetData])
  let cv : Poly code natBits (fun F => (output F).v) :=
    v.encodeCongr erase (fun _ => rfl) (fun _ => rfl)
  let cm : Poly code natBits (fun F => (output F).M) :=
    M.encodeCongr erase (fun _ => rfl) (fun F => by simp [output,erase,targetData])
  let cr : Poly (prodBits code natBits) FixedLC.rowCode (fun p : NEFormula × ℕ => row (erase p.1,p.2)) :=
    rowPoly.encodeCongr (fun p : NEFormula × ℕ => (erase p.1,p.2)) (fun _ => rfl) (fun _ => rfl)
  let F₀ : NEFormula := ⟨⟨1,[#v[⟨0,true⟩,⟨0,true⟩,⟨0,true⟩]]⟩,by decide⟩
  exact FixedLC.materializePoly code F₀ output (by decide) cu cv cm cr row_correct
end VertexCover.Machine.SimpleLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Main
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

namespace VertexCover.Machine.MainReduction
open UniqueGames UniqueGames.Foundations
open ClauseProjection
noncomputable section

def gapInput (F : Target.Formula) : SimpleLC.NEFormula :=
  ⟨PCP.TableIteration.gapMap fixedBaseTable F,
    PCP.TableIteration.gapMap_nonempty fixedBaseTable F⟩
def gapInputPoly : Poly FormulaParser.targetCode SimpleLC.code gapInput :=
  (FinalCNFMachine.gapPoly fixedBaseTable).encodeCongr id (fun _ => rfl) (fun _ => rfl)
def base (input : List Bool) : FixedLC 7 2 :=
  SimpleLC.output (gapInput (BinaryFormula.dense (inputFormula input)))
def basePoly : Poly id FixedLC.code base :=
  (((FormulaParser.inputFormulaPoly.comp FormulaParser.densePoly).comp gapInputPoly).comp
    SimpleLC.outputPoly).congr (fun _ => rfl)

def repeated (σ : ℝ) (hσ : 0<σ) (input : List Bool) :
    FixedLC (7^repetitionLength σ hσ) (2^repetitionLength σ hσ) :=
  (base input).power (repetitionLength σ hσ)
def repeatedPoly (σ : ℝ) (hσ : 0<σ) :
    Poly id FixedLC.code (repeated σ hσ) :=
  basePoly.comp (FixedLC.powerPoly (by decide) (by decide) (repetitionLength σ hσ))
def repetitionIso (σ : ℝ) (hσ : 0<σ) (input : List Bool) :
    LabelCover.Iso (repeated σ hσ input).toLC (binaryReduction σ hσ input) :=
  LabelCover.numberIso (base input).toLC (repetitionLength σ hσ)
theorem repeated_complete (σ : ℝ) (hσ : 0<σ) (input : List Bool) (h : ThreeSAT input) :
    ∃ A : (repeated σ hσ input).toLC.Labeling,
      ∀ e, (repeated σ hσ input).toLC.Satisfies A e := by
  obtain ⟨A,hA⟩ := binaryReduction_complete σ hσ input h
  exact ⟨(repetitionIso σ hσ input).symm.labeling A,
    (repetitionIso σ hσ input).symm.perfect A hA⟩
theorem repeated_sound (σ : ℝ) (hσ : 0<σ) (input : List Bool) (h : ¬ThreeSAT input) :
    (repeated σ hσ input).toLC.value < σ := by
  rw [(repetitionIso σ hσ input).value_eq]
  exact binaryReduction_sound σ hσ input h

def construct (m : ℕ) (hm : 4 ≤ m) (input : List Bool) : ExplicitGraph :=
  GraphMachine.explicitGraph (repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input)
    (Parameters.d m) (Parameters.t m)
def constructPoly (m : ℕ) (hm : 4 ≤ m) : Poly id ExplicitGraph.bits (construct m hm) :=
  (repeatedPoly (Parameters.σ m) (Parameters.σ_between m hm).1).comp
    (GraphMachine.outputPoly (pow_pos (by decide) _) (pow_pos (by decide) _)
      (Parameters.d m) (Parameters.t m))
theorem construct_complete (m : ℕ) (hm : 4 ≤ m) (input : List Bool) (h : ThreeSAT input) :
    ((construct m hm input).coverNumber:ℝ) <
      (1/2+1/(m:ℝ))*(construct m hm input).n := by
  let I := repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input
  obtain ⟨A,hA⟩ := repeated_complete (Parameters.σ m) (Parameters.σ_between m hm).1 input h
  obtain ⟨C,hC,hcard⟩ := I.toLC.graph_completeness_cover m hm A hA
  exact ExplicitGraph.numbered_complete _ (GraphMachine.fullEquiv I (Parameters.d m)) C hC _ hcard
theorem construct_sound (m : ℕ) (hm : 4 ≤ m) (input : List Bool) (h : ¬ThreeSAT input) :
    (1-1/(m:ℝ))*(construct m hm input).n < ((construct m hm input).coverNumber:ℝ) := by
  let I := repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input
  have hv := repeated_sound (Parameters.σ m) (Parameters.σ_between m hm).1 input h
  exact ExplicitGraph.numbered_sound _ (GraphMachine.fullEquiv I (Parameters.d m)) _
    (I.toLC.graph_soundness_cover m hm hv.le)

def reduction (m : ℕ) (hm : 4 ≤ m) : GapReduction m where
  construct := construct m hm
  computation := (constructPoly m hm).computation
  finiteAlphabet := (constructPoly m hm).finiteAlphabet
  completeness := construct_complete m hm
  soundness := construct_sound m hm
end
end VertexCover.Machine.MainReduction

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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


