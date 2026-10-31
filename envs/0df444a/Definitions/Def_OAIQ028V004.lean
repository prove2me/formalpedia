-- Prove2me | Definitions.Def_OAIQ028V004
-- name    : OAIQ028V004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:11:13.193975+00:00
-- url     : https://prove2.me/theorems/373ec50f-a212-40eb-8c70-41a1b952f9a6
-- title:
--   Definitions bundle OAIQ028V004 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 590 declarations of OpenAI's Lean: 214 definitions, 3 instances and 373 theorems. The definitions and types are `OAI.UniqueGames.Foundations.PCP.PoweringWalks.headTailEquiv`, `OAI.UniqueGames.Foundations.PCP.PoweringWalks.leftFromPivot`, `OAI.UniqueGames.Foundations.PCP.PoweringWalks.pivotEquiv`, `OAI.UniqueGames.Foundations.PCP.PreprocessingGuarantees.restrictedLabel`, `OAI.UniqueGames.Foundations.PCP.PreprocessingLevels.boundedLevel`, `OAI.UniqueGames.Foundations.PCP.PreprocessingLevels.cloudPaddedSize`, `OAI.UniqueGames.Foundations.PCP.PreprocessingLevels.paddedSize`, `OAI.UniqueGames.Foundations.PCP.PreprocessingLevels.searchResult`, `OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.lazy`, `OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.overlay`, `OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.extendLabeling`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.BaseTable`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.emptyTable`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.internalDegree`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.liftedLabel`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.padding`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.resizeTable`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.BaseTable`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.degree`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.regularVertices`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.vertices`, `OAI.UniqueGames.Foundations.PCP.RoundTables.BaseTable`, `OAI.UniqueGames.Foundations.PCP.SpectralCut.cut`, `OAI.UniqueGames.Foundations.PCP.SpectralReturn.iterateOperator`, `OAI.UniqueGames.Foundations.PCP.SpectralReturn.markedStep`, `OAI.UniqueGames.Foundations.PCP.SpectralReturn.returnMass`, `OAI.UniqueGames.Foundations.Repetition.normalizeOr`, `OAI.VertexCover.Approximation.cardPoly`, `OAI.VertexCover.Approximation.testPoly`, `OAI.VertexCover.ClauseProjection.Consistent`, `OAI.VertexCover.ClauseProjection.InputSAT`, `OAI.VertexCover.ClauseProjection.assignmentOf`, `OAI.VertexCover.ClauseProjection.clauseValue`, `OAI.VertexCover.ClauseProjection.decodedLabeling`, `OAI.VertexCover.ClauseProjection.defaultAssignment`, `OAI.VertexCover.ClauseProjection.defaultPattern`, `OAI.VertexCover.ClauseProjection.falseFormula`, `OAI.VertexCover.ClauseProjection.game`, `OAI.VertexCover.ClauseProjection.honestLabeling`, `OAI.VertexCover.ClauseProjection.inputFormula` and 174 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Analysis_BatchFunctionOwnLipschitz`, `VertexCover_Analysis_BatchGradientForm`, `VertexCover_Analysis_BlockLawNegInvariant`, `VertexCover_Analysis_CanonicalGradientInvariant`, `VertexCover_Analysis_CanonicalGradientValid`, `VertexCover_Analysis_DenseSeparatorData`, `VertexCover_Analysis_ErasedSeedSeparatorAverage`, `VertexCover_Analysis_FiniteMeanConditionBest`, `VertexCover_Analysis_GraphCompleteness`, `VertexCover_Analysis_IndependentSecondMomentLower`, `VertexCover_Analysis_IntegralUpdate`, `VertexCover_Analysis_ListMassHitMaximum`, `VertexCover_Analysis_MidpointGridTail`, `VertexCover_Analysis_OwnFiberTower`, `VertexCover_Analysis_OwnGradientMeasurable`, `VertexCover_Analysis_OwnGradientUnsupported`, `VertexCover_Analysis_OwnListEnergy`, `VertexCover_Analysis_OwnMeanPartialAe`, `VertexCover_Analysis_OwnPrivateListsDecoding`, `VertexCover_Analysis_OwnTotalEnergyNo`, `VertexCover_Analysis_OwnTotalVarianceNo`, `VertexCover_Analysis_Poincare`, `VertexCover_Analysis_PrivateMassSumHits`, `VertexCover_Analysis_Restriction`, `VertexCover_Analysis_RestrictionSum`, `VertexCover_Analysis_SeedEnergyBudget`, `VertexCover_Analysis_SelectedIntegralAbs`, `VertexCover_Analysis_SeparatorBoundCube`, `VertexCover_Analysis_SeparatorRoundingErrorAe`, `VertexCover_Analysis_StarEnergyBudget`, `VertexCover_Analysis_StarMeanContinuous`, `VertexCover_Analysis_ThresholdListEnergy`, `VertexCover_Analysis_VarianceCoordinateSum`, `VertexCover_Analysis_VariancePi`, `VertexCover_Analysis_WeightEnergyBudget`, `VertexCover_Analysis_ZeroMemIncidenceHull`, `VertexCover_Machines_Address`, `VertexCover_Machines_AlphabetFrame`, `VertexCover_Machines_Approximation`, `VertexCover_Machines_BinaryOutput`, `VertexCover_Machines_BoundedBinary`, `VertexCover_Machines_Cardinal`, `VertexCover_Machines_Cloud`, `VertexCover_Machines_CloudIndex`, `VertexCover_Machines_Codec`, `VertexCover_Machines_Composition`, `VertexCover_Machines_DescriptorMath`, `VertexCover_Machines_ExpanderStep`, `VertexCover_Machines_FinCode`, `VertexCover_Machines_FiniteMemory`, `VertexCover_Machines_FixedOps`, `VertexCover_Machines_Generic`, `VertexCover_Machines_ListFilter`, `VertexCover_Machines_ListMore`, `VertexCover_Machines_ListNat`, `VertexCover_Machines_Lists`, `VertexCover_Machines_Loop`, `VertexCover_Machines_NatDiv`, `VertexCover_Machines_Naturals`, `VertexCover_Machines_NumberedGraph`, `VertexCover_Machines_Option`, `VertexCover_Machines_Pair`, `VertexCover_Machines_ParseFrame`, `VertexCover_Machines_ParseName`, `VertexCover_Machines_ParseSize`, `VertexCover_Machines_Primitives`, `VertexCover_Machines_Profile`, `VertexCover_Machines_ProfileCompat`, `VertexCover_Machines_ProfileSlot`, `VertexCover_Machines_TableBase`, `VertexCover_PCP_PoweringLazy`, `VertexCover_PCP_PoweringReturn`, `VertexCover_PCP_PoweringWalks`, `VertexCover_PCP_PreprocessingCloudIndex`, `VertexCover_PCP_PreprocessingGuarantees`, `VertexCover_PCP_PreprocessingLevels`, `VertexCover_PCP_PreprocessingOverlayTables`, `VertexCover_PCP_PreprocessingPaddingTables`, `VertexCover_PCP_PreprocessingRegularSoundness`, `VertexCover_PCP_PreprocessingRegularTables`, `VertexCover_PCP_PreprocessingTableSpectral`, `VertexCover_PCP_PreprocessingTables`, `VertexCover_PCP_RoundTables`, `VertexCover_PCP_SpectralCut`, `VertexCover_PCP_SpectralReturn`, `VertexCover_PCP_VerifierToCNF`, `VertexCover_PCP_VertexPadding`, `VertexCover_Reduction_AverageCommute`, `VertexCover_Reduction_ConditionNested`, `VertexCover_Reduction_CoordinateProductInvariant`, `VertexCover_Reduction_FiniteMeanUnionBound`, `VertexCover_Reduction_GraphSoundness`, `VertexCover_Reduction_HighVectorsSeparated`, `VertexCover_Reduction_IntegralCoe`, `VertexCover_Reduction_PairEventMean`, `VertexCover_Reduction_PairHitsProbability`, `VertexCover_Reduction_PairSeedFiberCard`, `VertexCover_Reduction_PrivatePairProjectionRight`, `VertexCover_Reduction_PrivateProjectionBatchLower`, `VertexCover_Reduction_PrivateProjectionCoordinateVariance`, `VertexCover_Reduction_PrivateProjectionGroupLower`, `VertexCover_Reduction_PrivateProjectionSurvival`, `VertexCover_Reduction_PrivateTotalEnergyLaw`, `VertexCover_Reduction_RejectionCount`, `VertexCover_Reduction_RestrictionFrozen`, `VertexCover_Reduction_RestrictionStarBudget`, `VertexCover_Reduction_SeparatorContinuousSumOdd`, `VertexCover_Reduction_SeparatorStarOscillation`, `VertexCover_Reduction_SimpleParallel`, `VertexCover_Reduction_Soundness`, `VertexCover_Repetition_Completion`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`; the bundles `OAIQ028V000`, `OAIQ028V001` and `OAIQ028V002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ028V006` and `OAIQ028V007`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover
import Definitions.Def_OAIQ028V000
import Definitions.Def_OAIQ028V001
import Definitions.Def_OAIQ028V002

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_mul_right (f : A → ℝ) («c» : ℝ) :
    mean (fun x => f x * «c») = mean f * «c» :=
  (Finset.expect_mul _ f «c»).symm

end Averages

end

end UniqueGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairHitsProbability
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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
namespace Decoding

variable (Φ : LabelCover) {d : ℕ}
variable (iU : Fin Φ.u → Φ.Query d) (iV : Fin Φ.v → Φ.Query d)
variable (pU : ∀ x, x ∈ (iU x).scopeU) (pV : ∀ y, y ∈ (iV y).scopeV)
variable (LU : ∀ x, List (iU x).LocalLabel) (LV : ∀ y, List (iV y).LocalLabel)

theorem pairHit_decodes {ell : ℕ}
    (hLU : ∀ x, (LU x).length ≤ ell) (hLV : ∀ y, (LV y).length ≤ ell)
    (c : Fin Φ.M) (hc : PairHit Φ iU iV LU LV c) :
    ∃ ρ : Fin ell, ∃ τ : Fin ell,
      Φ.Satisfies (leftAt Φ iU pU LU ρ, rightAt Φ iV pV LV τ) c := by
  classical
  obtain ⟨labU, hlabU, labV, hlabV, hcompat⟩ := hc
  obtain ⟨ρ, hρ, eρ⟩ := List.mem_iff_getElem.mp hlabU
  obtain ⟨τ, hτ, eτ⟩ := List.mem_iff_getElem.mp hlabV
  refine ⟨⟨ρ, lt_of_lt_of_le hρ (hLU _)⟩, ⟨τ, lt_of_lt_of_le hτ (hLV _)⟩, ?_⟩
  have hs := hcompat.2.2.2 ⟨iU (Φ.left c), labU⟩ (by simp)
    ⟨iV (Φ.right c), labV⟩ (by simp) c (pU _) (pV _)
  simpa only [Satisfies, leftAt, rightAt, dite_eq_left hρ, dite_eq_left hτ, eρ, eτ] using hs

include pU pV

theorem pairHits_card_le {ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ)
    (hLU : ∀ x, (LU x).length ≤ ell) (hLV : ∀ y, (LV y).length ≤ ell) :
    ((pairHits Φ iU iV LU LV).card : ℝ) ≤ (ell : ℝ)^2 * σ * Φ.M := by
  classical
  let good : (Fin ell × Fin ell) → Finset (Fin Φ.M) := fun a =>
    Finset.univ.filter (Φ.Satisfies (leftAt Φ iU pU LU a.1, rightAt Φ iV pV LV a.2))
  have hs : pairHits Φ iU iV LU LV ⊆ Finset.univ.biUnion good := by
    intro c hc
    have hh : PairHit Φ iU iV LU LV c := (Finset.mem_filter.mp hc).2
    obtain ⟨ρ, τ, ha⟩ := pairHit_decodes Φ iU iV pU pV LU LV hLU hLV c hh
    exact Finset.mem_biUnion.mpr ⟨(ρ, τ), Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha⟩⟩
  have hcard := (Finset.card_le_card hs).trans Finset.card_biUnion_le
  calc
    ((pairHits Φ iU iV LU LV).card : ℝ) ≤
        ((∑ a : Fin ell × Fin ell, (good a).card : ℕ) : ℝ) := Nat.cast_le.mpr hcard
    _ = ∑ a : Fin ell × Fin ell, ((good a).card : ℝ) := by simp
    _ ≤ ∑ _a : Fin ell × Fin ell, σ * Φ.M := by
      apply Finset.sum_le_sum
      intro a _
      exact Φ.count_le_of_value_le hval _
    _ = (ell : ℝ)^2 * σ * Φ.M := by
      simp [Fintype.card_prod, pow_two]
      ring

end Decoding
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairSeedFiberCard
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

theorem query_update_left (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) :
    Φ.query (Φ.replaceSeed seed e c) e.1.1 = Φ.leftTemplate seed e (Φ.left c) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k
    dsimp only [query, replaceSeed, leftTemplate] at *
    by_cases hk : k = ⟨e.1.2, e.2⟩
    · subst k
      simp [query, replaceSeed, ]
    · have hne : (⟨(e.1.1, k.1), k.2⟩ : PositionPair d) ≠ e := by
        intro heq
        apply hk
        exact Subtype.ext (congrArg (fun a : PositionPair d => a.1.2) heq)
      simp only [Function.update, dite_eq_right hne]
      split_ifs with h
      · exact False.elim (hk (Subtype.ext (congrArg Subtype.val h)))
      · rfl
  · funext k
    have hne : (⟨(k.1, e.1.1), k.2⟩ : PositionPair d) ≠ e := by
      intro heq
      exact (ne_of_lt e.2) (congrArg (fun a : PositionPair d => a.1.2) heq)
    simp [query, replaceSeed, leftTemplate, Function.update_of_ne hne]

theorem query_update_right (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) :
    Φ.query (Φ.replaceSeed seed e c) e.1.2 = Φ.rightTemplate seed e (Φ.right c) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k
    have hne : (⟨(e.1.2, k.1), k.2⟩ : PositionPair d) ≠ e := by
      intro heq
      exact (ne_of_lt e.2).symm (congrArg (fun a : PositionPair d => a.1.1) heq)
    simp [query, replaceSeed, rightTemplate, Function.update_of_ne hne]
  · funext k
    dsimp only [query, replaceSeed, rightTemplate] at *
    by_cases hk : k = ⟨e.1.1, e.2⟩
    · subst k
      simp [query, replaceSeed, ]
    · have hne : (⟨(k.1, e.1.2), k.2⟩ : PositionPair d) ≠ e := by
        intro heq
        apply hk
        exact Subtype.ext (congrArg (fun a : PositionPair d => a.1.1) heq)
      simp only [Function.update, dite_eq_right hne]
      split_ifs with h
      · exact False.elim (hk (Subtype.ext (congrArg Subtype.val h)))
      · rfl

theorem pairSeedFiber_card_le (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d)
    (hL : ∀ i, (L i).length ≤ ell) (seed : Φ.Seeds d) (e : PositionPair d) :
    ((Φ.pairSeedFiber L seed e).card : ℝ) ≤ (ell : ℝ)^2 * σ * Φ.M := by
  classical
  have heq : Φ.pairSeedFiber L seed e = Decoding.pairHits Φ
      (Φ.leftTemplate seed e) (Φ.rightTemplate seed e)
      (fun x => L (Φ.leftTemplate seed e x)) (fun y => L (Φ.rightTemplate seed e y)) := by
    ext c
    simp only [pairSeedFiber, Decoding.pairHits, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold PairSeedHit Decoding.PairHit
    rw [Φ.query_update_left seed e c, Φ.query_update_right seed e c]
  rw [heq]
  exact Decoding.pairHits_card_le Φ _ _ (Φ.leftTemplate_mem seed e)
    (Φ.rightTemplate_mem seed e) _ _ hval (fun _ => hL _) (fun _ => hL _)

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairEventMean
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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
namespace VertexCover

theorem finiteMean_le_of_fibers {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (j : ι) (f : (ι → α) → ℝ) (B : ℝ)
    (h : ∀ seed, ∑ a : α, f (Function.update seed j a) ≤ B) :
    finiteMean f ≤ B / Fintype.card α := by
  classical
  have ha : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (0 : ℝ) < Fintype.card (ι → α) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ι → α)))
    (fun seed _ => h seed)
  rw [sum_updates] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  unfold finiteMean
  apply (div_le_div_iff₀ hs ha).mpr
  nlinarith

end VertexCover

namespace VertexCover.LabelCover

theorem pairEvent_mean_le (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d) (hL : ∀ i, (L i).length ≤ ell)
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (e : ↥(internalPairs J)) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
      ≤ (ell : ℝ)^2 * σ := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have h := VertexCover.finiteMean_le_of_fibers e
    (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
    ((ell : ℝ)^2 * σ * Φ.M) (fun hidden => ?_)
  · simpa only [Fintype.card_fin, mul_div_cancel_right₀ _ (show (Φ.M : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt Φ.M_pos))] using h
  · simp_rw [Φ.spliceSeeds_update]
    have hb := Φ.pairSeedFiber_card_le hval L hL (Φ.spliceSeeds J frozen hidden) e.1
    have heq : ((Φ.pairSeedFiber L (Φ.spliceSeeds J frozen hidden) e.1).card : ℝ) =
        ∑ c : Fin Φ.M, VertexCover.truthValue (Φ.PairSeedHit L
          (Φ.replaceSeed (Φ.spliceSeeds J frozen hidden) e.1 c) e.1) := by
      simp only [pairSeedFiber, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro c _
      unfold VertexCover.truthValue
      split_ifs <;> simp
    rwa [heq] at hb

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ListMassHitMaximum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

noncomputable def incidence (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) :
    Fin d → Fin (Φ.WeightDimension d) → ℝ := fun j k =>
  truthValue (∃ a : (Φ.query seed j).LocalLabel,
    (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I ∧ (Φ.query seed j).slot a = k)

theorem incidence_at_label (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) (j : Fin d) (a : (Φ.query seed j).LocalLabel) :
    Φ.incidence seed I j ((Φ.query seed j).slot a) =
      truthValue ((⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I) := by
  unfold incidence
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, heq⟩
    have : b = a := (Φ.query seed j).slot_injective heq
    simpa [this] using hb
  · intro ha; exact ⟨a, ha, rfl⟩

theorem incidence_eq_single (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d)
    (a : (Φ.query seed j).LocalLabel)
    (ha : (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I) (k : Fin (Φ.WeightDimension d)) :
    Φ.incidence seed I j k = truthValue ((Φ.query seed j).slot a = k) := by
  unfold incidence
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, hbk⟩
    have hab : b = a := by
      have := hI.1 ⟨_, b⟩ hb ⟨_, a⟩ ha rfl
      exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq
    simpa [hab] using hbk
  · intro h; exact ⟨a, ha, h⟩

theorem incidence_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d) :
    ∑ k, |Φ.incidence seed I j k| ≤ 1 := by
  classical
  by_cases h : ∃ a : (Φ.query seed j).LocalLabel,
      (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I
  · obtain ⟨a, ha⟩ := h
    simp_rw [Φ.incidence_eq_single seed hI j a ha]
    have ht : ∀ P, |truthValue P| = truthValue P := by
      intro P; by_cases hP : P <;> simp [truthValue, hP]
    simp_rw [ht]
    simp [truthValue, eq_comm]
  · have hz : ∀ k, Φ.incidence seed I j k = 0 := by
      intro k
      simp only [incidence, truthValue]
      rw [ite_eq_right (fun ⟨label, hlabel, _⟩ => h ⟨label, hlabel⟩)]
    simp [hz]

noncomputable def incidenceHull (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    Set (Fin d → Fin (Φ.WeightDimension d) → ℝ) :=
  convexHull ℝ {g | ∃ I, Φ.Compatible I ∧
    (g = Φ.incidence seed I ∨ g = -Φ.incidence seed I)}

theorem listMass_incidence (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) :
    Φ.listMass L seed J (Φ.incidence seed I) = (Φ.hitPositions L seed I J).card := by
  classical
  have hblock : ∀ j, (∑ a ∈ (L (Φ.query seed j)).toFinset,
      |Φ.incidence seed I j ((Φ.query seed j).slot a)|) =
      truthValue (Φ.ListHit L seed I j) := by
    intro j
    by_cases h : Φ.ListHit L seed I j
    · obtain ⟨a, haL, haI⟩ := h
      have honly : ∀ b : (Φ.query seed j).LocalLabel,
          (⟨Φ.query seed j, b⟩ : Φ.Coordinate d) ∈ I ↔ b = a := by
        intro b
        constructor
        · intro hb
          have := hI.1 ⟨_, b⟩ hb ⟨_, a⟩ haI rfl
          exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq
        · rintro rfl; exact haI
      simp_rw [Φ.incidence_at_label, honly]
      have ht : ∀ P, |truthValue P| = truthValue P := by
        intro P; by_cases hP : P <;> simp [truthValue, hP]
      simp_rw [ht]
      rw [show truthValue (Φ.ListHit L seed I j) = 1 by
        simp [truthValue, show Φ.ListHit L seed I j from ⟨a, haL, haI⟩]]
      rw [Finset.sum_eq_single a]
      · simp [truthValue]
      · intro b hb hba; simp [truthValue, hba]
      · intro ha; exact (ha (List.mem_toFinset.mpr haL)).elim
    · have hz : ∀ a ∈ (L (Φ.query seed j)).toFinset,
          (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∉ I := by
        intro a ha haI
        exact h ⟨a, List.mem_toFinset.mp ha, haI⟩
      rw [show truthValue (Φ.ListHit L seed I j) = 0 by simp [truthValue, h]]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Φ.incidence_at_label]
      simp [truthValue, hz a ha]
  simp only [listMass, hblock]
  rw [hitPositions, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : Φ.ListHit L seed I j <;> simp [truthValue, h]

theorem listMass_le_hitMaximum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) :
    Φ.listMass L seed J g ≤ Φ.listHitMaximum L seed J := by
  classical
  apply convexHull_min (t := {g | Φ.listMass L seed J g ≤
    (Φ.listHitMaximum L seed J : ℝ)}) ?_ (Φ.listMass_convex_sublevel L seed J _) hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · change Φ.listMass L seed J (Φ.incidence seed I) ≤ _
    rw [Φ.listMass_incidence L seed J hI]
    exact_mod_cast (Finset.le_sup (f := fun I => (Φ.hitPositions L seed I J).card)
      (show I ∈ Φ.compatibleSelections d from by
      simp [compatibleSelections, hI]))
  · change Φ.listMass L seed J (-Φ.incidence seed I) ≤ _
    have hn : Φ.listMass L seed J (-Φ.incidence seed I) =
        Φ.listMass L seed J (Φ.incidence seed I) := by simp [listMass]
    rw [hn, Φ.listMass_incidence L seed J hI]
    exact_mod_cast (Finset.le_sup (f := fun I => (Φ.hitPositions L seed I J).card)
      (show I ∈ Φ.compatibleSelections d from by
      simp [compatibleSelections, hI]))

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_FiniteMeanUnionBound
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
section

namespace VertexCover

theorem finiteMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem finiteMean_const {α : Type*} [Fintype α] [Nonempty α] (b : ℝ) :
    finiteMean (fun _ : α => b) = b := by
  simp only [finiteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (show (Fintype.card α : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos))]

theorem finiteMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a + g a) = finiteMean f + finiteMean g := by
  simp only [finiteMean, Finset.sum_add_distrib, add_div]

theorem finiteMean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    finiteMean (fun a => ∑ b, f a b) = ∑ b, finiteMean (fun a => f a b) := by
  unfold finiteMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteMean_one_add_sum {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : α → β → ℝ) :
    finiteMean (fun a => (1 : ℝ) + ∑ b, f a b) =
      1 + ∑ b, finiteMean (fun a => f a b) := by
  rw [finiteMean_add, finiteMean_const, finiteMean_sum]

theorem finiteMean_union_bound {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (z : α → ℝ) (f : α → β → ℝ) (B : ℝ)
    (hz : ∀ a, z a ≤ 1 + ∑ b, f a b)
    (hf : ∀ b, finiteMean (fun a => f a b) ≤ B) :
    finiteMean z ≤ 1 + Fintype.card β * B := by
  calc
    finiteMean z ≤ finiteMean (fun a => (1 : ℝ) + ∑ b, f a b) := finiteMean_mono hz
    _ = 1 + ∑ b, finiteMean (fun a => f a b) := finiteMean_one_add_sum f
    _ ≤ 1 + ∑ _b : β, B := add_le_add_right (Finset.sum_le_sum (fun b _ => hf b)) 1
    _ = 1 + Fintype.card β * B := by simp

end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_HighVectorsSeparated
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

open scoped Classical in
theorem pairEvents_card_eq_sum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    ((Φ.pairEvents L seed J).card : ℝ) =
      ∑ e : ↥(internalPairs J), VertexCover.truthValue (Φ.PairSeedHit L seed e.1) := by
  classical
  rw [← Finset.sum_subtype (internalPairs J) (fun _ => Iff.rfl)
    (fun e : PositionPair d => VertexCover.truthValue (Φ.PairSeedHit L seed e))]
  simp only [pairEvents, internalPairs, Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hj : e.1.1 ∈ J <;> by_cases hk : e.1.2 ∈ J <;>
    by_cases hh : Φ.PairSeedHit L seed e <;> simp [VertexCover.truthValue, hj, hk, hh]

theorem decoding_upper_bound (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d) (hL : ∀ i, (L i).length ≤ ell)
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum L (Φ.spliceSeeds J frozen hidden) J : ℝ)) ≤
      1 + (J.card.choose 2 : ℝ) * (ell : ℝ)^2 * σ := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have h := VertexCover.finiteMean_union_bound
    (fun hidden : Φ.HiddenSeeds J => (Φ.listHitMaximum L (Φ.spliceSeeds J frozen hidden) J : ℝ))
    (fun (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J)) =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
    ((ell : ℝ)^2 * σ) ?_ (fun e => Φ.pairEvent_mean_le hval L hL J frozen e)
  · simpa only [Fintype.card_coe, internalPairs_card, mul_assoc] using h
  · intro hidden
    have hpoint := Nat.cast_le (α := ℝ).mpr
      (Φ.listHitMaximum_le L (Φ.spliceSeeds J frozen hidden) J)
    simpa only [Nat.cast_add, Nat.cast_one, Φ.pairEvents_card_eq_sum] using hpoint

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BatchGradientForm
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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

theorem selectionForm_increment (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.selectionForm I (Φ.increment (Φ.query seed j) s) =
      ∑ k, Φ.incidence seed I j k * s k := by
  classical
  rw [Φ.selectionForm_apply]
  by_cases h : ∃ a : (Φ.query seed j).LocalLabel,
      (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I
  · obtain ⟨a, ha⟩ := h
    rw [Finset.sum_eq_single (⟨Φ.query seed j, a⟩ : Φ.Coordinate d)]
    · rw [Φ.increment_same]
      simp_rw [Φ.incidence_eq_single seed hI j a ha]
      simp [truthValue, eq_comm]
    · intro p hp hpa
      apply Φ.increment_other
      intro heq
      exact hpa (hI.1 p hp ⟨_, a⟩ ha heq)
    · intro hn; exact (hn ha).elim
  · have hz : ∀ p ∈ I, Φ.increment (Φ.query seed j) s p = 0 := by
      intro p hp
      apply Φ.increment_other
      intro heq
      rcases p with ⟨i,a⟩
      change i = Φ.query seed j at heq
      subst i
      exact h ⟨a,hp⟩
    rw [Finset.sum_eq_zero hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k hk
    have hi : Φ.incidence seed I j k = 0 := by
      simp only [incidence, truthValue]
      rw [ite_eq_right (fun ⟨label, hlabel, _⟩ => h ⟨label, hlabel⟩)]
    rw [hi, zero_mul]

theorem batchGradient_form (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I)
    (j : J) (k : Fin (Φ.WeightDimension d)) :
    Φ.batchGradient J ((Φ.selectionForm I).comp (Φ.batchSumCLM seed J)) j k =
      Φ.incidence seed I j k := by
  classical
  change Φ.selectionForm I (Φ.batchSum seed J (Pi.single j (Pi.single k 1))) = _
  unfold batchSum
  rw [map_sum]
  simp_rw [Φ.selectionForm_increment seed hI]
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply, mul_ite]
  · intro j' hj' hne
    simp [Pi.single_eq_of_ne hne]
  · simp

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ZeroMemIncidenceHull
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

theorem incidence_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) (j : Fin d) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    Φ.incidence seed I j k = 0 := by
  simp only [incidence, truthValue]
  rw [ite_eq_right (fun ⟨a, _, h⟩ => hk a h)]

theorem hull_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) (j : Fin d) : ∑ k, |g j k| ≤ 1 := by
  classical
  have hc : Convex ℝ {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
      ∑ k, |g j k| ≤ 1} := by
    intro x hx y hy a b ha hb hab
    change ∑ k, |a*x j k+b*y j k| ≤ 1
    calc
      _ ≤ ∑ k, (a*|x j k|+b*|y j k|) := by
        apply Finset.sum_le_sum; intro k hk
        simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
          abs_add_le (a*x j k) (b*y j k)
      _ = a*(∑ k, |x j k|)+b*(∑ k, |y j k|) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa using hab
  apply convexHull_min (t := {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
    ∑ k, |g j k| ≤ 1}) ?_ hc hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · exact Φ.incidence_block_bound seed hI j
  · simpa using Φ.incidence_block_bound seed hI j

theorem hull_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) (j : Fin d) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    g j k = 0 := by
  classical
  have hc : Convex ℝ {g : Fin d → Fin (Φ.WeightDimension d) → ℝ | g j k = 0} := by
    intro x hx y hy a b ha hb hab
    change a*x j k+b*y j k = 0
    change x j k = 0 at hx
    change y j k = 0 at hy
    rw [hx, hy]; ring
  apply convexHull_min (t := {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
    g j k = 0}) ?_ hc hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · exact Φ.incidence_unused seed I j k hk
  · change -Φ.incidence seed I j k = 0
    rw [Φ.incidence_unused seed I j k hk, neg_zero]

theorem zero_mem_incidenceHull (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    (0 : Fin d → Fin (Φ.WeightDimension d) → ℝ) ∈ Φ.incidenceHull seed := by
  classical
  apply subset_convexHull ℝ _
  refine ⟨∅, Φ.compatible_empty d, Or.inl ?_⟩
  ext j k
  simp [incidence, truthValue]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_CanonicalGradientValid
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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
open MeasureTheory

theorem batchFunction_hasFDerivAt (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (hs : VertexCover.AffineSelector.Regular (Φ.affineSlope seed J)
      (Φ.affineOffset c0 (A := A)) s) :
    ∃ im ip : Φ.AffineIndex A, HasFDerivAt (Φ.batchFunction seed J c0 A hA)
      ((1/2 : ℝ) • (Φ.affineSlope seed J im - Φ.affineSlope seed J ip)) s := by
  have hc : Continuous (fun s : Φ.BatchWeights J => c0 + Φ.batchSum seed J s) :=
    continuous_const.add (Φ.batchSumCLM seed J).continuous
  obtain ⟨ip, hp⟩ := VertexCover.AffineSelector.hasFDerivAt _ _
    ((Φ.distanceTo_continuous A hA).comp hc)
    (Φ.distance_plus_select seed J c0 A hA) hs
  obtain ⟨im, hm⟩ := VertexCover.AffineSelector.hasFDerivAt _ _
    ((Φ.distanceTo_continuous A hA).comp hc.neg)
    (Φ.distance_minus_select seed J c0 A hA) hs
  refine ⟨im, ip, ?_⟩
  have heq : Φ.batchFunction seed J c0 A hA = (fun y => (1/2 : ℝ) *
      (Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J y)) -
        Φ.distanceTo A hA (c0 + Φ.batchSum seed J y))) := by
    funext y
    unfold batchFunction separator
    ring
  rw [heq]
  exact (hm.sub hp).const_mul (1/2 : ℝ)

def BatchGradientValid (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (g : Φ.BatchWeights J) : Prop :=
  ∃ G ∈ Φ.incidenceHull seed, ∀ (j : J) k, g j k = G j k

theorem signed_incidence_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (e : Bool) :
    affineSign e • Φ.incidence seed I ∈ Φ.incidenceHull seed := by
  apply subset_convexHull ℝ
  cases e
  · exact ⟨I, hI, Or.inr (by simp)⟩
  · exact ⟨I, hI, Or.inl (by simp)⟩

theorem neg_signed_incidence_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (e : Bool) :
    -(affineSign e • Φ.incidence seed I) ∈ Φ.incidenceHull seed := by
  apply subset_convexHull ℝ
  cases e
  · exact ⟨I, hI, Or.inl (by simp)⟩
  · exact ⟨I, hI, Or.inr (by simp)⟩

theorem batchGradient_affineSlope (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) (j : J) (k : Fin (Φ.WeightDimension d)) :
    Φ.batchGradient J (Φ.affineSlope seed J i) j k =
      affineSign i.2.2.2 * Φ.incidence seed i.2.1.val j k := by
  change affineSign i.2.2.2 *
    Φ.batchGradient J ((Φ.selectionForm i.2.1.val).comp (Φ.batchSumCLM seed J)) j k = _
  rw [Φ.batchGradient_form seed J ((Φ.mem_compatibleSelections _).mp i.2.1.property)]

theorem batchGradient_half_difference_valid (Φ : LabelCover) {d : ℕ}
    (seed : Φ.Seeds d) (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (im ip : Φ.AffineIndex A) :
    Φ.BatchGradientValid seed J (Φ.batchGradient J
      ((1/2 : ℝ) • (Φ.affineSlope seed J im - Φ.affineSlope seed J ip))) := by
  let gm := affineSign im.2.2.2 • Φ.incidence seed im.2.1.val
  let gp := -(affineSign ip.2.2.2 • Φ.incidence seed ip.2.1.val)
  have hm := Φ.signed_incidence_mem seed
    ((Φ.mem_compatibleSelections _).mp im.2.1.property) im.2.2.2
  have hp := Φ.neg_signed_incidence_mem seed
    ((Φ.mem_compatibleSelections _).mp ip.2.1.property) ip.2.2.2
  refine ⟨(1/2 : ℝ) • gm + (1/2 : ℝ) • gp,
    (convex_convexHull ℝ _) hm hp (by norm_num) (by norm_num) (by norm_num), ?_⟩
  intro j k
  change (1/2 : ℝ) * (Φ.batchGradient J (Φ.affineSlope seed J im) j k -
    Φ.batchGradient J (Φ.affineSlope seed J ip) j k) = _
  rw [Φ.batchGradient_affineSlope, Φ.batchGradient_affineSlope]
  simp only [gm, gp, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

noncomputable def canonicalGradient (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    Φ.BatchWeights J := by
  classical
  exact if VertexCover.AffineSelector.Regular (Φ.affineSlope seed J)
    (Φ.affineOffset c0 (A := A)) s then
      Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) else 0

theorem canonicalGradient_valid (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    Φ.BatchGradientValid seed J (Φ.canonicalGradient seed J c0 A hA s) := by
  classical
  unfold canonicalGradient
  split_ifs with hs
  · obtain ⟨im, ip, hder⟩ := Φ.batchFunction_hasFDerivAt seed J c0 A hA s hs
    rw [hder.fderiv]
    exact Φ.batchGradient_half_difference_valid seed J im ip
  · exact ⟨0, Φ.zero_mem_incidenceHull seed, fun _ _ => rfl⟩

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_CanonicalGradientInvariant
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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
open MeasureTheory

theorem canonicalGradient_measurable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Measurable (Φ.canonicalGradient seed J c0 A hA) := by
  classical
  apply Measurable.ite (VertexCover.AffineSelector.regular_measurableSet _ _)
  · apply Measurable.of_eval; intro batchIndex
    apply Measurable.of_eval; intro weightIndex
    exact (ContinuousLinearMap.apply ℝ ℝ
      (Pi.single batchIndex (Pi.single weightIndex 1))).measurable.comp
      (measurable_fderiv ℝ (Φ.batchFunction seed J c0 A hA))
  · exact measurable_const

theorem canonicalGradient_ae_derivative (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (μ : Measure (Φ.BatchWeights J)) [μ.IsAddHaarMeasure] :
    ∀ᵐ s ∂μ, DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) s ∧
      Φ.canonicalGradient seed J c0 A hA s =
        Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) := by
  classical
  filter_upwards [VertexCover.AffineSelector.ae_regular μ (Φ.affineSlope seed J)
    (Φ.affineOffset c0 (A := A))] with s hs
  obtain ⟨im, ip, hder⟩ := Φ.batchFunction_hasFDerivAt seed J c0 A hA s hs
  exact ⟨hder.differentiableAt, by simp [canonicalGradient, hs]⟩

theorem canonicalGradient_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) (j : J) :
    ∑ k, |Φ.canonicalGradient seed J c0 A hA s j k| ≤ 1 := by
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  simp_rw [heq]
  exact Φ.hull_block_bound seed hG j

theorem canonicalGradient_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (j : J) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    Φ.canonicalGradient seed J c0 A hA s j k = 0 := by
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  rw [heq]
  exact Φ.hull_unused seed hG j k hk

theorem canonicalGradient_listMass (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (L : Φ.PrivateLists d) :
    (∑ j : J, ∑ a ∈ (L (Φ.query seed j)).toFinset,
      |Φ.canonicalGradient seed J c0 A hA s j ((Φ.query seed j).slot a)|) ≤
        Φ.listHitMaximum L seed J := by
  classical
  obtain ⟨G, hG, heq⟩ := Φ.canonicalGradient_valid seed J c0 A hA s
  simp_rw [heq]
  exact (Finset.sum_coe_sort J (fun j =>
    ∑ a ∈ (L (Φ.query seed j)).toFinset, |G j ((Φ.query seed j).slot a)|)).trans_le
      (Φ.listMass_le_hitMaximum L seed J hG)

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_SeparatorContinuousSumOdd
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

theorem continuousSum_change_blocks (Φ : LabelCover) {d : ℕ}
    (seed seed' : Φ.Seeds d) (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) (ht : Φ.InWeightCube t) (B : Finset (Fin d))
    (heq : ∀ j ∉ B, Φ.query seed j = Φ.query seed' j ∧ s j = t j) :
    Φ.compatibilityNorm (Φ.continuousSum seed s - Φ.continuousSum seed' t) ≤ 2*B.card := by
  classical
  unfold continuousSum
  rw [← Finset.sum_sub_distrib]
  apply (Φ.norm_sum_le _ _).trans
  calc
    (∑ j, Φ.compatibilityNorm
        (Φ.increment (Φ.query seed j) (s j) - Φ.increment (Φ.query seed' j) (t j))) ≤
        ∑ j : Fin d, if j ∈ B then (2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ B
      · rw [ite_eq_left hj]
        have hb := Φ.norm_sub_triangle (Φ.increment (Φ.query seed j) (s j)) 0
          (Φ.increment (Φ.query seed' j) (t j))
        have hh1 := Φ.increment_norm_le (Φ.query seed j) (s j) (by norm_num : (0:ℝ) ≤ 1) (hs j)
        have hh2 := Φ.increment_norm_le (Φ.query seed' j) (t j) (by norm_num : (0:ℝ) ≤ 1) (ht j)
        simp only [sub_zero, zero_sub, Φ.norm_neg] at hb
        linarith
      · obtain ⟨hq, hw⟩ := heq j hj
        rw [hq, hw, sub_self, ite_eq_right hj]
        exact (Φ.norm_zero d).le
    _ = 2*B.card := by simp [Finset.sum_ite_mem, mul_comm]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BatchFunctionOwnLipschitz
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.blockLaw_negInvariant _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory ProbabilityTheory

theorem canonicalGradient_ae_cube (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    ∀ᵐ s ∂Φ.batchLaw J, DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) s ∧
      Φ.canonicalGradient seed J c0 A hA s =
        Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) := by
  let : (volume : Measure (Φ.BatchWeights J)).IsAddHaarMeasure := by
    change (Measure.pi (fun _ : J => (volume : Measure (Fin (Φ.WeightDimension d) → ℝ)))).IsAddHaarMeasure
    apply Measure.pi.isAddHaarMeasure
  exact (VertexCover.Cube.blockLaw_ac J (Fin (Φ.WeightDimension d))).ae_le
    (Φ.canonicalGradient_ae_derivative seed J c0 A hA volume)

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BlockLawNegInvariant
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Product
open MeasureTheory

theorem piMap_measurePreserving {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (f : X → Y) (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (fun s : ι → X => fun i => f (s i))
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : ι => ν)) := by
  refine ⟨Measurable.of_eval (fun index => hf.measurable.comp (measurable_pi_apply index)), ?_⟩
  let : SigmaFinite (Measure.map f μ) := by rw [hf.map_eq]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hf.map_eq]

end VertexCover.Product

namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem vector_measurePreserving {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (fun s : ι → ℝ => fun i => index p hp (s i))
      (VertexCover.Cube.law ι) (uniformOn (Set.univ : Set (ι → Fin p))) := by
  let : NeZero p := ⟨hp.ne'⟩
  have h := VertexCover.Product.piMap_measurePreserving (ι := ι)
    VertexCover.Cube.intervalLaw (uniformOn (Set.univ : Set (Fin p)))
    (index p hp) (index_measurePreserving p hp)
  simpa only [pi_uniformOn_univ, VertexCover.Cube.law] using h

end VertexCover.GridCoupling


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_MidpointGridTail
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.FiniteAntiConcentration
noncomputable section
open AntiConcentration

theorem gridTailDensity_lower (d k t : ℕ) (hk : 0 < k) (ht : t < d) :
    1/2 - Real.sqrt 2 * ((t : ℝ)+1) / Real.sqrt (2*(k : ℝ)) <
      gridTailDensity d (2*k) t := by
  classical
  let C : ℝ := ((Finset.univ.filter (fun x : Fin (2*k) → Fin (2*d+1) =>
    -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ)
  let Q : ℝ := ((2*d+1 : ℕ)^(2*k) : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hP : 0 < (2:ℝ)^(2*k) := by positivity
  have hsqrt : 0 < Real.sqrt (2*(k:ℝ)) := by positivity
  have hc : C / Q ≤ (2*(t:ℝ)+1) * centralProbability k := by
    have h := grid_central_card d (2*k) t ht
    have hatom := sign_atom_le k (2*k/2)
    have hfirst : C/Q ≤ (2*(t:ℝ)+1) * (((2*k).choose (2*k/2) : ℝ)/(2:ℝ)^(2*k)) := by
      rw [mul_div, div_le_div_iff₀ hQ hP]
      dsimp [C, Q] at *
      nlinarith [h]
    exact hfirst.trans (mul_le_mul_of_nonneg_left hatom (by positivity))
  have hstrict : C / Q < (2*(t:ℝ)+2) * (Real.sqrt 2 / Real.sqrt (2*(k:ℝ))) := by
    have hstep := mul_lt_mul_of_pos_left (centralProbability_lt k hk)
      (by positivity : (0:ℝ) < 2*t+1)
    have hnonneg : 0 ≤ Real.sqrt 2 / Real.sqrt (2*(k:ℝ)) := by positivity
    exact lt_of_le_of_lt hc (hstep.trans_le (mul_le_mul_of_nonneg_right (by linarith) hnonneg))
  have htail : 2 * gridTailDensity d (2*k) t + C / Q = 1 := by
    have h := grid_tail_count d (2*k) t
    unfold gridTailDensity
    apply (div_eq_one_iff_eq (ne_of_gt hQ)).mpr at h
    dsimp [C, Q] at *
    convert h using 1 <;> first | rfl | ring
  have he : (2*(t:ℝ)+2) * (Real.sqrt 2 / Real.sqrt (2*(k:ℝ))) =
      2 * (Real.sqrt 2 * ((t:ℝ)+1) / Real.sqrt (2*(k:ℝ))) := by ring
  rw [he] at hstrict
  linarith

end
end VertexCover.FiniteAntiConcentration

namespace VertexCover.Parameters
noncomputable section

 theorem midpoint_grid_tail (m : ℕ) (hm : 4 ≤ m) :
    1/2 - Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) <
      FiniteAntiConcentration.gridTailDensity (d m) (d m) (t m) ∧
    1/2 - 1/(m:ℝ) <
      1/2 - Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) := by
  obtain ⟨k, hk⟩ := (dimensions m hm).2.2.2
  have hd : d m = 2*k := by omega
  have hkpos : 0 < k := by have := (dimensions m hm).1; omega
  have ht := FiniteAntiConcentration.gridTailDensity_lower (d m) k (t m) hkpos (t_lt_d m hm)
  have hs : Real.sqrt (2*(k:ℝ)) = Real.sqrt (d m) := by rw [hd]; push_cast; rfl
  rw [← hd, hs] at ht
  have hnonzero : Real.sqrt (d m) ≠ 0 := ne_of_gt (lt_trans (by positivity) (sqrt_d_gt m hm))
  have he : Real.sqrt 2 * ((t m : ℝ)+1) / Real.sqrt (d m) =
      Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) := by
    rw [t_eq m (by omega)]
    field_simp
  exact ⟨by simpa only [he] using ht, by linarith [tail_error_lt m hm]⟩

end
end VertexCover.Parameters


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_GraphCompleteness
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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
namespace VertexCover
noncomputable section

 theorem finiteMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteMean (fun x => f (e x)) = finiteMean f := by
  unfold finiteMean
  rw [e.sum_comp f, Fintype.card_congr e]

 theorem finiteMean_product {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

 theorem finiteMean_product_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → ℝ) : finiteMean (fun x : α × β => f x.1) = finiteMean f := by
  rw [finiteMean_product]
  simp only [finiteMean_const]

 theorem finiteMean_selected {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq ι] [DecidableEq κ] [Nonempty α] (slot : ι → κ) (f : (ι → α) → ℝ) :
    finiteMean (fun w : ι → κ → α => f (fun i => w i (slot i))) = finiteMean f := by
  classical
  calc
    _ = finiteMean (fun v : (ι → α) × ((i : ι) → {k : κ // k ≠ slot i} → α) => f v.1) :=
      finiteMean_equiv (splitSelected slot) (fun v => f v.1)
    _ = _ := finiteMean_product_fst f

 theorem finiteMean_truthValue {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    finiteMean (fun x => truthValue (P x)) =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  classical
  unfold finiteMean truthValue
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : P x <;> simp [hp]

end
end VertexCover

namespace VertexCover.LabelCover
noncomputable section

 theorem honestSum_density (Φ : LabelCover) (d t : ℕ) (A : Φ.Labeling)
    (hA : ∀ e, Φ.Satisfies A e) :
    finiteMean (fun v : Φ.Vertex d => truthValue ((t:ℝ) < Φ.honestSum A hA v)) =
      FiniteAntiConcentration.gridTailDensity d d t := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  rw [finiteMean_product]
  have hf (seed : Φ.Seeds d) :
      finiteMean (fun w : Fin d → Fin (Φ.WeightDimension d) → Fin (2*d+1) =>
        truthValue ((t:ℝ) < Φ.honestSum A hA (seed,w))) =
      FiniteAntiConcentration.gridTailDensity d d t := by
    unfold honestSum
    simp only [gridRational_real]
    rw [finiteMean_selected
      (fun j => (Φ.query seed j).slot (Φ.localOfSatisfying A hA (Φ.query seed j)))
      (fun x : Fin d → Fin (2*d+1) => truthValue ((t:ℝ) < ∑ i, FiniteAntiConcentration.grid d (x i)))]
    rw [finiteMean_truthValue]
    simp only [FiniteAntiConcentration.gridTailDensity, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  simp only [hf, finiteMean_const]

 theorem graph_completeness (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∃ I : Finset (Φ.Vertex (Parameters.d m)),
      (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet (I : Set (Φ.Vertex (Parameters.d m))) ∧
      ((1:ℝ)/2-1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) < I.card := by
  classical
  let I : Finset (Φ.Vertex (Parameters.d m)) :=
    Finset.univ.filter (fun v => (Parameters.t m : ℝ) < Φ.honestSum A hA v)
  refine ⟨I, ?_, ?_⟩
  · have he : (I : Set (Φ.Vertex (Parameters.d m))) = {v | (Parameters.t m : ℝ) < Φ.honestSum A hA v} := by
      ext v
      simp [I]
    rw [he]
    exact Φ.honest_large_sum_independent _ A hA
  · have htail := Parameters.midpoint_grid_tail m hm
    have hdense := Φ.honestSum_density (Parameters.d m) (Parameters.t m) A hA
    rw [finiteMean_truthValue] at hdense
    have hfinal : (1:ℝ)/2-1/(m:ℝ) <
        (I.card : ℝ) / Fintype.card (Φ.Vertex (Parameters.d m)) := by
      rw [hdense]
      exact htail.2.trans htail.1
    have hn : 0 < Fintype.card (Φ.Vertex (Parameters.d m)) := by
      rw [Φ.vertex_card]
      exact Nat.mul_pos (Nat.pow_pos Φ.M_pos) (Nat.pow_pos (by omega))
    exact (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mp hfinal

 theorem graph_completeness_cover (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∃ C : Finset (Φ.Vertex (Parameters.d m)),
      (Φ.graph (Parameters.d m) (Parameters.t m)).IsVertexCover (C : Set (Φ.Vertex (Parameters.d m))) ∧
      (C.card : ℝ) < ((1:ℝ)/2+1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) := by
  classical
  obtain ⟨I, hI, hcard⟩ := Φ.graph_completeness m hm A hA
  refine ⟨Iᶜ, ?_, ?_⟩
  · simpa only [Finset.coe_compl] using SimpleGraph.isVertexCover_compl.mpr hI
  · have hn := Finset.card_le_univ I
    rw [Finset.card_compl, Nat.cast_sub hn]
    nlinarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeparatorRoundingErrorAe
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory

theorem block_measurePreserving {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (fun s : ι → κ → ℝ => fun j k => index p hp (s j k))
      (VertexCover.Cube.blockLaw ι κ)
      (uniformOn (Set.univ : Set (ι → κ → Fin p))) := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  have h := VertexCover.Product.piMap_measurePreserving (ι := ι)
    (VertexCover.Cube.law κ) (uniformOn (Set.univ : Set (κ → Fin p)))
    (fun s : κ → ℝ => fun k => index p hp (s k)) (vector_measurePreserving p hp)
  simpa only [pi_uniformOn_univ, VertexCover.Cube.blockLaw] using h

end VertexCover.GridCoupling

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_IndependentSecondMomentLower
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory

theorem block_integral {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p : ℕ) (hp : 0 < p) (F : (ι → κ → Fin p) → ℝ) :
    (∫ s, F (fun j k => index p hp (s j k)) ∂VertexCover.Cube.blockLaw ι κ) =
      VertexCover.finiteMean F := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  have h := block_measurePreserving (ι := ι) (κ := κ) p hp
  have hm : AEStronglyMeasurable F (uniformOn (Set.univ : Set (ι → κ → Fin p))) :=
    (measurable_of_countable F).aestronglyMeasurable
  have he := integral_map h.aemeasurable (by simpa only [h.map_eq] using hm)
  rw [h.map_eq] at he
  rw [← he, integral_uniform_finite]
  rfl
end VertexCover.GridCoupling

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem independent_secondMoment_lower (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hround : (d:ℝ)/(2*d+1) < t/2)
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d)))
    (hV : (Φ.highVectors t A).Nonempty) :
    (t/2)^2 * (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).card /
        Fintype.card (Φ.Vertex d) ≤
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s))^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  let B := A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))
  let H : Φ.Vertex d → ℝ := fun v => if v ∈ B then (t/2)^2 else 0
  have hseed : ∀ seed : Φ.Seeds d,
      VertexCover.finiteMean (fun w => H (seed,w)) ≤
        ∫ s, (Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s))^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
    intro seed
    rw [← VertexCover.GridCoupling.block_integral (2*d+1) (by omega)
      (fun w => H (seed,w))]
    apply integral_mono_of_nonneg
    · apply Filter.Eventually.of_forall
      intro s
      dsimp [H]
      split_ifs <;> positivity
    · exact VertexCover.Cube.integrable_continuous_block
        ((Φ.separator_continuousSum_continuous (Φ.highVectors t A) hV seed).pow 2)
    · filter_upwards [Φ.separator_rounding_error_ae (Φ.highVectors t A) hV seed] with s hs
      change H (Φ.roundedVertex seed s) ≤ _
      dsimp only [H]
      split_ifs with hv
      · have hmem : Φ.sumVector (Φ.roundedVertex seed s) ∈ Φ.highVectors t A :=
          Finset.mem_image.mpr ⟨Φ.roundedVertex seed s, hv, rfl⟩
        have hpos := Φ.separator_pos_on (Φ.highVectors t A) hV
          (Φ.highVectors_separated t A hA) _ hmem
        have he := (abs_le.mp hs).1
        have hh : t/2 < Φ.separator (Φ.highVectors t A) hV (Φ.continuousSum seed s) := by
          linarith
        nlinarith
      · exact sq_nonneg _
  have h := VertexCover.finiteMean_mono hseed
  rw [← VertexCover.finiteMean_product H] at h
  have he : VertexCover.finiteMean H = (t/2)^2 * (B.card:ℝ) /
      Fintype.card (Φ.Vertex d) := by
    simp [VertexCover.finiteMean, H, Finset.sum_ite_mem, mul_comm]
  rwa [he] at h

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_DenseSeparatorData
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory ProbabilityTheory

theorem dense_separator_data (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    ∃ hV : (Φ.highVectors (Parameters.t m) A).Nonempty,
      (∀ seed : Φ.Seeds (Parameters.d m),
        (∫ s, Φ.separator (Φ.highVectors (Parameters.t m) A) hV (Φ.continuousSum seed s)
          ∂VertexCover.Cube.blockLaw (Fin (Parameters.d m))
            (Fin (Φ.WeightDimension (Parameters.d m)))) = 0) ∧
      Parameters.ν m * (Parameters.d m:ℝ) ≤
        VertexCover.finiteMean (fun seed : Φ.Seeds (Parameters.d m) =>
          variance (fun s => Φ.separator (Φ.highVectors (Parameters.t m) A) hV
            (Φ.continuousSum seed s))
            (VertexCover.Cube.blockLaw (Fin (Parameters.d m))
              (Fin (Φ.WeightDimension (Parameters.d m))))) := by
  classical
  have hfrac := Φ.dense_high_fraction m hm A hA hdense
  have hb0 : 0 < Parameters.b₀ m := by
    unfold Parameters.b₀
    have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hBN : (A.filter (fun v => (Parameters.t m:ℝ) <
      Φ.compatibilityNorm (Φ.sumVector v))).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : (A.filter (fun v => (Parameters.t m:ℝ) <
      Φ.compatibilityNorm (Φ.sumVector v))).card = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hfrac
    linarith
  have hV : (Φ.highVectors (Parameters.t m) A).Nonempty := hBN.image Φ.sumVector
  refine ⟨hV, fun seed => Φ.separator_continuousSum_mean_zero _ hV seed, ?_⟩
  have hround : (Parameters.d m:ℝ)/(2*Parameters.d m+1) < (Parameters.t m:ℝ)/2 := by
    have h := (Parameters.grid_budget m hm).1.trans (Parameters.grid_budget m hm).2.1
    simpa only [Parameters.p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h
  have hlow := Φ.independent_secondMoment_lower (Nat.cast_nonneg (Parameters.t m))
    hround A hA hV
  have hvareq : ∀ seed : Φ.Seeds (Parameters.d m),
      variance (fun s => Φ.separator (Φ.highVectors (Parameters.t m) A) hV
          (Φ.continuousSum seed s))
        (VertexCover.Cube.blockLaw (Fin (Parameters.d m))
          (Fin (Φ.WeightDimension (Parameters.d m)))) =
      ∫ s, (Φ.separator (Φ.highVectors (Parameters.t m) A) hV
          (Φ.continuousSum seed s))^2
        ∂VertexCover.Cube.blockLaw (Fin (Parameters.d m))
          (Fin (Φ.WeightDimension (Parameters.d m))) := by
    intro seed
    rw [variance_eq_integral
      (Φ.separator_continuousSum_continuous _ hV seed).measurable.aemeasurable,
      Φ.separator_continuousSum_mean_zero]
    simp only [sub_zero]
  simp_rw [hvareq]
  calc
    Parameters.ν m * (Parameters.d m:ℝ) =
        Parameters.b₀ m * ((Parameters.t m:ℝ)/2)^2 :=
      (Parameters.variance_scale m (by omega)).symm
    _ ≤ (((A.filter (fun v => (Parameters.t m:ℝ) <
        Φ.compatibilityNorm (Φ.sumVector v))).card:ℝ) /
          Fintype.card (Φ.Vertex (Parameters.d m))) * ((Parameters.t m:ℝ)/2)^2 :=
      mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
    _ = ((Parameters.t m:ℝ)/2)^2 *
        (A.filter (fun v => (Parameters.t m:ℝ) <
          Φ.compatibilityNorm (Φ.sumVector v))).card /
          Fintype.card (Φ.Vertex (Parameters.d m)) := by ring
    _ ≤ _ := hlow
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SelectedIntegralAbs
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.Average
open MeasureTheory

theorem sum_fiberAverage {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) :
    (∑ a, fiberAverage q f (q a)) = ∑ a, f (q a) a := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ q (fun a => fiberAverage q f (q a)),
    ← Finset.sum_fiberwise Finset.univ q (fun a => f (q a) a)]
  apply Finset.sum_congr rfl
  intro i hi
  have hq : ∀ a ∈ Finset.univ.filter (fun a => q a = i), q a = i := by
    intro a ha; exact (Finset.mem_filter.mp ha).2
  calc
    _ = ∑ _a ∈ Finset.univ.filter (fun a => q a = i), fiberAverage q f i := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hq a ha]
    _ = (Finset.univ.filter (fun a => q a = i)).card * fiberAverage q f i := by simp
    _ = ∑ a ∈ Finset.univ.filter (fun a => q a = i), f i a := by
      unfold fiberAverage
      by_cases hz : (Finset.univ.filter (fun a => q a = i)).card = 0
      · have he := Finset.card_eq_zero.mp hz
        simp [he]
      · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hq a ha]

theorem finiteMean_fiber_tower {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) :
    (by classical exact VertexCover.finiteMean (fun a : α =>
      VertexCover.finiteMean (fun a' : Finset.univ.filter (fun a' => q a' = q a) =>
        f (q a) a'))) = VertexCover.finiteMean (fun a : α => f (q a) a) := by
  classical
  have he : ∀ i, VertexCover.finiteMean (fun a : Finset.univ.filter (fun a => q a = i) => f i a) =
      fiberAverage q f i := by
    intro i
    unfold VertexCover.finiteMean fiberAverage
    rw [Finset.sum_coe_sort, Fintype.card_coe]
  simp_rw [he]
  unfold VertexCover.finiteMean
  rw [sum_fiberAverage]

theorem finiteMean_fiber_tower_of_mem {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : β → α → ℝ) (T : β → Finset α)
    (hT : ∀ i a, a ∈ T i ↔ q a = i) :
    VertexCover.finiteMean (fun a : α =>
      VertexCover.finiteMean (fun a' : T (q a) => f (q a) a')) =
      VertexCover.finiteMean (fun a : α => f (q a) a) := by
  classical
  have he : T = fun i => Finset.univ.filter (fun a => q a = i) := by
    funext i
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT]
  subst T
  exact finiteMean_fiber_tower q f

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_SeparatorStarOscillation
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
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

theorem separator_weight_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) (ht : Φ.InWeightCube t) (k : Fin d)
    (heq : ∀ j, j ≠ k → s j = t j) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum seed t)| ≤ 2 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed seed s t hs ht {k}
    (fun j hj => ⟨rfl, heq j (by simpa using hj)⟩)
  simpa using h

theorem separator_seed_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (hs : Φ.InWeightCube s)
    (e : PositionPair d) (c : Fin Φ.M) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s)| ≤ 4 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed (Φ.replaceSeed seed e c) s s hs hs
    {e.1.1, e.1.2} (fun j hj => ⟨Φ.query_replaceSeed_other seed e c j
      (fun h => hj (by simp [h]))
      (fun h => hj (by simp [h])), rfl⟩)
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  norm_num [hne] at h
  exact h

theorem separator_star_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed seed' : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (hs : Φ.InWeightCube s)
    (k : Fin d)
    (hL : ∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e))
    (hR : ∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e)) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum seed' s)| ≤ 2 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed seed' s s hs hs {k}
    (fun j hj => ⟨Φ.query_eq_away seed seed' k hL hR j (by simpa using hj), rfl⟩)
  simpa using h

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_StarMeanContinuous
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover

theorem finiteMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteMean (fun a => f a - g a) = finiteMean f - finiteMean g := by
  simp only [finiteMean, Finset.sum_sub_distrib, sub_div]

theorem finiteMean_abs_le {α : Type*} [Fintype α] (f : α → ℝ) :
    |finiteMean f| ≤ finiteMean (fun a => |f a|) := by
  unfold finiteMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card α from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

end VertexCover

namespace VertexCover.LabelCover
open MeasureTheory

theorem starKey_eq_questions (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (seed seed' : Φ.Seeds d) (h : Φ.starKey k seed = Φ.starKey k seed') :
    (∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e)) ∧
    (∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e)) := by
  constructor
  · intro e he
    have hh := congrArg (fun key : Φ.StarKey d => (key e).2.1) h
    simpa only [starKey, ite_eq_right he, Option.some.injEq] using hh
  · intro e he
    have hh := congrArg (fun key : Φ.StarKey d => (key e).2.2) h
    simpa only [starKey, ite_eq_right he, Option.some.injEq] using hh

noncomputable def starMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
    Φ.separator A hA (Φ.continuousSum seed'.1 s))

theorem star_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s| ≤ 2 := by
  classical
  let : Nonempty (Φ.starFiber k seed) := ⟨⟨seed, Φ.self_mem_starFiber k seed⟩⟩
  have heq : Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s =
      VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
        Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum seed'.1 s)) := by
    rw [VertexCover.finiteMean_sub, VertexCover.finiteMean_const]
    rfl
  rw [heq]
  apply (VertexCover.finiteMean_abs_le _).trans
  calc
    VertexCover.finiteMean (fun seed' : Φ.starFiber k seed =>
        |Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum seed'.1 s)|) ≤
        VertexCover.finiteMean (fun _ : Φ.starFiber k seed => (2 : ℝ)) := by
      apply VertexCover.finiteMean_mono
      intro seed'
      have hkey := (Φ.mem_starFiber k seed seed'.1).mp seed'.2
      obtain ⟨hL, hR⟩ := Φ.starKey_eq_questions k seed seed'.1 hkey.symm
      exact Φ.separator_star_oscillation A hA seed seed'.1 s hs k hL hR
    _ = 2 := VertexCover.finiteMean_const _

theorem starMean_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) : Continuous (Φ.starMean A hA k seed) := by
  classical
  unfold starMean VertexCover.finiteMean
  exact (continuous_finsetSum _ (fun seed' _ =>
    Φ.separator_continuousSum_continuous A hA seed'.1)).div_const _

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_FiniteMeanConditionBest
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Average

theorem finiteMean_finset {α : Type*} (T : Finset α) (f : α → ℝ) :
    VertexCover.finiteMean (fun a : T => f a) = (∑ a ∈ T, f a) / T.card := by
  classical
  unfold VertexCover.finiteMean
  rw [Finset.sum_coe_sort, Fintype.card_coe]

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_StarEnergyBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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
open MeasureTheory

theorem star_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 4 := by
  have hi := VertexCover.Cube.integrable_continuous_block
    (((Φ.separator_continuousSum_continuous A hA seed).sub
      (Φ.starMean_continuous A hA k seed)).pow 2)
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2 ≤ (4 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.star_residual_abs_le A hA k seed s hs
    have hsq := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2) |>.mpr hh
    rw [sq_abs] at hsq
    norm_num only [OfNat.ofNat, pow_two, Nat.reduceMul] at hsq ⊢
    nlinarith
  simpa using integral_mono_ae hi (integrable_const (4 : ℝ)) hb

theorem star_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 4*d := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _k : Fin d, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (4 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.star_residual_integral_le A hA k)
        _ = 4 := VertexCover.finiteMean_const _
    _ = 4*d := by simp [mul_comm]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeedEnergyBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
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

theorem starMean_eq_fiberAverage (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.starMean A hA k seed s =
      VertexCover.Average.fiberAverage (Φ.starKey k)
        (fun _ seed' => Φ.separator A hA (Φ.continuousSum seed' s)) (Φ.starKey k seed) := by
  classical
  calc
    _ = (∑ seed' ∈ Φ.starFiber k seed,
        Φ.separator A hA (Φ.continuousSum seed' s)) / (Φ.starFiber k seed).card :=
      VertexCover.Average.finiteMean_finset (Φ.starFiber k seed)
        (fun seed' => Φ.separator A hA (Φ.continuousSum seed' s))
    _ = _ := rfl

end VertexCover.LabelCover

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def seedMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  VertexCover.finiteMean (fun c : Fin Φ.M =>
    Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s))

theorem seed_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s| ≤ 4 := by
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have he : Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s =
      VertexCover.finiteMean (fun c : Fin Φ.M =>
        Φ.separator A hA (Φ.continuousSum seed s) -
          Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s)) := by
    rw [VertexCover.finiteMean_sub, VertexCover.finiteMean_const]
    rfl
  rw [he]
  apply (VertexCover.finiteMean_abs_le _).trans
  calc
    _ ≤ VertexCover.finiteMean (fun _ : Fin Φ.M => (4 : ℝ)) :=
      VertexCover.finiteMean_mono (Φ.separator_seed_oscillation A hA seed s hs e)
    _ = 4 := VertexCover.finiteMean_const _

theorem seedMean_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) : Continuous (Φ.seedMean A hA e seed) := by
  classical
  unfold seedMean VertexCover.finiteMean
  exact (continuous_finsetSum _ (fun c _ =>
    Φ.separator_continuousSum_continuous A hA (Φ.replaceSeed seed e c))).div_const _

theorem seed_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 16 := by
  have hi := VertexCover.Cube.integrable_continuous_block
    (((Φ.separator_continuousSum_continuous A hA seed).sub
      (Φ.seedMean_continuous A hA e seed)).pow 2)
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2 ≤ (16 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.seed_residual_abs_le A hA e seed s hs
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)).mpr hh
    rw [sq_abs] at hsq
    nlinarith
  simpa using integral_mono_ae hi (integrable_const (16 : ℝ)) hb

theorem seed_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ e : PositionPair d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 8*(d:ℝ)^2 := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _e : PositionPair d, (16 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (16 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.seed_residual_integral_le A hA e)
        _ = 16 := VertexCover.finiteMean_const _
    _ ≤ 8*(d:ℝ)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, positionPair_card]
      rw [Nat.cast_choose_two]
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ErasedSeedSeparatorAverage
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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

theorem erasedSeed_fiberAverage (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) (f : Φ.Seeds d → ℝ) :
    VertexCover.Average.fiberAverage
      (fun seed' : Φ.Seeds d => Function.update seed' e ⟨0, Φ.M_pos⟩)
      (fun _ => f) (Function.update seed e ⟨0, Φ.M_pos⟩) =
      VertexCover.finiteMean (fun c : Fin Φ.M => f (Function.update seed e c)) := by
  classical
  calc
    _ = VertexCover.finiteMean (fun seed' : Φ.erasedSeedFiber e seed => f seed'.1) := by
      unfold VertexCover.Average.fiberAverage
      simpa only [erasedSeedFiber] using
        (VertexCover.Average.finiteMean_finset (Φ.erasedSeedFiber e seed) f).symm
    _ = _ := (VertexCover.finiteMean_equiv (Φ.erasedSeedFiberEquiv e seed).symm
      (fun seed' : Φ.erasedSeedFiber e seed => f seed'.1)).symm

theorem erasedSeed_separator_average (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (e : PositionPair d) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    VertexCover.Average.fiberAverage
      (fun seed' : Φ.Seeds d => Function.update seed' e ⟨0, Φ.M_pos⟩)
      (fun _ seed' => Φ.separator A hA (Φ.continuousSum seed' s))
      (Function.update seed e ⟨0, Φ.M_pos⟩) = Φ.seedMean A hA e seed s := by
  exact Φ.erasedSeed_fiberAverage e seed
    (fun seed' => Φ.separator A hA (Φ.continuousSum seed' s))

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnGradientUnsupported
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory ProbabilityTheory

noncomputable def ownMean (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) : ℝ := by
  classical
  exact VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
    ∫ other, Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J c0 A hA
      (Function.update other j s) ∂Φ.batchLaw J)

noncomputable def ownGradient (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d)) : ℝ := by
  classical
  exact VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
    ∫ other, Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
      (Function.update other j s) j k ∂Φ.batchLaw J)

theorem canonicalGradient_update_measurable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) (k : Fin (Φ.WeightDimension d)) :
    Measurable (fun other : Φ.BatchWeights J =>
      Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) := by
  classical
  exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
    ((Φ.canonicalGradient_measurable seed J c0 A hA).comp
      (continuous_id.update j continuous_const).measurable))

theorem ownGradient_block_bound (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) :
    ∑ k, |Φ.ownGradient J frozen c0 A hA j i s k| ≤ 1 := by
  classical
  apply VertexCover.Average.finite_l1_le
  intro hidden
  apply VertexCover.Average.integral_l1_le
  · intro k
    exact (Φ.canonicalGradient_update_measurable _ J c0 A hA j s k).aestronglyMeasurable
  · intro other
    exact Φ.canonicalGradient_block_bound _ J c0 A hA (Function.update other j s) j

theorem ownGradient_unused (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d)) (hk : ∀ a : i.LocalLabel, i.slot a ≠ k) :
    Φ.ownGradient J frozen c0 A hA j i s k = 0 := by
  classical
  unfold ownGradient VertexCover.finiteMean
  have hz : ∀ hidden : Φ.ownFiber J frozen j i, ∀ other : Φ.BatchWeights J,
      Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j k = 0 := by
    intro hidden other
    apply Φ.canonicalGradient_unused
    have hq := (Φ.mem_ownFiber J frozen j i hidden).mp hidden.property
    rw [hq]
    exact hk
  simp only [hz, integral_zero, Finset.sum_const_zero, zero_div]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnGradientMeasurable
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory

theorem ownMean_lipschitz (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    LipschitzWith 1 (Φ.ownMean J frozen c0 A hA j i) := by
  classical
  have hI : ∀ hidden : Φ.ownFiber J frozen j i,
      LipschitzWith 1 (fun s => ∫ other,
        Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) ∂Φ.batchLaw J) := by
    intro hidden
    apply VertexCover.Average.integral_lipschitz
    · intro s
      exact VertexCover.Cube.integrable_continuous_block
        ((Φ.batchFunction_continuous _ J c0 A hA).comp
          (continuous_id.update j continuous_const))
    · intro other
      exact Φ.batchFunction_own_lipschitz _ J c0 A hA other j
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, ownMean, VertexCover.finiteMean,
    ← sub_div, ← Finset.sum_sub_distrib]
  apply VertexCover.Average.finite_abs_le (hB := dist_nonneg)
  intro hidden
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (hI hidden).dist_le_mul s t

theorem ownGradient_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (k : Fin (Φ.WeightDimension d)) :
    Measurable (fun s => Φ.ownGradient J frozen c0 A hA j i s k) := by
  classical
  have hI : ∀ hidden : Φ.ownFiber J frozen j i,
      StronglyMeasurable (fun s => ∫ other,
        Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j k ∂Φ.batchLaw J) := by
    intro hidden
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp
      ((Φ.canonicalGradient_measurable _ J c0 A hA).comp
        (continuous_snd.update j continuous_fst).measurable))
  unfold ownGradient VertexCover.finiteMean
  exact (Finset.measurable_sum _ (fun hidden _ => (hI hidden).measurable)).div_const _

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ThresholdListEnergy
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.Threshold

theorem energy_le {ι : Type*} [Fintype ι] (b : ℝ) (hb : 0 ≤ b) (g : ι → ℝ)
    (hg : ∑ k, |g k| ≤ 1) :
    (∑ k, (g k)^2) ≤ b + ∑ k ∈ slots b g, |g k| := by
  classical
  have hpoint : ∀ k, (g k)^2 ≤ b * |g k| + if k ∈ slots b g then |g k| else 0 := by
    intro k
    have hab := abs_nonneg (g k)
    have hsq : (g k)^2 = |g k|^2 := (sq_abs _).symm
    have hc := coordinate_bound hg k
    by_cases hk : k ∈ slots b g
    · rw [ite_eq_left hk, hsq]
      have := mul_nonneg hb hab
      nlinarith
    · rw [ite_eq_right hk, add_zero, hsq]
      have hk' : |g k| < b := lt_of_not_ge ((mem_slots b g k).not.mp hk)
      nlinarith
  calc
    (∑ k, (g k)^2) ≤ ∑ k, (b * |g k| + if k ∈ slots b g then |g k| else 0) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = b * (∑ k, |g k|) + ∑ k ∈ slots b g, |g k| := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, slots, Finset.sum_filter]
    _ ≤ b * 1 + ∑ k ∈ slots b g, |g k| := add_le_add (mul_le_mul_of_nonneg_left hg hb) le_rfl
    _ = b + ∑ k ∈ slots b g, |g k| := by ring

end VertexCover.Threshold

namespace VertexCover.LabelCover.Query

theorem thresholdList_energy {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (hb : 0 < b) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hg : ∑ k, |g k| ≤ 1)
    (hzero : ∀ k, (∀ a : i.LocalLabel, i.slot a ≠ k) → g k = 0) :
    (∑ k, (g k)^2) ≤ b + ∑ a ∈ (i.thresholdList b g).toFinset, |g (i.slot a)| := by
  classical
  have heq : (∑ a ∈ (i.thresholdList b g).toFinset, |g (i.slot a)|) =
      ∑ k ∈ VertexCover.Threshold.slots b g, |g k| := by
    rw [← i.thresholdList_slots b hb g hzero,
      Finset.sum_image i.slot_injective.injOn]
  rw [heq]
  exact VertexCover.Threshold.energy_le b hb.le g hg

end VertexCover.LabelCover.Query


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnListEnergy
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def ownList (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ) :
    List i.LocalLabel :=
  i.thresholdList (β/2) (Φ.ownGradient J frozen c0 A hA j i s)

@[simp] theorem mem_ownList (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ)
    (a : i.LocalLabel) :
    a ∈ Φ.ownList J frozen c0 A hA j i s β ↔
      β/2 ≤ |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)| :=
  i.mem_thresholdList _ _ a

theorem ownList_membership_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (β : ℝ) (a : i.LocalLabel) :
    MeasurableSet {s | a ∈ Φ.ownList J frozen c0 A hA j i s β} := by
  simp only [mem_ownList]
  exact measurableSet_le measurable_const
    (Φ.ownGradient_measurable J frozen c0 A hA j i (i.slot a)).abs

theorem ownList_length (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    (m : ℕ) (hm : 0 < m) :
    (Φ.ownList J frozen c0 A hA j i s (Parameters.β m)).length ≤ Parameters.ell m := by
  have h := i.thresholdList_card (Parameters.β m / 2) _
    (Φ.ownGradient_block_bound J frozen c0 A hA j i s)
  have hβ : 0 < Parameters.β m / 2 := by
    have := (Parameters.positive m hm).2.1
    positivity
  apply Nat.cast_le (α := ℝ) |>.mp
  change ((i.thresholdList _ _).length : ℝ) ≤ _
  rw [Parameters.ell_eq m hm]
  have hh := (le_div_iff₀ hβ).mpr h
  simpa only [div_div_eq_mul_div, one_mul] using hh

theorem ownList_energy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    {β : ℝ} (hβ : 0 < β) :
    (∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2) ≤ β/2 +
      ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)| := by
  classical
  exact i.thresholdList_energy (β/2) (by positivity) _
    (Φ.ownGradient_block_bound J frozen c0 A hA j i s)
    (fun k hk => Φ.ownGradient_unused J frozen c0 A hA j i s k hk)

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnPrivateListsDecoding
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def ownPrivateLists (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (β : ℝ) : Φ.PrivateLists d := by
  classical
  exact fun i => if hi : i.1 ∈ J then
    Φ.ownList J frozen c0 A hA ⟨i.1, hi⟩ i (s ⟨i.1, hi⟩) β else []

theorem ownPrivateLists_length (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (m : ℕ) (hm : 0 < m) (i : Φ.Query d) :
    (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m) i).length ≤ Parameters.ell m := by
  classical
  unfold ownPrivateLists
  split_ifs with hi
  · exact Φ.ownList_length J frozen c0 A hA ⟨i.1, hi⟩ i _ m hm
  · simp

theorem ownPrivateLists_membership_measurable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (i : Φ.Query d) (a : i.LocalLabel) :
    MeasurableSet {s | a ∈ Φ.ownPrivateLists J frozen c0 A hA s β i} := by
  classical
  unfold ownPrivateLists
  by_cases hi : i.1 ∈ J
  · simp only [dite_eq_left hi, mem_ownList]
    exact measurableSet_le measurable_const
      (((Φ.ownGradient_measurable J frozen c0 A hA ⟨i.1, hi⟩ i (i.slot a)).comp
        (measurable_pi_apply (⟨i.1, hi⟩ : J))).abs)
  · simp only [dite_eq_right hi, List.not_mem_nil, Set.ofPred_false]
    exact MeasurableSet.empty

theorem ownPrivateLists_decoding_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    (∫ s, finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J) < 3/2 := by
  classical
  let B : ℝ := 1 + ((Parameters.h m).choose 2 : ℝ) *
    (Parameters.ell m : ℝ)^2 * Parameters.σ m
  have hbound : ∀ s : Φ.BatchWeights J, finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)) ≤ B := by
    intro s
    have hh := Φ.decoding_upper_bound hval
      (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
      (Φ.ownPrivateLists_length J frozen c0 A hA s m (by omega)) J frozen
    simpa only [hJ] using hh
  have hint := integral_mono_of_nonneg (μ := Φ.batchLaw J)
    (f := fun s => finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s (Parameters.β m))
        (Φ.spliceSeeds J frozen hidden) J : ℝ)))
    (g := fun _ => B) (Filter.Eventually.of_forall (fun s => by
      unfold finiteMean
      exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (Nat.cast_nonneg _))) (integrable_const B) (Filter.Eventually.of_forall hbound)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hp := Parameters.pair_budget_lt m hm
  dsimp [B] at hint
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_IntegralUpdate
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
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
section
namespace VertexCover.LabelCover
open MeasureTheory

theorem listHitMaximum_measurable {E : Type*} [MeasurableSpace E]
    (Φ : LabelCover) {d : ℕ} (L : E → Φ.PrivateLists d)
    (hL : ∀ i (a : i.LocalLabel), MeasurableSet {x | a ∈ L x i})
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    Measurable (fun x => Φ.listHitMaximum (L x) seed J) := by
  classical
  have hhit : ∀ I : Finset (Φ.Coordinate d), ∀ j : Fin d,
      MeasurableSet {x | Φ.ListHit (L x) seed I j} := by
    intro I j
    change MeasurableSet {x | ∃ a : (Φ.query seed j).LocalLabel,
      a ∈ L x (Φ.query seed j) ∧ (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro a
    exact (hL _ a).inter (MeasurableSet.const _)
  have hcard : ∀ I : Finset (Φ.Coordinate d),
      Measurable (fun x => (Φ.hitPositions (L x) seed I J).card) := by
    intro I
    simp only [hitPositions, Finset.card_filter]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (hhit I j) measurable_const measurable_const
  have hsup : ∀ S : Finset (Finset (Φ.Coordinate d)),
      Measurable (fun x => S.sup (fun I => (Φ.hitPositions (L x) seed I J).card)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert I S hi ih =>
      simp only [Finset.sup_insert]
      exact (hcard I).sup ih
  exact hsup _

theorem ownPrivateLists_hits_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen seed : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ) :
    Integrable (fun s => (Φ.listHitMaximum
      (Φ.ownPrivateLists J frozen c0 A hA s β) seed J : ℝ)) (Φ.batchLaw J) := by
  classical
  have hmeas := Φ.listHitMaximum_measurable
    (fun s => Φ.ownPrivateLists J frozen c0 A hA s β)
    (Φ.ownPrivateLists_membership_measurable J frozen c0 A hA β) seed J
  have hcast : Measurable (fun s => (Φ.listHitMaximum
      (Φ.ownPrivateLists J frozen c0 A hA s β) seed J : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hmeas
  apply Integrable.of_bound hcast.aestronglyMeasurable (J.card : ℝ)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  apply Nat.cast_le.mpr
  apply Finset.sup_le
  intro I _
  exact Finset.card_le_card (Finset.filter_subset _ _)

end VertexCover.LabelCover

namespace VertexCover.Product
open MeasureTheory

theorem update_measurePreserving {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    MeasurePreserving (fun p : E × (ι → E) => Function.update p.2 j p.1)
      (μ.prod (Measure.pi (fun _ : ι => μ))) (Measure.pi (fun _ : ι => μ)) := by
  have hm : Measurable (fun p : E × (ι → E) => Function.update p.2 j p.1) :=
    Measurable.of_eval (fun k => by
      by_cases hk : k = j
      · subst k; simpa using measurable_fst
      · simpa only [Function.update_of_ne hk, Function.comp_def] using
          (measurable_pi_apply k).comp measurable_snd)
  refine ⟨hm, (Measure.pi_eq (fun S hS => ?_)).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hpre : (fun p : E × (ι → E) => Function.update p.2 j p.1) ⁻¹' Set.univ.pi S =
      S j ×ˢ Set.univ.pi (Function.update S j Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · simpa using hp j
      · intro k
        by_cases hk : k = j
        · subst k; simp
        · simpa [Function.update_of_ne hk] using hp k
    · rintro ⟨hp, hq⟩ k
      by_cases hk : k = j
      · subst k; simpa using hp
      · simpa [Function.update_of_ne hk] using hq k
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hfun : (fun k => μ (Function.update S j Set.univ k)) =
      Function.update (fun k => μ (S k)) j 1 := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.mul_prod_erase Finset.univ (fun k => μ (S k)) (Finset.mem_univ j)

theorem update_ae {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {P : (ι → E) → Prop} (hP : ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P s) :
    ∀ᵐ x ∂μ, ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P (Function.update s j x) := by
  exact Measure.ae_ae_of_ae_prod ((update_measurePreserving μ j).quasiMeasurePreserving.ae hP)

theorem integral_update {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {f : (ι → E) → ℝ} (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ x, ∫ s, f (Function.update s j x) ∂Measure.pi (fun _ : ι => μ) ∂μ) =
      ∫ s, f s ∂Measure.pi (fun _ : ι => μ) := by
  have hp := update_measurePreserving μ j
  calc
    _ = ∫ p, f (Function.update p.2 j p.1)
        ∂(μ.prod (Measure.pi (fun _ : ι => μ))) := by
      simpa only [Function.comp_apply] using
        (integral_prod _ (hp.integrable_comp_of_integrable hf)).symm
    _ = ∫ s, f s ∂Measure.map (fun p : E × (ι → E) => Function.update p.2 j p.1)
        (μ.prod (Measure.pi (fun _ : ι => μ))) := by
      exact (integral_map hp.measurable.aemeasurable
        (by simpa only [hp.map_eq] using hf.aestronglyMeasurable)).symm
    _ = _ := by rw [hp.map_eq]

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnFiberTower
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory

theorem canonicalGradient_update_integrable (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) (k : Fin (Φ.WeightDimension d)) :
    Integrable (fun other : Φ.BatchWeights J =>
      Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (Φ.batchLaw J) := by
  apply Integrable.of_bound
    (Φ.canonicalGradient_update_measurable seed J c0 A hA j s k).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro other
  simpa only [Real.norm_eq_abs] using VertexCover.Threshold.coordinate_bound
    (Φ.canonicalGradient_block_bound seed J c0 A hA (Function.update other j s) j) k

theorem ownList_jensen (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ) (β : ℝ) :
    (∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
      |Φ.ownGradient J frozen c0 A hA j i s (i.slot a)|) ≤
    VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
      ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J) := by
  classical
  exact VertexCover.Average.selected_integral_abs_le (Φ.batchLaw J)
    (Φ.ownList J frozen c0 A hA j i s β).toFinset
    (fun (hidden : Φ.ownFiber J frozen j i) other a =>
      Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j (i.slot a))
    (fun hidden a => Φ.canonicalGradient_update_integrable _ J c0 A hA j s (i.slot a))

theorem ownGradient_energy_le_averaged_mass (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (s : Fin (Φ.WeightDimension d) → ℝ)
    {β : ℝ} (hβ : 0 < β) :
    (∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j i =>
      ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
        |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
          (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J) := by
  exact (Φ.ownList_energy J frozen c0 A hA j i s hβ).trans
    (add_le_add le_rfl (Φ.ownList_jensen J frozen c0 A hA j i s β))

theorem ownFiber_tower (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (F : Φ.Query d → Φ.HiddenSeeds J → ℝ) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      VertexCover.finiteMean (fun hidden' : Φ.ownFiber J frozen j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) =>
          F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden')) =
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden) := by
  classical
  exact VertexCover.Average.finiteMean_fiber_tower_of_mem
    (fun hidden : Φ.HiddenSeeds J => Φ.query (Φ.spliceSeeds J frozen hidden) j) F
    (Φ.ownFiber J frozen j) (fun i hidden => Φ.mem_ownFiber J frozen j i hidden)

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnMeanPartialAe
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.law_negInvariant _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem batchFunction_own_partial (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (other : Φ.BatchWeights J) (j : J) (s : Fin (Φ.WeightDimension d) → ℝ)
    (k : Fin (Φ.WeightDimension d))
    (hd : DifferentiableAt ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))
    (hg : Φ.canonicalGradient seed J c0 A hA (Function.update other j s) =
      Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))) :
    HasDerivAt (fun x => Φ.batchFunction seed J c0 A hA
      (Function.update other j (Function.update s k x)))
      (Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (s k) := by
  classical
  have hD : HasFDerivAt (Φ.batchFunction seed J c0 A hA)
      (fderiv ℝ (Φ.batchFunction seed J c0 A hA) (Function.update other j s))
      (Function.update other j (Function.update s k (s k))) := by
    simpa only [Function.update_eq_self] using hd.hasFDerivAt
  rw [hg]
  exact hD.comp_hasDerivAt (s k) (VertexCover.Product.hasDerivAt_nested_update other j s k)

theorem ownIntegral_partial_ae (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (k : Fin (Φ.WeightDimension d)) :
    ∀ᵐ s ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      HasDerivAt (fun x => ∫ other, Φ.batchFunction seed J c0 A hA
        (Function.update other j (Function.update s k x)) ∂Φ.batchLaw J)
        (∫ other, Φ.canonicalGradient seed J c0 A hA
          (Function.update other j s) j k ∂Φ.batchLaw J) (s k) := by
  classical
  have hfull := Φ.canonicalGradient_ae_cube seed J c0 A hA
  have hae := VertexCover.Product.update_ae
    (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) j hfull
  filter_upwards [hae] with s hs
  have hi : ∀ x : ℝ, Integrable (fun other => Φ.batchFunction seed J c0 A hA
      (Function.update other j (Function.update s k x))) (Φ.batchLaw J) := by
    intro x
    exact VertexCover.Cube.integrable_continuous_block
      ((Φ.batchFunction_continuous _ J c0 A hA).comp
        (continuous_id.update j continuous_const))
  have hdiff : ∀ᵐ other ∂Φ.batchLaw J,
      HasDerivAt (fun x => Φ.batchFunction seed J c0 A hA
        (Function.update other j (Function.update s k x)))
        (Φ.canonicalGradient seed J c0 A hA (Function.update other j s) j k) (s k) := by
    filter_upwards [hs] with other ho
    exact Φ.batchFunction_own_partial seed J c0 A hA other j s k ho.1 ho.2
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := Set.univ) (bound := fun _ => (1 : ℝ)) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun x => (hi x).aestronglyMeasurable))
    (hi (s k))
    (Φ.canonicalGradient_update_measurable seed J c0 A hA j s k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun other => by
      have hl := (Φ.batchFunction_own_lipschitz seed J c0 A hA other j).comp
        (VertexCover.Product.update_lipschitz s k)
      simpa [Function.comp_def] using hl.lipschitzOnWith (s := Set.univ)))
    (integrable_const (1 : ℝ)) hdiff).2

theorem ownMean_partial_ae (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) (k : Fin (Φ.WeightDimension d)) :
    ∀ᵐ s ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      HasDerivAt (fun x => Φ.ownMean J frozen c0 A hA j i (Function.update s k x))
        (Φ.ownGradient J frozen c0 A hA j i s k) (s k) := by
  classical
  have hall := (ae_all_iff.mpr (fun hidden : Φ.ownFiber J frozen j i =>
    Φ.ownIntegral_partial_ae (Φ.spliceSeeds J frozen hidden) J c0 A hA j k))
  filter_upwards [hall] with s hs
  simpa only [ownMean, ownGradient, VertexCover.finiteMean, Finset.sum_apply] using
    (HasDerivAt.sum (u := Finset.univ) (fun hidden _ => hs hidden)).div_const
      (Fintype.card (Φ.ownFiber J frozen j i) : ℝ)

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PrivateMassSumHits
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory

noncomputable def privateMass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) : ℝ := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  exact ∑ a ∈ (Φ.ownList J frozen c0 A hA j i (s j) β).toFinset,
    |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA s j (i.slot a)|

theorem privateMass_nonneg (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) :
    0 ≤ Φ.privateMass J frozen c0 A hA β hidden s j := by
  unfold privateMass
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem privateMass_le_one (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) (j : J) :
    Φ.privateMass J frozen c0 A hA β hidden s j ≤ 1 := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  let L := (Φ.ownList J frozen c0 A hA j i (s j) β).toFinset
  change (∑ a ∈ L, |Φ.canonicalGradient _ J c0 A hA s j (i.slot a)|) ≤ 1
  calc
    _ = ∑ k ∈ L.image i.slot, |Φ.canonicalGradient _ J c0 A hA s j k| := by
      rw [Finset.sum_image i.slot_injective.injOn]
    _ ≤ ∑ k, |Φ.canonicalGradient _ J c0 A hA s j k| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => abs_nonneg _)
    _ ≤ 1 := Φ.canonicalGradient_block_bound _ J c0 A hA s j

theorem privateMass_measurable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (j : J) :
    Measurable (fun s => Φ.privateMass J frozen c0 A hA β hidden s j) := by
  classical
  let i := Φ.query (Φ.spliceSeeds J frozen hidden) j
  apply VertexCover.Average.selected_sum_measurable
  · intro a
    exact (Φ.ownList_membership_measurable J frozen c0 A hA j i β a).preimage
      (measurable_pi_apply j)
  · intro a
    exact ((measurable_pi_apply (i.slot a)).comp ((measurable_pi_apply j).comp
      (Φ.canonicalGradient_measurable _ J c0 A hA))).abs

theorem privateMass_integrable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (j : J) :
    Integrable (fun s => Φ.privateMass J frozen c0 A hA β hidden s j) (Φ.batchLaw J) := by
  apply Integrable.of_bound (Φ.privateMass_measurable J frozen c0 A hA β hidden j).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (Φ.privateMass_nonneg J frozen c0 A hA β hidden s j)]
  exact Φ.privateMass_le_one J frozen c0 A hA β hidden s j

theorem ownEnergy_le_resampled_mass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (s : Fin (Φ.WeightDimension d) → ℝ) {β : ℝ} (hβ : 0 < β) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ other, Φ.privateMass J frozen c0 A hA β hidden
        (Function.update other j s) j ∂Φ.batchLaw J) := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  let F : Φ.Query d → Φ.HiddenSeeds J → ℝ := fun i hidden =>
    ∫ other, ∑ a ∈ (Φ.ownList J frozen c0 A hA j i s β).toFinset,
      |Φ.canonicalGradient (Φ.spliceSeeds J frozen hidden) J c0 A hA
        (Function.update other j s) j (i.slot a)| ∂Φ.batchLaw J
  have h := VertexCover.finiteMean_mono (fun hidden : Φ.HiddenSeeds J =>
    Φ.ownGradient_energy_le_averaged_mass J frozen c0 A hA j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) s hβ)
  rw [VertexCover.finiteMean_add, VertexCover.finiteMean_const] at h
  change _ ≤ β/2 + VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    VertexCover.finiteMean (fun hidden' : Φ.ownFiber J frozen j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) =>
      F (Φ.query (Φ.spliceSeeds J frozen hidden) j) hidden')) at h
  rw [Φ.ownFiber_tower] at h
  simpa only [privateMass, Function.update_self] using h

theorem privateMass_sum_le_hits (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    (∑ j : J, Φ.privateMass J frozen c0 A hA β hidden s j) ≤
      Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
        (Φ.spliceSeeds J frozen hidden) J := by
  classical
  have h := Φ.canonicalGradient_listMass (Φ.spliceSeeds J frozen hidden) J c0 A hA s
    (Φ.ownPrivateLists J frozen c0 A hA s β)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j hj
  unfold privateMass ownPrivateLists
  have hpos : (Φ.query (Φ.spliceSeeds J frozen hidden) j).1 ∈ J := j.property
  rw [dite_eq_left hpos]
  rw [show (⟨(Φ.query (Φ.spliceSeeds J frozen hidden) j).1, hpos⟩ : J) = j from Subtype.ext rfl]

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnTotalEnergyNo
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.law_negInvariant _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover
open MeasureTheory

theorem integrable_finiteMean {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : α → Ω → ℝ) (hF : ∀ a, Integrable (F a) μ) :
    Integrable (fun x => finiteMean (fun a => F a x)) μ := by
  classical
  exact (integrable_finsetSum Finset.univ (fun a _ => hF a)).div_const _

theorem integral_finiteMean {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : α → Ω → ℝ) (hF : ∀ a, Integrable (F a) μ) :
    (∫ x, finiteMean (fun a => F a x) ∂μ) = finiteMean (fun a => ∫ x, F a x ∂μ) := by
  classical
  unfold finiteMean
  rw [integral_div, integral_finsetSum _ (fun a _ => hF a)]

end VertexCover

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def ownTotalEnergy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : ℝ :=
  ∑ j : J, ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    ∑ k, (Φ.ownGradient J frozen c0 A hA j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2)
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))

theorem ownEnergy_integral_le_mass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) {β : ℝ} (hβ : 0 < β) :
    (∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2)
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J) := by
  classical
  let μ := VertexCover.Cube.law (Fin (Φ.WeightDimension d))
  let R : Φ.HiddenSeeds J → (Fin (Φ.WeightDimension d) → ℝ) → ℝ := fun hidden s =>
    ∫ other, Φ.privateMass J frozen c0 A hA β hidden
      (Function.update other j s) j ∂Φ.batchLaw J
  have hR : ∀ hidden, Integrable (R hidden) μ := by
    intro hidden
    have hp := VertexCover.Product.update_measurePreserving μ j
    have hf := hp.integrable_comp_of_integrable
      (Φ.privateMass_integrable J frozen c0 A hA β hidden j)
    exact hf.integral_prod_left
  have ht : ∀ hidden, (∫ s, R hidden s ∂μ) =
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J := by
    intro hidden
    exact VertexCover.Product.integral_update μ j
      (Φ.privateMass_integrable J frozen c0 A hA β hidden j)
  have hI := VertexCover.integrable_finiteMean μ R hR
  calc
    _ ≤ ∫ s, β/2 + VertexCover.finiteMean (fun hidden => R hidden s) ∂μ := by
      apply integral_mono_of_nonneg
      · apply Filter.Eventually.of_forall
        intro s
        exact div_nonneg (Finset.sum_nonneg (fun hidden _ =>
          Finset.sum_nonneg (fun k _ => sq_nonneg _))) (Nat.cast_nonneg _)
      · exact (integrable_const _).add hI
      · exact Filter.Eventually.of_forall (fun s =>
          Φ.ownEnergy_le_resampled_mass J frozen c0 A hA j s hβ)
    _ = β/2 + VertexCover.finiteMean (fun hidden => ∫ s, R hidden s ∂μ) := by
      rw [integral_add (integrable_const _) hI, VertexCover.integral_finiteMean μ R hR]
      simp only [integral_const, probReal_univ, one_smul]
    _ = _ := by simp only [ht]

theorem ownTotalEnergy_le_hits (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    Φ.ownTotalEnergy J frozen c0 A hA ≤ (J.card : ℝ)*β/2 +
      ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
          (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J := by
  classical
  let mass := fun (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) =>
    ∑ j : J, Φ.privateMass J frozen c0 A hA β hidden s j
  have hm : ∀ hidden, Integrable (mass hidden) (Φ.batchLaw J) := fun hidden =>
    integrable_finsetSum _ (fun j _ => Φ.privateMass_integrable J frozen c0 A hA β hidden j)
  have he : (∑ j : J, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J)) =
      ∫ s, VertexCover.finiteMean (fun hidden => mass hidden s) ∂Φ.batchLaw J := by
    rw [VertexCover.integral_finiteMean _ mass hm]
    simp only [mass, integral_finsetSum _ (fun j _ =>
      Φ.privateMass_integrable J frozen c0 A hA β _ j)]
    exact (VertexCover.finiteMean_sum _).symm
  have hh : (∫ s, VertexCover.finiteMean (fun hidden => mass hidden s) ∂Φ.batchLaw J) ≤
      ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
          (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J := by
    apply integral_mono_of_nonneg
    · apply Filter.Eventually.of_forall
      intro s
      exact div_nonneg (Finset.sum_nonneg (fun hidden _ => Finset.sum_nonneg
        (fun j _ => Φ.privateMass_nonneg J frozen c0 A hA β hidden s j))) (Nat.cast_nonneg _)
    · exact VertexCover.integrable_finiteMean _ _ (fun hidden =>
        Φ.ownPrivateLists_hits_integrable J frozen (Φ.spliceSeeds J frozen hidden) c0 A hA β)
    · exact Filter.Eventually.of_forall (fun s => VertexCover.finiteMean_mono
        (fun hidden => Φ.privateMass_sum_le_hits J frozen c0 A hA β hidden s))
  calc
    _ ≤ ∑ j : J, (β/2 + VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J)) :=
      Finset.sum_le_sum (fun j _ => Φ.ownEnergy_integral_le_mass J frozen c0 A hA j hβ)
    _ = (J.card : ℝ)*β/2 + ∫ s, VertexCover.finiteMean (fun hidden => mass hidden s)
        ∂Φ.batchLaw J := by
      rw [Finset.sum_add_distrib, he]
      simp [mul_div_assoc]
    _ ≤ _ := add_le_add le_rfl hh

theorem ownTotalEnergy_no_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalEnergy J frozen c0 A hA < 7/2 := by
  have hm0 : 0 < m := by omega
  have hβ := (Parameters.positive m hm0).2.1
  have he := Φ.ownTotalEnergy_le_hits J frozen c0 A hA hβ
  have hz := Φ.ownPrivateLists_decoding_upper m hm hval J hJ frozen c0 A hA
  have hc : (J.card : ℝ)*Parameters.β m/2 = 2 := by
    rw [hJ, mul_comm]
    exact Parameters.β_h m hm0
  rw [hc] at he
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_VariancePi
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.Product
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem update_joint_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun p : (Fin n → X) × X => Function.update p.1 j p.2) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k = j
  · subst k; simpa using measurable_snd
  · simpa only [Function.update_of_ne hk, Function.comp_def] using (measurable_pi_apply k).comp measurable_fst

theorem coordinateVariance_integrable {n : ℕ} (f : (Fin n → X) → ℝ)
    (hf : Measurable f) {C : ℝ} (hb : ∀ s, ‖f s‖ ≤ C) (j : Fin n) :
    Integrable (coordinateVariance μ f j) (Measure.pi (fun _ : Fin n => μ)) :=
  section_variance_integrable _ μ _ (hf.comp (update_joint_measurable j)) (fun _s _x => hb _)

theorem variance_pi_le (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ s, ‖f s‖ ≤ C) :
    variance f (Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ j, ∫ s, coordinateVariance μ f j s ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
      have he : f = fun _ => f (fun i => Fin.elim0 i) := by
        funext s
        exact congrArg f (Subsingleton.elim _ _)
      rw [he, variance_eq_integral measurable_const.aemeasurable]
      simp
  | succ n ih =>
      let P := Measure.pi (fun _ : Fin n => μ)
      let F : X → (Fin n → X) → ℝ := fun x s => f (Fin.cons x s)
      have hF : Measurable (Function.uncurry F) := hf.comp (cons_measurePreserving μ n).measurable
      have hFb : ∀ x s, ‖F x s‖ ≤ C := fun x s => hb _
      have hsec : ∀ x, Measurable (F x) := fun x => hF.comp (measurable_const.prodMk measurable_id)
      have hpre : variance f (Measure.pi (fun _ : Fin (n+1) => μ)) ≤
          (∫ x, variance (F x) P ∂μ) + ∫ s, variance (fun x => F x s) μ ∂P := by
        rw [← (cons_measurePreserving μ n).variance_fun_comp hf.aemeasurable]
        exact variance_product_le μ P F hF hFb
      have hci := fun j : Fin (n+1) => coordinateVariance_integrable μ f hf hb j
      have hstep : ∀ x s (j : Fin n),
          coordinateVariance μ (F x) j s = coordinateVariance μ f j.succ (Fin.cons x s) := by
        intro x s j
        unfold coordinateVariance F
        simp only [Fin.cons_update]
      have hIi : ∀ j : Fin n, Integrable
          (fun x => ∫ s, coordinateVariance μ (F x) j s ∂P) μ := by
        intro j
        simp_rw [hstep]
        exact ((cons_measurePreserving μ n).integrable_comp_of_integrable (hci j.succ)).integral_prod_left
      have ht : (∫ x, variance (F x) P ∂μ) ≤
          ∑ j : Fin n, ∫ s, coordinateVariance μ f j.succ s ∂Measure.pi (fun _ => μ) := by
        calc
          _ ≤ ∫ x, ∑ j : Fin n, ∫ s, coordinateVariance μ (F x) j s ∂P ∂μ := by
            apply integral_mono (section_variance_integrable μ P F hF hFb)
              (integrable_finsetSum _ (fun j _ => hIi j))
            intro x
            exact ih (F x) (hsec x) (hFb x)
          _ = _ := by
            rw [integral_finsetSum _ (fun j _ => hIi j)]
            apply Finset.sum_congr rfl
            intro j hj
            simp_rw [hstep]
            exact (integral_cons μ n _ (hci j.succ)).symm
      have hz : (∫ s, variance (fun x => F x s) μ ∂P) =
          ∫ s, coordinateVariance μ f 0 s ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
        rw [integral_cons μ n _ (hci 0)]
        simp only [coordinateVariance, Fin.update_cons_zero]
        simp only [F, integral_const, probReal_univ, one_smul]
        rfl
      calc
        _ ≤ (∫ x, variance (F x) P ∂μ) + ∫ s, variance (fun x => F x s) μ ∂P := hpre
        _ ≤ (∑ j : Fin n, ∫ s, coordinateVariance μ f j.succ s ∂Measure.pi (fun _ => μ)) +
            ∫ s, coordinateVariance μ f 0 s ∂Measure.pi (fun _ => μ) := by
          rw [← hz]
          exact add_le_add ht le_rfl
        _ = _ := by rw [Fin.sum_univ_succ]; exact add_comm _ _

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralCut
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

noncomputable section
namespace UniqueGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

end Indicators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

end UniqueGames.Foundations.PCP.SpectralCut
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_VarianceCoordinateSum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.intervalLaw_negInvariant _root_.OAI.VertexCover.Cube.law_negInvariant _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Product
open MeasureTheory

theorem update_right_measurePreserving {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    MeasurePreserving (fun p : (ι → E) × E => Function.update p.1 j p.2)
      ((Measure.pi (fun _ : ι => μ)).prod μ) (Measure.pi (fun _ : ι => μ)) := by
  exact (update_measurePreserving μ j).comp Measure.measurePreserving_swap

theorem update_right_ae {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {P : (ι → E) → Prop} (hP : ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P s) :
    ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), ∀ᵐ x ∂μ, P (Function.update s j x) := by
  exact Measure.ae_ae_of_ae_prod ((update_right_measurePreserving μ j).quasiMeasurePreserving.ae hP)

theorem integral_update_right {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {f : (ι → E) → ℝ} (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ s, ∫ x, f (Function.update s j x) ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s ∂Measure.pi (fun _ : ι => μ) := by
  have hp := update_right_measurePreserving μ j
  calc
    _ = ∫ p, f (Function.update p.1 j p.2)
        ∂((Measure.pi (fun _ : ι => μ)).prod μ) := by
      simpa only [Function.comp_apply] using
        (integral_prod _ (hp.integrable_comp_of_integrable hf)).symm
    _ = ∫ s, f s ∂Measure.map (fun p : (ι → E) × E => Function.update p.1 j p.2)
        ((Measure.pi (fun _ : ι => μ)).prod μ) := by
      exact (integral_map hp.measurable.aemeasurable
        (by simpa only [hp.map_eq] using hf.aestronglyMeasurable)).symm
    _ = _ := by rw [hp.map_eq]

end VertexCover.Product

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem variance_le_coordinate_sum {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith 1 f) :
    variance f (law (Fin n)) ≤
      ∑ j, ∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n) := by
  have he := boundedVersion_ae f
  have hb := VertexCover.Product.variance_pi_le intervalLaw n (boundedVersion f)
    (boundedVersion_measurable hf.continuous.measurable) (boundedVersion_bound hf)
  have hv : variance (boundedVersion f) (law (Fin n)) = variance f (law (Fin n)) :=
    variance_congr he
  change variance (boundedVersion f) (law (Fin n)) ≤ _ at hb
  rw [hv] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [VertexCover.Product.update_right_ae intervalLaw j he] with s hs
  exact (variance_congr hs).symm

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_Poincare
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.intervalLaw_negInvariant _root_.OAI.VertexCover.Cube.law_negInvariant _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory

theorem deriv_on_resampled_fibers {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : (Fin n → ℝ) → Fin n → ℝ) (j : Fin n)
    (hD : ∀ᵐ s ∂law (Fin n),
      HasDerivAt (fun x => f (Function.update s j x)) (G s j) (s j)) :
    ∀ᵐ s ∂law (Fin n), ∀ᵐ x ∂intervalLaw,
      deriv (fun y => f (Function.update s j y)) x = G (Function.update s j x) j := by
  filter_upwards [VertexCover.Product.update_right_ae intervalLaw j hD] with s hs
  filter_upwards [hs] with x hx
  simp only [Function.update_idem, Function.update_self] at hx
  exact hx.deriv

theorem poincare {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : LipschitzWith 1 f)
    (G : (Fin n → ℝ) → Fin n → ℝ)
    (hGm : ∀ j, Measurable (fun s => G s j))
    (hGb : ∀ s j, |G s j| ≤ 1)
    (hD : ∀ j, ∀ᵐ s ∂law (Fin n),
      HasDerivAt (fun x => f (Function.update s j x)) (G s j) (s j)) :
    variance f (law (Fin n)) ≤ 2 * ∫ s, ∑ j, (G s j)^2 ∂law (Fin n) := by
  have hGi : ∀ j, Integrable (fun s => (G s j)^2) (law (Fin n)) := by
    intro j
    apply Integrable.of_bound ((hGm j).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hGb s j, abs_nonneg (G s j), sq_abs (G s j)]
  have hres : ∀ j, Integrable
      (fun p : (Fin n → ℝ) × ℝ => (G (Function.update p.1 j p.2) j)^2)
      ((law (Fin n)).prod intervalLaw) := fun j =>
    (VertexCover.Product.update_right_measurePreserving intervalLaw j).integrable_comp_of_integrable (hGi j)
  have hvb : ∀ j, Integrable
      (VertexCover.Product.coordinateVariance intervalLaw (boundedVersion f) j) (law (Fin n)) := by
    intro j
    exact VertexCover.Product.coordinateVariance_integrable intervalLaw (boundedVersion f)
      (boundedVersion_measurable hf.continuous.measurable) (boundedVersion_bound hf) j
  have hvi : ∀ j, Integrable
      (VertexCover.Product.coordinateVariance intervalLaw f j) (law (Fin n)) := by
    intro j
    apply (hvb j).congr
    filter_upwards [VertexCover.Product.update_right_ae intervalLaw j (boundedVersion_ae f)] with s hs
    exact variance_congr hs
  have hs : ∀ j, (∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n)) ≤
      2 * ∫ s, (G s j)^2 ∂law (Fin n) := by
    intro j
    calc
      _ ≤ ∫ s, 2 * ∫ x, (G (Function.update s j x) j)^2 ∂intervalLaw ∂law (Fin n) := by
        apply integral_mono_ae (hvi j) ((hres j).integral_prod_left.const_mul 2)
        filter_upwards [deriv_on_resampled_fibers f G j (hD j)] with s hs
        have hfs : LipschitzWith 1 (fun x => f (Function.update s j x)) := by
          simpa only [one_mul, Function.comp_def] using hf.comp (VertexCover.Product.update_lipschitz s j)
        have he : (∫ x, (deriv (fun y => f (Function.update s j y)) x)^2 ∂intervalLaw) =
            ∫ x, (G (Function.update s j x) j)^2 ∂intervalLaw := by
          apply integral_congr_ae
          filter_upwards [hs] with x hx
          rw [hx]
        simpa only [VertexCover.Product.coordinateVariance, he] using poincare_one hfs
      _ = _ := by
        rw [integral_const_mul]
        exact congrArg (fun z : ℝ => 2*z) (VertexCover.Product.integral_update_right intervalLaw j (hGi j))
  calc
    _ ≤ ∑ j, ∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n) :=
      variance_le_coordinate_sum hf
    _ ≤ ∑ j, 2 * ∫ s, (G s j)^2 ∂law (Fin n) := Finset.sum_le_sum (fun j _ => hs j)
    _ = _ := by rw [← Finset.mul_sum, integral_finsetSum _ (fun j _ => hGi j)]

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnTotalVarianceNo
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.law_negInvariant _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory ProbabilityTheory

theorem ownMean_poincare (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    variance (Φ.ownMean J frozen c0 A hA j i)
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) ≤
      2 * ∫ s, ∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
  apply VertexCover.Cube.poincare (Φ.ownMean_lipschitz J frozen c0 A hA j i)
    (Φ.ownGradient J frozen c0 A hA j i)
    (Φ.ownGradient_measurable J frozen c0 A hA j i)
  · intro s k
    exact VertexCover.Threshold.coordinate_bound (Φ.ownGradient_block_bound J frozen c0 A hA j i s) k
  · exact Φ.ownMean_partial_ae J frozen c0 A hA j i

noncomputable def ownTotalVariance (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : ℝ :=
  ∑ j : J, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    variance (Φ.ownMean J frozen c0 A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))))

theorem ownGradient_sq_integrable (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) (i : Φ.Query d) :
    Integrable (fun s => ∑ k, (Φ.ownGradient J frozen c0 A hA j i s k)^2)
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) := by
  apply integrable_finsetSum
  intro k hk
  apply Integrable.of_bound ((Φ.ownGradient_measurable J frozen c0 A hA j i k).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with s
  have hb := VertexCover.Threshold.coordinate_bound (Φ.ownGradient_block_bound J frozen c0 A hA j i s) k
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg (Φ.ownGradient J frozen c0 A hA j i s k),
    sq_abs (Φ.ownGradient J frozen c0 A hA j i s k)]

theorem ownTotalVariance_le_energy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalVariance J frozen c0 A hA ≤ 2 * Φ.ownTotalEnergy J frozen c0 A hA := by
  classical
  unfold ownTotalVariance ownTotalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [VertexCover.integral_finiteMean _ _ (fun hidden =>
    Φ.ownGradient_sq_integrable J frozen c0 A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))]
  calc
    _ ≤ VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      2 * ∫ s, ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))) :=
      VertexCover.finiteMean_mono (fun hidden => Φ.ownMean_poincare J frozen c0 A hA j _)
    _ = _ := by simp only [VertexCover.finiteMean, ← Finset.mul_sum]; ring

theorem ownTotalVariance_no_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalVariance J frozen c0 A hA < 7 := by
  have he := Φ.ownTotalVariance_le_energy J frozen c0 A hA
  have hu := Φ.ownTotalEnergy_no_upper m hm hval J hJ frozen c0 A hA
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_Restriction
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
                                                               

namespace VertexCover.Restriction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace EnergyForm
variable (B : EnergyForm E)

namespace Projection
variable {B : EnergyForm E}

@[simp] theorem natExtension_fin {d : ℕ} (P : Fin d → B.Projection) (i : Fin d) :
    natExtension P i.val = P i := dite_eq_left i.isLt

theorem natExtension_commute {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) :
    ∀ i j, ∀ x, natExtension P i (natExtension P j x) =
      natExtension P j (natExtension P i x) := by
  intro i j x
  unfold natExtension
  split_ifs <;> simp only [ident_apply, h]

theorem natExtension_commute_of {d : ℕ} (P : Fin d → B.Projection) (Q : B.Projection)
    (h : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (i : ℕ) (x : E) :
    natExtension P i (Q x) = Q (natExtension P i x) := by
  unfold natExtension
  split_ifs <;> simp only [ident_apply, h]

theorem productMap_range_natExtension {d : ℕ} (P : Fin d → B.Projection) (x : E) :
    productMap (natExtension P) (List.range d) x = productMap P (List.finRange d) x := by
  have he : (List.finRange d).map Fin.val = List.range d := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [← he, productMap_map]
  simp only [natExtension_fin]

def finDifference {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : Fin d) : B.Projection :=
  difference (natExtension P) (natExtension_commute P h) i.val

theorem finDifference_energy_sum {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (x : E) :
    (∑ i : Fin d, B.energy (finDifference P h i x)) +
      B.energy (productMap P (List.finRange d) x) = B.energy x := by
  have he := difference_energy_sum (natExtension P) (natExtension_commute P h) d x
  rw [← Fin.sum_univ_eq_sum_range, productMap_range_natExtension] at he
  exact he

theorem finDifference_residual_budget {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (x : E) :
    (∑ i : Fin d, B.energy (Q.residual (finDifference P h i x))) ≤
      B.energy (Q.residual x) := by
  have he := difference_residual_budget (natExtension P) (natExtension_commute P h)
    Q (natExtension_commute_of P Q hq) d x
  rw [← Fin.sum_univ_eq_sum_range] at he
  exact he

theorem finDifference_retained_le {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x)) (i : Fin d) (x : E) :
    B.energy (Q (finDifference P h i x)) ≤ B.energy (Q x) :=
  difference_retained_le (natExtension P) (natExtension_commute P h)
    Q (natExtension_commute_of P Q hq) i.val x

theorem finDifference_centered {d : ℕ} (P : Fin d → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : Fin d) (x : E) :
    (P i).residual (finDifference P h i x) = finDifference P h i x := by
  simp only [finDifference, difference_apply, natExtension_fin, residual_apply,
    map_sub, apply_idem, sub_self, sub_zero]

theorem product_loss_finset {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (s : Finset ι) (x : E) :
    B.energy ((product P h s.toList).residual x) ≤ ∑ i ∈ s, B.energy ((P i).residual x) := by
  classical
  have he := product_loss_le P h s.toList x
  rw [← List.sum_toFinset _ s.nodup_toList] at he
  simpa using he

end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ConditionNested
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
section
namespace VertexCover.Restriction
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace EnergyForm

noncomputable def finite {S : Type*} [Fintype S] (B : EnergyForm E) : EnergyForm (S → E) where
  form :=
    { toFun := fun f =>
        { toFun := fun g => (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s)
          map_add' := fun g h => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun a g => by simp [mul_left_comm, Finset.mul_sum] }
      map_add' := fun f g => by
        ext h
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        ext g
        simp [mul_left_comm, Finset.mul_sum] }
  symm f g := by
    change (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s) =
      (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (g s) (f s)
    simp only [B.symm]
  nonneg f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun s _ => B.nonneg (f s)))

@[simp] theorem finite_form {S : Type*} [Fintype S] (B : EnergyForm E) (f g : S → E) :
    B.finite.form f g = (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (g s) := rfl

@[simp] theorem finite_energy {S : Type*} [Fintype S] (B : EnergyForm E) (f : S → E) :
    B.finite.energy f = (Fintype.card S : ℝ)⁻¹ * ∑ s, B.energy (f s) := rfl

namespace Projection
variable {B : EnergyForm E}

def lift {S : Type*} [Fintype S] (P : B.Projection) : (B.finite (S := S)).Projection where
  toLinearMap :=
    { toFun := fun f s => P (f s)
      map_add' := fun f g => funext (fun s => P.map_add (f s) (g s))
      map_smul' := fun a f => funext (fun s => P.map_smul a (f s)) }
  idem f := funext (fun s => P.apply_idem (f s))
  selfAdjoint f g := by
    change (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (P (f s)) (g s) =
      (Fintype.card S : ℝ)⁻¹ * ∑ s, B.form (f s) (P (g s))
    simp only [P.selfAdjoint]

@[simp] theorem lift_apply {S : Type*} [Fintype S] (P : B.Projection) (f : S → E) (s : S) :
    P.lift f s = P (f s) := rfl

theorem productMap_lift {S ι : Type*} [Fintype S] (P : ι → B.Projection)
    (is : List ι) (f : S → E) (s : S) :
    productMap (fun i => (P i).lift) is f s = productMap P is (f s) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [productMap_cons, lift_apply, ih]

section Conditional
variable {S T : Type*} [Fintype S]

theorem fiberSize_pos (q : S → T) (s : S) : 0 < fiberSize q (q s) := by
  classical
  exact Finset.card_pos.mpr ⟨s, by simp⟩

theorem fiberKernel_symm (q : S → T) (s t : S) : fiberKernel q s t = fiberKernel q t s := by
  classical
  by_cases h : q t = q s
  · simp [fiberKernel, h]
  · simp [fiberKernel, h, Ne.symm h]

theorem fiberKernel_sum (q : S → T) (s : S) : ∑ t, fiberKernel q s t = 1 := by
  classical
  simp only [fiberKernel, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (fiberSize q (q s) : ℝ) * (fiberSize q (q s) : ℝ)⁻¹ = 1
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (fiberSize_pos q s).ne')

noncomputable def conditionMap (q : S → T) : (S → E) →ₗ[ℝ] (S → E) where
  toFun f s := ∑ t, fiberKernel q s t • f t
  map_add' f g := by
    ext s
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext s
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem conditionMap_apply (q : S → T) (f : S → E) (s : S) :
    conditionMap q f s = ∑ t, fiberKernel q s t • f t := rfl

theorem conditionMap_congr {R : Type*} (q : S → T) (r : S → R)
    (h : ∀ s t, q s = q t ↔ r s = r t) :
    (conditionMap q : (S → E) →ₗ[ℝ] (S → E)) = conditionMap r := by
  classical
  have hs : ∀ s, fiberSize q (q s) = fiberSize r (r s) := by
    intro s
    unfold fiberSize
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
  apply LinearMap.ext
  intro f
  funext s
  simp only [conditionMap_apply, fiberKernel, h, hs]

theorem conditionMap_eq_of_key_eq (q : S → T) (f : S → E) {s t : S}
    (h : q s = q t) : conditionMap q f s = conditionMap q f t := by
  classical
  change (∑ x, (if q x = q s then (fiberSize q (q s) : ℝ)⁻¹ else 0) • f x) =
    ∑ x, (if q x = q t then (fiberSize q (q t) : ℝ)⁻¹ else 0) • f x
  rw [h]

theorem conditionMap_of_invariant (q : S → T) (f : S → E)
    (hf : ∀ s t, q s = q t → f s = f t) (s : S) : conditionMap q f s = f s := by
  classical
  calc
    conditionMap q f s = ∑ t, fiberKernel q s t • f s := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : q t = q s
      · rw [hf t s ht]
      · simp [fiberKernel, ht]
    _ = f s := by rw [← Finset.sum_smul, fiberKernel_sum, one_smul]

noncomputable def condition (q : S → T) : (B.finite (S := S)).Projection where
  toLinearMap := conditionMap q
  idem f := funext (conditionMap_of_invariant q (conditionMap q f)
    (fun _ _ h => conditionMap_eq_of_key_eq q f h))
  selfAdjoint f g := by
    simp only [finite_form, conditionMap_apply, _root_.map_sum, _root_.map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [fiberKernel_symm]

@[simp] theorem condition_apply (q : S → T) (f : S → E) (s : S) :
    condition (B := B) q f s = conditionMap q f s := rfl

theorem condition_lift_commute (q : S → T) (P : B.Projection) (f : S → E) :
    condition (B := B) q (P.lift f) = P.lift (condition (B := B) q f) := by
  ext s
  simp only [condition_apply, conditionMap_apply, lift_apply, _root_.map_sum,
    _root_.map_smul]

theorem condition_nested {R : Type*} (q : S → T) (r : S → R)
    (h : ∀ s t, q s = q t → r s = r t) (f : S → E) :
    condition (B := B) q (condition (B := B) r f) = condition (B := B) r f := by
  ext s
  apply conditionMap_of_invariant
  intro s t he
  exact conditionMap_eq_of_key_eq r f (h s t he)

end Conditional
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_CoordinateProductInvariant
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Restriction.EnergyForm.Projection
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {I C T : Type*} [DecidableEq I]

variable [Fintype I] [Fintype C]

theorem conditionMap_coordinate (c0 : C) (i : I) (q : C → T)
    (f : (I → C) → E) (s : I → C) :
    conditionMap (coordinateKey c0 i q) f s =
      ∑ c, fiberKernel q (s i) c • f (Function.update s i c) := by
  classical
  have hi : Function.Injective (Function.update s i) := by
    intro a b h
    simpa only [Function.update_self] using congrFun h i
  have hc : fiberSize (coordinateKey c0 i q) (coordinateKey c0 i q s) =
      fiberSize q (q (s i)) := by
    have hf := congrArg Finset.card (coordinateKey_fiber c0 i q s)
    rw [Finset.card_image_of_injective _ hi] at hf
    unfold fiberSize
    convert hf using 2
    all_goals try with_reducible_and_instances rfl
    congr 1
  simp only [conditionMap_apply, fiberKernel, ite_smul, zero_smul,
    ← Finset.sum_filter, hc]
  rw [coordinateKey_fiber, Finset.sum_image]
  exact fun _ _ _ _ h => hi h

theorem conditionMap_coordinate_commute {R : Type*} (c0 : C)
    (i j : I) (hij : i ≠ j) (q : C → T) (r : C → R)
    (f : (I → C) → E) :
    conditionMap (coordinateKey c0 i q) (conditionMap (coordinateKey c0 j r) f) =
      conditionMap (coordinateKey c0 j r) (conditionMap (coordinateKey c0 i q) f) := by
  classical
  funext s
  simp only [conditionMap_coordinate, Finset.smul_sum, smul_smul,
    Function.update_of_ne hij, Function.update_of_ne hij.symm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij, mul_comm]

variable (B : EnergyForm E)

noncomputable def coordinateCondition (c0 : C) (i : I) (q : C → T) :
    (B.finite (S := I → C)).Projection := condition (coordinateKey c0 i q)

end VertexCover.Restriction.EnergyForm.Projection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_WeightEnergyBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList
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
open MeasureTheory

theorem weight_residual_abs_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s| ≤ 2 := by
  classical
  have hi : Integrable (fun x => Φ.separator A hA (Φ.continuousSum seed (Function.update s k x)))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) :=
    VertexCover.Cube.integrable_continuous
      ((Φ.separator_continuousSum_continuous A hA seed).comp
        (continuous_const.update k continuous_id))
  have he : Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s =
      ∫ x, (Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.continuousSum seed (Function.update s k x)))
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
    rw [integral_sub (integrable_const _) hi]
    simp [weightMean]
  rw [he]
  have hb : ∀ᵐ x ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)),
      ‖Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.continuousSum seed (Function.update s k x))‖ ≤ (2:ℝ) := by
    filter_upwards [VertexCover.Cube.ae_cube] with x hx
    have hu : Φ.InWeightCube (Function.update s k x) := by
      intro j c
      by_cases hj : j = k
      · subst j
        simpa using hx c
      · simpa only [Function.update_of_ne hj] using hs j c
    simpa only [Real.norm_eq_abs] using Φ.separator_weight_oscillation A hA seed s
      (Function.update s k x) hs hu k (fun j hj => (Function.update_of_ne hj _ _).symm)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

theorem weight_residual_integral_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) :
    (∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) ≤ 4 := by
  have hb : ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2 ≤ (4 : ℝ) := by
    filter_upwards [VertexCover.Cube.ae_block_cube] with s hs
    have hh := Φ.weight_residual_abs_le A hA k seed s hs
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hh
    rw [sq_abs] at hsq
    nlinarith
  have hi : Integrable (fun s =>
      (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2)
      (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    apply Integrable.of_bound
      (((Φ.separator_continuousSum_continuous A hA seed).measurable.sub
        (Φ.weightMean_measurable A hA k seed)).pow_const 2).aestronglyMeasurable 4
    filter_upwards [hb] with s hs
    simpa only [Real.norm_eq_abs, Pi.sub_apply, abs_pow, sq_abs] using hs
  simpa using integral_mono_ae hi (integrable_const (4 : ℝ)) hb

theorem weight_energy_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, VertexCover.finiteMean (fun seed : Φ.Seeds d =>
      ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
        ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) ≤ 4*d := by
  classical
  let : Nonempty (Φ.Seeds d) := ⟨fun _ => ⟨0, Φ.M_pos⟩⟩
  calc
    _ ≤ ∑ _k : Fin d, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => (4 : ℝ)) :=
          VertexCover.finiteMean_mono (Φ.weight_residual_integral_le A hA k)
        _ = 4 := VertexCover.finiteMean_const _
    _ = 4*d := by simp [mul_comm]

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_AverageCommute
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.Restriction.EnergyForm.Projection.condition_apply _root_.OAI.VertexCover.Restriction.EnergyForm.Projection.lift_apply _root_.OAI.VertexCover.Restriction.EnergyForm.finite_energy _root_.OAI.VertexCover.Restriction.EnergyForm.finite_form
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
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

namespace EnergyForm

section Integral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def integral : EnergyForm C(X, ℝ) where
  form :=
    { toFun := fun f =>
        { toFun := fun g => ∫ x, f x * g x ∂μ
          map_add' := fun g h => by
            simp only [ContinuousMap.add_apply, mul_add]
            exact integral_add (continuous_mul_integrable μ f g)
              (continuous_mul_integrable μ f h)
          map_smul' := fun a g => by
            simp only [ContinuousMap.smul_apply, smul_eq_mul]
            simp_rw [mul_left_comm (f _) a]
            exact integral_const_mul _ _ }
      map_add' := fun f g => by
        ext h
        simp only [LinearMap.add_apply, ContinuousMap.add_apply, add_mul]
        exact integral_add (continuous_mul_integrable μ f h)
          (continuous_mul_integrable μ g h)
      map_smul' := fun a f => by
        ext g
        simp only [LinearMap.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_assoc]
        exact integral_const_mul _ _ }
  symm f g := by
    change (∫ x, f x * g x ∂μ) = ∫ x, g x * f x ∂μ
    simp only [mul_comm]
  nonneg f := integral_nonneg (fun x => mul_self_nonneg (f x))

@[simp] theorem integral_form (f g : C(X, ℝ)) :
    (integral μ).form f g = ∫ x, f x * g x ∂μ := rfl

@[simp] theorem integral_energy (f : C(X, ℝ)) :
    (integral μ).energy f = ∫ x, (f x)^2 ∂μ := by
  simp only [energy, integral_form, pow_two]

end Integral

namespace Projection
section Averaging
variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype ι] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
@[simp] theorem updateFunction_apply (i : ι) (f : C(ι → X, ℝ)) (x : X) (s : ι → X) :
    updateFunction i f x s = f (Function.update s i x) := rfl

omit [Fintype ι] [SecondCountableTopology X] in
theorem updateFunction_integrable (i : ι) (f : C(ι → X, ℝ)) :
    Integrable (updateFunction i f) μ :=
  (updateFunction i f).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def averageMap (i : ι) : C(ι → X, ℝ) →ₗ[ℝ] C(ι → X, ℝ) where
  toFun f := ∫ x, updateFunction i f x ∂μ
  map_add' f g := by
    have he : (fun x => updateFunction i (f + g) x) =
        (fun x => updateFunction i f x + updateFunction i g x) := by
      funext x
      ext s
      rfl
    rw [he, integral_add (updateFunction_integrable μ i f)
      (updateFunction_integrable μ i g)]
  map_smul' a f := by
    have he : (fun x => updateFunction i (a • f) x) =
        (fun x => a • updateFunction i f x) := by
      funext x
      ext s
      rfl
    rw [he, integral_smul]
    rfl

omit [Fintype ι] [SecondCountableTopology X] in
@[simp] theorem averageMap_apply (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) :
    averageMap μ i f s = ∫ x, f (Function.update s i x) ∂μ :=
  ContinuousMap.integral_apply (updateFunction_integrable μ i f) s

omit [Fintype ι] [SecondCountableTopology X] in
theorem average_update (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) (x : X) :
    averageMap μ i f (Function.update s i x) = averageMap μ i f s := by
  simp only [averageMap_apply, Function.update_idem]

omit [Fintype ι] [SecondCountableTopology X] in
theorem average_idem (i : ι) (f : C(ι → X, ℝ)) :
    averageMap μ i (averageMap μ i f) = averageMap μ i f := by
  ext s
  simp only [averageMap_apply, Function.update_idem]
  simp

theorem integral_average_mul_fixed (i : ι) (f g : C(ι → X, ℝ))
    (hg : ∀ s x, g (Function.update s i x) = g s) :
    (∫ s, averageMap μ i f s * g s ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s * g s ∂Measure.pi (fun _ : ι => μ) := by
  have hi : Integrable (fun p : (ι → X) × X =>
      f (Function.update p.1 i p.2) * g (Function.update p.1 i p.2))
      ((Measure.pi (fun _ : ι => μ)).prod μ) :=
    ((f.continuous.comp (continuous_fst.update i continuous_snd)).mul
      (g.continuous.comp (continuous_fst.update i continuous_snd))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ s, ∫ x, f (Function.update s i x) * g (Function.update s i x)
        ∂μ ∂Measure.pi (fun _ : ι => μ) := by
      simp only [hg, integral_mul_const, averageMap_apply]
    _ = ∫ x, ∫ s, f (Function.update s i x) * g (Function.update s i x)
        ∂Measure.pi (fun _ : ι => μ) ∂μ := integral_integral_swap hi
    _ = _ := VertexCover.Product.integral_update μ i (continuous_mul_integrable _ f g)

noncomputable def average (i : ι) :
    (integral (Measure.pi (fun _ : ι => μ))).Projection where
  toLinearMap := averageMap μ i
  idem := average_idem μ i
  selfAdjoint f g := by
    change (∫ s, averageMap μ i f s * g s ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s * averageMap μ i g s ∂Measure.pi (fun _ : ι => μ)
    have h₁ := integral_average_mul_fixed μ i g (averageMap μ i f)
      (average_update μ i f)
    have h₂ := integral_average_mul_fixed μ i f (averageMap μ i g)
      (average_update μ i g)
    calc
      _ = ∫ s, g s * averageMap μ i f s ∂Measure.pi (fun _ : ι => μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => mul_comm _ _)
      _ = ∫ s, averageMap μ i g s * averageMap μ i f s
          ∂Measure.pi (fun _ : ι => μ) := h₁.symm
      _ = ∫ s, averageMap μ i f s * averageMap μ i g s
          ∂Measure.pi (fun _ : ι => μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => mul_comm _ _)
      _ = _ := h₂

@[simp] theorem average_apply (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) :
    average μ i f s = ∫ x, f (Function.update s i x) ∂μ := averageMap_apply μ i f s

theorem average_commute (i j : ι) (f : C(ι → X, ℝ)) :
    average μ i (average μ j f) = average μ j (average μ i f) := by
  by_cases hij : i = j
  · subst j
    rfl
  ext s
  simp only [average_apply]
  have hi : Integrable (fun p : X × X =>
      f (Function.update (Function.update s i p.1) j p.2)) (μ.prod μ) :=
    (f.continuous.comp ((continuous_const.update i continuous_fst).update j
      continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  simp only [Function.update_comm hij]

end Averaging
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_IntegralCoe
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

theorem continuous_plug_right {ι X : Type*} [DecidableEq ι] [TopologicalSpace X]
    (J : Finset ι) (s : ι → X) : Continuous (plug J s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ J
  · simpa only [plug, ite_eq_left hi] using continuous_apply i
  · simpa only [plug, ite_eq_right hi] using (continuous_const : Continuous (fun _ : ι → X => s i))

namespace EnergyForm.Projection
section Averaging
variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem product_average_apply (is : List ι) (his : is.Nodup)
    (f : C(ι → X, ℝ)) (s : ι → X) :
    productMap (average μ) is f s =
      ∫ t, f (plug is.toFinset s t) ∂Measure.pi (fun _ : ι => μ) := by
  induction is generalizing s with
  | nil => simp
  | cons i is ih =>
    rcases List.nodup_cons.mp his with ⟨hnot, hn⟩
    have hni : i ∉ is.toFinset := by simpa using hnot
    simp only [productMap_cons, average_apply]
    simp_rw [ih hn]
    simp only [List.toFinset_cons]
    simp_rw [plug_insert_update is.toFinset i hni]
    exact VertexCover.Product.integral_update μ i
      ((f.continuous.comp (continuous_plug_right (insert i is.toFinset) s)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

end Averaging
end EnergyForm.Projection

theorem continuous_splice_right {ι X : Type*} [DecidableEq ι] [TopologicalSpace X]
    (J : Finset ι) (s : ι → X) : Continuous (splice J s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ J
  · simpa only [splice, dite_eq_left hi] using continuous_apply (⟨i,hi⟩ : J)
  · simpa only [splice, dite_eq_right hi] using (continuous_const : Continuous (fun _ : J → X => s i))

theorem integral_plug_erase {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι) (j : J)
    (f : C(ι → X, ℝ)) (s : ι → X) :
    (∫ t, f (plug (J.erase j) s t) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ t, f (splice J s (Function.update t j (s j))) ∂Measure.pi (fun _ : J => μ) := by
  simp_rw [plug_erase_eq_splice_update J j s]
  apply integral_restrict μ J (g := fun t => f (splice J s (Function.update t j (s j))))
  exact (f.continuous.comp ((continuous_splice_right J s).comp
    (continuous_id.update j continuous_const))).measurable.aestronglyMeasurable

end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_RestrictionStarBudget
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.Restriction.EnergyForm.Projection
open scoped BigOperators

theorem conditionMap_apply_function {S T X : Type*} [Fintype S]
    [TopologicalSpace X] (q : S → T) (f : S → C(X, ℝ)) (s : S) (x : X) :
    conditionMap q f s x = VertexCover.Average.fiberAverage q
      (fun _ t => f t x) (q s) := by
  classical
  simp only [conditionMap_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fiberKernel, VertexCover.Average.fiberAverage, fiberSize]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rw [div_eq_mul_inv, mul_comm]

end VertexCover.Restriction.EnergyForm.Projection

namespace VertexCover.LabelCover
open MeasureTheory
open VertexCover.Restriction
open EnergyForm.Projection

abbrev RestrictionWeights (Φ : LabelCover) (d : ℕ) :=
  Fin d → Fin (Φ.WeightDimension d) → CompactCube.Interval

abbrev RestrictionSpace (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d → C(Φ.RestrictionWeights d, ℝ)

noncomputable def restrictionBase (Φ : LabelCover) (d : ℕ) :
    EnergyForm C(Φ.RestrictionWeights d, ℝ) :=
  EnergyForm.integral (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))

noncomputable def restrictionForm (Φ : LabelCover) (d : ℕ) :
    EnergyForm (Φ.RestrictionSpace d) := (Φ.restrictionBase d).finite

noncomputable def restrictionFunction (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : Φ.RestrictionSpace d :=
  fun seed => ⟨fun s => Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights s)),
    (Φ.separator_continuousSum_continuous A hA seed).comp CompactCube.continuous_realWeights⟩

@[simp] theorem restrictionFunction_apply (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.restrictionFunction A hA seed s =
      Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights s)) := rfl

@[simp] theorem restrictionForm_energy (Φ : LabelCover) {d : ℕ} (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy f = VertexCover.finiteMean (fun seed =>
      ∫ s, (f seed s)^2 ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  simp only [restrictionForm, EnergyForm.finite_energy, restrictionBase,
    EnergyForm.integral_energy, VertexCover.finiteMean, div_eq_mul_inv, mul_comm]

noncomputable def weightProjection (Φ : LabelCover) {d : ℕ} (k : Fin d) :
    (Φ.restrictionForm d).Projection :=
  (average (CompactCube.law (Fin (Φ.WeightDimension d))) k).lift

@[simp] theorem weightProjection_apply (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (f : Φ.RestrictionSpace d) (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.weightProjection k f seed s =
      ∫ x, f seed (Function.update s k x) ∂CompactCube.law (Fin (Φ.WeightDimension d)) :=
  average_apply _ k (f seed) s

theorem weightProjection_commute (Φ : LabelCover) {d : ℕ} (k l : Fin d)
    (f : Φ.RestrictionSpace d) :
    Φ.weightProjection k (Φ.weightProjection l f) =
      Φ.weightProjection l (Φ.weightProjection k f) := by
  funext seed
  exact average_commute _ k l (f seed)

theorem restriction_full_mean_zero (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    productMap (Φ.weightProjection (d := d)) (List.finRange d)
      (Φ.restrictionFunction A hA) = 0 := by
  ext seed s
  change productMap (fun i => (average (CompactCube.law (Fin (Φ.WeightDimension d))) i).lift)
    (List.finRange d) (Φ.restrictionFunction A hA) seed s = 0
  rw [productMap_lift, product_average_apply _ _ (List.nodup_finRange d)]
  simp only [List.toFinset_finRange, plug_univ, restrictionFunction_apply]
  change (∫ t, Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights t))
    ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) = 0
  rw [CompactCube.integral_realWeights
    (Φ.separator_continuousSum_continuous A hA seed).measurable.aestronglyMeasurable]
  exact Φ.separator_continuousSum_mean_zero A hA seed

noncomputable def weightGroup (Φ : LabelCover) {d : ℕ} (j : Fin d) :
    (Φ.restrictionForm d).Projection :=
  finDifference Φ.weightProjection Φ.weightProjection_commute j

theorem weightGroup_centered (Φ : LabelCover) {d : ℕ} (j : Fin d)
    (f : Φ.RestrictionSpace d) :
    (Φ.weightProjection j).residual (Φ.weightGroup j f) = Φ.weightGroup j f :=
  finDifference_centered _ _ _ _

theorem weightGroup_energy_sum (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, (Φ.restrictionForm d).energy
      (Φ.weightGroup j (Φ.restrictionFunction A hA))) =
      (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) := by
  have he := finDifference_energy_sum Φ.weightProjection Φ.weightProjection_commute
    (Φ.restrictionFunction A hA)
  rw [Φ.restriction_full_mean_zero A hA, EnergyForm.energy_zero, add_zero] at he
  exact he

noncomputable def seedProjection (Φ : LabelCover) {d : ℕ} (e : PositionPair d) :
    (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d)
    (fun seed : Φ.Seeds d => Function.update seed e ⟨0, Φ.M_pos⟩)

noncomputable def starProjection (Φ : LabelCover) {d : ℕ} (k : Fin d) :
    (Φ.restrictionForm d).Projection := condition (B := Φ.restrictionBase d) (Φ.starKey k)

noncomputable def oppositeProjection (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (e : PositionPair d) : (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d) (Φ.oppositePairKey k e)

theorem oppositeProjection_charge (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.oppositeProjection k e).residual f) ≤
      (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f) := by
  apply residual_le_of_nested
  apply condition_nested
  intro s t h
  have hh := congrArg (Φ.starFromOppositePair k e) h
  simpa only [Φ.starFromOppositePair_key k e he] using hh

theorem condition_weightProjection_commute (Φ : LabelCover) {d : ℕ} {T : Type*}
    (q : Φ.Seeds d → T) (k : Fin d) (f : Φ.RestrictionSpace d) :
    condition (B := Φ.restrictionBase d) q (Φ.weightProjection k f) =
      Φ.weightProjection k (condition (B := Φ.restrictionBase d) q f) :=
  condition_lift_commute q _ f

theorem weightProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.weightProjection k (Φ.restrictionFunction A hA) seed s =
      Φ.weightMean A hA k seed (CompactCube.realWeights s) := by
  simp only [weightProjection_apply, restrictionFunction_apply, CompactCube.realWeights_update]
  unfold weightMean
  apply CompactCube.integral_coe (f := fun x =>
    Φ.separator A hA (Φ.continuousSum seed (Function.update (CompactCube.realWeights s) k x)))
  exact ((Φ.separator_continuousSum_continuous A hA seed).comp
    (continuous_const.update k continuous_id)).measurable.aestronglyMeasurable

theorem seedProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.seedProjection e (Φ.restrictionFunction A hA) seed s =
      Φ.seedMean A hA e seed (CompactCube.realWeights s) := by
  change conditionMap _ (Φ.restrictionFunction A hA) seed s = _
  rw [conditionMap_apply_function]
  exact Φ.erasedSeed_separator_average A hA e seed (CompactCube.realWeights s)

theorem starProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.starProjection k (Φ.restrictionFunction A hA) seed s =
      Φ.starMean A hA k seed (CompactCube.realWeights s) := by
  change conditionMap _ (Φ.restrictionFunction A hA) seed s = _
  rw [conditionMap_apply_function]
  exact (Φ.starMean_eq_fiberAverage A hA k seed (CompactCube.realWeights s)).symm

theorem restriction_weight_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.weightProjection k).residual (Φ.restrictionFunction A hA))) ≤ 4*d := by
  have he : ∀ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.weightProjection k).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro k
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, weightProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).measurable.sub
        (Φ.weightMean_measurable A hA k seed)).pow_const 2).aestronglyMeasurable
  simp_rw [he]
  exact Φ.weight_energy_budget A hA

theorem restriction_seed_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA))) ≤ 8*(d:ℝ)^2 := by
  have he : ∀ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro e
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, seedProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).sub
        (Φ.seedMean_continuous A hA e seed)).pow 2).measurable.aestronglyMeasurable
  simp_rw [he]
  exact Φ.seed_energy_budget A hA

theorem restriction_star_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.starProjection k).residual (Φ.restrictionFunction A hA))) ≤ 4*d := by
  have he : ∀ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.starProjection k).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro k
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, starProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).sub
        (Φ.starMean_continuous A hA k seed)).pow 2).measurable.aestronglyMeasurable
  simp_rw [he]
  exact Φ.star_energy_budget A hA

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivatePairProjectionRight
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

noncomputable def privateLocalKey (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) (c : Fin Φ.M) :
    Option (Fin Φ.M) × Option (Fin Φ.u) × Option (Fin Φ.v) := by
  classical
  exact (if e ∈ internalPairs J then none else some c,
    if e ∈ internalPairs J ∧ e.1.1 = j then some (Φ.left c) else none,
    if e ∈ internalPairs J ∧ e.1.2 = j then some (Φ.right c) else none)

noncomputable def privateSeedKey (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (seed : Φ.Seeds d) :=
  fun e => Φ.privateLocalKey J j e (seed e)

noncomputable def privateSeedProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d) (Φ.privateSeedKey J j)

noncomputable def privatePairProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) :
    (Φ.restrictionForm d).Projection :=
  coordinateCondition (Φ.restrictionBase d) ⟨0, Φ.M_pos⟩ e (Φ.privateLocalKey J j e)

theorem privatePairProjection_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e b : PositionPair d) (f : Φ.RestrictionSpace d) :
    Φ.privatePairProjection J j e (Φ.privatePairProjection J j b f) =
      Φ.privatePairProjection J j b (Φ.privatePairProjection J j e f) := by
  by_cases heb : e = b
  · subst b; rfl
  · change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
      (conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ b (Φ.privateLocalKey J j b)) f) =
      conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ b (Φ.privateLocalKey J j b))
      (conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f)
    apply conditionMap_coordinate_commute
    exact heb

theorem privateSeedProjection_product (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j
      (productMap (Φ.privatePairProjection J j) Finset.univ.toList f) =
      productMap (Φ.privatePairProjection J j) Finset.univ.toList f := by
  classical
  let F := productMap (Φ.privatePairProjection J j) Finset.univ.toList f
  change Φ.privateSeedProjection J j F = F
  funext seed
  apply conditionMap_of_invariant
  intro s t hst
  apply invariant_of_coordinate_invariant (Φ.privateLocalKey J j) F _ s t
    (fun e => congrFun hst e)
  intro e a c hc
  have he := productMap_fixed_of_mem (Φ.privatePairProjection J j)
    (Φ.privatePairProjection_commute J j) Finset.univ.toList e (by simp) f
  change Φ.privatePairProjection J j e F = F at he
  rw [← he]
  apply conditionMap_eq_of_key_eq
  simp only [coordinateKey, Function.update_idem, Function.update_self, hc]

theorem query_eq_questions_iff (Φ : LabelCover) {d : ℕ} (s t : Φ.Seeds d) (j : Fin d) :
    Φ.query s j = Φ.query t j ↔
      (∀ k (h : j < k), Φ.left (s ⟨(j,k),h⟩) = Φ.left (t ⟨(j,k),h⟩)) ∧
      (∀ k (h : k < j), Φ.right (s ⟨(k,j),h⟩) = Φ.right (t ⟨(k,j),h⟩)) := by
  constructor
  · intro h
    have hp := eq_of_heq (Sigma.mk.inj h).2
    exact ⟨fun k hk => congrFun (congrArg Prod.fst hp) ⟨k,hk⟩,
      fun k hk => congrFun (congrArg Prod.snd hp) ⟨k,hk⟩⟩
  · rintro ⟨hL,hR⟩
    exact Φ.query_eq_of_questions s t j hL hR

theorem privateSeedKey_eq_iff (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (s t : Φ.Seeds d) :
    Φ.privateSeedKey J j s = Φ.privateSeedKey J j t ↔
      (∀ e, e ∉ internalPairs J → s e = t e) ∧ Φ.query s j = Φ.query t j := by
  classical
  constructor
  · intro h
    have hs : ∀ e, e ∉ internalPairs J → s e = t e := by
      intro e he
      have hh := congrArg Prod.fst (congrFun h e)
      simpa only [privateSeedKey, privateLocalKey, ite_eq_right he, Option.some.injEq] using hh
    refine ⟨hs, (Φ.query_eq_questions_iff s t j).mpr ⟨?_, ?_⟩⟩
    · intro k hkj
      let e : PositionPair d := ⟨(j,k),hkj⟩
      by_cases he : e ∈ internalPairs J
      · have hh := congrArg (fun x => x.2.1) (congrFun h e)
        simpa [privateSeedKey, privateLocalKey, he, e] using hh
      · exact congrArg Φ.left (hs e he)
    · intro k hkj
      let e : PositionPair d := ⟨(k,j),hkj⟩
      by_cases he : e ∈ internalPairs J
      · have hh := congrArg (fun x => x.2.2) (congrFun h e)
        simpa [privateSeedKey, privateLocalKey, he, e] using hh
      · exact congrArg Φ.right (hs e he)
  · rintro ⟨hs,hq⟩
    obtain ⟨hL,hR⟩ := (Φ.query_eq_questions_iff s t j).mp hq
    funext e
    by_cases he : e ∈ internalPairs J
    · by_cases hlj : e.1.1 = j
      · have hrj : e.1.2 ≠ j := by have := e.2; rw [hlj] at this; exact ne_of_gt this
        have ht := hL e.1.2 (hlj ▸ e.2)
        have hp : (⟨(j,e.1.2), hlj ▸ e.2⟩ : PositionPair d) = e := by
          apply Subtype.ext; simp only [← hlj, Prod.mk.eta]
        rw [hp] at ht
        simp [privateSeedKey, privateLocalKey, he, hlj, hrj, ht]
      · by_cases hrj : e.1.2 = j
        · have ht := hR e.1.1 (hrj ▸ e.2)
          have hp : (⟨(e.1.1,j), hrj ▸ e.2⟩ : PositionPair d) = e := by
            apply Subtype.ext; simp only [← hrj, Prod.mk.eta]
          rw [hp] at ht
          simp [privateSeedKey, privateLocalKey, he, hlj, hrj, ht]
        · simp [privateSeedKey, privateLocalKey, he, hlj, hrj]
    · simp [privateSeedKey, privateLocalKey, he, hs e he]

theorem privatePairProjection_outside (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) (he : e ∉ internalPairs J) :
    Φ.privatePairProjection J j e = ident := by
  classical
  apply EnergyForm.Projection.ext
  intro f
  funext seed
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f seed = f seed
  apply conditionMap_of_invariant
  intro s t hst
  obtain ⟨ho,hq⟩ := (coordinateKey_eq_iff ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e) s t).mp hst
  have heq : s e = t e := by
    have hh := congrArg Prod.fst hq
    simpa [privateLocalKey, he] using hh
  have hst' : s = t := by
    funext b
    by_cases hb : b = e
    · subst b; exact heq
    · exact ho b hb
  rw [hst']

theorem privatePairProjection_nonincident (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hL : e.1.1 ≠ j) (hR : e.1.2 ≠ j) :
    Φ.privatePairProjection J j e = Φ.seedProjection e := by
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (fun seed : Φ.Seeds d => Function.update seed e ⟨0,Φ.M_pos⟩) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (fun seed : Φ.Seeds d => Function.update seed e ⟨0,Φ.M_pos⟩) (fun s t => by
    simp [coordinateKey, privateLocalKey, he, hL, hR]))

theorem privatePairProjection_left (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hL : e.1.1 = j) :
    Φ.privatePairProjection J j e = Φ.oppositeProjection e.1.2 e := by
  classical
  have hR : e.1.2 ≠ j := by rw [← hL]; exact ne_of_gt e.2
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (Φ.oppositePairKey e.1.2 e) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (Φ.oppositePairKey e.1.2 e) (fun s t => by
    simp only [coordinateKey, privateLocalKey, oppositePairKey, he, hL,
      and_self, ite_true, hR, and_false, ite_false, Prod.mk.injEq,
      Option.some.injEq, true_and, and_true, ite_eq_right (Ne.symm hR)]
    constructor
    · rintro ⟨ho,hq⟩
      exact Prod.ext ho (congrArg Sum.inl hq)
    · intro h
      exact ⟨congrArg Prod.fst h, Sum.inl.inj (congrArg Prod.snd h)⟩))

theorem privatePairProjection_right (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hR : e.1.2 = j) :
    Φ.privatePairProjection J j e = Φ.oppositeProjection e.1.1 e := by
  classical
  have hL : e.1.1 ≠ j := by rw [← hR]; exact ne_of_lt e.2
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (Φ.oppositePairKey e.1.1 e) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (Φ.oppositePairKey e.1.1 e) (fun s t => by
    simp only [coordinateKey, privateLocalKey, oppositePairKey, he, hL, hR,
      and_false, and_self, ite_false, ite_true, Prod.mk.injEq, Option.some.injEq,
      true_and]
    constructor
    · rintro ⟨ho,hq⟩
      exact Prod.ext ho (congrArg Sum.inr hq)
    · intro h
      exact ⟨congrArg Prod.fst h, Sum.inr.inj (congrArg Prod.snd h)⟩))

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateProjectionGroupLower
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

noncomputable def otherWeightProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  product Φ.weightProjection Φ.weightProjection_commute (J.erase j).toList

theorem privateSeed_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateSeedProjection J j f) :=
  Φ.condition_weightProjection_commute (Φ.privateSeedKey J j) k f

theorem privateSeed_otherWeight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j (Φ.otherWeightProjection J j f) =
      Φ.otherWeightProjection J j (Φ.privateSeedProjection J j f) :=
  (productMap_commute Φ.weightProjection (Φ.privateSeedProjection J j)
    (fun k x => (Φ.privateSeed_weight_commute J j k x).symm) (J.erase j).toList f).symm

noncomputable def privateAverageProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  (Φ.privateSeedProjection J j).comp (Φ.otherWeightProjection J j)
    (Φ.privateSeed_otherWeight_commute J j)

theorem privateAverage_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateAverageProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateAverageProjection J j f) := by
  change Φ.privateSeedProjection J j
      (productMap Φ.weightProjection (J.erase j).toList (Φ.weightProjection k f)) = _
  rw [productMap_commute Φ.weightProjection (Φ.weightProjection k)
    (fun l => Φ.weightProjection_commute l k), Φ.privateSeed_weight_commute]
  rfl

noncomputable def privateProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  (Φ.weightProjection j).residual.comp (Φ.privateAverageProjection J j)
    (residual_commute _ _ (fun f => (Φ.privateAverage_weight_commute J j j f).symm))

theorem privateProjection_weight_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j k : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateProjection J j (Φ.weightProjection k f) =
      Φ.weightProjection k (Φ.privateProjection J j f) := by
  change (Φ.weightProjection j).residual
    (Φ.privateAverageProjection J j (Φ.weightProjection k f)) = _
  rw [Φ.privateAverage_weight_commute, residual_commute _ _ (Φ.weightProjection_commute j k)]
  rfl

theorem privateProjection_group_le (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.privateProjection J j (Φ.weightGroup j f)) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) :=
  finDifference_retained_le Φ.weightProjection Φ.weightProjection_commute
    (Φ.privateProjection J j) (fun k x => (Φ.privateProjection_weight_commute J j k x).symm) j f

theorem privateProjection_group_eq (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateProjection J j (Φ.weightGroup j f) =
      Φ.privateAverageProjection J j (Φ.weightGroup j f) := by
  change (Φ.weightProjection j).residual
    (Φ.privateAverageProjection J j (Φ.weightGroup j f)) = _
  rw [residual_commute _ _ (fun x => (Φ.privateAverage_weight_commute J j j x).symm),
    Φ.weightGroup_centered]

theorem privateAverage_loss_le (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.privateAverageProjection J j).residual f) ≤
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy ((Φ.weightProjection k).residual f)) +
      ∑ e : PositionPair d, (Φ.restrictionForm d).energy ((Φ.privatePairProjection J j e).residual f) := by
  have hc := comp_loss_le (Φ.privateSeedProjection J j) (Φ.otherWeightProjection J j)
    (Φ.privateSeed_otherWeight_commute J j) f
  have hw := product_loss_finset Φ.weightProjection Φ.weightProjection_commute (J.erase j) f
  have hs := residual_le_of_nested (Φ.privateSeedProjection J j)
    (product (Φ.privatePairProjection J j) (Φ.privatePairProjection_commute J j) Finset.univ.toList)
    (Φ.privateSeedProjection_product J j) f
  have hsp := product_loss_finset (Φ.privatePairProjection J j)
    (Φ.privatePairProjection_commute J j) Finset.univ f
  change (Φ.restrictionForm d).energy ((Φ.privateAverageProjection J j).residual f) ≤ _ at hc
  change (Φ.restrictionForm d).energy ((Φ.otherWeightProjection J j).residual f) ≤ _ at hw
  linarith

theorem privateProjection_group_lower (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.weightGroup j f) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) +
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy
        ((Φ.weightProjection k).residual (Φ.weightGroup j f))) +
      ∑ e : PositionPair d, (Φ.restrictionForm d).energy
        ((Φ.privatePairProjection J j e).residual (Φ.weightGroup j f)) := by
  have he := (Φ.privateAverageProjection J j).pythagoras (Φ.weightGroup j f)
  have hl := Φ.privateAverage_loss_le J j (Φ.weightGroup j f)
  have hr := Φ.privateProjection_group_le J j f
  rw [Φ.privateProjection_group_eq] at hr
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateProjectionSurvival
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
section
namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

def otherEndpoint {d : ℕ} (j : Fin d) (e : PositionPair d) : Fin d :=
  if e.1.1 = j then e.1.2 else e.1.1

theorem otherEndpoint_ne {d : ℕ} (j : Fin d) (e : PositionPair d) :
    otherEndpoint j e ≠ j := by
  unfold otherEndpoint
  split_ifs with h
  · rw [← h]; exact ne_of_gt e.2
  · exact h

theorem otherEndpoint_injective {d : ℕ} (j : Fin d) (e b : PositionPair d)
    (he : e.1.1 = j ∨ e.1.2 = j) (hb : b.1.1 = j ∨ b.1.2 = j)
    (h : otherEndpoint j e = otherEndpoint j b) : e = b := by
  rcases he with he | he <;> rcases hb with hb | hb
  · simp only [otherEndpoint, ite_eq_left he, ite_eq_left hb] at h
    exact Subtype.ext (Prod.ext (he.trans hb.symm) h)
  · have hbl : b.1.1 ≠ j := by rw [← hb]; exact ne_of_lt b.2
    simp only [otherEndpoint, ite_eq_left he, ite_eq_right hbl] at h
    have := e.2; have := b.2
    omega
  · have hel : e.1.1 ≠ j := by rw [← he]; exact ne_of_lt e.2
    simp only [otherEndpoint, ite_eq_right hel, ite_eq_left hb] at h
    have := e.2; have := b.2
    omega
  · have hel : e.1.1 ≠ j := by rw [← he]; exact ne_of_lt e.2
    have hbl : b.1.1 ≠ j := by rw [← hb]; exact ne_of_lt b.2
    simp only [otherEndpoint, ite_eq_right hel, ite_eq_right hbl] at h
    exact Subtype.ext (Prod.ext h (he.trans hb.symm))

theorem incident_sum_le {d : ℕ} (J : Finset (Fin d)) (j : Fin d)
    (g : Fin d → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∑ e ∈ (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j),
      g (otherEndpoint j e)) ≤ ∑ k ∈ J.erase j, g k := by
  classical
  let T := (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j)
  have hi : Set.InjOn (otherEndpoint j) ↑T := by
    intro e he b hb h
    exact otherEndpoint_injective j e b (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hb).2 h
  have hs : T.image (otherEndpoint j) ⊆ J.erase j := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨heJ, _hei⟩ := Finset.mem_filter.mp he
    have hep : e.1.1 ∈ J ∧ e.1.2 ∈ J := (Finset.mem_filter.mp heJ).2
    refine Finset.mem_erase.mpr ⟨otherEndpoint_ne j e, ?_⟩
    unfold otherEndpoint
    split_ifs <;> tauto
  calc
    _ = ∑ k ∈ T.image (otherEndpoint j), g k := (Finset.sum_image hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => hg k)

theorem privatePair_incident_charge (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hi : e.1.1 = j ∨ e.1.2 = j)
    (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.privatePairProjection J j e).residual f) ≤
      (Φ.restrictionForm d).energy ((Φ.starProjection (otherEndpoint j e)).residual f) := by
  rcases hi with hi | hi
  · rw [Φ.privatePairProjection_left J j e he hi]
    simp only [otherEndpoint, ite_eq_left hi]
    exact Φ.oppositeProjection_charge e.1.2 e (Or.inr rfl) f
  · have hL : e.1.1 ≠ j := by rw [← hi]; exact ne_of_lt e.2
    rw [Φ.privatePairProjection_right J j e he hi]
    simp only [otherEndpoint, ite_eq_right hL]
    exact Φ.oppositeProjection_charge e.1.1 e (Or.inl rfl) f

theorem privatePair_loss_sum (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (∑ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.privatePairProjection J j e).residual f)) ≤
      (∑ k ∈ J.erase j, (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f)) +
      ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)),
        (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual f) := by
  classical
  let l := fun e : PositionPair d => (Φ.restrictionForm d).energy
    ((Φ.privatePairProjection J j e).residual f)
  have hz : (∑ e, l e) = ∑ e ∈ internalPairs J, l e := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp only [l, Φ.privatePairProjection_outside J j e he, residual_apply, ident_apply,
      sub_self, EnergyForm.energy_zero]
  change (∑ e, l e) ≤ _
  rw [hz, ← Finset.sum_filter_add_sum_filter_not (internalPairs J)
    (fun e => e.1.1 = j ∨ e.1.2 = j) l]
  apply add_le_add
  · calc
      _ ≤ ∑ e ∈ (internalPairs J).filter (fun e => e.1.1 = j ∨ e.1.2 = j),
          (Φ.restrictionForm d).energy ((Φ.starProjection (otherEndpoint j e)).residual f) := by
        apply Finset.sum_le_sum
        intro e he
        exact Φ.privatePair_incident_charge J j e (Finset.mem_filter.mp he).1
          (Finset.mem_filter.mp he).2 f
      _ ≤ _ := incident_sum_le J j
        (fun k => (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f))
        (fun _ => (Φ.restrictionForm d).energy_nonneg _)
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨heJ, hei⟩ := Finset.mem_filter.mp he
    obtain ⟨hL,hR⟩ := not_or.mp hei
    dsimp [l]
    rw [Φ.privatePairProjection_nonincident J j e heJ hL hR]

theorem privateProjection_survival (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy (Φ.weightGroup j f) ≤
      (Φ.restrictionForm d).energy (Φ.privateProjection J j f) +
      (∑ k ∈ J.erase j, ((Φ.restrictionForm d).energy
        ((Φ.weightProjection k).residual (Φ.weightGroup j f)) +
        (Φ.restrictionForm d).energy ((Φ.starProjection k).residual (Φ.weightGroup j f)))) +
      ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)),
        (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual (Φ.weightGroup j f)) := by
  have h := Φ.privateProjection_group_lower J j f
  have hs := Φ.privatePair_loss_sum J j (Φ.weightGroup j f)
  rw [Finset.sum_add_distrib]
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_RestrictionSum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem weightGroup_residual_budget (Φ : LabelCover) {d : ℕ}
    (Q : (Φ.restrictionForm d).Projection)
    (hQ : ∀ k f, Φ.weightProjection k (Q f) = Q (Φ.weightProjection k f))
    (f : Φ.RestrictionSpace d) :
    (∑ j : Fin d, (Φ.restrictionForm d).energy (Q.residual (Φ.weightGroup j f))) ≤
      (Φ.restrictionForm d).energy (Q.residual f) :=
  finDifference_residual_budget _ Φ.weightProjection_commute Q hQ f

theorem weightGroup_pair_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, ∑ k : Fin d,
      ((Φ.restrictionForm d).energy ((Φ.weightProjection k).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA))) +
       (Φ.restrictionForm d).energy ((Φ.starProjection k).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA))))) ≤ 8*d := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ k : Fin d,
        ((Φ.restrictionForm d).energy ((Φ.weightProjection k).residual
          (Φ.restrictionFunction A hA)) +
         (Φ.restrictionForm d).energy ((Φ.starProjection k).residual
          (Φ.restrictionFunction A hA))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_add_distrib]
      apply add_le_add
      · exact Φ.weightGroup_residual_budget (Φ.weightProjection k)
          (fun i f => Φ.weightProjection_commute i k f) _
      · exact Φ.weightGroup_residual_budget (Φ.starProjection k)
          (fun i f => (Φ.condition_weightProjection_commute (Φ.starKey k) i f).symm) _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      have hw := Φ.restriction_weight_budget A hA
      have hs := Φ.restriction_star_budget A hA
      linarith

theorem weightGroup_seed_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, ∑ e : PositionPair d,
      (Φ.restrictionForm d).energy ((Φ.seedProjection e).residual
        (Φ.weightGroup j (Φ.restrictionFunction A hA)))) ≤ 8*(d:ℝ)^2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ e : PositionPair d, (Φ.restrictionForm d).energy
        ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA)) := by
      apply Finset.sum_le_sum
      intro e _
      exact Φ.weightGroup_residual_budget (Φ.seedProjection e)
        (fun i f => (Φ.condition_weightProjection_commute
          (fun seed : Φ.Seeds d => Function.update seed e ⟨0, Φ.M_pos⟩) i f).symm) _
    _ ≤ _ := Φ.restriction_seed_budget A hA

theorem privateProjection_batch_bound (Φ : LabelCover) {d h : ℕ} (hh : 3 ≤ h)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    ((d-1).choose (h-1) : ℝ) * (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) ≤
      (∑ J ∈ batches d h, ∑ j ∈ J, (Φ.restrictionForm d).energy
        (Φ.privateProjection J j (Φ.restrictionFunction A hA))) +
      ((d-2).choose (h-2) : ℝ)*(8*d) + ((d-3).choose (h-3) : ℝ)*(8*(d:ℝ)^2) := by
  classical
  let B := Φ.restrictionForm d
  let f := Φ.restrictionFunction A hA
  let pairLoss := fun j k : Fin d => B.energy ((Φ.weightProjection k).residual (Φ.weightGroup j f)) +
    B.energy ((Φ.starProjection k).residual (Φ.weightGroup j f))
  let seedLoss := fun (j : Fin d) (e : PositionPair d) =>
    B.energy ((Φ.seedProjection e).residual (Φ.weightGroup j f))
  have hsurv : (∑ J ∈ batches d h, ∑ j ∈ J, B.energy (Φ.weightGroup j f)) ≤
      (∑ J ∈ batches d h, ∑ j ∈ J, B.energy (Φ.privateProjection J j f)) +
      (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, pairLoss j k) +
      (∑ J ∈ batches d h, ∑ j ∈ J,
        ∑ e ∈ (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)), seedLoss j e) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro J _
    apply Finset.sum_le_sum
    intro j _
    exact Φ.privateProjection_survival J j f
  have hpair := batches_pair_sum_le (by omega : 2 ≤ h) pairLoss
    (fun j k => add_nonneg (B.energy_nonneg _) (B.energy_nonneg _))
  have htriple := batches_triple_sum_le hh
    (fun e : PositionPair d => e.1.1) (fun e : PositionPair d => e.1.2)
    (fun e => ne_of_lt e.2) seedLoss (fun _ _ => B.energy_nonneg _)
  have hsets (J : Finset (Fin d)) (j : Fin d) :
      (internalPairs J).filter (fun e => ¬ (e.1.1 = j ∨ e.1.2 = j)) =
        Finset.univ.filter (fun e : PositionPair d =>
          e.1.1 ∈ J ∧ e.1.2 ∈ J ∧ ¬ (e.1.1 = j ∨ e.1.2 = j)) := by
    ext e
    simp only [internalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [hsets] at hsurv
  rw [batches_singleton_sum (by omega : 1 ≤ h), Φ.weightGroup_energy_sum A hA] at hsurv
  have hpb : (∑ j, ∑ k, pairLoss j k) ≤ 8*d := Φ.weightGroup_pair_budget A hA
  have hsb : (∑ j, ∑ e, seedLoss j e) ≤ 8*(d:ℝ)^2 := Φ.weightGroup_seed_budget A hA
  have hpb' := mul_le_mul_of_nonneg_left hpb (Nat.cast_nonneg ((d-2).choose (h-2)) : (0:ℝ) ≤ _)
  have hsb' := mul_le_mul_of_nonneg_left hsb (Nat.cast_nonneg ((d-3).choose (h-3)) : (0:ℝ) ≤ _)
  dsimp only [B, f] at hsurv
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeparatorBoundCube
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open MeasureTheory ProbabilityTheory

theorem continuousSum_splice (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    Φ.continuousSum (Φ.spliceSeeds J frozen hidden) (Φ.spliceWeights J weights s) =
      Φ.outsideSum J frozen weights + Φ.batchSum (Φ.spliceSeeds J frozen hidden) J s := by
  classical
  unfold continuousSum outsideSum batchSum
  rw [← Finset.sum_add_sum_compl J]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hnj : j ∉ J := Finset.mem_compl.mp hj
    simp only [spliceWeights, dite_eq_right hnj, Φ.query_splice_outside J frozen hidden j hnj]
  · rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    simp only [spliceWeights, dite_eq_left j.2]

theorem batchFunction_is_restriction (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J (Φ.outsideSum J frozen weights) A hA s =
      Φ.separator A hA (Φ.continuousSum (Φ.spliceSeeds J frozen hidden)
        (Φ.spliceWeights J weights s)) := by
  rw [Φ.continuousSum_splice]
  rfl

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Composition
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
open Turing
open Turing.TM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Compose

variable (A B : FinTM2)

variable (outA : A.Γ A.k₁ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)

open UniqueGames.Foundations.Complexity.MachineComposition

def outputs (input : List (A.Γ A.k₀)) (middle : List Bool) (output : List (B.Γ B.k₁))
    (n₁ n₂ : ℕ)
    (h₁ : Turing.TM2OutputsInTime A input (some (middle.map outA.symm)) n₁)
    (h₂ : Turing.TM2OutputsInTime B (middle.map inB.symm) (some output) n₂) :
    Turing.TM2OutputsInTime (machine A B outA inB) input (some output)
      (n₁ + 2 * (middle.length + 1) + n₂) := by
  have e₁ := liftExecutionInTime A.step (machine A B outA inB).step
    (firstCfg A B B.initialState none (fun _ => []) [])
    (first_step A B outA inB B.initialState none (fun _ => []) []) h₁
  rw [first_initial, first_halted] at e₁
  have e₂ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeOne A B (middle.map outA.symm) [] none)
      (some (bridgeTwo A B middle.reverse [] none)) (middle.length+1) := by
    simpa only [List.map_map, Equiv.apply_symm_apply, Function.comp_def,
      List.map_id_fun, List.map_id, List.map_id', List.append_nil, List.length_map] using
      bridgeOne_run A B outA inB (middle.map outA.symm) [] none
  have e₃ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeTwo A B middle.reverse [] none)
      (some (secondCfg A B A.initialState none (fun _ => []) []
        (initList B (middle.map inB.symm)))) (middle.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      bridgeTwo_run A B outA inB middle.reverse [] none
  have e₄ := liftExecutionInTime B.step (machine A B outA inB).step
    (secondCfg A B A.initialState none (fun _ => []) [])
    (second_step A B outA inB A.initialState none (fun _ => []) []) h₂
  rw [second_halted] at e₄
  have e₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
  have e₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁₂ e₃
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁₂₃ e₄
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

end Compose

open UniqueGames.Foundations.Complexity

noncomputable def compose {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ}
    (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g) :
    Turing.TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm := Compose.machine c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet
  inputAlphabet := c₁.inputAlphabet
  outputAlphabet := c₂.outputAlphabet
  time := MachineComposition.compositionPolynomial c₁.time c₂.time
    (Polynomial.X + Polynomial.C (Runtime.programPushBound c₁.tm)*c₁.time)
  outputsFun a := by
    have run := Compose.outputs c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet
      ((eα a).map c₁.inputAlphabet.symm) (eβ (f a)) ((eγ (g (f a))).map c₂.outputAlphabet.symm)
      (c₁.time.eval (eα a).length) (c₂.time.eval (eβ (f a)).length)
      (c₁.outputsFun a) (c₂.outputsFun (f a))
    refine { run with steps_le_m := ?_ }
    exact run.steps_le_m.trans
      (MachineComposition.compositionBudget_le _ _ _ _ _ (Runtime.encodedOutputLength c₁ a))

theorem compose_finite {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ}
    (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g)
    (h₁ : ∀ k, Finite (c₁.tm.Γ k)) (h₂ : ∀ k, Finite (c₂.tm.Γ k)) :
    ∀ k, Finite ((compose c₁ c₂).tm.Γ k) :=
  Compose.finiteAlphabet c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet h₁ h₂

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Pair
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
open Turing Turing.TM2
open UniqueGames.Foundations.Complexity.MachineComposition (liftExecutionInTime)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Pair
open Compose (K Γ State tapes first second temporary tapes_first tapes_second
  tapes_temporary tapes_update_first tapes_update_second tapes_update_temporary
  tapeOnly init_tapes halt_tapes tapeOnly_self tapeOnly_nil tapeOnly_update)
variable (A B : FinTM2)

variable (inA : A.Γ A.k₀ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)
  (outA : A.Γ A.k₁ ≃ Bool) (outB : B.Γ B.k₁ ≃ Bool)

def outputs (input left right : List Bool) (n₁ n₂ : ℕ)
    (h₁ : TM2OutputsInTime A (input.map inA.symm) (some (left.map outA.symm)) n₁)
    (h₂ : TM2OutputsInTime B (input.map inB.symm) (some (right.map outB.symm)) n₂) :
    TM2OutputsInTime (machine A B inA inB outA outB) (input.map inA.symm)
      (some ((pairBits left right).map outB.symm))
      (2*(input.length+1) + n₁ + n₂ + 2*(left.length+1)) := by
  have e₀ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (initList (machine A B inA inB outA outB) (input.map inA.symm))
      (some (cfg1 A B [] [] input.reverse none)) (input.length+1) := by
    have e := cfg0_run A B inA inB outA outB (input.map inA.symm) [] none
    rw [initial_eq] at e
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using e
  have e₁ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg1 A B [] [] input.reverse none)
      (some (firstCfg A B B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) []
        (initList A (input.map inA.symm)))) (input.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg1_run A B inA inB outA outB input.reverse [] [] none
  have e₂ := liftExecutionInTime A.step (machine A B inA inB outA outB).step
    (firstCfg A B B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) [])
    (first_step A B inA inB outA outB B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) []) h₁
  rw [first_halted] at e₂
  have e₃ := liftExecutionInTime B.step (machine A B inA inB outA outB).step
    (secondCfg A B A.initialState none (tapeOnly A.k₁ (left.map outA.symm)) [])
    (second_step A B inA inB outA outB A.initialState none (tapeOnly A.k₁ (left.map outA.symm)) []) h₂
  rw [second_halted] at e₃
  have e₄ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg2 A B (left.map outA.symm) (right.map outB.symm) [] none)
      (some (cfg3 A B (outB.symm false::right.map outB.symm) left.reverse none))
      (left.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg2_run A B inA inB outA outB (left.map outA.symm) (right.map outB.symm) [] none
  have e₅ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg3 A B (outB.symm false::right.map outB.symm) left.reverse none)
      (some (haltList (machine A B inA inB outA outB) ((pairBits left right).map outB.symm)))
      (left.length+1) := by
    have e := cfg3_run A B inA inB outA outB left.reverse (outB.symm false::right.map outB.symm) none
    have hword : left.flatMap (fun b => [outB.symm true, outB.symm b]) ++
        outB.symm false::right.map outB.symm = (pairBits left right).map outB.symm := by
      rw [← frame_eq, List.map_append, List.map_flatMap]
      rfl
    simpa only [List.reverse_reverse, hword, List.length_reverse] using e
  have e₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁
  have e₀₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₁ e₂
  have e₀₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₂ e₃
  have e₀₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₃ e₄
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₄ e₅
  exact { all with steps_le_m := by have h := all.steps_le_m; omega }

end Pair
open UniqueGames.Foundations.Complexity

noncomputable def pair {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ}
    (c₁ : TM2ComputableInPolyTime eα eβ f) (c₂ : TM2ComputableInPolyTime eα eγ g) :
    TM2ComputableInPolyTime eα (fun p : β × γ => pairBits (eβ p.1) (eγ p.2))
      (fun a => (f a,g a)) where
  tm := Pair.machine c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
    c₁.outputAlphabet c₂.outputAlphabet
  inputAlphabet := c₁.inputAlphabet
  outputAlphabet := c₂.outputAlphabet
  time := Polynomial.C 2 * (Polynomial.X + 1) + c₁.time + c₂.time +
    Polynomial.C 2 * (Polynomial.X + Polynomial.C (Runtime.programPushBound c₁.tm) * c₁.time + 1)
  outputsFun a := by
    have run := Pair.outputs c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
      c₁.outputAlphabet c₂.outputAlphabet (eα a) (eβ (f a)) (eγ (g a))
      (c₁.time.eval (eα a).length) (c₂.time.eval (eα a).length)
      (c₁.outputsFun a) (c₂.outputsFun a)
    refine { run with steps_le_m := ?_ }
    apply run.steps_le_m.trans
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    have bound := Runtime.encodedOutputLength c₁ a
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at bound
    omega

theorem pair_finite {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ}
    (c₁ : TM2ComputableInPolyTime eα eβ f) (c₂ : TM2ComputableInPolyTime eα eγ g)
    (h₁ : ∀ k, Finite (c₁.tm.Γ k)) (h₂ : ∀ k, Finite (c₂.tm.Γ k)) :
    ∀ k, Finite ((pair c₁ c₂).tm.Γ k) :=
  Pair.finiteAlphabet c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
    c₁.outputAlphabet c₂.outputAlphabet h₁ h₂

noncomputable def Poly.comp {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ} (c₁ : Poly eα eβ f) (c₂ : Poly eβ eγ g) :
    Poly eα eγ (g ∘ f) :=
  ⟨compose c₁.computation c₂.computation,
    compose_finite c₁.computation c₂.computation c₁.finiteAlphabet c₂.finiteAlphabet⟩

noncomputable def Poly.pair {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ} (c₁ : Poly eα eβ f) (c₂ : Poly eα eγ g) :
    Poly eα (fun p : β × γ => pairBits (eβ p.1) (eγ p.2)) (fun a => (f a,g a)) :=
  ⟨VertexCover.Machine.pair c₁.computation c₂.computation,
    pair_finite c₁.computation c₂.computation c₁.finiteAlphabet c₂.finiteAlphabet⟩

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Primitives
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory
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
open Turing

noncomputable def Poly.tail : Poly id id List.tail := by
  let δ : Bool → Bool → Bool × List Bool := fun first x => (false, if first then [] else [x])
  have rest (s : List Bool) : Stream.output δ (fun _ => []) false s = s := by
    induction s with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, ih]
  have first (s : List Bool) : Stream.output δ (fun _ => []) true s = s.tail := by
    cases s with
    | nil => rfl
    | cons x xs => simp [Stream.output, δ, rest]
  exact (Stream.poly true δ (fun _ => []) 1 (by intro q x; cases q <;> simp [δ])
    (by simp)).realizes first

noncomputable def Poly.isEmpty : Poly id boolBits List.isEmpty := by
  let δ : Bool → Bool → Bool × List Bool := fun _ _ => (false,[])
  have h (q : Bool) (s : List Bool) :
      Stream.output δ boolBits q s = [q && s.isEmpty] := by
    induction s generalizing q with
    | nil => simp [Stream.output, boolBits]
    | cons x xs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly true δ boolBits 1 (by simp [δ]) (by simp [boolBits])).realizes
    (fun s => by simpa only [Bool.true_and, boolBits, id_eq] using h true s)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Codec
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

theorem boolBits_injective : Function.Injective boolBits := by
  intro a b h
  exact List.singleton_injective h

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FiniteMemory
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

noncomputable def Poly.ite {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {test : α → Bool} {yes no : α → β} (ct : Poly ea boolBits test)
    (cy : Poly ea eb yes) (cn : Poly ea eb no) :
    Poly ea eb (fun a => if test a then yes a else no a) :=
  ((ct.pair (cy.pair cn)).comp (Poly.select eb)).congr (fun _ => rfl)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Loop
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
open Turing Turing.TM2
open UniqueGames.Foundations.Complexity
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Loop
variable (A : FinTM2)
abbrev Γ := MachineEmbedding.Alphabet A.Γ (fun _ : Bool => Bool)
abbrev Cfg := Turing.TM2.Cfg (Γ A) (Λ A) (State A)
abbrev Stmt := Turing.TM2.Stmt (Γ A) (Λ A) (State A)
abbrev tapes := @MachineEmbedding.tapes A.K Bool A.Γ (fun _ => Bool)

variable (inA : A.Γ A.k₀ ≃ Bool) (outA : A.Γ A.k₁ ≃ Bool)

def extra : Fin 3 → Stmt A
  | i => if i = 0 then
      .pop (.inl A.k₁) (fun s x => (s.1, (x.map outA).getD false, none))
        (.goto (fun _ => phase A 1))
    else if i = 1 then
      .pop (.inl A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A 1)))
          (.goto (fun _ => phase A 2)))
    else
      .pop (temporary A) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.branch (fun s => s.2.1)
            (.push (.inl A.k₀) (fun s => inA.symm (s.2.2.getD false))
              (.goto (fun _ => phase A 2)))
            (.push (output A) (fun s => s.2.2.getD false)
              (.goto (fun _ => phase A 2))))
          (.branch (fun s => s.2.1)
            (.load (fun _ => (A.initialState,false,none)) (.goto (fun _ => .inl A.main)))
            (.load (fun _ => (A.initialState,false,none)) .halt)))

abbrev program := MachineEmbedding.program (haltTarget A) A.m (extra A inA outA)

abbrev machine : FinTM2 where
  K := K A
  Γ := Γ A
  k₀ := .inl A.k₀
  k₁ := output A
  Λ := Λ A
  σ := State A
  main := .inl A.main
  initialState := (A.initialState,false,none)
  m := program A inA outA
  Γk₀Fin := A.Γk₀Fin

open Compose (tapeOnly tapeOnly_nil tapeOnly_self tapeOnly_update init_tapes halt_tapes)

theorem tapes_update_extra (ta : ∀ k, List (A.Γ k)) (tb : Bool → List Bool)
    (j : Bool) (s : List Bool) :
    tapes A ta (Function.update tb j s) = Function.update (tapes A ta tb) (.inr j) s := by
  funext k
  rcases k with k | k
  · simp [tapes, MachineEmbedding.tapes, Function.update]
  · by_cases h : k = j
    · subst k; simp [tapes, MachineEmbedding.tapes]
    · simp [tapes, MachineEmbedding.tapes, Function.update, h]

abbrev embedded (c : A.Cfg) : Cfg A :=
  MachineEmbedding.configuration (haltTarget A) (false,none) (extraTapes [] []) c

def cfg1 (mode : Bool) (s : List (A.Γ A.k₁)) (temp : List Bool)
    (flag : Option Bool) : Cfg A where
  l := some (phase A 1)
  var := (A.initialState,mode,flag)
  stk := tapes A (tapeOnly A.k₁ s) (extraTapes temp [])

def cfg2true (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) : Cfg A where
  l := some (phase A 2)
  var := (A.initialState,true,flag)
  stk := tapes A (tapeOnly A.k₀ s) (extraTapes temp [])

def cfg2false (s temp : List Bool) (flag : Option Bool) : Cfg A where
  l := some (phase A 2)
  var := (A.initialState,false,flag)
  stk := tapes A (fun _ => []) (extraTapes temp s)

theorem cfg_ext {c c' : Cfg A} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

theorem cfg0_step (mode : Bool) (s : List Bool) :
    (machine A inA outA).step (embedded A (haltList A ((mode::s).map outA.symm))) =
      some (cfg1 A mode (s.map outA.symm) [] none) := by
  change step (program A inA outA) _ = _
  simp only [embedded, MachineEmbedding.configuration, halt_tapes, halt_label, halt_var,
    MachineEmbedding.label, haltTarget, phase, step, program, MachineEmbedding.program,
    extra, ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, List.map_cons, tapeOnly_self,
    List.head?_cons, List.tail_cons, Option.map_some, Equiv.apply_symm_apply, Option.getD_some]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  rfl

theorem cfg1_cons (mode : Bool) (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁))
    (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A mode (x::xs) temp flag) =
      some (cfg1 A mode xs (outA x::temp) (some (outA x))) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [temporary, MachineEmbedding.tapes_inr, extraTapes_false]
  rw [← tapes_update_extra, update_extra_false]

theorem cfg1_nil_true (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A true [] temp flag) =
      some (cfg2true A [] temp none) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [tapeOnly_nil, cfg2true]

theorem cfg1_nil_false (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A false [] temp flag) =
      some (cfg2false A [] temp none) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [tapeOnly_nil, cfg2false]

theorem cfg2true_cons (x : Bool) (xs : List Bool) (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    (machine A inA outA).step (cfg2true A s (x::xs) flag) =
      some (cfg2true A (inA.symm x::s) xs (some x)) := by
  change step (program A inA outA) _ = _
  simp only [cfg2true, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_extra, update_extra_false]
  simp only [MachineEmbedding.tapes_inl, tapeOnly_self]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]

theorem cfg2false_cons (x : Bool) (xs s : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg2false A s (x::xs) flag) =
      some (cfg2false A (x::s) xs (some x)) := by
  change step (program A inA outA) _ = _
  simp only [cfg2false, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some]
  rw [← tapes_update_extra, update_extra_false]
  simp only [output, MachineEmbedding.tapes_inr, extraTapes_true]
  rw [← tapes_update_extra, update_extra_true]

theorem initial_eq (s : List (A.Γ A.k₀)) :
    embedded A (initList A s) = initList (machine A inA outA) s := by
  apply cfg_ext A
  · rfl
  · rfl
  · rw [init_tapes]
    change tapes A (initList A s).stk (extraTapes [] []) = _
    rw [init_tapes]
    funext k
    rcases k with k | k
    · by_cases h : k = A.k₀
      · subst k; simp [tapes, MachineEmbedding.tapes, tapeOnly]
      · simp [tapes, MachineEmbedding.tapes, tapeOnly, Function.update, h]
    · cases k <;> simp [tapes, MachineEmbedding.tapes, tapeOnly, Function.update, extraTapes]

theorem cfg2true_nil (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    (machine A inA outA).step (cfg2true A s [] flag) =
      some (initList (machine A inA outA) s) := by
  rw [← initial_eq]
  change step (program A inA outA) _ = _
  simp only [cfg2true, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_true, Bool.cond_false]
  rw [← tapes_update_extra, update_extra_false]
  simp only [embedded, MachineEmbedding.configuration, init_tapes]
  rfl

theorem cfg2false_nil (s : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg2false A s [] flag) =
      some (haltList (machine A inA outA) s) := by
  change step (program A inA outA) _ = _
  simp only [cfg2false, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_extra, update_extra_false]
  congr 1
  apply cfg_ext A
  · rfl
  · rfl
  · rw [halt_tapes]
    funext k
    rcases k with k | k
    · simp [tapes, MachineEmbedding.tapes, tapeOnly, output, Function.update]
    · cases k <;> simp [tapes, MachineEmbedding.tapes, tapeOnly, output, Function.update, extraTapes]
def cfg1_run_true (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A true s temp flag)
      (some (cfg2true A [] ((s.map outA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact Pair.oneStep _ _ _ (cfg1_nil_true A inA outA temp flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg1_cons A inA outA true x xs temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg1_run_false (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A false s temp flag)
      (some (cfg2false A [] ((s.map outA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact Pair.oneStep _ _ _ (cfg1_nil_false A inA outA temp flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg1_cons A inA outA false x xs temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2true_run (temp : List Bool) (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2true A s temp flag)
      (some (initList (machine A inA outA) ((temp.map inA.symm).reverse ++ s)))
      (temp.length+1) := by
  induction temp generalizing s flag with
  | nil => exact Pair.oneStep _ _ _ (cfg2true_nil A inA outA s flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg2true_cons A inA outA x xs s flag)
    have e₂ := ih (inA.symm x::s) (some x)
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2false_run (temp s : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2false A s temp flag)
      (some (haltList (machine A inA outA) (temp.reverse ++ s))) (temp.length+1) := by
  induction temp generalizing s flag with
  | nil => exact Pair.oneStep _ _ _ (cfg2false_nil A inA outA s flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg2false_cons A inA outA x xs s flag)
    have e₂ := ih (x::s) (some x)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

open MachineComposition (embeddedExecution)

def bodyRun (mode : Bool) (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((mode::next).map outA.symm)) n) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (initList (machine A inA outA) (input.map inA.symm))
      (some (cfg1 A mode (next.map outA.symm) [] none)) (n+1) := by
  have e := embeddedExecution (haltTarget A) (false,none) (extraTapes [] []) A.m
    (extra A inA outA) h
  change @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
    (embedded A (initList A (input.map inA.symm)))
    (some (embedded A (haltList A ((mode::next).map outA.symm)))) n at e
  rw [initial_eq] at e
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e
    (Pair.oneStep _ _ _ (cfg0_step A inA outA mode next))
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

def restart (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((true::next).map outA.symm)) n) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (initList (machine A inA outA) (input.map inA.symm))
      (some (initList (machine A inA outA) (next.map inA.symm)))
      (n+1+2*(next.length+1)) := by
  have e₀ := bodyRun A inA outA true input next n h
  have e₁ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A true (next.map outA.symm) [] none)
      (some (cfg2true A [] next.reverse none)) (next.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg1_run_true A inA outA (next.map outA.symm) [] none
  have e₂ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2true A [] next.reverse none)
      (some (initList (machine A inA outA) (next.map inA.symm))) (next.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg2true_run A inA outA next.reverse [] none
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁) e₂
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

def finish (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((false::next).map outA.symm)) n) :
    TM2OutputsInTime (machine A inA outA) (input.map inA.symm) (some next)
      (n+1+2*(next.length+1)) := by
  have e₀ := bodyRun A inA outA false input next n h
  have e₁ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A false (next.map outA.symm) [] none)
      (some (cfg2false A [] next.reverse none)) (next.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg1_run_false A inA outA (next.map outA.symm) [] none
  have e₂ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2false A [] next.reverse none)
      (some (haltList (machine A inA outA) next)) (next.length+1) := by
    simpa only [List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg2false_run A inA outA next.reverse [] none
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁) e₂
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) :
    ∀ k, Finite ((machine A inA outA).Γ k) := by
  rintro (k | k)
  · exact hA k
  · exact inferInstanceAs (Finite Bool)

end Loop

noncomputable def loopCost {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body) : Polynomial ℕ :=
  c.time + 1 + Polynomial.C 2 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound c.tm) * c.time + 1)

theorem loopCost_bound {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body)
    (a : α) (B : ℕ) (ha : (e a).length ≤ B) :
    c.time.eval (e a).length + 1 + 2*((e (body a).2).length + 1) ≤ (loopCost c).eval B := by
  have ho := Runtime.encodedOutputLength c a
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    List.length_cons] at ho
  have ht := MachineComposition.natPolynomial_eval_mono c.time ha
  have hp := Nat.mul_le_mul_left (Runtime.programPushBound c.tm) ht
  simp only [loopCost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

theorem boundedRun_execution {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body)
    {B : ℕ} {a z : α} {n : ℕ} (h : BoundedRun e body B a z n) :
    Nonempty (TM2OutputsInTime (Loop.machine c.tm c.inputAlphabet c.outputAlphabet)
      ((e a).map c.inputAlphabet.symm) (some (e z)) (n*(loopCost c).eval B)) := by
  induction h with
  | stop a ha stop =>
    have ho := c.outputsFun a
    simp only [stop] at ho
    have run := Loop.finish c.tm c.inputAlphabet c.outputAlphabet (e a) (e (body a).2)
      (c.time.eval (e a).length) ho
    refine ⟨{ run with steps_le_m := ?_ }⟩
    simpa only [one_mul] using run.steps_le_m.trans (loopCost_bound c a B ha)
  | next a z n ha more tail ih =>
    obtain ⟨ih⟩ := ih
    have ho := c.outputsFun a
    simp only [more] at ho
    have run := Loop.restart c.tm c.inputAlphabet c.outputAlphabet (e a) (e (body a).2)
      (c.time.eval (e a).length) ho
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run ih
    refine ⟨{ all with steps_le_m := ?_ }⟩
    have h := all.steps_le_m
    have hb := loopCost_bound c a B ha
    rw [Nat.add_mul]
    omega

noncomputable def Poly.loop {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : Poly e (fun p : Bool × α => p.1 :: e p.2) body)
    (result : α → α) (size count : Polynomial ℕ)
    (spec : ∀ a, ∃ n, n ≤ count.eval (e a).length ∧
      BoundedRun e body (size.eval (e a).length) a (result a) n) : Poly e e result where
  computation := {
    tm := Loop.machine c.computation.tm c.computation.inputAlphabet c.computation.outputAlphabet
    inputAlphabet := c.computation.inputAlphabet
    outputAlphabet := Equiv.refl Bool
    time := count * (loopCost c.computation).comp size
    outputsFun := fun a => Classical.choice (by
      simp only [show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      obtain ⟨n, hn, run⟩ := spec a
      obtain ⟨execution⟩ := boundedRun_execution c.computation run
      refine ⟨{ execution with steps_le_m := ?_ }⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_comp]
      exact execution.steps_le_m.trans (Nat.mul_le_mul_right _ hn)) }
  finiteAlphabet := Loop.finiteAlphabet _ _ _ c.finiteAlphabet

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Lists
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

theorem listBits_length_pos {α : Type} (e : α → List Bool) (as : List α) :
    0 < (listBits e as).length := by
  cases as <;> simp

theorem listBits_reverse_length {α : Type} (e : α → List Bool) (as : List α) :
    (listBits e as.reverse).length = (listBits e as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons]
    have h := listBits_append_length e as.reverse [a]
    simp only [listBits_cons_length, listBits_nil, List.length_singleton, ih] at h ⊢
    omega

noncomputable def Poly.listCons {α : Type} (e : α → List Bool) :
    Poly (prodBits e (listBits e)) (listBits e) (fun p : α × List α => p.1::p.2) :=
  (Poly.cons true).realizes (fun _ => rfl)

noncomputable def Poly.swap {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) (prodBits eb ea) Prod.swap :=
  ((Poly.snd ea eb).pair (Poly.fst ea eb)).congr (fun _ => rfl)

noncomputable def Poly.flagPair {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → Bool} {g : α → β} (cf : Poly ea boolBits f) (cg : Poly ea eb g) :
    Poly ea (flagBits eb) (fun a => (f a,g a)) :=
  ((cf.pair cg).comp (Poly.flag eb)).congr (fun _ => rfl)

namespace Fold
variable {α β : Type} (f : β × α → β)

noncomputable def bodyPoly (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    (cf : Poly (prodBits eb ea) eb f) :
    Poly (prodBits eb (listBits ea)) (flagBits (prodBits eb (listBits ea))) (body f) := by
  let left := Poly.fst eb (listBits ea)
  let right := Poly.snd eb (listBits ea)
  let test := right.comp (Poly.listHasHead ea)
  let head := right.comp (Poly.listHeadD ea a₀)
  let tail := right.comp (Poly.listTail ea)
  let next := ((left.pair head).comp cf).pair tail
  exact (test.flagPair (test.ite next (Poly.identity _))).congr (by
    intro ⟨b,as⟩; cases as <;> rfl)

end Fold

noncomputable def Poly.fold {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    {f : β × α → β} (cf : Poly (prodBits eb ea) eb f) (size : Polynomial ℕ)
    (bound : ∀ b xs pre suf, pre++suf=xs →
      (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) b,suf)).length ≤
        size.eval (prodBits eb (listBits ea) (b,xs)).length) :
    Poly (prodBits eb (listBits ea)) eb (fun p => p.2.foldl (fun b a => f (b,a)) p.1) := by
  let result : β × List α → β × List α := fun p => (p.2.foldl (fun b a => f (b,a)) p.1,[])
  let c := (Fold.bodyPoly f ea eb a₀ cf).loop result size (Polynomial.X+1) (by
    intro ⟨b,xs⟩
    refine ⟨xs.length+1,?_, Fold.run f ea eb b xs _ (bound b xs)⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, prodBits, pairBits_length]
    have h := list_length_le_bits ea xs
    omega)
  exact (c.comp (Poly.fst eb (listBits ea))).congr (fun _ => rfl)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Naturals
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
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

noncomputable def Poly.natPred : Poly natBits natBits Nat.pred :=
  Poly.tail.realizes (fun n => by cases n <;> rfl)

noncomputable def Poly.natZero : Poly natBits boolBits (fun n => decide (n=0)) :=
  Poly.isEmpty.encodeCongr natBits (fun _ => rfl) (fun n => by cases n <;> rfl)

noncomputable def Poly.natPositive : Poly natBits boolBits (fun n => decide (0<n)) :=
  (Poly.natZero.comp (Poly.bool Bool.not)).congr (fun n => by cases n <;> rfl)

namespace Iterate
variable {α : Type} (f : α → α)

noncomputable def bodyPoly (e : α → List Bool) (cf : Poly e e f) :
    Poly (prodBits natBits e) (flagBits (prodBits natBits e)) (body f) := by
  let cn := Poly.fst natBits e
  let ca := Poly.snd natBits e
  let test := cn.comp Poly.natPositive
  let next := (cn.comp Poly.natPred).pair (ca.comp cf)
  exact (test.flagPair (test.ite next (Poly.identity _))).congr (by
    intro ⟨n,a⟩; cases n <;> rfl)

theorem bounded (e : α → List Bool) (n : ℕ) (a : α) (B : ℕ)
    (bound : ∀ k l, k+l=n → (prodBits natBits e (l,run f k a)).length ≤ B) :
    BoundedRun (prodBits natBits e) (body f) B (n,a) (0,run f n a) (n+1) := by
  induction n generalizing a with
  | zero => exact .stop _ (bound 0 0 rfl) rfl
  | succ n ih =>
    exact .next _ _ _ (bound 0 (n+1) (Nat.zero_add _)) rfl (ih (f a) (by
      intro k l h
      exact bound (k+1) l (by omega)))
end Iterate

noncomputable def Poly.iterate {α : Type} (e : α → List Bool) {f : α → α}
    (cf : Poly e e f) (size : Polynomial ℕ)
    (bound : ∀ n a k l, k+l=n →
      (prodBits natBits e (l,Iterate.run f k a)).length ≤ size.eval (prodBits natBits e (n,a)).length) :
    Poly (prodBits natBits e) e (fun p : ℕ × α => Iterate.run f p.1 p.2) := by
  let result : ℕ × α → ℕ × α := fun p => (0,Iterate.run f p.1 p.2)
  let c := (Iterate.bodyPoly f e cf).loop result size (Polynomial.X+1) (by
    intro ⟨n,a⟩
    refine ⟨n+1,?_, Iterate.bounded f e n a _ (bound n a)⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, prodBits,
      pairBits_length,natBits_length]
    omega)
  exact (c.comp (Poly.snd natBits e)).congr (fun _ => rfl)

noncomputable def Poly.natSub : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1-p.2) := by
  let c := Poly.iterate natBits Poly.natPred Polynomial.X (by
    intro n a k l h
    simp only [Polynomial.eval_X,prodBits,pairBits_length,natBits_length,iterate_pred]
    omega)
  exact ((Poly.swap natBits natBits).comp c).congr (fun p => iterate_pred p.2 p.1)

noncomputable def Poly.natLE : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1≤p.2)) :=
  (Poly.natSub.comp Poly.natZero).congr (fun p => by
    simp only [Function.comp_apply,Nat.sub_eq_zero_iff_le])

noncomputable def Poly.bool₂ (f : Bool × Bool → Bool) :
    Poly (prodBits boolBits boolBits) boolBits f :=
  Poly.finite _ _ (by
    intro a b h
    simp only [prodBits,pairBits,boolBits,frame,List.cons_append,List.nil_append,List.cons.injEq] at h
    exact Prod.ext h.2.1 h.2.2.2.1) f

noncomputable def Poly.natBEq : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1=p.2)) := by
  let cr := (Poly.swap natBits natBits).comp Poly.natLE
  exact ((Poly.natLE.pair cr).comp (Poly.bool₂ (fun p => p.1 && p.2))).congr (by
    intro ⟨n,m⟩
    change (decide (n≤ m) && decide (m≤n)) = decide (n=m)
    simp only [← Bool.decide_and, Nat.le_antisymm_iff])

theorem iterate_add (k n a : ℕ) :
    Iterate.run (fun p : ℕ × ℕ => (p.1,p.1+p.2)) k (n,a) = (n,k*n+a) := by
  induction k generalizing a with
  | zero => simp [Iterate.run]
  | succ k ih => simp only [Iterate.run,ih]; congr 1; ring

noncomputable def Poly.natMul : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1*p.2) := by
  let e := prodBits natBits natBits
  let step := (Poly.fst natBits natBits).pair Poly.natAdd
  have bound (m : ℕ) (p : ℕ × ℕ) (k l : ℕ) (h : k+l=m) :
      (prodBits natBits e (l,Iterate.run (fun p : ℕ × ℕ => (p.1,p.1+p.2)) k p)).length ≤
        (10*(Polynomial.X+1)^2 : Polynomial ℕ).eval (prodBits natBits e (m,p)).length := by
    rcases p with ⟨n,a⟩
    simp only [iterate_add,prodBits,e,pairBits_length,natBits_length,Polynomial.eval_mul,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow,
      Polynomial.eval_ofNat]
    have hk : k≤ m := by omega
    have hkn := Nat.mul_le_mul_right n hk
    nlinarith [Nat.zero_le (m*n), Nat.zero_le ((m-n)^2)]
  let loop := Poly.iterate e step (10*(Polynomial.X+1)^2) bound
  let input := (Poly.fst natBits natBits).pair
    ((Poly.snd natBits natBits).pair (Poly.const _ natBits 0))
  exact ((input.comp loop).comp (Poly.snd natBits natBits)).congr (fun p => by
    simp only [Function.comp_apply,iterate_add,Nat.add_zero])

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatDiv
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
namespace Divide
abbrev enc : State → List Bool := prodBits natBits (prodBits natBits natBits)

noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let d := Poly.fst natBits (prodBits natBits natBits)
  let rq := Poly.snd natBits (prodBits natBits natBits)
  let r := rq.comp (Poly.fst natBits natBits)
  let q := rq.comp (Poly.snd natBits natBits)
  let test := ((d.comp Poly.natPositive).pair ((d.pair r).comp Poly.natLE)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
  let next := d.pair (((r.pair d).comp Poly.natSub).pair (q.comp Poly.natSucc))
  exact (test.flagPair (test.ite next (Poly.identity enc))).congr (by
    intro ⟨d,r,q⟩
    simp only [Function.comp_apply,body]
    by_cases hd : 0<d <;> by_cases hr : d ≤ r <;> simp [hd,hr])

end Divide

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinCode
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

def finCode {n : ℕ} (i : Fin n) : List Bool := natBits i.val

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FixedOps
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

noncomputable def Poly.fixedList {α ι β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → ι → β) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly ea (listBits eb) (fun a => xs.map (f a))
  | [] => Poly.const ea (listBits eb) []
  | i::xs => ((cf i).pair (Poly.fixedList ea eb f cf xs)).comp (Poly.listCons eb)

theorem fixedSelect_mem {α ι β : Type} [DecidableEq ι]
    (f : α → ι → β) (i₀ : ι) (a : α) :
    ∀ (xs : List ι) (i : ι), i ∈ xs → fixedSelect f i₀ xs (a,i) = f a i := by
  intro xs
  induction xs with
  | nil => simp
  | cons j xs ih =>
    intro i hi
    by_cases h : i=j
    · subst i; simp [fixedSelect]
    · rw [fixedSelect,ite_eq_right h]
      exact ih i ((List.mem_cons.mp hi).resolve_left h)

noncomputable def Poly.fixedSelect {α ι β : Type} [Fintype ι] [DecidableEq ι]
    (ea : α → List Bool) (ei : ι → List Bool) (eb : β → List Bool) (hi : Function.Injective ei)
    (f : α → ι → β) (i₀ : ι) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly (prodBits ea ei) eb (fixedSelect f i₀ xs)
  | [] => (Poly.fst ea ei).comp (cf i₀)
  | i::xs => (((Poly.snd ea ei).comp (Poly.finite ei boolBits hi (fun j => decide (j=i)))).ite
    ((Poly.fst ea ei).comp (cf i)) (Poly.fixedSelect ea ei eb hi f i₀ cf xs)).congr (fun _ => by
      simp only [Function.comp_apply,VertexCover.Machine.fixedSelect,decide_eq_true_eq])

noncomputable def Poly.finiteBranch {α ι β : Type} [Fintype ι] [Nonempty ι]
    (ea : α → List Bool) (ei : ι → List Bool) (eb : β → List Bool) (hi : Function.Injective ei)
    (f : α → ι → β) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    Poly (prodBits ea ei) eb (fun x => f x.1 x.2) := by
  classical
  let i₀ := Classical.choice (inferInstance : Nonempty ι)
  exact (Poly.fixedSelect ea ei eb hi f i₀ cf Finset.univ.toList).congr
    (fun x => fixedSelect_mem f i₀ x.1 _ x.2 (by simp))

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListMore
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
open UniqueGames.Foundations.Complexity

noncomputable def Poly.outputPolynomial {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (c : Poly ea eb f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (Runtime.programPushBound c.computation.tm) * c.computation.time

theorem Poly.output_length {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (c : Poly ea eb f) (a : α) :
    (eb (f a)).length ≤ c.outputPolynomial.eval (ea a).length :=
  Runtime.encodedOutputLength c.computation a

noncomputable def Poly.reverseAppend {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (prodBits (listBits e) (listBits e)) (listBits e)
      (fun p : List α × List α => p.2.reverse++p.1) := by
  let c := (Poly.swap (listBits e) e).comp (Poly.listCons e)
  have bound (b xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits (listBits e) (listBits e) (pre.foldl (fun b a => a::b) b, suf)).length ≤
        (Polynomial.C 2 * Polynomial.X + 1).eval
          (prodBits (listBits e) (listBits e) (b,xs)).length := by
    simp only [prodBits, pairBits_length, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, foldl_cons_eq_reverse_append]
    have h₁ := listBits_append_length e pre.reverse b
    have h₂ := listBits_append_length e pre suf
    rw [listBits_reverse_length] at h₁
    rw [h] at h₂
    omega
  exact (Poly.fold e (listBits e) a₀ c (Polynomial.C 2 * Polynomial.X+1) bound).congr
    (fun p => foldl_cons_eq_reverse_append p.2 p.1)

noncomputable def Poly.listReverse {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (listBits e) (listBits e) List.reverse :=
  (((Poly.const (listBits e) (listBits e) []).pair (Poly.identity (listBits e))).comp
    (Poly.reverseAppend e a₀)).congr (fun _ => List.append_nil _)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListNat
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

theorem listBits_drop_length_le {α : Type} (e : α → List Bool) (n : ℕ) (xs : List α) :
    (listBits e (xs.drop n)).length ≤ (listBits e xs).length := by
  have h := listBits_append_length e (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  have := listBits_length_pos e (xs.take n)
  omega

theorem iterate_tail {α : Type} (k : ℕ) (xs : List α) :
    Iterate.run List.tail k xs = xs.drop k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp only [Iterate.run,ih,List.drop_tail]

noncomputable def Poly.listDrop {α : Type} (e : α → List Bool) :
    Poly (prodBits natBits (listBits e)) (listBits e)
      (fun p : ℕ × List α => p.2.drop p.1) := by
  let c := Poly.iterate (listBits e) (Poly.listTail e) Polynomial.X (by
    intro n xs k l h
    simp only [Polynomial.eval_X,prodBits,pairBits_length,natBits_length,iterate_tail]
    have hd := listBits_drop_length_le e k xs
    omega)
  exact c.congr (fun p => iterate_tail p.1 p.2)

noncomputable def Poly.listGetD {α : Type} (e : α → List Bool) (a : α) :
    Poly (prodBits natBits (listBits e)) e
      (fun p : ℕ × List α => (p.2.drop p.1).headD a) :=
  (Poly.listDrop e).comp (Poly.listHeadD e a)

noncomputable def Poly.lengthFold {α : Type} (e : α → List Bool) (a : α) :
    Poly (prodBits natBits (listBits e)) natBits
      (fun p : ℕ × List α => p.2.length+p.1) := by
  let step := (Poly.fst natBits e).comp Poly.natSucc
  let size : Polynomial ℕ := 3*Polynomial.X+3
  have bound (b : ℕ) (xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits natBits (listBits e) (pre.foldl (fun n _ => n+1) b,suf)).length ≤
        size.eval (prodBits natBits (listBits e) (b,xs)).length := by
    have hd := listBits_append_length e pre suf
    rw [h] at hd
    have hl := list_length_le_bits e pre
    simp only [prodBits,pairBits_length,natBits_length,size,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,foldl_count]
    omega
  exact (Poly.fold e natBits a step size bound).congr (fun p => foldl_count p.2 p.1)

noncomputable def Poly.listLength {α : Type} (e : α → List Bool) (a : α) :
    Poly (listBits e) natBits List.length :=
  (((Poly.const (listBits e) natBits 0).pair (Poly.identity (listBits e))).comp
    (Poly.lengthFold e a)).congr (fun _ => Nat.add_zero _)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Option
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

noncomputable def Poly.some {α : Type} (ea : α → List Bool) :
    Poly ea (optionBits ea) Option.some :=
  (Poly.cons true).encodeCongr ea (fun _ => rfl) (fun _ => rfl)

noncomputable def Poly.isSome {α : Type} (ea : α → List Bool) :
    Poly (optionBits ea) boolBits Option.isSome :=
  (Poly.headD false).encodeCongr (optionBits ea) (fun _ => rfl) (fun a => by cases a <;> rfl)

noncomputable def Poly.getD {α : Type} (ea : α → List Bool) (a₀ : α) :
    Poly (optionBits ea) ea (fun o => o.getD a₀) := by
  let test := Poly.headD false
  let c := test.ite Poly.tail (Poly.const id id (ea a₀))
  exact c.encodeCongr (optionBits ea) (fun _ => rfl) (fun a => by cases a <;> rfl)

noncomputable def Poly.optionBind {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : α → Option β} (cf : Poly ea (optionBits eb) f) :
    Poly (optionBits ea) (optionBits eb) (fun o => o.bind f) :=
  ((Poly.isSome ea).ite ((Poly.getD ea a₀).comp cf)
    (Poly.const (optionBits ea) (optionBits eb) none)).congr (fun a => by cases a <;> rfl)

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
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLazy
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGames.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem operator_binomialMean [Fintype D] (G : PortGraph V D)
    (n : Nat) (g : Nat → V → ℝ) (v : V) :
    averagingOperator G (fun w => LazySmoothing.binomialMean n (fun k => g k w)) v =
      LazySmoothing.binomialMean n (fun k => averagingOperator G (g k) v) := by
  unfold averagingOperator LazySmoothing.binomialMean
  exact Finset.expect_comm Finset.univ Finset.univ
    (fun d tape => g (LazySmoothing.bitCount tape) (G.rot (v, d)).1)

end UniqueGames.Foundations.PCP.PoweringLazy

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.VertexPadding

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

end UniqueGames.Foundations.PCP.VertexPadding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingOverlayTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

theorem rotation_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) :
    PortTables.rotation (materialize G ports) x =
      ((G.reverse (x.1, ports.symm x.2)).1,
        ports (G.reverse (x.1, ports.symm x.2)).2) := by
  simp only [materialize, PortTables.rotation_ofPortGraph, GraphTransport.reindex,
    Overlay.originalPortGraph, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, Prod.map]
  rfl

theorem rotation_materialize_image {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (v : Fin n) (i : D) :
    PortTables.rotation (materialize G ports) (v, ports i) =
      ((G.reverse (v, i)).1, ports (G.reverse (v, i)).2) := by
  rw [rotation_materialize, Equiv.symm_apply_apply]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hreverse : ∀ e, G.reverse e = H.reverse e)
    (htail : ∀ e, G.tail e = H.tail e)
    (haccepts : ∀ e a b, G.accepts e a b = H.accepts e a b) : G = H := by
  rcases G with ⟨r, hi, t, p, hp⟩
  rcases H with ⟨r', hi', t', p', hp'⟩
  have hr : r = r' := Equiv.ext hreverse
  cases hr
  have ht : t = t' := funext htail
  cases ht
  have ha : p = p' := funext fun e => funext fun a => funext fun b => haccepts e a b
  cases ha
  rfl

theorem baseGraph_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (htail : G.tail = Prod.fst) :
    PortTables.baseGraph (materialize G ports) =
      G.reindex (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) ports) (Equiv.refl _) := by
  apply constraintGraph_ext
  · intro x
    rw [PortTables.baseGraph_reverse, rotation_materialize]
    rfl
  · intro x
    change x.1 = G.tail (x.1, ports.symm x.2)
    rw [htail]
  · intro x a b
    rw [PortTables.baseGraph_accepts, accepts_materialize]
    rfl

def overlay {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.Table n (d + e) :=
  materialize (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
    (overlayPorts d e)

theorem overlay_rotation_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inl i)) =
      ((PortTables.rotation G (v, i)).1,
        overlayPorts d e (Sum.inl (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inl i)

theorem overlay_rotation_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inr i)) =
      ((ExpanderTables.lookup H (v, i)).1,
        overlayPorts d e (Sum.inr (ExpanderTables.lookup H (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inr i)

@[simp] theorem overlay_accepts_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inl i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem overlay_accepts_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inr i)) a b = true := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

theorem overlay_semantics {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.baseGraph (overlay G H) =
      (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (overlayPorts d e))
        (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

def lazy {n d : Nat} (G : PortTables.Table n d) : PortTables.Table n (2 * d) :=
  materialize (LazyConstraint.constraintGraph (PortTables.baseGraph G)) (lazyPorts d)

theorem lazy_rotation_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (false, i)) =
      (v, lazyPorts d (false, i)) := by
  exact rotation_materialize_image _ _ v (false, i)

theorem lazy_rotation_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (true, i)) =
      ((PortTables.rotation G (v, i)).1,
        lazyPorts d (true, (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (true, i)

@[simp] theorem lazy_accepts_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (false, i)) a b = true := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem lazy_accepts_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (true, i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

theorem lazy_semantics {n d : Nat} (G : PortTables.Table n d) :
    PortTables.baseGraph (lazy G) =
      (LazyConstraint.constraintGraph (PortTables.baseGraph G)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (lazyPorts d)) (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

end UniqueGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingPaddingTables
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_false _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.lazy_accepts_true _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_expander _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.overlay_accepts_old
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem reverseIndex_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      rowIndex m d (vertexEquiv h (Sum.inr v), p) := by
  rw [← rowIndex_rotation, rotation_pad_new]

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply relation_ext
  intro a b
  exact accepts_pad_old table h v p a b

theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  constructor
  · intro hs e
    simpa only [edgeSatisfied_pad_old] using hs (e.1.castLE h, e.2)
  · intro hs e
    obtain ⟨v, hv⟩ := (vertexEquiv h).surjective e.1
    have he : e = (vertexEquiv h v, e.2) := Prod.ext hv.symm rfl
    rw [he]
    cases v with
    | inl v => simpa only [vertexEquiv_inl, edgeSatisfied_pad_old] using hs (v, e.2)
    | inr v => exact edgeSatisfied_pad_new table h labeling v e.2

def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

end UniqueGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingCloudIndex
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

namespace UniqueGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

theorem cloudSize_eq_card_cloud (t : Table) (v : Fin t.vertices) :
    cloudSize t v = Fintype.card (Cloud (semantics t) v) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (cloudEquiv t v)).symm

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end UniqueGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingLevels
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingLevels

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

def boundedLevel (k : Nat) : Nat := (searchResult k).1

def paddedSize (k : Nat) : Nat := (searchResult k).2

@[simp] theorem boundedLevel_zero : boundedLevel 0 = 0 := rfl

@[simp] theorem paddedSize_zero : paddedSize 0 = 1 := rfl

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

def cloudPaddedSize (k : Nat) : Nat := if k = 0 then 0 else paddedSize k

@[simp] theorem cloudPaddedSize_zero : cloudPaddedSize 0 = 0 := rfl

theorem cloudPaddedSize_of_pos {k : Nat} (hk : 0 < k) :
    cloudPaddedSize k = paddedSize k := by
  simp only [cloudPaddedSize, Nat.ne_of_gt hk, ite_false]

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

end UniqueGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

def emptyTable (q : Nat) : ExpanderTables.Table 0 q :=
  ExpanderTables.ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

def resizeTable {n m q : Nat} (h : n = m) (table : ExpanderTables.Table n q) :
    ExpanderTables.Table m q := h ▸ table

abbrev BaseTable := ExpanderTables.Table
  ((Expanders.baseDegree * Expanders.baseDegree) *
    (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

def padding (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) -
    PreprocessingCloudIndex.cloudSize t v

end UniqueGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingTables
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

abbrev BaseTable := PreprocessingRegularTables.BaseTable

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

end UniqueGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_TableBase
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail
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

namespace TableMachine
open PCP.GraphTables

abbrev Row := (ℕ × ℕ) × RelationTable
abbrev Data := ℕ × List Row

def relationCode (r : RelationTable) : List Bool := r.toList
def rowCode : Row → List Bool := prodBits (prodBits natBits natBits) relationCode
def rowData {n m : ℕ} (r : DartRow n m) : Row := ((r.tail.val,r.reverseIndex.val),r.relation)
def tableData (T : Table) : Data := (T.vertices,T.rows.toList.map rowData)

def relationDefault : RelationTable := Vector.replicate 4096 false
def rowDefault : Row := ((0,0),relationDefault)

@[simp] theorem relationCode_length (r : RelationTable) : (relationCode r).length = 4096 := by
  simp [relationCode]

@[simp] theorem lookup_valid (T : Table) (i : Fin T.darts) :
    (tableData T).2.getD i.val rowDefault = rowData T.rows[i] := by
  simp only [tableData,List.getD_eq_getElem?_getD,List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp)]
  rfl

end TableMachine
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderStep
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

namespace ExpandMachine

abbrev Input (q : ℕ) := Σ v, ExpanderTables.Table v q
def dataCode : Data → List Bool := prodBits natBits (listBits natBits)
def erase {q : ℕ} (T : Input q) : Data := (T.1,T.2.rows.toList.map Fin.val)

end ExpandMachine
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListFilter
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

noncomputable def Poly.natEq : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => p.1 == p.2) := Poly.natBEq.congr (fun _ => rfl)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Cloud
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

namespace CloudMachine
open TableMachine

def cloud (p : GraphTables.Table × ℕ) : List ℕ :=
  (List.range p.1.darts).filter (fun i => ((tableData p.1).2.getD i rowDefault).1.1 == p.2)

end CloudMachine
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_CloudIndex
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

abbrev Dummy (T : GraphTables.Table) := Σ v : Fin T.vertices, Fin (PreprocessingRegularTables.padding T v)

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Address
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

namespace FixedSearch

 theorem eq_scan {ι β : Type} (p : ι → Prop) [DecidablePred p] (f : ι → β) (z : β) :
    ∀ (xs : List ι) (h : ∃ i ∈ xs, p i),
      run (fun (_ : Unit) i => decide (p i)) (fun _ i => f i) z xs () =
        f (UniqueGames.Foundations.PCP.PoweringLabels.scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons i xs ih =>
    intro h
    by_cases hp : p i
    · simp [run,UniqueGames.Foundations.PCP.PoweringLabels.scanWitness,hp]
    · simp only [run,decide_eq_true_eq,hp,↓reduceIte,
        UniqueGames.Foundations.PCP.PoweringLabels.scanWitness,↓reduceDIte]
      exact ih _

end FixedSearch

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseFrame
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.VertexCover.Machine.listBits_cons _root_.OAI.VertexCover.Machine.pairBits_length
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

namespace VertexCover.Machine.FrameParser
open UniqueGames.BinaryEncoding

def scan (mode : Fin 3) (q : Fin 3) (bs : List Bool) : List Bool :=
  Stream.output (trans mode) (finish mode) q bs

theorem flag (q : Fin 3) (bs : List Bool) : scan 2 q bs = [decide (state q bs=2)] := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => exact ih (next q b)

theorem after_digits (bs : List Bool) : scan 0 2 bs = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [scan,Stream.output,trans,next,finish] using ih

theorem after_rest (bs : List Bool) : scan 1 2 bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [scan,Stream.output,trans,next,finish] using congrArg (List.cons b) ih

def parsed (bs : List Bool) : Option (List Bool × List Bool) :=
  if state 0 bs=2 then some (scan 0 0 bs,scan 1 0 bs) else none

theorem correct (bs : List Bool) : parsed bs = parseFrame bs := by
  induction bs using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons a b bs ih _ =>
    cases a with
    | false =>
      change (if state 2 (b::bs)=2 then some (scan 0 2 (b::bs),scan 1 2 (b::bs)) else none) = some ([],b::bs)
      rw [after_state,after_digits,after_rest]
      rfl
    | true =>
      have hs : state 0 (true::b::bs) = state 0 bs := rfl
      have hd : scan 0 0 (true::b::bs) = b::scan 0 0 bs := rfl
      have hr : scan 1 0 (true::b::bs) = scan 1 0 bs := rfl
      simp only [parsed,hs,hd,hr,parseFrame]
      rw [← ih]
      by_cases h : state 0 bs=2 <;> simp [parsed,h]

noncomputable def scanner (mode : Fin 3) : Poly id id (scan mode 0) :=
  Stream.poly 0 (trans mode) (finish mode) 1
    (by intros; dsimp [trans]; split <;> simp)
    (by intros; dsimp [finish]; split <;> simp)

noncomputable def poly : Poly id (optionBits (prodBits id id)) parseFrame := by
  let valid : Poly id boolBits (fun bs => decide (state 0 bs=2)) := (scanner 2).encodeCongr id (fun _ => rfl) (fun bs => flag 0 bs)
  let pair := (scanner 0).pair (scanner 1)
  let somePair := pair.comp (Poly.some (prodBits id id))
  let c := valid.ite somePair (Poly.const id (optionBits (prodBits id id)) none)
  exact c.congr (fun bs => by
    have h : (if decide (state 0 bs=2) then some (scan 0 0 bs,scan 1 0 bs) else none) = parsed bs := by
      simp [parsed]
    exact h.trans (correct bs))

end VertexCover.Machine.FrameParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseName
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.VertexCover.Machine.listBits_cons _root_.OAI.VertexCover.Machine.pairBits_length
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

namespace VertexCover.Machine.NameParser
open UniqueGames.BinaryEncoding

theorem canonical_iff (bs : List Bool) : canonical bs = true ↔ (bitsValue bs).bits = bs := by
  induction bs with
  | nil => simp [canonical,bitsValue]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp [canonical,bitsValue,Nat.bit]
    | cons c cs =>
      change canonical (c::cs)=true ↔ (bitsValue (b::c::cs)).bits=b::c::cs
      constructor
      · intro h
        have hc := ih.mp h
        have hn : bitsValue (c::cs) ≠ 0 := by
          intro hz
          rw [hz,Nat.zero_bits] at hc
          contradiction
        change (Nat.bit b (bitsValue (c::cs))).bits = _
        rw [Nat.bits_append_bit _ _ (fun hz => False.elim (hn hz)),hc]
      · intro h
        apply ih.mpr
        have ht := congrArg List.tail h
        simpa only [bitsValue,← Nat.div2_bits_eq_tail,Nat.div2_bit,List.tail_cons] using ht

theorem canon_scan (q : Bool) (b : Bool) (bs : List Bool) :
    Stream.output trans (fun q => [q]) q (b::bs) = [canonical (b::bs)] := by
  induction bs generalizing q b with
  | nil => rfl
  | cons c cs ih => exact ih b c

noncomputable def canonicalPoly : Poly id boolBits canonical :=
  (Stream.poly true trans (fun q => [q]) 1 (by intros; exact Nat.zero_le _) (by intros; rfl)).realizes
    (fun bs => by cases bs with | nil => rfl | cons b bs => exact canon_scan true b bs)

def core (p : List Bool × List Bool) : Option (ℕ × List Bool) :=
  if p.1=(bitsValue p.1).bits then some (bitsValue p.1,p.2) else none

noncomputable def corePoly : Poly (prodBits id id) (optionBits (prodBits Nat.bits id)) core := by
  let test := (Poly.fst id id).comp canonicalPoly
  let c := test.ite (Poly.some (prodBits id id))
    (Poly.const (prodBits id id) (optionBits (prodBits id id)) none)
  refine c.encodeCongr id (fun _ => rfl) ?_
  intro ⟨digits,rest⟩
  by_cases h : canonical digits=true
  · have hc := (canonical_iff digits).mp h
    simp [core,h,hc,optionBits,prodBits]
  · have hc : digits ≠ (bitsValue digits).bits := by
      intro he
      exact h ((canonical_iff digits).mpr he.symm)
    simp [core,h,hc,optionBits]

noncomputable def poly : Poly id (optionBits (prodBits Nat.bits id)) parseName :=
  (FrameParser.poly.comp (Poly.optionBind (prodBits id id) (prodBits Nat.bits id) ([],[]) corePoly)).congr (fun _ => rfl)

end VertexCover.Machine.NameParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseSize
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

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

noncomputable def rawLength : Poly id natBits List.length :=
  (Poly.rawToList.comp (Poly.listLength boolBits false)).congr (fun _ => rfl)

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringReturn
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem iterateOperator_succ_right [Fintype D] (G : PortGraph V D)
    (n : Nat) (f : V → ℝ) :
    iterateOperator G n (averagingOperator G f) = iterateOperator G (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (averagingOperator G) ih

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

theorem mean_marked_bit [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
      markedStep G bad f v := by
  change mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
    mean (fun d : D => if bad (v, d) then f (next G v d) else 0)
  congr 1
  funext d
  cases bad (v, d) <;> simp [bit]

end UniqueGames.Foundations.PCP.PoweringReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

theorem portGraph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

end UniqueGames.Foundations.PCP.PreprocessingTableSpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                      

namespace UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

end UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingGuarantees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

noncomputable section

namespace UniqueGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree )

variable {n d e : Nat}

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

end UniqueGames.Foundations.PCP.PreprocessingGuarantees
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RoundTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.RoundTables

abbrev BaseTable := PreprocessingTables.BaseTable

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

end UniqueGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VerifierToCNF
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.patternRelationIndex_eq _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.«variables» + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

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
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Completion
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
    («c» : ℝ) (x : X) (y : Y) :
    («c» * (∑ z, left z) * (∑ z, right z)) *
      ((normalizeOr left hl defaultLeft).weight x *
        (normalizeOr right hr defaultRight).weight y) = «c» * left x * right y := by
  calc
    _ = «c» * ((∑ z, left z) * (normalizeOr left hl defaultLeft).weight x) *
        ((∑ z, right z) * (normalizeOr right hr defaultRight).weight y) := by ring
    _ = _ := by rw [sum_mul_normalizeOr, sum_mul_normalizeOr]

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_RejectionCount
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open UniqueGames.Foundations.Target

def literalAt (F : Formula) (i : Fin F.clauses.length) (k : Fin 3) : Literal F.«variables» :=
  (F.clauses.get i)[k]

noncomputable def game (F : Formula) (hne : F.clauses ≠ []) : LabelCover where
  u := F.clauses.length
  v := F.«variables»
  qU := 7
  qV := 2
  M := F.clauses.length * 3
  qU_pos := by decide
  qV_pos := by decide
  M_pos := Nat.mul_pos (List.length_pos_iff.mpr hne) (by decide)
  left e := (finProdFinEquiv.symm e).1
  right e := (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).variableIndex
  projection e label := finTwoEquiv.symm
    (flipSign (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).positive
      ((patternEquiv.symm label).val (finProdFinEquiv.symm e).2))

def clauseValue (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (k : Fin 3) : Bool :=
  (literalAt F i k).eval a

theorem clause_eval_iff (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) :
    (F.clauses.get i).eval a = true ↔ ∃ k : Fin 3, clauseValue F a i k = true := by
  simp only [Clause.eval, Bool.or_eq_true]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk

noncomputable def honestLabeling (F : Formula) (hne : F.clauses ≠ [])
    (a : Fin F.«variables» → Bool)
    (ha : ∀ clause ∈ F.clauses, clause.eval a = true) : (game F hne).Labeling :=
  (fun i => patternEquiv ⟨clauseValue F a i,
      (clause_eval_iff F a i).mp (ha _ (List.get_mem _ i))⟩,
   fun v => finTwoEquiv.symm (a v))

theorem honest_satisfies (F : Formula) (hne : F.clauses ≠ [])
    (a : Fin F.«variables» → Bool)
    (ha : ∀ clause ∈ F.clauses, clause.eval a = true) :
    ∀ e, (game F hne).Satisfies (honestLabeling F hne a ha) e := by
  intro e
  simp only [LabelCover.Satisfies, game, honestLabeling, Equiv.symm_apply_apply]
  congr 1
  change flipSign _ (flipSign _ _) = _
  exact flipSign_flipSign _ _

noncomputable def assignmentOf (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (v : Fin F.«variables») : Bool := finTwoEquiv (A.2 v)

theorem satisfies_iff (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (i : Fin F.clauses.length) (k : Fin 3) :
    (game F hne).Satisfies A (finProdFinEquiv (i,k)) ↔
      (patternEquiv.symm (A.1 i)).val k = clauseValue F (assignmentOf F hne A) i k := by
  simp only [LabelCover.Satisfies, game, Equiv.symm_apply_apply]
  change finTwoEquiv.symm (flipSign (literalAt F i k).positive
    ((patternEquiv.symm (A.1 i)).val k)) = A.2 (literalAt F i k).variableIndex ↔
    (patternEquiv.symm (A.1 i)).val k =
      flipSign (literalAt F i k).positive (assignmentOf F hne A (literalAt F i k).variableIndex)
  constructor
  · intro h
    have hh := congrArg finTwoEquiv h
    simp only [Equiv.apply_symm_apply] at hh
    have hf := congrArg (flipSign (literalAt F i k).positive) hh
    simpa only [flipSign_flipSign, assignmentOf] using hf
  · intro h
    rw [h, flipSign_flipSign]
    exact finTwoEquiv.symm_apply_apply _

def unsatisfiedClauses (F : Formula) (a : Fin F.«variables» → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun i => (F.clauses.get i).eval a = false)

theorem reject_of_unsatisfied (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (i : Fin F.clauses.length)
    (hi : i ∈ unsatisfiedClauses F (assignmentOf F hne A)) :
    ∃ k : Fin 3, ¬(game F hne).Satisfies A (finProdFinEquiv (i,k)) := by
  obtain ⟨k, hk⟩ := (patternEquiv.symm (A.1 i)).property
  refine ⟨k, ?_⟩
  intro hsat
  have hclause := (clause_eval_iff F (assignmentOf F hne A) i).mpr
    ⟨k, (satisfies_iff F hne A i k).mp hsat ▸ hk⟩
  have hfalse := (Finset.mem_filter.mp hi).2
  rw [hfalse] at hclause
  cases hclause

theorem rejection_count (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) :
    (unsatisfiedClauses F (assignmentOf F hne A)).card ≤
      (Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e)).card := by
  classical
  let bad := unsatisfiedClauses F (assignmentOf F hne A)
  let witness : {i // i ∈ bad} → Fin 3 := fun i =>
    (reject_of_unsatisfied F hne A i.val i.property).choose
  let occurrence : {i // i ∈ bad} → Fin (game F hne).M :=
    fun i => finProdFinEquiv (i.val, witness i)
  have hmap : ∀ i, occurrence i ∈ Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e) := by
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (reject_of_unsatisfied F hne A i.val i.property).choose_spec⟩
  have hinj : Function.Injective occurrence := by
    intro i j hij
    exact Subtype.ext (congrArg Prod.fst (finProdFinEquiv.injective hij))
  have hcard := Fintype.card_le_of_injective
    (fun i => (⟨occurrence i, hmap i⟩ :
      {e // e ∈ Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e)}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  simpa only [Fintype.card_coe] using hcard

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_SimpleParallel
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open UniqueGames.Foundations.Target

def Consistent (F : Formula) (i : Fin F.clauses.length) (P : Pattern) : Prop :=
  ∀ k l : Fin 3, (literalAt F i k).variableIndex = (literalAt F i l).variableIndex →
    flipSign (literalAt F i k).positive (P.val k) =
      flipSign (literalAt F i l).positive (P.val l)

instance instDecidableConsistent (F : Formula) (i : Fin F.clauses.length) (P : Pattern) :
    Decidable (Consistent F i P) := inferInstanceAs (Decidable (∀ _k _l, _ → _))

theorem consistent_truth (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (hp : ∃ k, clauseValue F a i k = true) :
    Consistent F i ⟨clauseValue F a i, hp⟩ := by
  intro k l hkl
  change flipSign _ (flipSign _ _) = flipSign _ (flipSign _ _)
  simp only [flipSign_flipSign]
  rw [hkl]

def defaultAssignment (F : Formula) (i : Fin F.clauses.length)
    (v : Fin F.«variables») : Bool :=
  if v = (literalAt F i 0).variableIndex then (literalAt F i 0).positive else false

theorem default_true (F : Formula) (i : Fin F.clauses.length) :
    clauseValue F (defaultAssignment F i) i 0 = true := by
  simp only [clauseValue, Literal.eval, defaultAssignment, ↓reduceIte]
  cases (literalAt F i 0).positive <;> rfl

def defaultPattern (F : Formula) (i : Fin F.clauses.length) : Pattern :=
  ⟨clauseValue F (defaultAssignment F i) i, ⟨0, default_true F i⟩⟩

def normalizePattern (F : Formula) (i : Fin F.clauses.length) (P : Pattern) : Pattern :=
  if Consistent F i P then P else defaultPattern F i

theorem normalize_consistent (F : Formula) (i : Fin F.clauses.length) (P : Pattern) :
    Consistent F i (normalizePattern F i P) := by
  unfold normalizePattern
  split
  · assumption
  · exact consistent_truth F (defaultAssignment F i) i _

theorem normalize_truth (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (hp : ∃ k, clauseValue F a i k = true) :
    normalizePattern F i ⟨clauseValue F a i, hp⟩ = ⟨clauseValue F a i, hp⟩ := by
  exact ite_eq_left (consistent_truth F a i hp)

noncomputable def normalizeLabel (F : Formula) (i : Fin F.clauses.length) (l : Fin 7) : Fin 7 :=
  patternEquiv (normalizePattern F i (patternEquiv.symm l))

noncomputable def simpleGame (F : Formula) (hne : F.clauses ≠ []) : LabelCover :=
  { game F hne with projection := fun e label =>
      (game F hne).projection e (normalizeLabel F ((game F hne).left e) label) }

noncomputable def decodedLabeling (F : Formula) (hne : F.clauses ≠ [])
    (A : (simpleGame F hne).Labeling) : (game F hne).Labeling :=
  (fun i => normalizeLabel F i (A.1 i), A.2)

theorem simple_perfect_complete (F : Formula) (hne : F.clauses ≠ []) (hF : F.Satisfiable) :
    ∃ A : (simpleGame F hne).Labeling, ∀ e, (simpleGame F hne).Satisfies A e := by
  obtain ⟨a, ha⟩ := hF
  let A : (simpleGame F hne).Labeling := honestLabeling F hne a ha
  refine ⟨A, ?_⟩
  intro e
  change (game F hne).Satisfies (decodedLabeling F hne A) e
  have hdecode : decodedLabeling F hne A = honestLabeling F hne a ha := by
    apply Prod.ext
    · change (fun i : Fin F.clauses.length => normalizeLabel F i
        (patternEquiv ⟨clauseValue F a i, _⟩)) =
        (fun i : Fin F.clauses.length => patternEquiv ⟨clauseValue F a i, _⟩)
      funext i
      simp only [normalizeLabel, Equiv.symm_apply_apply, normalize_truth]
    · rfl
  rw [hdecode]
  exact honest_satisfies F hne a ha e

theorem simple_rejection_count (F : Formula) (hne : F.clauses ≠ [])
    (A : (simpleGame F hne).Labeling) :
    (unsatisfiedClauses F (assignmentOf F hne (decodedLabeling F hne A))).card ≤
      (Finset.univ.filter (fun e => ¬(simpleGame F hne).Satisfies A e)).card :=
  rejection_count F hne (decodedLabeling F hne A)

theorem simple_parallel (F : Formula) (hne : F.clauses ≠ [])
    (e e' : Fin (simpleGame F hne).M)
    (hl : (simpleGame F hne).left e = (simpleGame F hne).left e')
    (hr : (simpleGame F hne).right e = (simpleGame F hne).right e') :
    (simpleGame F hne).projection e = (simpleGame F hne).projection e' := by
  funext label
  change (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e').1 at hl
  change (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).variableIndex =
    (literalAt F (finProdFinEquiv.symm e').1 (finProdFinEquiv.symm e').2).variableIndex at hr
  simp only [simpleGame, game, normalizeLabel, Equiv.symm_apply_apply]
  rw [hl] at hr ⊢
  congr 1
  exact normalize_consistent F (finProdFinEquiv.symm e').1 (patternEquiv.symm label) _ _ hr

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
section
namespace VertexCover.ClauseProjection
open UniqueGames
noncomputable section

def falseFormula : BinaryFormula.Formula :=
  ⟨[#v[⟨0,true⟩, ⟨0,true⟩, ⟨0,true⟩], #v[⟨0,false⟩, ⟨0,false⟩, ⟨0,false⟩]]⟩

theorem falseFormula_unsat : ¬falseFormula.Satisfiable := by
  rintro ⟨A, hA⟩
  have hpos := hA #v[⟨0,true⟩, ⟨0,true⟩, ⟨0,true⟩] (by simp [falseFormula])
  have hneg := hA #v[⟨0,false⟩, ⟨0,false⟩, ⟨0,false⟩] (by simp [falseFormula])
  cases h : A 0 <;> simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at hpos hneg

def inputFormula (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD falseFormula

def InputSAT (input : List Bool) : Prop :=
  ∃ F, BinaryEncoding.decodeFormula input = some F ∧ F.Satisfiable

theorem inputFormula_sat (input : List Bool) : (inputFormula input).Satisfiable ↔ InputSAT input := by
  unfold inputFormula InputSAT
  cases h : BinaryEncoding.decodeFormula input with
  | none => simp [falseFormula_unsat]
  | some F => simp

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
abbrev Row (q : ℕ) := (ℕ × ℕ) × RelationTable q
abbrev Data (q : ℕ) := ℕ × List (Row q)
def relationCode {q : ℕ} (r : RelationTable q) : List Bool := r.toList
def rowCode {q : ℕ} : Row q → List Bool := prodBits (prodBits natBits natBits) relationCode
def dataCode {q : ℕ} : Data q → List Bool := prodBits natBits (listBits rowCode)
def rowData {q n m : ℕ} (r : DartRow q n m) : Row q := ((r.tail.val,r.reverseIndex.val),r.relation)
def relationDefault (q : ℕ) : RelationTable q := Vector.replicate (q*q) false
def rowDefault (q : ℕ) : Row q := ((0,0),relationDefault q)

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

@[instance_reducible] noncomputable def relationFintype (q : ℕ) : Fintype (GenericGraphTables.RelationTable q) :=
  Fintype.ofEquiv (Fin (q*q) → Bool)
    {toFun := Vector.ofFn, invFun := fun r i => r[i]
     left_inv := by intro f; funext i; simp
     right_inv := by intro r; ext i; simp}
 theorem relationCode_injective (q : ℕ) : Function.Injective (GenericMachine.relationCode (q := q)) :=
  fun _ _ h => Vector.toList_inj.mp h

abbrev Local (q : ℕ) := (AlphabetGraph.LocalEvent (Fin q) × Fin 6) × Bool

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BoundedBinary
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
open UniqueGames.BinaryEncoding

noncomputable def Poly.natMin : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => min p.1 p.2) :=
  (Poly.natLE.ite (Poly.fst natBits natBits) (Poly.snd natBits natBits)).congr (by
    intro ⟨a,b⟩
    by_cases h : a ≤ b <;> simp [h,Nat.min_def])

namespace CappedBinary

noncomputable def stepPoly : Poly (prodBits enc boolBits) enc step := by
  let s := Poly.fst enc boolBits
  let B := s.comp (Poly.fst natBits natBits)
  let v := s.comp (Poly.snd natBits natBits)
  let b := Poly.snd enc boolBits
  let twice := (v.pair v).comp Poly.natAdd
  let val := b.ite (twice.comp Poly.natSucc) twice
  let cap := (B.pair val).comp Poly.natMin
  exact (B.pair cap).congr (fun ⟨⟨B,v⟩,b⟩ => by cases b <;> simp [step,Nat.bit,two_mul])

noncomputable def foldPoly : Poly (prodBits enc (listBits boolBits)) enc
    (fun p : State × List Bool => p.2.foldl (fun s b => step (s,b)) p.1) := by
  refine Poly.fold boolBits enc false stepPoly (3*Polynomial.X+3) ?_
  intro ⟨B,v⟩ xs pre suf h
  have hh := fold_bound pre B v
  have hs := listBits_append_length boolBits pre suf
  rw [h] at hs
  have hp := listBits_length_pos boolBits pre
  simp only [prodBits,enc,pairBits_length,natBits_length,hh.1,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

theorem foldr (bs : List Bool) (B : ℕ) :
    bs.foldr (fun b s => step (s,b)) (B,0) = (B,min B (bitsValue bs)) := by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    rw [List.foldr_cons,ih]
    simp only [step,bitsValue,min_bit]

end CappedBinary

noncomputable def Poly.decodeBounded : Poly (prodBits natBits id) natBits
    (fun p : ℕ × List Bool => min p.1 (bitsValue p.2)) := by
  let B := Poly.fst natBits id
  let bs := (Poly.snd natBits id).comp Poly.rawToList
  let input := (B.pair (Poly.const (prodBits natBits id) natBits 0)).pair
    (bs.comp (Poly.listReverse boolBits false))
  let c := (input.comp CappedBinary.foldPoly).comp (Poly.snd natBits natBits)
  refine c.congr ?_
  intro ⟨B,bs⟩
  change (bs.reverse.foldl (fun s b => CappedBinary.step (s,b)) (B,0)).2 = _
  rw [List.foldl_reverse,CappedBinary.foldr]

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Cardinal
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
open UniqueGames.BinaryEncoding

def firstName (bs : List Bool) : ℕ := ((parseName bs).getD (0,[])).1

noncomputable def firstNamePoly : Poly id Nat.bits firstName :=
  (NameParser.poly.comp (Poly.getD (prodBits Nat.bits id) (0,[]))).comp (Poly.fst Nat.bits id)

noncomputable def boundedFirstNamePoly : Poly id natBits (fun bs => min bs.length (firstName bs)) := by
  let digits : Poly id id (fun bs => (firstName bs).bits) :=
    firstNamePoly.encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact ((FormulaParser.rawLength.pair digits).comp Poly.decodeBounded).congr (fun bs => by
    simp only [Function.comp_apply,bitsValue_bits])

theorem firstName_encoded (n : ℕ) (rest : List Bool) :
    firstName (nameBits n++rest) = n := by simp [firstName]

theorem names_length (ns : List ℕ) : ns.length ≤ (ns.flatMap nameBits).length := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,nameBits_length]
    omega

theorem firstName_graph (G : ExplicitGraph) : firstName G.bits = G.n := by
  simp only [ExplicitGraph.bits,List.singleton_append]
  exact firstName_encoded _ _

theorem graph_card_le_bits (G : ExplicitGraph) : G.n ≤ G.bits.length := by
  have h := names_length ([G.n] ++ List.range G.n ++ [G.edges.length] ++
    G.edges.flatMap (fun e => [e.1.val,e.2.val]))
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_range] at h
  exact (by omega : G.n ≤ 1+G.n+1+(G.edges.flatMap (fun e => [e.1.val,e.2.val])).length).trans h

noncomputable def Poly.graphCard : Poly ExplicitGraph.bits natBits (fun G => G.n) :=
  boundedFirstNamePoly.encodeCongr ExplicitGraph.bits (fun _ => rfl) (fun G => by
    rw [firstName_graph,Nat.min_eq_right (graph_card_le_bits G)])

theorem firstName_list (xs : List ℕ) : firstName (natListBits xs) = xs.length := by
  exact firstName_encoded _ _

theorem natList_length_le_bits (xs : List ℕ) : xs.length ≤ (natListBits xs).length := by
  exact (Nat.le_succ _).trans (names_length (xs.length::xs))

noncomputable def Poly.natListCard : Poly natListBits natBits (List.length : List ℕ → ℕ) :=
  boundedFirstNamePoly.encodeCongr natListBits (fun _ => rfl) (fun xs => by
    rw [firstName_list,Nat.min_eq_right (natList_length_le_bits xs)])

noncomputable def Poly.natLT : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1<p.2)) :=
  ((((Poly.fst natBits natBits).comp Poly.natSucc).pair (Poly.snd natBits natBits)).comp
    Poly.natLE).congr (fun p => by simp only [Function.comp_apply,Nat.succ_le_iff])

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Approximation
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

namespace VertexCover
open Machine

namespace Approximation
variable {α : ℝ}

theorem coverNumber_le_length (A : Approximation α) (G : ExplicitGraph) :
    G.coverNumber ≤ (A.run G).length := by
  classical
  let L := (A.run G).toFinset
  let e : {n // n ∈ L} ↪ Fin G.n :=
    ⟨fun n => ⟨n.val,A.vertices G n.val (List.mem_toFinset.mp n.property)⟩,
      fun _ _ h => Subtype.ext (congrArg Fin.val h)⟩
  let S : Finset (Fin G.n) := L.attach.map e
  have memS (n : Fin G.n) (hn : n.val ∈ A.run G) : n ∈ S := by
    apply Finset.mem_map.mpr
    exact ⟨⟨n.val,List.mem_toFinset.mpr hn⟩,Finset.mem_attach _ _,Fin.ext rfl⟩
  have hc : G.Cover S := by
    intro p hp
    exact (A.covers G p hp).imp (memS p.1) (memS p.2)
  have hcard : S.card = (A.run G).length := by
    simp only [S,Finset.card_map,Finset.card_attach,L]
    exact List.toFinset_card_of_nodup (A.nodup G)
  simpa only [hcard] using ExplicitGraph.coverNumber_le S hc

noncomputable def cardPoly (A : Approximation α) :
    Machine.Poly ExplicitGraph.bits natBits (fun G => (A.run G).length) :=
  (⟨A.computation,A.finiteAlphabet⟩ : Machine.Poly ExplicitGraph.bits natListBits A.run).comp Machine.Poly.natListCard

noncomputable def testPoly (A : Approximation α) (m : ℕ) :
    Machine.Poly ExplicitGraph.bits boolBits (A.test m) := by
  let lhs := ((Machine.Poly.const ExplicitGraph.bits natBits m).pair A.cardPoly).comp Machine.Poly.natMul
  let rhs := ((Machine.Poly.const ExplicitGraph.bits natBits (m-1)).pair Machine.Poly.graphCard).comp Machine.Poly.natMul
  exact (lhs.pair rhs).comp Machine.Poly.natLT

end Approximation

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BinaryOutput
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
namespace BinaryOutput
abbrev enc : State → List Bool := prodBits natBits id
def body (p : State) : Bool × State :=
  if p.1=0 then (false,p) else (true,(p.1/2,decide (p.1%2=1)::p.2))
def result (p : State) : State := (0,p.1.bits.reverse++p.2)
end BinaryOutput
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Profile
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
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

namespace VertexCover.LabelCover.Query

variable {Φ : LabelCover} {d : ℕ}
@[simp] theorem encode_u (i : Φ.Query d) (A : i.Assignment) (k : Fin d) (h : i.1 < k) :
    (i.encodeAssignment A).1 k = A.1 ⟨i.2.1 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ :=
  dite_eq_left h
@[simp] theorem encode_v (i : Φ.Query d) (A : i.Assignment) (k : Fin d) (h : k < i.1) :
    (i.encodeAssignment A).2 k = A.2 ⟨i.2.2 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ :=
  dite_eq_left h
 theorem encodeAssignment_injective (i : Φ.Query d) : Function.Injective i.encodeAssignment := by
  intro A B h
  apply Prod.ext
  · funext x
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp x.property
    have hh := congrArg (fun P : Profile Φ.qU Φ.qV d => P.1 k) h
    simp only [encode_u i _ k k.property] at hh
    have he : (⟨i.2.1 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {x // x ∈ i.scopeU})=x := Subtype.ext hk
    simpa only [he] using hh
  · funext y
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp y.property
    have hh := congrArg (fun P : Profile Φ.qU Φ.qV d => P.2 k) h
    simp only [encode_v i _ k k.property] at hh
    have he : (⟨i.2.2 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {y // y ∈ i.scopeV})=y := Subtype.ext hk
    simpa only [he] using hh
 theorem encode_injective (i : Φ.Query d) : Function.Injective i.encode := by
  intro A B h
  exact Subtype.ext (i.encodeAssignment_injective h)

def ProfileValid (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) : Prop :=
  (∀ k, ¬i.1 < k → P.1 k=⟨0,Φ.qU_pos⟩) ∧
  (∀ k, ¬k < i.1 → P.2 k=⟨0,Φ.qV_pos⟩) ∧
  (∀ k l : {k : Fin d // i.1 < k}, i.2.1 k=i.2.1 l → P.1 k=P.1 l) ∧
  (∀ k l : {k : Fin d // k < i.1}, i.2.2 k=i.2.2 l → P.2 k=P.2 l) ∧
  (∀ c : Fin Φ.M, ∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // k < i.1},
    Φ.left c=i.2.1 k → Φ.right c=i.2.2 l → Φ.projection c (P.1 k)=P.2 l)
instance instDecidableProfileValid (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) : Decidable (i.ProfileValid P) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
 theorem encode_valid (i : Φ.Query d) (A : i.LocalLabel) : i.ProfileValid (i.encode A) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk; exact dite_eq_right hk
  · intro k hk; exact dite_eq_right hk
  · intro k l he
    simp only [encode,encode_u i _ k k.property,encode_u i _ l l.property]
    exact congrArg A.val.1 (Subtype.ext he)
  · intro k l he
    simp only [encode,encode_v i _ k k.property,encode_v i _ l l.property]
    exact congrArg A.val.2 (Subtype.ext he)
  · intro c k l hx hy
    simp only [encode,encode_u i _ k k.property,encode_v i _ l l.property]
    have hc := A.property c (hx.symm ▸ Finset.mem_image.mpr ⟨k,by simp,rfl⟩)
      (hy.symm ▸ Finset.mem_image.mpr ⟨l,by simp,rfl⟩)
    have ex : (⟨i.2.1 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {x // x ∈ i.scopeU}) =
        ⟨Φ.left c,hx.symm ▸ Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ := Subtype.ext hx.symm
    have ey : (⟨i.2.2 l,Finset.mem_image.mpr ⟨l,by simp,rfl⟩⟩ : {y // y ∈ i.scopeV}) =
        ⟨Φ.right c,hy.symm ▸ Finset.mem_image.mpr ⟨l,by simp,rfl⟩⟩ := Subtype.ext hy.symm
    rw [ex,ey]
    exact hc

noncomputable def positionU (i : Φ.Query d) (x : {x // x ∈ i.scopeU}) : {k : Fin d // i.1 < k} :=
  (Finset.mem_image.mp x.property).choose
noncomputable def positionV (i : Φ.Query d) (y : {y // y ∈ i.scopeV}) : {k : Fin d // k < i.1} :=
  (Finset.mem_image.mp y.property).choose
 theorem positionU_eq (i : Φ.Query d) (x : {x // x ∈ i.scopeU}) : i.2.1 (i.positionU x)=x :=
  (Finset.mem_image.mp x.property).choose_spec.2
 theorem positionV_eq (i : Φ.Query d) (y : {y // y ∈ i.scopeV}) : i.2.2 (i.positionV y)=y :=
  (Finset.mem_image.mp y.property).choose_spec.2
noncomputable def decode (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) (hP : i.ProfileValid P) : i.LocalLabel :=
  ⟨(fun x => P.1 (i.positionU x),fun y => P.2 (i.positionV y)),fun c hx hy =>
    hP.2.2.2.2 c (i.positionU ⟨Φ.left c,hx⟩) (i.positionV ⟨Φ.right c,hy⟩)
      (i.positionU_eq ⟨Φ.left c,hx⟩).symm (i.positionV_eq ⟨Φ.right c,hy⟩).symm⟩
 theorem encode_decode (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) (hP : i.ProfileValid P) :
    i.encode (i.decode P hP)=P := by
  apply Prod.ext
  · funext k
    dsimp only [encode,encodeAssignment]
    split_ifs with hk
    · dsimp only [decode]
      exact hP.2.2.1 _ ⟨k,hk⟩ (i.positionU_eq ⟨i.2.1 ⟨k,hk⟩,Finset.mem_image.mpr ⟨⟨k,hk⟩,by simp,rfl⟩⟩)
    · exact (hP.1 k hk).symm
  · funext k
    dsimp only [encode,encodeAssignment]
    split_ifs with hk
    · dsimp only [decode]
      exact hP.2.2.2.1 _ ⟨k,hk⟩ (i.positionV_eq ⟨i.2.2 ⟨k,hk⟩,Finset.mem_image.mpr ⟨⟨k,hk⟩,by simp,rfl⟩⟩)
    · exact (hP.2.1 k hk).symm
 theorem valid_iff (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) :
    i.ProfileValid P ↔ ∃ A : i.LocalLabel, i.encode A=P := by
  constructor
  · intro h; exact ⟨i.decode P h,i.encode_decode P h⟩
  · rintro ⟨A,rfl⟩; exact i.encode_valid A
end VertexCover.LabelCover.Query
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ProfileCompat
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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

namespace VertexCover.LabelCover.Query
variable {Φ : LabelCover} {d : ℕ}
def ProfilePair (i j : Φ.Query d) (P R : Profile Φ.qU Φ.qV d) : Prop :=
  (∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // j.1 < k},
    i.2.1 k=j.2.1 l → P.1 k=R.1 l) ∧
  (∀ k : {k : Fin d // k < i.1}, ∀ l : {k : Fin d // k < j.1},
    i.2.2 k=j.2.2 l → P.2 k=R.2 l) ∧
  (∀ c : Fin Φ.M, ∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // k < j.1},
    Φ.left c=i.2.1 k → Φ.right c=j.2.2 l → Φ.projection c (P.1 k)=R.2 l)
instance instDecidableProfilePair (i j : Φ.Query d) (P R : Profile Φ.qU Φ.qV d) : Decidable (ProfilePair i j P R) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def LabelPair (i j : Φ.Query d) (A : i.LocalLabel) (B : j.LocalLabel) : Prop :=
  (∀ x (hi : x ∈ i.scopeU) (hj : x ∈ j.scopeU), A.val.1 ⟨x,hi⟩=B.val.1 ⟨x,hj⟩) ∧
  (∀ y (hi : y ∈ i.scopeV) (hj : y ∈ j.scopeV), A.val.2 ⟨y,hi⟩=B.val.2 ⟨y,hj⟩) ∧
  (∀ c (hi : Φ.left c ∈ i.scopeU) (hj : Φ.right c ∈ j.scopeV),
    Φ.projection c (A.val.1 ⟨Φ.left c,hi⟩)=B.val.2 ⟨Φ.right c,hj⟩)
 theorem encode_at_u (i : Φ.Query d) (A : i.LocalLabel) (k : {k : Fin d // i.1 < k})
    (x : {x // x ∈ i.scopeU}) (h : i.2.1 k=x) : (i.encode A).1 k=A.val.1 x := by
  simp only [encode,encode_u i _ k k.property]
  exact congrArg A.val.1 (Subtype.ext h)
 theorem encode_at_v (i : Φ.Query d) (A : i.LocalLabel) (k : {k : Fin d // k < i.1})
    (y : {y // y ∈ i.scopeV}) (h : i.2.2 k=y) : (i.encode A).2 k=A.val.2 y := by
  simp only [encode,encode_v i _ k k.property]
  exact congrArg A.val.2 (Subtype.ext h)
 theorem profilePair_iff (i j : Φ.Query d) (A : i.LocalLabel) (B : j.LocalLabel) :
    ProfilePair i j (i.encode A) (j.encode B) ↔ LabelPair i j A B := by
  constructor
  · rintro ⟨hu,hv,hc⟩
    refine ⟨?_,?_,?_⟩
    · intro x hi hj
      have ei := i.positionU_eq ⟨x,hi⟩
      have ej := j.positionU_eq ⟨x,hj⟩
      have h := hu _ _ (ei.trans ej.symm)
      rwa [i.encode_at_u A _ ⟨x,hi⟩ ei,j.encode_at_u B _ ⟨x,hj⟩ ej] at h
    · intro y hi hj
      have ei := i.positionV_eq ⟨y,hi⟩
      have ej := j.positionV_eq ⟨y,hj⟩
      have h := hv _ _ (ei.trans ej.symm)
      rwa [i.encode_at_v A _ ⟨y,hi⟩ ei,j.encode_at_v B _ ⟨y,hj⟩ ej] at h
    · intro c hi hj
      have ei := i.positionU_eq ⟨Φ.left c,hi⟩
      have ej := j.positionV_eq ⟨Φ.right c,hj⟩
      have h := hc c _ _ ei.symm ej.symm
      rwa [i.encode_at_u A _ ⟨Φ.left c,hi⟩ ei,j.encode_at_v B _ ⟨Φ.right c,hj⟩ ej] at h
  · rintro ⟨hu,hv,hc⟩
    refine ⟨?_,?_,?_⟩
    · intro k l h
      have hi : i.2.1 k ∈ i.scopeU := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      have hj : i.2.1 k ∈ j.scopeU := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,h.symm⟩
      rw [i.encode_at_u A k ⟨_,hi⟩ rfl,j.encode_at_u B l ⟨_,hj⟩ h.symm]
      exact hu _ hi hj
    · intro k l h
      have hi : i.2.2 k ∈ i.scopeV := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      have hj : i.2.2 k ∈ j.scopeV := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,h.symm⟩
      rw [i.encode_at_v A k ⟨_,hi⟩ rfl,j.encode_at_v B l ⟨_,hj⟩ h.symm]
      exact hv _ hi hj
    · intro c k l hx hy
      have hi : Φ.left c ∈ i.scopeU := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hx.symm⟩
      have hj : Φ.right c ∈ j.scopeV := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,hy.symm⟩
      rw [i.encode_at_u A k ⟨_,hi⟩ hx.symm,j.encode_at_v B l ⟨_,hj⟩ hy.symm]
      exact hc c hi hj
end VertexCover.LabelCover.Query

namespace VertexCover.LabelCover
 theorem compatible_pair_iff (Φ : LabelCover) {d : ℕ} (I : Finset (Φ.Coordinate d)) :
    Φ.Compatible I ↔
      (∀ p ∈ I, ∀ q ∈ I, p.1=q.1 → p=q) ∧
      (∀ p ∈ I, ∀ q ∈ I, Query.LabelPair p.1 q.1 p.2 q.2) := by
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨h₁,fun p hp q hq => ⟨h₂ p hp q hq,h₃ p hp q hq,h₄ p hp q hq⟩⟩
  · rintro ⟨h₁,h⟩
    exact ⟨h₁,fun p hp q hq => (h p hp q hq).1,
      fun p hp q hq => (h p hp q hq).2.1,fun p hp q hq => (h p hp q hq).2.2⟩
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ProfileSlot
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
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

namespace VertexCover.LabelCover.Query

variable {Φ : LabelCover} {d : ℕ}
noncomputable def profileLabels (i : Φ.Query d) : List (Profile Φ.qU Φ.qV d) := by
  classical
  exact Finset.univ.toList.filter (fun P => decide (i.ProfileValid P))
@[simp] theorem mem_profileLabels (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) :
    P ∈ i.profileLabels ↔ i.ProfileValid P := by
  classical
  simp [profileLabels]
 theorem profileLabels_nodup (i : Φ.Query d) : i.profileLabels.Nodup := by
  classical
  exact (Finset.nodup_toList _).filter _
 theorem profileLabels_length (i : Φ.Query d) : i.profileLabels.length=Fintype.card i.LocalLabel := by
  classical
  have hp : i.profileLabels.Perm (i.labels.map i.encode) := by
    apply (List.perm_ext_iff_of_nodup (i.profileLabels_nodup) ((by simp [labels] : i.labels.Nodup).map i.encode_injective)).mpr
    intro P
    simp only [mem_profileLabels,List.mem_map,mem_labels,true_and,i.valid_iff]
  simpa using hp.length_eq
noncomputable def profileSlot (i : Φ.Query d) (A : i.LocalLabel) : Fin (Φ.WeightDimension d) :=
  ⟨i.profileLabels.idxOf (i.encode A),lt_of_lt_of_le
    (by simpa only [profileLabels_length] using (List.idxOf_lt_length_iff.mpr ((i.mem_profileLabels _).mpr (i.encode_valid A)))) i.localLabel_card_le⟩
 theorem profileSlot_injective (i : Φ.Query d) : Function.Injective i.profileSlot := by
  classical
  intro A B h
  apply i.encode_injective
  exact (List.idxOf_inj ((i.mem_profileLabels _).mpr (i.encode_valid A))).mp (congrArg Fin.val h)
noncomputable def slotPermutation (i : Φ.Query d) : Equiv.Perm (Fin (Φ.WeightDimension d)) :=
  (Equiv.Perm.exists_extending_pair i.slot i.profileSlot i.slot_injective i.profileSlot_injective).choose
 theorem slotPermutation_apply (i : Φ.Query d) (A : i.LocalLabel) :
    i.slotPermutation (i.slot A)=i.profileSlot A :=
  (Equiv.Perm.exists_extending_pair i.slot i.profileSlot i.slot_injective i.profileSlot_injective).choose_spec A
end VertexCover.LabelCover.Query

namespace VertexCover.LabelCover

noncomputable def profileVertexEquiv (Φ : LabelCover) (d : ℕ) : Φ.Vertex d ≃ Φ.Vertex d where
  toFun v := (v.1,fun j k => v.2 j ((Φ.query v.1 j).slotPermutation k))
  invFun v := (v.1,fun j k => v.2 j ((Φ.query v.1 j).slotPermutation.symm k))
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_DescriptorMath
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
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
abbrev ProfileRep (a b d : ℕ) := TracePos d × Query.Profile a b d
abbrev Descriptor (a b d : ℕ) :=
  (ProfileRep a b d → Bool) × ((TracePos d × TracePos d → Bool) ×
    ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d))
namespace Descriptor
variable {a b d : ℕ}
abbrev Rep (D : Descriptor a b d) := {r : ProfileRep a b d // D.1 r=true}
noncomputable def slot (D : Descriptor a b d) (r : ProfileRep a b d) : ℕ := by
  classical
  exact (Finset.univ.toList.filter (fun P => D.1 (r.1,P))).idxOf r.2
noncomputable def term (D : Descriptor a b d) (r : ProfileRep a b d) : ℝ :=
  ∑ x : TracePos d, if D.2.1 (x,r.1)=true then
    if h : D.slot r < (max a b)^(d-1) then (gridRational d (D.2.2.2 x ⟨D.slot r,h⟩) : ℝ) else 0
    else 0
def Good (D : Descriptor a b d) (S : Finset D.Rep) : Prop :=
  (∀ r ∈ S, ∀ s ∈ S, D.2.1 (r.val.1,s.val.1)=true → r=s) ∧
  (∀ r ∈ S, ∀ s ∈ S, D.2.2.1 (r.val,s.val)=true)
noncomputable def test (t : ℝ) (D : Descriptor a b d) : Bool := by
  classical
  exact decide (∀ S : Finset D.Rep, D.Good S → |∑ r ∈ S, D.term r.val| ≤ 2*t)
end Descriptor

variable {Φ : LabelCover} {d : ℕ}
def diagram (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) : Descriptor Φ.qU Φ.qV d :=
  (fun r => decide ((Q r.1).ProfileValid r.2),
    (fun xy => decide (Q xy.1=Q xy.2), (fun rs => decide (Query.ProfilePair (Q rs.1.1) (Q rs.2.1) rs.1.2 rs.2.2),W)))
noncomputable def diagramCoordinate (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : Φ.Coordinate d :=
  ⟨Q r.val.1,(Q r.val.1).decode r.val.2 (of_decide_eq_true r.property)⟩
noncomputable def diagramSum (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) : Φ.Coordinate d → ℝ :=
  ∑ x, Φ.increment (Q x) (fun k => (gridRational d (W x ((Q x).slotPermutation k)) : ℝ))
 theorem diagram_coordinate_encode (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (Q r.val.1).encode (diagramCoordinate Q W r).2=r.val.2 :=
  (Q r.val.1).encode_decode r.val.2 (of_decide_eq_true r.property)
 theorem diagram_slot (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (diagram Q W).slot r.val=((Q r.val.1).profileSlot (diagramCoordinate Q W r).2).val := by
  classical
  simp only [Descriptor.slot,diagram,Query.profileSlot,Query.profileLabels,diagram_coordinate_encode]
 theorem diagram_term (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (diagram Q W).term r.val=diagramSum Q W (diagramCoordinate Q W r) := by
  classical
  rw [Descriptor.term]
  simp only [diagramSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  change (if decide (Q x=Q r.val.1)=true then
    if h : (diagram Q W).slot r.val < Φ.WeightDimension d then
      (gridRational d (W x ⟨_,h⟩) : ℝ) else 0 else 0)=_
  simp only [decide_eq_true_eq]
  by_cases h : Q x=Q r.val.1
  · have hs := diagram_slot Q W r
    have ht : (diagram Q W).slot r.val < Φ.WeightDimension d := hs.symm ▸ ((Q r.val.1).profileSlot _).isLt
    rw [ite_eq_left h,dite_eq_left ht]
    simp only [h,diagramCoordinate,increment_same,Query.slotPermutation_apply]
    exact congrArg (fun k => (gridRational d (W x k) : ℝ)) (Fin.ext hs)
  · rw [ite_eq_right h]
    exact (Φ.increment_other (Q x) _ (diagramCoordinate Q W r) (Ne.symm h)).symm
 theorem diagram_good (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (S : Finset (diagram Q W).Rep) :
    (diagram Q W).Good S ↔ Set.InjOn (diagramCoordinate Q W) S ∧
      Φ.Compatible (S.image (diagramCoordinate Q W)) := by
  classical
  have pair (r s : (diagram Q W).Rep) :
      (diagram Q W).2.2.1 (r.val,s.val)=true ↔
        Query.LabelPair (diagramCoordinate Q W r).1 (diagramCoordinate Q W s).1
          (diagramCoordinate Q W r).2 (diagramCoordinate Q W s).2 := by
    simp only [diagram,decide_eq_true_eq]
    rw [← diagram_coordinate_encode Q W r,← diagram_coordinate_encode Q W s]
    exact Query.profilePair_iff _ _ _ _
  constructor
  · rintro ⟨hu,hp⟩
    have hi : Set.InjOn (diagramCoordinate Q W) S := by
      intro r hr s hs he
      exact hu r hr s hs (by simp only [diagram,decide_eq_true_eq]; exact congrArg Sigma.fst he)
    refine ⟨hi,(Φ.compatible_pair_iff _).mpr ⟨?_,?_⟩⟩
    · intro p hp' q hq' he
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq'
      exact congrArg (diagramCoordinate Q W) (hu r hr s hs (by change Q r.val.1=Q s.val.1 at he; exact decide_eq_true he))
    · intro p hp' q hq'
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq'
      exact (pair r s).mp (hp r hr s hs)
  · rintro ⟨hi,hc⟩
    obtain ⟨hu,hp⟩ := (Φ.compatible_pair_iff _).mp hc
    refine ⟨?_,?_⟩
    · intro r hr s hs he
      exact hi hr hs (hu _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩) _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
        (by change decide (Q r.val.1=Q s.val.1)=true at he; exact of_decide_eq_true he))
    · intro r hr s hs
      exact (pair r s).mpr (hp _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩) _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩))
 theorem diagram_test (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) (t : ℝ) :
    (diagram Q W).test t=true ↔ Φ.compatibilityNorm (diagramSum Q W) ≤ 2*t := by
  classical
  let B := Finset.univ.image Q
  have hz (p : Φ.Coordinate d) (hp : p.1 ∉ B) : diagramSum Q W p=0 := by
    simp only [diagramSum,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro x _
    exact Φ.increment_other _ _ _ (fun he => hp (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,he.symm⟩))
  have hc (p : Φ.Coordinate d) (hp : p.1 ∈ B) : ∃ r, diagramCoordinate Q W r=p := by
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hp
    rcases p with ⟨i,A⟩
    dsimp at hx
    subst i
    let r : (diagram Q W).Rep := ⟨(x,(Q x).encode A),decide_eq_true ((Q x).encode_valid A)⟩
    refine ⟨r,?_⟩
    change (⟨Q x,(Q x).decode ((Q x).encode A) _⟩ : Φ.Coordinate d)=⟨Q x,A⟩
    congr 1
    apply (Q x).encode_injective
    exact (Q x).encode_decode _ _
  rw [Φ.norm_le_representations (diagramCoordinate Q W) _ B hz hc]
  simp only [Descriptor.test,decide_eq_true_eq,diagram_term]
  constructor
  · intro h S hi hs; exact h S ((diagram_good Q W S).mpr ⟨hi,hs⟩)
  · intro h S hs
    obtain ⟨hi,hc'⟩ := (diagram_good Q W S).mp hs
    exact h S hi hc'
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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateProjectionBatchLower
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid
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
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem privateProjection_batch_lower (Φ : LabelCover) {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (ν : ℝ)
    (hscale : 16*(h:ℝ)+32*(h:ℝ)^2 ≤ ν*d/2)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (henergy : ν*d ≤ (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA)) :
    (d.choose h:ℝ)*ν*h/2 ≤
      ∑ J ∈ batches d h, ∑ j ∈ J,
        (Φ.restrictionForm d).energy (Φ.privateProjection J j (Φ.restrictionFunction A hA)) := by
  have hb := Φ.privateProjection_batch_bound hh A hA
  have hC1 : (0:ℝ) ≤ (d-1).choose (h-1) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left henergy hC1
  have hs := mul_le_mul_of_nonneg_left hscale hC1
  have hp := batch_pair_scale d h hd hh
  have ht := batch_triple_scale d h hd hh
  have he := choose_step d h (by omega) (by omega)
  have he' : ((d-1).choose (h-1):ℝ)*ν*d = (d.choose h:ℝ)*ν*h := by
    calc
      _ = ν*((d:ℝ)*((d-1).choose (h-1):ℝ)) := by ring
      _ = _ := by rw [he]; ring
  nlinarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateProjectionCoordinateVariance
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.encode_u _root_.OAI.VertexCover.LabelCover.Query.encode_v _root_.OAI.VertexCover.LabelCover.Query.mem_profileLabels
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
open MeasureTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem spliceSeeds_at_inside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J)) :
    Φ.spliceSeeds J frozen hidden e = hidden e := by
  simp only [spliceSeeds, dite_eq_left e.2]

theorem spliceSeeds_at_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : PositionPair d)
    (he : e ∉ internalPairs J) : Φ.spliceSeeds J frozen hidden e = frozen e := by
  simp only [spliceSeeds, dite_eq_right he]

noncomputable def privateFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (j : Fin d) (seed : Φ.Seeds d) : Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun t => Φ.privateSeedKey J j t = Φ.privateSeedKey J j seed)

@[simp] theorem mem_privateFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (j : Fin d) (seed t : Φ.Seeds d) : t ∈ Φ.privateFiber J j seed ↔
      Φ.privateSeedKey J j t = Φ.privateSeedKey J j seed := by
  classical
  simp only [privateFiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem spliceSeeds_restrict_of_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen seed : Φ.Seeds d) (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e) :
    Φ.spliceSeeds J frozen (fun e : ↥(internalPairs J) => seed e) = seed := by
  funext e
  by_cases he : e ∈ internalPairs J
  · simp only [spliceSeeds, dite_eq_left he]
  · simpa only [spliceSeeds, dite_eq_right he] using ho e he

noncomputable def privateFiberEquiv (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e) :
    Φ.ownFiber J frozen j (Φ.query seed j) ≃ Φ.privateFiber J j seed := by
  classical
  have reconstruct : ∀ t : Φ.privateFiber J j seed,
      Φ.spliceSeeds J frozen (fun e : ↥(internalPairs J) => t.1 e) = t.1 := by
    intro t
    apply Φ.spliceSeeds_restrict_of_outside
    intro e he
    have ht := (Φ.privateSeedKey_eq_iff J j t.1 seed).mp ((Φ.mem_privateFiber J j seed t.1).mp t.2)
    exact (ho e he).trans (ht.1 e he).symm
  exact {
    toFun := fun hidden => ⟨Φ.spliceSeeds J frozen hidden.1, by
      apply (Φ.mem_privateFiber J j seed _).mpr
      apply (Φ.privateSeedKey_eq_iff J j _ _).mpr
      exact ⟨fun e he => (Φ.spliceSeeds_at_outside J frozen hidden.1 e he).trans (ho e he),
        (Φ.mem_ownFiber J frozen j (Φ.query seed j) hidden.1).mp hidden.2⟩⟩
    invFun := fun t => ⟨fun e => t.1 e, by
      apply (Φ.mem_ownFiber J frozen j (Φ.query seed j) _).mpr
      rw [reconstruct t]
      exact ((Φ.privateSeedKey_eq_iff J j t.1 seed).mp
        ((Φ.mem_privateFiber J j seed t.1).mp t.2)).2⟩
    left_inv := fun hidden => by
      apply Subtype.ext
      funext e
      exact Φ.spliceSeeds_at_inside J frozen hidden.1 e
    right_inv := fun t => Subtype.ext (reconstruct t) }

theorem fiberAverage_eq_finiteMean {S T : Type*} [Fintype S]
    (q : S → T) (f : S → ℝ) (i : T) (ts : Finset S)
    (ht : ∀ s, s ∈ ts ↔ q s = i) :
    VertexCover.Average.fiberAverage q (fun _ => f) i =
      VertexCover.finiteMean (fun s : ts => f s) := by
  classical
  have he : Finset.univ.filter (fun s => q s = i) = ts := by
    ext s
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (ht s).symm
  unfold VertexCover.Average.fiberAverage
  rw [he, VertexCover.Average.finiteMean_finset ts f]

theorem privateSeedProjection_fiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (f : Φ.RestrictionSpace d) (s : Φ.RestrictionWeights d) :
    Φ.privateSeedProjection J j f seed s =
      VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j (Φ.query seed j) =>
        f (Φ.spliceSeeds J frozen hidden.1) s) := by
  classical
  change conditionMap _ f seed s = _
  rw [conditionMap_apply_function]
  calc
    _ = VertexCover.finiteMean (fun t : Φ.privateFiber J j seed => f t.1 s) := by
      exact fiberAverage_eq_finiteMean (Φ.privateSeedKey J j) (fun t => f t s)
        (Φ.privateSeedKey J j seed) (Φ.privateFiber J j seed)
        (fun t => Φ.mem_privateFiber J j seed t)
    _ = _ := (VertexCover.finiteMean_equiv (Φ.privateFiberEquiv J frozen j seed ho)
      (fun t : Φ.privateFiber J j seed => f t.1 s)).symm

theorem otherWeightProjection_apply (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : J) (f : Φ.RestrictionSpace d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.otherWeightProjection J j f seed s =
      ∫ t, f seed (splice J s (Function.update t j (s j)))
        ∂CompactCube.blockLaw J (Fin (Φ.WeightDimension d)) := by
  change productMap (fun i => (average (CompactCube.law (Fin (Φ.WeightDimension d))) i).lift)
    (J.erase j).toList f seed s = _
  rw [productMap_lift, product_average_apply _ _ (J.erase j).nodup_toList,
    Finset.toList_toFinset]
  exact integral_plug_erase _ J j (f seed) s

theorem realWeights_splice (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (s : Φ.RestrictionWeights d)
    (t : J → Fin (Φ.WeightDimension d) → CompactCube.Interval) :
    CompactCube.realWeights (splice J s t) =
      Φ.spliceWeights J (CompactCube.realWeights s) (CompactCube.realWeights t) := by
  classical
  funext i k
  by_cases hi : i ∈ J
  · simp only [splice, spliceWeights, CompactCube.realWeights, dite_eq_left hi]
  · simp only [splice, spliceWeights, CompactCube.realWeights, dite_eq_right hi]

theorem otherWeightProjection_separator_splice (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hidden : Φ.HiddenSeeds J) (s : Φ.RestrictionWeights d) :
    Φ.otherWeightProjection J j (Φ.restrictionFunction A hA)
      (Φ.spliceSeeds J frozen hidden) s =
      ∫ other, Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J
        (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        (Function.update other j (CompactCube.realWeights s j)) ∂Φ.batchLaw J := by
  classical
  rw [Φ.otherWeightProjection_apply]
  simp only [restrictionFunction_apply, Φ.realWeights_splice, CompactCube.realWeights_update]
  simp_rw [← Φ.batchFunction_is_restriction J frozen (CompactCube.realWeights s) A hA]
  apply CompactCube.integral_realWeights (f := fun other : Φ.BatchWeights J =>
    Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J
      (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
      (Function.update other j (CompactCube.realWeights s j)))
  exact ((Φ.batchFunction_continuous _ J _ A hA).comp
    (continuous_id.update j continuous_const)).measurable.aestronglyMeasurable

theorem privateAverageProjection_separator (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    Φ.privateAverageProjection J j (Φ.restrictionFunction A hA) seed s =
      Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) (CompactCube.realWeights s j) := by
  change Φ.privateSeedProjection J j
    (Φ.otherWeightProjection J j (Φ.restrictionFunction A hA)) seed s = _
  rw [Φ.privateSeedProjection_fiber J frozen j seed ho]
  unfold ownMean
  congr 1
  funext hidden
  exact Φ.otherWeightProjection_separator_splice J frozen j A hA hidden.1 s

theorem outsideSum_update (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (j : J)
    (x : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.outsideSum J frozen (Function.update s j x) = Φ.outsideSum J frozen s := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := by
    intro h
    exact (Finset.mem_compl.mp hk) (h ▸ j.2)
  rw [Function.update_of_ne hkj]

theorem privateProjection_separator (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s =
      Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) (CompactCube.realWeights s j) -
      ∫ x, Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) x ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
  classical
  change Φ.privateAverageProjection J j (Φ.restrictionFunction A hA) seed s -
    Φ.weightProjection j (Φ.privateAverageProjection J j (Φ.restrictionFunction A hA)) seed s = _
  rw [Φ.privateAverageProjection_separator J frozen j seed ho,
    Φ.weightProjection_apply]
  simp_rw [Φ.privateAverageProjection_separator J frozen j seed ho,
    CompactCube.realWeights_update, Φ.outsideSum_update J frozen _ j,
    Function.update_self]
  congr 1
  exact CompactCube.integral_coe
    (Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.measurable.aestronglyMeasurable

theorem privateProjection_coordinate_variance (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    (∫ x, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed
      (Function.update s j x))^2 ∂CompactCube.law (Fin (Φ.WeightDimension d))) =
      ProbabilityTheory.variance (Φ.ownMean J frozen
        (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j))
        (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) := by
  classical
  simp_rw [Φ.privateProjection_separator J frozen j seed ho,
    CompactCube.realWeights_update, Φ.outsideSum_update J frozen _ j,
    Function.update_self]
  rw [ProbabilityTheory.variance_eq_integral
    (Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.measurable.aemeasurable]
  apply CompactCube.integral_coe (f := fun x =>
    (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j) x -
      ∫ y, Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j) y
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)))^2)
  exact (((Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.sub
    continuous_const).pow 2).measurable.aestronglyMeasurable

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateTotalEnergyLaw
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
namespace VertexCover.Restriction
open scoped BigOperators

theorem finiteMean_splice {ι X : Type*} [Fintype ι] [Fintype X] [Nonempty X]
    [DecidableEq ι] (J : Finset ι) (f : (ι → X) → ℝ) :
    VertexCover.finiteMean (fun s => VertexCover.finiteMean (fun t => f (splice J s t))) =
      VertexCover.finiteMean f := by
  rw [← VertexCover.finiteMean_product (fun p : (ι → X) × (J → X) => f (splice J p.1 p.2))]
  exact (VertexCover.finiteMean_equiv (spliceSwap J)
    (fun p : (ι → X) × (J → X) => f p.1)).trans (VertexCover.finiteMean_product_fst f)

end VertexCover.Restriction

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem ownVariance_frozen_continuous (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))) := by
  let F : C(Φ.RestrictionWeights d, ℝ) :=
    ⟨fun s => (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2,
      (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed).continuous.pow 2⟩
  have he : (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))) =
        (fun s => EnergyForm.Projection.average (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d) F s) := by
    funext s
    rw [EnergyForm.Projection.average_apply]
    exact (Φ.privateProjection_coordinate_variance J frozen j seed ho A hA s).symm
  rw [he]
  exact (EnergyForm.Projection.average (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d) F).continuous

theorem ownVariance_frozen_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Integrable (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d))))
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) :=
  (Φ.ownVariance_frozen_continuous J frozen j seed ho A hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem privateProjection_integral_variance (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∫ s, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2
      ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) =
    ∫ s : Φ.RestrictionWeights d,
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))
      ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
  classical
  calc
    _ = ∫ s, ∫ x, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed
        (Function.update s j x))^2 ∂CompactCube.law (Fin (Φ.WeightDimension d))
        ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
      symm
      apply VertexCover.Product.integral_update_right
        (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d)
        (f := fun s => (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2)
      exact ((Φ.privateProjection J j (Φ.restrictionFunction A hA) seed).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (Φ.privateProjection_coordinate_variance J frozen j seed ho A hA))

theorem finiteMean_spliceSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (f : Φ.Seeds d → ℝ) :
    VertexCover.finiteMean (fun frozen => VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      f (Φ.spliceSeeds J frozen hidden))) = VertexCover.finiteMean f := by
  classical
  have : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  exact finiteMean_splice (internalPairs J) f

theorem ownTotalVariance_frozen_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Integrable (fun s : Φ.RestrictionWeights d => Φ.ownTotalVariance J frozen
      (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA)
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  apply integrable_finsetSum
  intro j _
  apply VertexCover.integrable_finiteMean
  intro hidden
  exact Φ.ownVariance_frozen_integrable J frozen j (Φ.spliceSeeds J frozen hidden)
    (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA

theorem privateTotal_energy_law (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : J, (Φ.restrictionForm d).energy
      (Φ.privateProjection J j (Φ.restrictionFunction A hA))) =
      VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
        ∫ s : Φ.RestrictionWeights d, Φ.ownTotalVariance J frozen
          (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
          ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  let V := fun (frozen : Φ.Seeds d) (j : J) (hidden : Φ.HiddenSeeds J)
      (s : Φ.RestrictionWeights d) =>
    variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
      A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))
  have hI : ∀ frozen j hidden, Integrable (V frozen j hidden)
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro frozen j hidden
    exact Φ.ownVariance_frozen_integrable J frozen j (Φ.spliceSeeds J frozen hidden)
      (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA
  have he : ∀ j : J, (Φ.restrictionForm d).energy
      (Φ.privateProjection J j (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
        ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J => V frozen j hidden s)
          ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro j
    rw [restrictionForm_energy]
    calc
      _ = VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
          VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
            ∫ s, (Φ.privateProjection J j (Φ.restrictionFunction A hA)
              (Φ.spliceSeeds J frozen hidden) s)^2
              ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) :=
        (Φ.finiteMean_spliceSeeds J (fun seed : Φ.Seeds d =>
          ∫ s : Φ.RestrictionWeights d,
            (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2
            ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))).symm
      _ = VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
          VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
            ∫ s, V frozen j hidden s
              ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) := by
        apply congrArg VertexCover.finiteMean
        funext frozen
        apply congrArg VertexCover.finiteMean
        funext hidden
        exact Φ.privateProjection_integral_variance J frozen j (Φ.spliceSeeds J frozen hidden)
          (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA
      _ = _ := by
        apply congrArg VertexCover.finiteMean
        funext frozen
        exact (VertexCover.integral_finiteMean _ _ (hI frozen j)).symm
  simp_rw [he]
  rw [← VertexCover.finiteMean_sum]
  apply congrArg VertexCover.finiteMean
  funext frozen
  unfold ownTotalVariance
  exact (integral_finsetSum _ (fun j _ =>
    VertexCover.integrable_finiteMean _ _ (hI frozen j))).symm

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_RestrictionFrozen
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.VertexCover.LabelCover.Query.encode_u _root_.OAI.VertexCover.LabelCover.Query.encode_v _root_.OAI.VertexCover.LabelCover.Query.mem_profileLabels
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
open MeasureTheory ProbabilityTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem restrictionFunction_energy_variance (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        variance (fun s => Φ.separator A hA (Φ.continuousSum seed s))
          (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) := by
  rw [restrictionForm_energy]
  apply congrArg VertexCover.finiteMean
  funext seed
  rw [variance_eq_integral
    (Φ.separator_continuousSum_continuous A hA seed).measurable.aemeasurable,
    Φ.separator_continuousSum_mean_zero]
  simp only [sub_zero, restrictionFunction_apply]
  exact CompactCube.integral_realWeights
    ((Φ.separator_continuousSum_continuous A hA seed).pow 2).measurable.aestronglyMeasurable

theorem restriction_frozen_exists (Φ : LabelCover) {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (hhd : h ≤ d) (ν : ℝ) (hν : 0 < ν)
    (hscale : 16*(h:ℝ)+32*(h:ℝ)^2 ≤ ν*d/2)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (henergy : ν*d ≤ (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA)) :
    ∃ J : Finset (Fin d), J.card = h ∧ ∃ frozen : Φ.Seeds d,
      ∃ s : Φ.RestrictionWeights d,
        ν*h/4 ≤ Φ.ownTotalVariance J frozen
          (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA := by
  classical
  have : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  by_contra hno
  push Not at hno
  have hbound (J : Finset (Fin d)) (hJ : J ∈ batches d h) :
      (∑ j ∈ J, (Φ.restrictionForm d).energy
        (Φ.privateProjection J j (Φ.restrictionFunction A hA))) ≤ ν*h/4 := by
    rw [← Finset.sum_coe_sort J, Φ.privateTotal_energy_law J A hA]
    calc
      _ ≤ VertexCover.finiteMean (fun _ : Φ.Seeds d => ν*h/4) := by
        apply VertexCover.finiteMean_mono
        intro frozen
        have hb := integral_mono (Φ.ownTotalVariance_frozen_integrable J frozen A hA)
          (integrable_const (ν*h/4))
          (fun s => (hno J (mem_batches.mp hJ) frozen s).le)
        simpa using hb
      _ = _ := VertexCover.finiteMean_const _
  have hsum := Finset.sum_le_sum hbound
  have hl := Φ.privateProjection_batch_lower hd hh ν hscale A hA henergy
  simp only [Finset.sum_const, nsmul_eq_mul, card_batches] at hsum
  have hpos : 0 < (d.choose h:ℝ)*ν*h :=
    mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hhd)) hν)
      (Nat.cast_pos.mpr (by omega))
  linarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_GraphSoundness
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
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
open VertexCover.Restriction

theorem dense_privateVariance_lower (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    ∃ hV : (Φ.highVectors (Parameters.t m) A).Nonempty,
      ∃ J : Finset (Fin (Parameters.d m)), J.card = Parameters.h m ∧
      ∃ frozen : Φ.Seeds (Parameters.d m),
      ∃ weights : Fin (Parameters.d m) → Fin (Φ.WeightDimension (Parameters.d m)) → ℝ,
        Φ.InWeightCube weights ∧
        8 ≤ Φ.ownTotalVariance J frozen (Φ.outsideSum J frozen weights)
          (Φ.highVectors (Parameters.t m) A) hV := by
  obtain ⟨hV, _hzero, henergy⟩ := Φ.dense_separator_data m hm A hA hdense
  rw [← Φ.restrictionFunction_energy_variance] at henergy
  have hdim := Parameters.dimensions m hm
  obtain ⟨J, hJ, frozen, s, hs⟩ := Φ.restriction_frozen_exists
    hdim.1 (Parameters.h_ge_three m (by omega)) hdim.2.2.1.le
    (Parameters.ν m) (Parameters.positive m (by omega)).1
    (Parameters.restriction_budget m hm) _ hV henergy
  refine ⟨hV, J, hJ, frozen, CompactCube.realWeights s, ?_, ?_⟩
  · intro j k
    exact abs_le.mpr (s j k).2
  · simpa only [Parameters.private_variance_threshold m (by omega)] using hs

theorem graph_soundness_independent (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m)))) :
    (A.card:ℝ) < (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) := by
  by_contra hn
  obtain ⟨hV, J, hJ, frozen, weights, _hw, hlow⟩ :=
    Φ.dense_privateVariance_lower m hm A hA (le_of_not_gt hn)
  have hu := Φ.ownTotalVariance_no_upper m hm hval J hJ frozen
    (Φ.outsideSum J frozen weights) _ hV
  linarith

theorem graph_soundness_cover (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (C : Finset (Φ.Vertex (Parameters.d m)))
    (hC : (Φ.graph (Parameters.d m) (Parameters.t m)).IsVertexCover
      (C : Set (Φ.Vertex (Parameters.d m)))) :
    (1-1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) < (C.card:ℝ) := by
  classical
  have hI : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (↑(Cᶜ) : Set (Φ.Vertex (Parameters.d m))) := by
    simpa only [Finset.coe_compl] using SimpleGraph.isIndepSet_compl_iff_isVertexCover.mpr hC
  have hi := Φ.graph_soundness_independent m hm hval Cᶜ hI
  rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ C)] at hi
  simp only [div_eq_mul_inv, one_mul] at hi ⊢
  nlinarith

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
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NumberedGraph
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
                                  
section

namespace VertexCover.ExplicitGraph
noncomputable section

 theorem numbered_complete {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (E : Fin n ≃ V) (C : Finset V) (hc : G.IsVertexCover (C : Set V)) (ρ : ℝ)
    (hb : (C.card:ℝ) < ρ*Fintype.card V) :
    ((numbered (G.comap E)).coverNumber:ℝ) < ρ*(numbered (G.comap E)).n := by
  classical
  let S := C.map E.symm.toEmbedding
  have hs : (numbered (G.comap E)).Cover S := by
    rw [numbered_cover_iff]
    intro u v h
    exact (hc h).imp
      (fun hu => Finset.mem_map.mpr ⟨E u,hu,E.symm_apply_apply u⟩)
      (fun hv => Finset.mem_map.mpr ⟨E v,hv,E.symm_apply_apply v⟩)
  have hn : n=Fintype.card V := by simpa using Fintype.card_congr E
  have hcard : S.card=C.card := Finset.card_map _
  have hm := coverNumber_le (G := numbered (G.comap E)) S hs
  change (numbered (G.comap E)).coverNumber ≤ S.card at hm
  rw [hcard] at hm
  simpa only [numbered_n,hn] using (Nat.cast_le.mpr hm).trans_lt hb
end
end VertexCover.ExplicitGraph
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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


