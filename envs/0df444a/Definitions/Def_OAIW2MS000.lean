-- Prove2me | Definitions.Def_OAIW2MS000
-- name    : OAIW2MS000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:27:03.2691+00:00
-- url     : https://prove2.me/theorems/2d9cbfd5-0395-4d11-9d58-554d749f3c6a
-- title:
--   Definitions bundle OAIW2MS000 of the split of OpenAI, One-sample matroid prophet inequalities against an almighty adversary
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatroidProphet.Assigned.secretary`, `OAI.MatroidProphet.Assigned.one_sample` and `OAI.MatroidProphet.Assigned.hidden_vector`, carved from OpenAI's openai/math development (OpenAI, *One-sample matroid prophet inequalities against an almighty adversary*, OpenAI Math Release, September 23, 2026, result family 111, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 368 declarations of OpenAI's Lean: 272 definitions, 6 inductive types or structures, 17 instances and 73 theorems. The definitions and types are `OAI.MatroidProphet.Candidates.candidates`, `OAI.MatroidProphet.Candidates.greedy`, `OAI.MatroidProphet.Candidates.orderedWeights`, `OAI.MatroidProphet.Candidates.prefixCount`, `OAI.MatroidProphet.Candidates.prior`, `OAI.MatroidProphet.Candidates.priorityTime`, `OAI.MatroidProphet.Candidates.timeCount`, `OAI.MatroidProphet.FiniteLaw.weightMeasure`, `OAI.MatroidProphet.FiniteLaw.weightPMF`, `OAI.MatroidProphet.IsDensityMax`, `OAI.MatroidProphet.IsSafeSample`, `OAI.MatroidProphet.MainAlgorithm.analyzedComparisonMass`, `OAI.MatroidProphet.MainAlgorithm.analyzedLevels`, `OAI.MatroidProphet.MainAlgorithm.assign`, `OAI.MatroidProphet.MainAlgorithm.birth`, `OAI.MatroidProphet.MainAlgorithm.candidate`, `OAI.MatroidProphet.MainAlgorithm.candidateLabels`, `OAI.MatroidProphet.MainAlgorithm.candidateSet`, `OAI.MatroidProphet.MainAlgorithm.comparisonMass`, `OAI.MatroidProphet.MainAlgorithm.competition`, `OAI.MatroidProphet.MainAlgorithm.core`, `OAI.MatroidProphet.MainAlgorithm.eligible`, `OAI.MatroidProphet.MainAlgorithm.finalPath`, `OAI.MatroidProphet.MainAlgorithm.focalIndex`, `OAI.MatroidProphet.MainAlgorithm.focalMasks`, `OAI.MatroidProphet.MainAlgorithm.focalReference`, `OAI.MatroidProphet.MainAlgorithm.focalResidualFamily`, `OAI.MatroidProphet.MainAlgorithm.groupBirthRegion`, `OAI.MatroidProphet.MainAlgorithm.groupGround`, `OAI.MatroidProphet.MainAlgorithm.groupMask`, `OAI.MatroidProphet.MainAlgorithm.groups`, `OAI.MatroidProphet.MainAlgorithm.hidden`, `OAI.MatroidProphet.MainAlgorithm.higher`, `OAI.MatroidProphet.MainAlgorithm.higherTrueGroups`, `OAI.MatroidProphet.MainAlgorithm.listed`, `OAI.MatroidProphet.MainAlgorithm.listedLambda`, `OAI.MatroidProphet.MainAlgorithm.listedRankStatistic`, `OAI.MatroidProphet.MainAlgorithm.listedSafeStatistic`, `OAI.MatroidProphet.MainAlgorithm.listedTransferGap`, `OAI.MatroidProphet.MainAlgorithm.listedZ` and 238 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `MatroidProphet_AdaptiveResampling`, `MatroidProphet_Algorithm_LayerRank`, `MatroidProphet_Algorithm_Mean`, `MatroidProphet_Algorithm_Rule`, `MatroidProphet_Algorithm_SeedLaw`, `MatroidProphet_Algorithm_Selection`, `MatroidProphet_Algorithm_Statistics`, `MatroidProphet_Algorithm_Worst`, `MatroidProphet_AnalyzedMass`, `MatroidProphet_BatchReveal`, `MatroidProphet_BranchMix`, `MatroidProphet_CandidateFilter`, `MatroidProphet_Candidates`, `MatroidProphet_Certificates_Budget`, `MatroidProphet_Certificates_Execution`, `MatroidProphet_CommonBudget`, `MatroidProphet_CompletePayoff`, `MatroidProphet_Constants`, `MatroidProphet_Density_Basic`, `MatroidProphet_Density_Birth`, `MatroidProphet_Density_Guarded`, `MatroidProphet_ExitNumerics`, `MatroidProphet_FiniteBits`, `MatroidProphet_FocalTransfer`, `MatroidProphet_GreedyOptimal`, `MatroidProphet_GroupConditioning`, `MatroidProphet_GroupPayoff`, `MatroidProphet_GroupSafety`, `MatroidProphet_Groups`, `MatroidProphet_HazardCover`, `MatroidProphet_LayerGreedy`, `MatroidProphet_LayerOnline`, `MatroidProphet_Maximum_Basic`, `MatroidProphet_Maximum_Mask`, `MatroidProphet_Maximum_Score`, `MatroidProphet_PathRankCost`, `MatroidProphet_PathStatistics`, `MatroidProphet_Pivots_Basic`, `MatroidProphet_Pivots_BlockPatterns`, `MatroidProphet_Pivots_Blocks`, `MatroidProphet_Pivots_Encoding`, `MatroidProphet_Pivots_Entropy`, `MatroidProphet_Pivots_Greedy`, `MatroidProphet_Pivots_GreedyScan`, `MatroidProphet_Pivots_Guarantee`, `MatroidProphet_Pivots_Interleavings`, `MatroidProphet_Pivots_OccurrenceSupport`, `MatroidProphet_Pivots_Patterns`, `MatroidProphet_Pivots_PhasePattern`, `MatroidProphet_Pivots_Phases`, `MatroidProphet_Pivots_Reindex`, `MatroidProphet_Pivots_ResidualFamily`, `MatroidProphet_Pivots_Sign`, `MatroidProphet_Priority`, `MatroidProphet_RankAccounting`, `MatroidProphet_RankCost`, `MatroidProphet_Residual_Constants`, `MatroidProphet_Residual_Encoding`, `MatroidProphet_Residual_Gap`, `MatroidProphet_Residual_Generators`, `MatroidProphet_Residual_LabeledFamily`, `MatroidProphet_Residual_Probability`, `MatroidProphet_Residual_Statistics`, `MatroidProphet_Residual_Timeline`, `MatroidProphet_Residual_Transfer`, `MatroidProphet_RevealComposition`, `MatroidProphet_Reverse_Bands`, `MatroidProphet_Reverse_BirthSafety`, `MatroidProphet_Reverse_Certificates`, `MatroidProphet_Reverse_Cost`, `MatroidProphet_Reverse_Exposure`, `MatroidProphet_Reverse_Hazard`, `MatroidProphet_Reverse_Hybrid`, `MatroidProphet_Reverse_Iteration`, `MatroidProphet_Reverse_LowHazard`, `MatroidProphet_Reverse_Paths`, `MatroidProphet_Reverse_PrefixTree`, `MatroidProphet_Reverse_SquareSum`, `MatroidProphet_Reverse_Squared`, `MatroidProphet_Reverse_Trace`, `MatroidProphet_Rounding`, `MatroidProphet_SafeParity`, `MatroidProphet_SafeSamples`, `MatroidProphet_Seed`, `MatroidProphet_SeedLaw`, `MatroidProphet_Simulation`, `MatroidProphet_WeightGroups`, `MatroidSecretary_Secretary_ConditionalLaw`, `MatroidSecretary_Secretary_Coupling`, `MatroidSecretary_Secretary_KernelModel`, `MatroidSecretary_Secretary_Observation`, `MatroidSecretary_Secretary_PrefixObservationModel`, `MatroidSecretary_Secretary_ProbabilityModel`, `MatroidSecretary_Secretary_ReplayRule`, `MatroidSecretary_Secretary_SeedModel`, `MatroidSecretary_Weights_FiniteWeightLawModel`, `MatroidSecretary_Weights_FiniteWeightLawTheorems`.
--
--   **Imports.** It imports the published bundle `Def_MatroidSecretary`.
--
--   **Imported by** (directly, in this split): the statements `OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff` and `OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le`; the proofs of `OAI.MatroidProphet.Assigned.hidden_vector`, `OAI.MatroidProphet.Assigned.one_sample`, `OAI.MatroidProphet.Assigned.secretary`, `OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff` and `OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le`.
-- source:
--   OpenAI, One-sample matroid prophet inequalities against an almighty adversary, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 111; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_MatroidSecretary

section
-- module Solutions.OAIW2_MatroidSec.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FiniteBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def bitsWeight (q : α → ℝ) (V S : Finset α) : ℝ :=
  ∏ e ∈ V, if e ∈ S then q e else 1 - q e

noncomputable def bitsExpectation (q : α → ℝ) (V : Finset α)
    (f : Finset α → ℝ) : ℝ :=
  ∑ S ∈ V.powerset, bitsWeight q V S * f S

lemma bitsWeight_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V S : Finset α) : 0 ≤ bitsWeight q V S := by
  apply prod_nonneg
  intro e he
  split_ifs
  · exact hq0 e
  · exact sub_nonneg.2 (hq1 e)

lemma bitsWeight_insert_no (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) (hS : S ⊆ V) :
    bitsWeight q (insert e V) S = (1 - q e) * bitsWeight q V S := by
  have heS : e ∉ S := fun h => he (hS h)
  simp [bitsWeight, he, heS]

lemma bitsWeight_insert_yes (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) :
    bitsWeight q (insert e V) (insert e S) = q e * bitsWeight q V S := by
  simp only [bitsWeight, prod_insert he, mem_insert_self, ite_true]
  congr 1
  apply prod_congr rfl
  intro x hx
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  simp [hxe]

lemma bitsExpectation_insert (q : α → ℝ) (V : Finset α) (e : α) (he : e ∉ V)
    (f : Finset α → ℝ) :
    bitsExpectation q (insert e V) f =
      (1 - q e) * bitsExpectation q V f +
        q e * bitsExpectation q V (fun S => f (insert e S)) := by
  unfold bitsExpectation
  rw [sum_powerset_insert he, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_no q V S e he (mem_powerset.1 hS)]
    ring
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_yes q V S e he]
    ring

@[simp] lemma bitsExpectation_empty (q : α → ℝ) (f : Finset α → ℝ) :
    bitsExpectation q ∅ f = f ∅ := by
  simp [bitsExpectation, bitsWeight]

@[simp] lemma bitsExpectation_one (q : α → ℝ) (V : Finset α) :
    bitsExpectation q V (fun _ => 1) = 1 := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    simp only [ih]
    ring

noncomputable def bitsFailure (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) : ℝ :=
  bitsExpectation q V (fun S => if cert (I ∪ S) then 0 else 1)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_AdaptiveResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α]

inductive RevealTree (α β : Type*) where
  | leaf (value : β)
  | query (e : α) (no yes : RevealTree α β)

def RevealTree.Fresh : RevealTree α β → Finset α → Prop
  | .leaf _, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)

def RevealTree.run : RevealTree α β → Finset α → β
  | .leaf value, _ => value
  | .query e no yes, S => if e ∈ S then yes.run (S.erase e) else no.run (S.erase e)

def RevealTree.queried : RevealTree α β → Finset α → Finset α
  | .leaf _, _ => ∅
  | .query e no yes, S => insert e (if e ∈ S then yes.queried (S.erase e) else no.queried (S.erase e))

def RevealTree.hybrid : RevealTree α β → Finset α → Finset α → Finset α
  | .leaf _, S, _ => S
  | .query e no yes, S, T =>
      let H := if e ∈ S then yes.hybrid (S.erase e) (T.erase e)
        else no.hybrid (S.erase e) (T.erase e)
      if e ∈ T then insert e H else H

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

noncomputable def natRank (M : Matroid α) (X : Set α) : ℕ :=
  (M.eRk X).toNat

lemma rank_ne_top (M : Matroid α) (X : Set α) : M.eRk X ≠ ⊤ :=
  (M.isRkFinite_set X).eRk_lt_top.ne

omit [Fintype α] in
@[simp] lemma natRank_closure (M : Matroid α) (X : Set α) :
    natRank M (M.closure X) = natRank M X := by
  simp [natRank]

omit [Fintype α] in
@[simp] lemma natRank_empty (M : Matroid α) : natRank M ∅ = 0 := by
  simp [natRank]

lemma natRank_submod (M : Matroid α) (X Y : Set α) :
    natRank M (X ∩ Y) + natRank M (X ∪ Y) ≤ natRank M X + natRank M Y := by
  have h := ENat.toNat_le_toNat (M.eRk_submod X Y)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, rank_ne_top M Y⟩)
  simpa only [ENat.toNat_add (rank_ne_top M _) (rank_ne_top M _), natRank] using h

omit [Fintype α] in
lemma flat_inter (M : Matroid α) {X Y : Set α} (hX : M.IsFlat X)
    (hY : M.IsFlat Y) : M.IsFlat (X ∩ Y) := by
  apply Matroid.isFlat_iff_closure_eq.2
  apply Subset.antisymm
  · exact subset_inter ((M.closure_subset_closure inter_subset_left).trans_eq hX.closure)
      ((M.closure_subset_closure inter_subset_right).trans_eq hY.closure)
  · exact M.subset_closure _ (inter_subset_left.trans hX.subset_ground)

noncomputable def densityObjective (M : Matroid α) (κ : ℕ) (D X : Set α) : ℤ :=
  (D ∩ X).ncard - (κ : ℤ) * natRank M X

lemma densityObjective_supermod (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D X Y : Set α) :
    densityObjective M κ D X + densityObjective M κ D Y ≤
      densityObjective M κ D (X ∩ Y) + densityObjective M κ D (M.closure (X ∪ Y)) := by
  have hc := ncard_union_add_ncard_inter (D ∩ X) (D ∩ Y)
  have hm := ncard_mono (inter_subset_inter_right D
    (M.subset_closure (X ∪ Y) (by simp [hE])))
  have hr := natRank_submod M X Y
  have hu : (D ∩ X) ∪ (D ∩ Y) = D ∩ (X ∪ Y) := (Set.inter_union_distrib_left D X Y).symm
  have hi : (D ∩ X) ∩ (D ∩ Y) = D ∩ (X ∩ Y) := (Set.inter_inter_distrib_left D X Y).symm
  rw [hu, hi] at hc
  have hmul : (κ : ℤ) * (natRank M (X ∩ Y) + natRank M (X ∪ Y)) ≤
      (κ : ℤ) * (natRank M X + natRank M Y) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by exact_mod_cast (Nat.zero_le κ))
  dsimp [densityObjective]
  rw [natRank_closure]
  simp only [mul_add] at hmul
  omega

def IsDensityMax (M : Matroid α) (κ : ℕ) (D P Q : Set α) : Prop :=
  M.IsFlat Q ∧ P ⊆ Q ∧ ∀ Z, M.IsFlat Z → P ⊆ Z →
    densityObjective M κ D Z ≤ densityObjective M κ D Q

lemma exists_densityMax (M : Matroid α) (κ : ℕ) (D P : Set α)
    (hP : P ⊆ M.E) : ∃ Q, IsDensityMax M κ D P Q := by
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | M.IsFlat Z ∧ P ⊆ Z}
    (densityObjective M κ D) (Set.toFinite _) ⟨M.E, M.ground_isFlat, hP⟩
  exact ⟨Q, hQ.1, hQ.2, fun Z hZ hPZ => hmax Z ⟨hZ, hPZ⟩⟩

lemma densityMax_union (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) {Q Q' : Set α}
    (hQ : IsDensityMax M κ D P Q) (hQ' : IsDensityMax M κ D P Q') :
    IsDensityMax M κ D P (M.closure (Q ∪ Q')) := by
  have hPQQ' : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 hQ'.2.1
  have hPc : P ⊆ M.closure (Q ∪ Q') :=
    hQ.2.1.trans ((subset_union_left).trans (M.subset_closure _ (by simp [hE])))
  refine ⟨Matroid.isFlat_closure (M := M) _, hPc, ?_⟩
  intro Z hZ hPZ
  have h1 := hQ.2.2 Z hZ hPZ
  have h2 := hQ'.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPQQ'
  have h3 := densityObjective_supermod M hE κ D Q Q'
  omega

lemma exists_largest_densityMax (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    ∃ Q, IsDensityMax M κ D P Q ∧ ∀ Q', IsDensityMax M κ D P Q' → Q' ⊆ Q := by
  obtain ⟨Q₀, hQ₀⟩ := exists_densityMax M κ D P (by simp [hE])
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | IsDensityMax M κ D P Z}
    Set.ncard (Set.toFinite _) ⟨Q₀, hQ₀⟩
  refine ⟨Q, hQ, ?_⟩
  intro Q' hQ'
  have hu := densityMax_union M hE κ D P hQ hQ'
  have hcard := hmax _ hu
  have hsub : Q ⊆ M.closure (Q ∪ Q') :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have heq : Q = M.closure (Q ∪ Q') := Set.eq_of_subset_of_ncard_le hsub hcard
  rw [heq]
  exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

noncomputable def densityExpansion (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : Set α :=
  (exists_largest_densityMax M hE κ D P).choose

lemma densityExpansion_spec (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    IsDensityMax M κ D P (densityExpansion M hE κ D P) ∧
      ∀ Q, IsDensityMax M κ D P Q → Q ⊆ densityExpansion M hE κ D P :=
  (exists_largest_densityMax M hE κ D P).choose_spec

lemma densityExpansion_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : P ⊆ densityExpansion M hE κ D P :=
  (densityExpansion_spec M hE κ D P).1.2.1

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Guarded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def densityEnabled (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) : Set α :=
  if a ≤ k then densityExpansion M hE κ D P else P

lemma densityEnabled_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) :
    P ⊆ densityEnabled M hE κ D a k P := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_extensive M hE κ D P
  · simp only [densityEnabled, ite_eq_right hak, Subset.rfl]

lemma densityEnabled_univ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) : densityEnabled M hE κ D a k univ = univ :=
  Set.eq_univ_of_univ_subset (densityEnabled_extensive M hE κ D a k univ)

def activation (h : ℕ) : ℤ := -3 * ((h : ℤ) + 1)

noncomputable def guardedPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : ℕ → ℤ → Set α
  | 0, k => if k < 0 then M.closure ∅ else univ
  | h + 1, k =>
      M.closure (densityEnabled M hE κ (D h) (activation h) k
          (guardedPath M hE κ D C h k) ∪
        (C h ∩ densityEnabled M hE κ (D h) (activation h) (k + 1)
          (guardedPath M hE κ D C h (k + 1))))

noncomputable def nominalPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (guardedPath M hE κ D C h k)

lemma guardedPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    guardedPath M hE κ D C h k = univ := by
  induction h generalizing k with
  | zero => simp [guardedPath, not_lt_of_ge hk]
  | succ h ih =>
    rw [guardedPath, ih hk, ih (by omega), densityEnabled_univ, densityEnabled_univ]
    simp [hE]

lemma nominalPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    nominalPath M hE κ D C h k = univ := by
  rw [nominalPath, guardedPath_nonnegative M hE κ D C h hk, densityEnabled_univ]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Birth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def pathHorizon (h : ℕ) : ℕ := 3 * (h + 1)

lemma activation_add_horizon (h : ℕ) : activation h + (pathHorizon h : ℤ) = 0 := by
  dsimp [activation, pathHorizon]
  omega

lemma exists_nominal_member (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) :
    ∃ j : ℕ, e ∈ nominalPath M hE κ D C h (activation h + j) := by
  refine ⟨pathHorizon h, ?_⟩
  rw [activation_add_horizon, nominalPath_nonnegative M hE κ D C h (by omega)]
  trivial

noncomputable def nominalBirth (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) : ℤ :=
  activation h + Nat.find (exists_nominal_member M hE κ D C h e)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RankAccounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α]

noncomputable def conditionalRank (M : Matroid α) (S P : Set α) : ℕ :=
  natRank M (S ∪ P) - natRank M P

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [DecidableEq α]

noncomputable def layerPrior (E : Finset α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (k : ℕ) : Set α := {e | e ∈ E ∧ layer e = b ∧ time e < k}

noncomputable def layerGreedy (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) : Finset α := by
  classical
  exact E.filter fun e => e ∉ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Constants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable section

def weightBase : ℝ := 2 ^ 32
def densityThreshold : ℝ := 2 ^ 100
def thinningRate : ℝ := ((2 : ℝ) ^ 140)⁻¹
def exitThreshold : ℝ := ((2 : ℝ) ^ 12)⁻¹
def retainedFraction : ℝ := ((2 : ℝ) ^ 16)⁻¹

end

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open MeasureTheory

instance levelMeasurableSpace : MeasurableSpace (Option ℤ) := ⊤
instance levelMeasurableSingletonClass : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedLevel (B x : ℝ) : Option ℤ :=
  if 0 < x then some ⌊Real.logb B x⌋ else none

noncomputable def levelWeight (B : ℝ) : Option ℤ → ℝ
  | none => 0
  | some i => B ^ i

noncomputable def roundedWeight (B x : ℝ) : ℝ := levelWeight B (roundedLevel B x)

theorem measurable_roundedLevel (B : ℝ) : Measurable (roundedLevel B) := by
  unfold roundedLevel
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_countable (some : ℤ → Option ℤ)).comp
      (Int.measurable_floor.comp (Real.measurable_log.div_const _))
  · exact measurable_const

noncomputable def discreteOnlineRule {K : Type*} [Countable K] [MeasurableSpace K]
    [MeasurableSingletonClass K] {n bits : ℕ}
    (key : ℝ → K) (hkey : Measurable key)
    (choose : (k : Fin n) → Seed bits → (Fin n → K) →
      (Fin (k.val + 1) → Fin n × K) → Bool) : OnlineRule n bits where
  decide k r s hist := choose k r (fun e => key (s e))
    (fun j => ((hist j).1, key (hist j).2))
  measurable_decide k := by
    have hc : Measurable (fun x : Seed bits × ((Fin n → K) ×
        (Fin (k.val + 1) → Fin n × K)) => choose k x.1 x.2.1 x.2.2) :=
      measurable_of_countable _
    have hs : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun e => key (x.2.1 e)) := by
      apply Measurable.of_eval
      intro e
      exact hkey.comp ((measurable_pi_apply e).comp (measurable_fst.comp measurable_snd))
    have hh : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun j => ((x.2.2 j).1, key (x.2.2 j).2)) := by
      apply Measurable.of_eval
      intro j
      have hj : Measurable (fun x : Seed bits × (Weights n × History n k) => x.2.2 j) :=
        (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
      exact (measurable_fst.comp hj).prodMk (hkey.comp (measurable_snd.comp hj))
    exact hc.comp (measurable_fst.prodMk (hs.prodMk hh))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_LayerOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

noncomputable def assignedEligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) : Finset (Fin n) := by
  classical
  exact univ.filter fun e => assign e (v e) ≠ none

def assignedLayer {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n) : ℤ :=
  (assign e (v e)).getD 0

noncomputable def layerKeyDecision {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (k : Fin n)
    (hist : Fin (k.val+1) → Fin n × K) : Bool := by
  classical
  let current := hist ⟨k.val, Nat.lt_succ_self _⟩
  exact match assign current.1 current.2 with
  | none => false
  | some b => decide (current.1 ∉ M.closure (base b ∪
      {f | ∃ j : Fin (k.val+1), j.val < k.val ∧ (hist j).1 = f ∧
        assign (hist j).1 (hist j).2 = some b}))

def keyHistory {n : ℕ} {K : Type*} (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) : Fin (k.val+1) → Fin n × K :=
  fun j => (π (prefixIndex k j), v (π (prefixIndex k j)))

noncomputable def layerOnlineRule {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ) : OnlineRule n bits :=
  discreteOnlineRule key hkey fun k r s hist =>
    layerKeyDecision M (base r s) (assign r s) k hist

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Rule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

structure MainMasks (n : ℕ) where
  H : Finset (Fin n)
  D : Finset (Fin n)
  C : Finset (Fin n)
  T : Finset (Fin n)
  odd : Bool

def mainSeedBits (n : ℕ) : ℕ := 4*n+2

def seedMask {n : ℕ} (r : Seed (mainSeedBits n)) (j : Fin 4) : Finset (Fin n) :=
  univ.filter fun e => r ⟨4*e.val+j.val, by dsimp [mainSeedBits]; omega⟩ = true

def mainMasks {n : ℕ} (r : Seed (mainSeedBits n)) : MainMasks n where
  H := seedMask r 0
  D := seedMask r 1
  C := seedMask r 2
  T := seedMask r 3
  odd := r ⟨4*n+1, by dsimp [mainSeedBits]; omega⟩

def mainBranch {n : ℕ} (r : Seed (mainSeedBits n)) : Bool :=
  r ⟨4*n, by dsimp [mainSeedBits]; omega⟩

namespace MainAlgorithm
variable {n : ℕ}

def higher (f : Fin n) (a : Option ℤ) (e : Fin n) (b : Option ℤ) : Prop :=
  match a, b with
  | some i, some j => j < i ∨ j = i ∧ f < e
  | some _, none => True
  | _, _ => False

def candidate (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (e : Fin n) (w : Option ℤ) : Prop :=
  w ≠ none ∧ e ∉ d.H ∧ e ∉ M.closure {f | f ∈ d.H ∧ higher f (seen f) e w}

noncomputable def listed (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : Finset ℤ := by
  classical
  exact d.D.biUnion fun e => if candidate M d seen e (seen e) then (seen e).toFinset else ∅

noncomputable def groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : List ℤ := (listed M d seen).sort (· ≤ ·)

def groupMask (M : Matroid (Fin n)) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (mask : Finset (Fin n)) (h : ℕ) : Set (Fin n) :=
  {e | e ∈ mask ∧ candidate M d seen e (seen e) ∧ seen e = (groups M d seen)[h]?}

noncomputable def finalPath (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) : ℤ → Set (Fin n) :=
  guardedPath M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    (groups M d seen).length

noncomputable def birth (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : ℤ :=
  nominalBirth M hE (2^100) (groupMask M d seen d.D) (groupMask M d seen d.C)
    ((groups M d seen).idxOf i) e

def eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (i : ℤ) : Prop :=
  e ∉ d.H ∪ d.D ∪ d.C ∧ candidate M d seen e (some i) ∧ i ∈ groups M d seen ∧
  e ∈ d.T ∧ activation ((groups M d seen).idxOf i) + 2 ≤ birth M hE d seen e i ∧
  (birth M hE d seen e i) % 2 = (if d.odd then 1 else 0) ∧
  e ∉ finalPath M hE d seen (birth M hE d seen e i - 2)

noncomputable def assign (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) : Option ℤ → Option ℤ := by
  classical
  exact fun w => match w with
    | none => none
    | some i => if eligible M hE d seen e i then some (birth M hE d seen e i) else none

noncomputable def core (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    OnlineRule n (mainSeedBits n) :=
  layerOnlineRule M (roundedLevel weightBase) (measurable_roundedLevel weightBase)
    (fun r seen b => finalPath M hE (mainMasks r) seen (b-2))
    (fun r seen => assign M hE (mainMasks r) seen)

noncomputable def hidden (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) where
  mask r := (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
  core := core M hE

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

noncomputable def selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) : Finset (Fin n) :=
  layerGreedy M (assignedEligible (assign M hE d w) w)
    (fun b => finalPath M hE d w (b-2)) (assignedLayer (assign M hE d w) w)
    (fun e => (π.symm e).val)

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Groups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

@[simp] lemma mem_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) :
    i ∈ groups M d seen ↔ i ∈ listed M d seen := by
  simp [groups]

@[simp] lemma groups_length (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).length = (listed M d seen).card := by
  simp [groups]

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Generators
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

noncomputable def timedGeneratorSet (G : Set α) (τ : α → ℕ) (a k : ℤ) : Set α :=
  {g | g ∈ G ∧ a + (τ g : ℤ) ≤ k}

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CommonBudget
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

def commonPathGenerators (C J : ℕ → Set α) (h : ℕ) : ℕ → Set α
  | 0 => C h
  | t+1 => commonPathGenerators C J h t ∪ C (h+1+t) ∪ J (h+1+t)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Paths
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def reversePrefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) : ℕ → Set α
  | 0 => if k < 0 then M.closure ∅ else univ
  | h+1 => M.closure (densityEnabled M hE κ (D h) (activation h) k
      (reversePrefix M hE κ D C S k h) ∪ (C h ∩ S h))

noncomputable def reverseNominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (reversePrefix M hE κ D C S k h)

noncomputable def departingGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  C h ∩ (S h \ reverseNominal M hE κ D C S k h)

noncomputable def hybridGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) : Set α :=
  (C h ∩ nominalPath M hE κ D C h (b-1)) ∪
    (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

noncomputable def lowerCompetition (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) : ℕ → Set α
  | 0 => ∅
  | h+1 => lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_PathRankCost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

noncomputable def unobservedBirthRegion (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) : Set α :=
  if activation h + 2 ≤ b then
    (G ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1))) \ O
  else ∅

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_LayerRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def groupBirthRegion (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  unobservedBirthRegion M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w univ h) (d.H ∪ d.D ∪ d.C : Finset (Fin n)) h b

noncomputable def competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  lowerCompetition M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) b h

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Basic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

variable {α : Type*} {M : Matroid α} {I J : Set α} {e : α}

def support (M : Matroid α) (I : Set α) (e : α) : Set α :=
  ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_GreedyScan
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

noncomputable def keptOccurrences (M : Matroid α) (label : β → α) (time : β → ℕ) :
    Finset β := by
  classical
  exact Finset.univ.filter (fun o => label o ∉ M.closure (label '' {p | time p < time o}))

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_OccurrenceSupport
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

noncomputable def occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) : Finset β := by
  classical
  exact J.filter (fun o => label o ∈ support M (label '' (J : Set β)) e)

def IsPivot (M : Matroid α) (label : β → α) (time : β → ℕ) (e : α) (o : β) : Prop :=
  e ∈ M.closure (label '' {p | time p ≤ time o}) ∧
    e ∉ M.closure (label '' {p | time p < time o})

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Greedy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

def oldPrefix (b : ℕ → α) (k : ℕ) : Set α := {x | ∃ i < k, b i = x}

@[simp] lemma oldPrefix_zero
    {α : Type u_1} [Fintype α] (b : ℕ → α) : oldPrefix b 0 = ∅ := by
  ext x
  simp [oldPrefix]

noncomputable def omittable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k => b k ∈ M.closure (oldPrefix b k ∪ A))

noncomputable def vulnerable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k =>
    b k ∉ M.closure (oldPrefix b k) ∧ b k ∈ M.closure (oldPrefix b k ∪ A))

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Interleavings
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

abbrev Occurrence (r s : ℕ) := Fin r ⊕ Fin s

def occurrenceLabel {r s : ℕ} (b : ℕ → α) (a : Fin s → α) : Occurrence r s → α :=
  Sum.elim (fun i => b i.val) a

def OldOrdered {r s : ℕ} (time : Occurrence r s → ℕ) : Prop :=
  ∀ i j : Fin r, i < j → time (Sum.inl i) < time (Sum.inl j)

noncomputable def retained {r s : ℕ} (M : Matroid α) (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) : Finset (Occurrence r s) := by
  classical
  exact Finset.univ.filter (fun o => occurrenceLabel b a o ∉
    M.closure (occurrenceLabel b a '' {p | time p < time o}))

noncomputable def retainedFamily {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) : Finset (Finset (Occurrence r s)) := by
  classical
  exact Finset.univ.filter (fun J => ∃ time, OldOrdered time ∧ retained M b a time = J)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Encoding
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Finset

variable {r q : ℕ}

def oldBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin r => time (Sum.inl i) < t)).card

def movableBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin q => time (Sum.inr i) < t)).card

def scoreExponent (s : ℕ) (time : Occurrence r q → ℕ) : Occurrence r q → ℕ
  | Sum.inl i => (s + 1) * (i.val + 1)
  | Sum.inr i => (s + 1) * oldBefore time (time (Sum.inr i)) +
      movableBefore time (time (Sum.inr i)) + 1

@[simp] lemma scoreExponent_old (s : ℕ) (time : Occurrence r q → ℕ) (i : Fin r) :
    scoreExponent s time (Sum.inl i) = (s + 1) * (i.val + 1) := rfl

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Sign
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup X] [Module ℝ X]

def RealizesSigns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (t : Finset ι) (x : X) : Prop :=
  ∀ i, if i ∈ t then 0 < v i x + c i else v i x + c i < 0

noncomputable def affinePatterns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, RealizesSigns v c t x)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Patterns
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

def occurrenceMark (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    Occurrence r q → Bool := Sum.elim oldMark movableMark

noncomputable def markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) : ℝ :=
  if occurrenceMark oldMark movableMark o then (2 : ℝ) ^ scoreExponent s time o
  else -(2 : ℝ) ^ scoreExponent s time o

noncomputable def fixedOldScore (s : ℕ) (oldMark : Fin r → Bool) (i : Fin r) : ℝ :=
  if oldMark i then (2 : ℝ)^((s+1)*(i.val+1)) else -(2 : ℝ)^((s+1)*(i.val+1))

noncomputable def constantScore (s : ℕ) (oldMark : Fin r → Bool) : Occurrence r q → ℝ :=
  Sum.elim (fixedOldScore s oldMark) (fun _ => 0)

noncomputable def coordinateScore : Occurrence r q → ((Fin q → ℝ) →ₗ[ℝ] ℝ) :=
  Sum.elim (fun _ => 0) (fun i => LinearMap.proj i)

noncomputable def patternLinear (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) : (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, coordinateScore o

noncomputable def patternConstant (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (oldMark : Fin r → Bool) : ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, constantScore s oldMark o

def RecordsPivots (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (t : Finset (Fin n)) : Prop :=
  ∀ f, ∃ o, IsPivot M label time (test f) o ∧
    (occurrenceMark oldMark movableMark o = true ↔ f ∈ t)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Guarantee
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

noncomputable def markedPivotPatterns (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun t => ∃ time : Occurrence r q → ℕ,
    OldOrdered time ∧ Function.Injective time ∧ ∃ movableMark : Fin q → Bool,
      RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Reindex
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α β γ O A : Type*} [Fintype α]

noncomputable def freeMarkedPatterns [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun t => ∃ time : O ⊕ A → ℕ,
    StrictMono (fun o => time (Sum.inl o)) ∧ Function.Injective time ∧
    ∃ mark : A → Bool, ∀ f, ∃ o,
      IsPivot M (Sum.elim oldLabel movableLabel) time (test f) o ∧
        (Sum.elim oldMark mark o = true ↔ f ∈ t)

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Blocks
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]

abbrev BlockOld (F : T → Set α) :=
  {p : T ×ₗ α // (ofLex p).2 ∈ F (ofLex p).1}

noncomputable instance instFintypeBlockOld (F : T → Set α) : Fintype (BlockOld F) := Fintype.ofFinite _

def blockOldStage {F : T → Set α} (o : BlockOld F) : T := (ofLex o.val).1

def blockOldLabel {F : T → Set α} (o : BlockOld F) : α := (ofLex o.val).2

def blockStage (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → T :=
  Sum.elim (blockOldStage (F := F)) τ

noncomputable def blockKey (F : T → Set α) (τ : A → T) :
    BlockOld F ⊕ A → T ×ₗ (WithTop α ×ₗ ℕ)
  | Sum.inl o => toLex (blockOldStage (F := F) o, toLex ((blockOldLabel (α := α) (F := F) o : WithTop α), 0))
  | Sum.inr a => toLex (τ a, toLex (⊤, ((Fintype.equivFin A) a).val))

lemma blockKey_injective
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (τ : A → T) :
    Function.Injective (blockKey F τ) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hs : blockOldStage (F := F) x = blockOldStage (F := F) y := congrArg (fun z => (ofLex z).1) h
      have hl : (blockOldLabel (α := α) (F := F) x : WithTop α) = blockOldLabel (α := α) (F := F) y :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      have hl' : blockOldLabel (α := α) (F := F) x = blockOldLabel (α := α) (F := F) y := WithTop.coe_inj.mp hl
      have heq : x = y := Subtype.ext (congrArg toLex (Prod.ext hs hl'))
      exact congrArg Sum.inl heq
    | inr y =>
      have hh : (blockOldLabel (α := α) (F := F) x : WithTop α) = ⊤ :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      exact (WithTop.coe_ne_top hh).elim
  | inr x =>
    cases y with
    | inl y =>
      have hh : (blockOldLabel (α := α) (F := F) y : WithTop α) = ⊤ :=
        (congrArg (fun z => (ofLex (ofLex z).2).1) h).symm
      exact (WithTop.coe_ne_top hh).elim
    | inr y =>
      have hi : ((Fintype.equivFin A) x).val = ((Fintype.equivFin A) y).val :=
        congrArg (fun z => (ofLex (ofLex z).2).2) h
      exact congrArg Sum.inr ((Fintype.equivFin A).injective (Fin.ext hi))

noncomputable def blockTime (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → ℕ := by
  letI := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  exact fun o => ((Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm o).val

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_BlockPatterns
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T] {n : ℕ}

def blockLabel (F : T → Set α) (a : A → α) : BlockOld F ⊕ A → α :=
  Sum.elim (blockOldLabel (F := F)) a

def blockPrefix (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o ≤ k}

def blockBefore (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o < k}

noncomputable def blockBirthPattern (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ k, mark k = true ∧
    test f ∈ M.closure (blockPrefix F a τ k) ∧ test f ∉ M.closure (blockBefore F a τ k)

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Phases
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B]

def phaseOld (F K : B → Set α) (p : B ×ₗ Bool) : Set α :=
  if (ofLex p).2 then F (ofLex p).1 else K (ofLex p).1

def phasePlacement (θ : G → B) (β : Z → B) : G ⊕ Z → B ×ₗ Bool :=
  Sum.elim (fun g => toLex (θ g, true)) (fun z => toLex (β z, false))

def upperPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure (F b ∪ a '' {g | θ g ≤ b})

def lowerPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure ((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b})

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_PhasePattern
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B] {n : ℕ}

noncomputable def residualOfLayers (M : Matroid α) (F K : B → Set α) (a : G → α)
    (z : Z → α) (θ : G → B) (β : Z → B) (test : Fin n → α)
    (P : B → Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ P b ∧
    test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b})

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Entropy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Finset

noncomputable def binomialSum (n d : ℕ) : ℕ := ∑ k ∈ Iic d, n.choose k

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_ResidualFamily
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α O₁ O₂ : Type*} [Fintype α] [Fintype O₁] [LinearOrder O₁]
    [Fintype O₂] [LinearOrder O₂] {n : ℕ}

noncomputable def smallSubsets (U : Finset α) (q : ℕ) : Finset (Finset α) := by
  classical
  exact U.powerset.filter (fun J => J.card ≤ q)

noncomputable def intersectionFamily (F G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (F ×ˢ G).image (fun p => p.1 ∩ p.2)

noncomputable def residualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) : Finset (Finset (Fin n)) := by
  classical
  exact (smallSubsets U q).biUnion fun J => (smallSubsets U q).biUnion fun Z =>
    intersectionFamily
      (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
      (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Timeline
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

abbrev IntWindow (a : ℤ) := {k : ℤ // k ∈ Set.Icc (a - 2) 1}

noncomputable instance instFintypeIntWindow (a : ℤ) : Fintype (IntWindow a) := Fintype.ofFinite _

abbrev ParityWindow (a : ℤ) (ε : Fin 2) := {k : IntWindow a // k.val % 2 = (ε.val : ℤ)}

noncomputable instance instFintypeParityWindow (a : ℤ) (ε : Fin 2) : Fintype (ParityWindow a ε) := Fintype.ofFinite _

def roundParity (ε : Fin 2) (k : ℤ) : ℤ := if k % 2 = (ε.val : ℤ) then k else k + 1

lemma roundParity_bounds (ε : Fin 2) (k : ℤ) : k ≤ roundParity ε k ∧ roundParity ε k ≤ k + 1 := by
  unfold roundParity
  split <;> omega

lemma roundParity_mod (ε : Fin 2) (k : ℤ) : roundParity ε k % 2 = (ε.val : ℤ) := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

variable {α G : Type*} [Fintype α] [LinearOrder α] [Fintype G]

def windowPlacement (a : ℤ) (ν : G → ℤ) (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → IntWindow a :=
  fun g => ⟨ν g, by have := hν g; constructor <;> omega⟩

def parityPlacement (a : ℤ) (ε : Fin 2) (ν : G → ℤ)
    (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → ParityWindow a ε :=
  fun g => ⟨⟨roundParity ε (ν g), by
    have := hν g
    have := roundParity_bounds ε (ν g)
    constructor <;> omega⟩, roundParity_mod ε (ν g)⟩

def generatedPath (M : Matroid α) (F : ℤ → Set α) (g : G → α) (ν : G → ℤ) (k : ℤ) : Set α :=
  M.closure (F k ∪ g '' {i | ν i ≤ k})

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Encoding
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

noncomputable def validBirthMark (a : ℤ) (ε : Fin 2) (k : IntWindow a) : Bool :=
  decide (a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ))

noncomputable def integerBirthLayer (X : ℤ → Set α) (test : Fin n → α) (a : ℤ)
    (ε : Fin 2) (b : ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    test f ∈ X b.val.val ∧ test f ∉ X (b.val.val - 1)

noncomputable def integerResidual {Z : Type*} (M : Matroid α) (X : ℤ → Set α)
    (test : Fin n → α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (z : Z → α) (β : Z → ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ integerBirthLayer X test a ε b ∧
    test f ∉ M.closure (X (b.val.val - 2) ∪ K b ∪ z '' {w | β w = b})

noncomputable def integerResidualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (test : Fin n → α) : Finset (Finset (Fin n)) :=
  residualFamily M U q
    (blockOldLabel (F := fun t : IntWindow a => F t.val))
    (blockOldLabel (F := phaseOld (fun t : ParityWindow a ε => F t.val.val) K))
    (fun o => validBirthMark a ε (blockOldStage o))
    (fun o => (ofLex (blockOldStage o)).2) test

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable def residualDelta : ℝ := ((2 : ℝ)^26)⁻¹

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Probability
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def residualBad (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : Prop :=
  ∃ R ∈ F, t < (R.card : ℝ) ∧ R ⊆ S

noncomputable def residualBadIndicator (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : ℝ := by
  classical
  exact if residualBad F t S then 1 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Transfer
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

noncomputable def tripleMaskExpectation (p q r : α → ℝ) (V : Finset α)
    (f : Finset α → Finset α → Finset α → ℝ) : ℝ :=
  bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (f D C)))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Statistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α]

noncomputable def nominalLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  {e | e ∈ U ∧ activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    e ∈ nominalPath M hE κ D C h b.val.val ∧ e ∉ nominalPath M hE κ D C h (b.val.val - 1)}

noncomputable def nominalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M (nominalLayerSet M hE κ D C h U ε b \ O)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : Set α :=
  (I ∩ nominalLayerSet M hE κ D C h U ε b) \
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def safeLayerStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε, (safeLayerSet M hE κ D C T h U I ε b).ncard

def boolParity (parity : Bool) : Fin 2 := if parity then 1 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  univ.filter fun e => candidate M d s e (s e) ∧ s e = some i

@[simp] lemma mem_trueGroup (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (e : Fin n) :
    e ∈ trueGroup M d s i ↔ candidate M d s e (s e) ∧ s e = some i := by
  simp [trueGroup]

def withMasks (d : MainMasks n) (A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := A, C := B, T := C }

@[simp] lemma candidate_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (withMasks d A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_withMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (withMasks d A B C) s i = trueGroup M d s i := rfl

def focalMasks (d : MainMasks n) (U A B C : Finset (Fin n)) : MainMasks n :=
  { d with D := (d.D \ U) ∪ A, C := (d.C \ U) ∪ B, T := (d.T \ U) ∪ C }

@[simp] lemma candidate_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ) :
    candidate M (focalMasks d U A B C) s e v ↔ candidate M d s e v := Iff.rfl

@[simp] lemma trueGroup_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (U A B C : Finset (Fin n)) (s : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M (focalMasks d U A B C) s i = trueGroup M d s i := rfl

noncomputable def focalReference (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : MainMasks n :=
  focalMasks d (trueGroup M d s i) (trueGroup M d s i) ∅ ∅

noncomputable def focalIndex (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : ℕ :=
  (groups M (focalReference M d s i) s).idxOf i

end MatroidProphet.MainAlgorithm

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

namespace MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def listedSafeStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    safeLayerStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) ε
  else 0

noncomputable def listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) : ℕ :=
  if i ∈ groups M d s then
    nominalRankStatistic M hE κ (groupMask M d s d.D) (groupMask M d s d.C)
      (groupMask M d s d.T) ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) ε
  else 0

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_LabeledFamily
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

noncomputable def groupLabel (U : Finset α) (i : Fin U.card) : α := (U.equivFin.symm i).val

noncomputable def labeledResidualFamily (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) : Finset (Finset α) :=
  (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).image
    (fun R => R.image (groupLabel U))

noncomputable def nominalResidualSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) : Set α :=
  ⋃ b, nominalLayerSet M hE κ D C h U ε b \
    M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
      lowerCompetition M hE κ D C T b.val.val h) ∪ W b)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Gap
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

noncomputable def nominalTransferGap (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) : ℝ :=
  max ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_BatchReveal
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.map (f : β → γ) : RevealTree α β → RevealTree α γ
  | .leaf b => .leaf (f b)
  | .query e no yes => .query e (no.map f) (yes.map f)

def revealBatch : List α → (Finset α → RevealTree α β) → RevealTree α β
  | [], cont => cont ∅
  | e :: xs, cont => .query e (revealBatch xs cont)
      (revealBatch xs (fun I => cont (insert e I)))

structure RevealRecord (α β : Type*) where
  value : β
  queried : Finset α
  positive : Finset α

def RevealTree.record : RevealTree α β → RevealTree α (RevealRecord α β)
  | .leaf b => .leaf ⟨b, ∅, ∅⟩
  | .query e no yes => .query e
      (no.record.map (fun r => ⟨r.value, insert e r.queried, r.positive⟩))
      (yes.record.map (fun r => ⟨r.value, insert e r.queried, insert e r.positive⟩))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Certificates_Budget
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

inductive QueryProgram (α : Type*) where
  | stop
  | query (e : α) (no yes : QueryProgram α)
  | finish (rest : QueryProgram α)

def QueryProgram.Fresh : QueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)
  | .finish rest, V => rest.Fresh V

noncomputable def QueryProgram.expected (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => (1 - q e) * no.expected cert q I +
      q e * yes.expected cert q (insert e I)
  | .finish rest, I => (if cert I then 1 else 0) + rest.expected cert q ∅

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Certificates_Execution
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

def QueryProgram.run (cert : Finset α → Prop) [DecidablePred cert]
    (S : Finset α) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => if e ∈ S then yes.run cert S (insert e I) else no.run cert S I
  | .finish rest, I => (if cert I then 1 else 0) + rest.run cert S ∅

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RevealComposition
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.bind (tree : RevealTree α β) (cont : β → RevealTree α γ) : RevealTree α γ :=
  match tree with
  | .leaf b => cont b
  | .query e no yes => .query e (no.bind cont) (yes.bind cont)

def RevealTree.transaction (tree : RevealTree α β) (cont : β → QueryProgram α) : QueryProgram α :=
  match tree with
  | .leaf b => .finish (cont b)
  | .query e no yes => .query e (no.transaction cont) (yes.transaction cont)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Exposure
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseLayer (α : Type*) where
  group : Finset α
  density : Set α
  state : Set α
  enabledAt : ℤ

noncomputable def layerNominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Set α :=
  densityEnabled M hE κ L.density L.enabledAt k A

noncomputable def layerBatch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Finset α :=
  L.group.filter (fun e => e ∈ L.state ∧ e ∉ layerNominal M hE κ k L A)

noncomputable def layerUpdate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) : Set α :=
  M.closure (layerNominal M hE κ k L A ∪ ((C : Set α) ∩ (L.group : Set α) ∩ L.state))

noncomputable def runReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Set α
  | [], A, _ => A
  | L::Ls, A, C => runReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

noncomputable def reverseExposureTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → RevealTree α (Set α)
  | [], A => .leaf A
  | L::Ls, A =>
      revealBatch (layerBatch M hE κ k L A).toList (fun I =>
        reverseExposureTree M hE κ k Ls (M.closure (layerNominal M hE κ k L A ∪ (I : Set α))))

def sourceLayer (D S : ℕ → Set α) (G : ℕ → Finset α) (j : ℕ) : ReverseLayer α :=
  ⟨G j, D j, S j, activation j⟩

def sourceLayers (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) : List (ReverseLayer α) :=
  (List.range n).map (sourceLayer D S G)

noncomputable def queriedReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Finset α
  | [], _, _ => ∅
  | L::Ls, A, C => layerBatch M hE κ k L A ∪
      queriedReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Hybrid
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def sourceReverseTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (Set α) :=
  reverseExposureTree M hE κ k (sourceLayers D S G n)
    (if k < 0 then M.closure ∅ else Set.univ)

noncomputable def transitionHybrid (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (j : ℕ) : Set α :=
  ((C : Set α) ∩ (G j : Set α) ∩
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∪
  ((T : Set α) ∩ (G j : Set α) ∩
    (S j \ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Iteration
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def ReverseClosed (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ)
    (D : ℕ → Set α) (k : ℤ) (S : ℕ → Set α) : Prop :=
  ∀ C j, reverseNominal M hE κ D C S k j ⊆ S j

noncomputable def reverseStepTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (ℕ → Set α) :=
  (sourceReverseTree M hE κ k D S G n).record.map
    (fun r j => reverseNominal M hE κ D (fun i => (r.positive : Set α) ∩ (G i : Set α)) S k j)

noncomputable def reverseTransactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) : ℕ → ℤ → (ℕ → Set α) → QueryProgram α
  | 0, _, _ => .stop
  | m+1, k, S => if stop k S then .stop else
      (reverseStepTree M hE κ k D S G n).transaction
        (fun S' => reverseTransactions M hE κ D G n stop m (k-1) S')

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Certificates
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseNonexitCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => if stop k S then 0 else
      (if d ∈ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) +
        reverseNonexitCount M hE κ D G n stop d h m (k-1)
          ((reverseStepTree M hE κ k D S G n).run C) C

noncomputable def reverseStayEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ)
    (C : Finset α) : Prop :=
  d ∈ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k h

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Cost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
      reverseCost M hE κ D G n cost m (k-1)
        ((reverseStepTree M hE κ k D S G n).run C) C

noncomputable def reverseMeanCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsExpectation q univ (reverseCost M hE κ D G n cost m k S)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Hazard
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseHazard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsFailure (reverseStayEvent M hE κ D S G k d h) q univ ∅

noncomputable def bandNonexitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S' h then 1 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Trace
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseTransition (α : Type*) where
  time : ℤ
  before : ℕ → Set α
  after : ℕ → Set α

noncomputable def reverseTrace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → List (ReverseTransition α)
  | 0, _, _, _ => []
  | m+1, k, S, C =>
      ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ ::
      reverseTrace M hE κ D G n m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C

noncomputable def traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : Finset ℝ :=
  univ.biUnion (fun C : Finset α => ((reverseTrace M hE κ D G n m k S C).map
    (fun t => reverseHazard M hE κ D G q d h t.time t.before)).toFinset)

noncomputable def reverseFinal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → (ℕ → Set α)
  | 0, _, S, _ => S
  | m+1, k, S, C => reverseFinal M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C) C

noncomputable def exitCost (d : α) (h : ℕ) (_ : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ d ∉ S' h then 1 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_PrefixTree
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reversePrefixTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → RevealTree α (ℕ → Set α)
  | 0, _, S => .leaf S
  | m+1, k, S => (reverseStepTree M hE κ k D S G n).bind
      (fun S' => reversePrefixTree M hE κ D G n m (k-1) S')

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ExitNumerics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

noncomputable def hazardBandBound (l : ℕ) : ℝ :=
  (((l : ℝ) + 1) * Real.log 2 + 1) / 2 ^ l

noncomputable def hazardTailPotential (l : ℕ) : ℝ :=
  2 * (((l : ℝ) + 2) * Real.log 2 + 1) / 2 ^ l

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_HazardCover
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

noncomputable def inHazardBand (p : ℝ) (l : ℕ) : Prop :=
  ((2 : ℝ) ^ (l+1))⁻¹ ≤ p ∧ p < ((2 : ℝ) ^ l)⁻¹

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Bands
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def bandExitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h ∧ d ∉ S' h then 1 else 0

noncomputable def bandCountCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h then 1 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_LowHazard
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def bandHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h
    then reverseHazard M hE κ D G q d h k S else 0

noncomputable def lowHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (η : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ reverseHazard M hE κ D G q d h k S < η
    then reverseHazard M hE κ D G q d h k S else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Squared
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def exitHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then reverseHazard M hE κ D G q d h k S else 0

noncomputable def squareHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_BirthSafety
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseDoubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (h : ℕ) (d : α)
    (C T : Finset α) : ℝ :=
  if d ∈ S h then
    (if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) *
    (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k h then 1 else 0)
  else 0

noncomputable def safeBirthEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (b : ℤ)
    (C T : Finset α) : Prop :=
  nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_SquareSum
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def pathExitSquare (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ) (m : ℕ)
    (C : Finset α) : ℝ :=
  if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
    (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
      (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SafeSamples
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T then 1 else 0

noncomputable def safeCountBeforeParity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) : ℝ :=
  ∑ d ∈ I, safeEndpointCount M hE κ D G h d C T

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SafeParity
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointParityCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧
    (-(i:ℤ)) % 2 = (if parity then 1 else 0) then 1 else 0

noncomputable def safeSampleCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : ℝ :=
  ∑ d ∈ I, safeEndpointParityCount M hE κ D G h d C T parity

noncomputable def fairParityExpectation (f : Bool → ℝ) : ℝ := (f false + f true) / 2

noncomputable def IsSafeSample (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : Prop :=
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  activation h + 2 ≤ b ∧ b ≤ 0 ∧ b % 2 = (if parity then 1 else 0) ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

noncomputable def safeSampleSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : Finset α :=
  I.filter (fun d => IsSafeSample M hE κ D G h d C T parity)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FocalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset Pivots
variable {n : ℕ}

noncomputable def listedTransferGap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℝ :=
  max ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0

noncomputable def focalResidualFamily (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) :
    Finset (Finset (Fin n)) :=
  let r := focalReference M d s i
  labeledResidualFamily M (trueGroup M d s i) κ
    (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i))
    (activation (focalIndex M d s i)) ε
    (fun b => lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
      (groupMask M r s r.T) b.val.val (focalIndex M d s i))

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainMean (d : MainMasks n) (f : MainMasks n → ℝ) : ℝ :=
  tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
    univ (fun D C T => fairParityExpectation (fun p => f {withMasks d D C T with odd := p}))

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_SeedLaw
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def seedSet {bits : ℕ} (r : Seed bits) : Finset (Fin bits) :=
  Finset.univ.filter fun e => r e = true

noncomputable def setSeed {bits : ℕ} (S : Finset (Fin bits)) : Seed bits :=
  fun e => decide (e ∈ S)

@[simp] lemma seedSet_setSeed {bits : ℕ} (S : Finset (Fin bits)) : seedSet (setSeed S) = S := by
  classical
  ext e
  simp [seedSet, setSeed]

@[simp] lemma setSeed_seedSet {bits : ℕ} (r : Seed bits) : setSeed (seedSet r) = r := by
  funext e
  simp [seedSet, setSeed]

noncomputable def seedFinsetEquiv (bits : ℕ) : Seed bits ≃ Finset (Fin bits) where
  toFun := seedSet
  invFun := setSeed
  left_inv := setSeed_seedSet
  right_inv := seedSet_setSeed

lemma seedWeight_sum {bits : ℕ} (q : Fin bits → ℝ) :
    (∑ r : Seed bits, bitsWeight q Finset.univ (seedSet r)) = 1 := by
  classical
  have h := (seedFinsetEquiv bits).sum_comp (bitsWeight q Finset.univ)
  change (∑ r, bitsWeight q Finset.univ ((seedFinsetEquiv bits) r)) = 1
  rw [h]
  simpa only [bitsExpectation, Finset.powerset_univ, mul_one] using
    bitsExpectation_one q Finset.univ

noncomputable def seedPMF {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : PMF (Seed bits) :=
  PMF.ofFintype (fun r => ENNReal.ofReal (bitsWeight q Finset.univ (seedSet r))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => bitsWeight_nonneg q h0 h1 _ _),
      seedWeight_sum, ENNReal.ofReal_one])

noncomputable def bernoulliSeedLaw {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : Measure (Seed bits) :=
  (seedPMF q h0 h1).toMeasure

instance bernoulliSeedLaw_probability {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) :
    IsProbabilityMeasure (bernoulliSeedLaw q h0 h1) := by
  unfold bernoulliSeedLaw
  infer_instance

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_SeedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

abbrev MainSeedBlocks (n : ℕ) := Seed n × (Seed n × (Seed n × (Seed n × Seed 2)))

noncomputable def encodeMainSeed {n : ℕ} (b : MainSeedBlocks n) : Seed (mainSeedBits n) :=
  fun i => if hi : i.val < 4*n then
    let e : Fin n := ⟨i.val / 4, by omega⟩
    if i.val % 4 = 0 then b.1 e else
    if i.val % 4 = 1 then b.2.1 e else
    if i.val % 4 = 2 then b.2.2.1 e else b.2.2.2.1 e
  else b.2.2.2.2 ⟨i.val-4*n, by have := i.isLt; dsimp [mainSeedBits] at this; omega⟩

noncomputable def maskCoinLaw (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Measure (Seed n) :=
  bernoulliSeedLaw (fun _ => p) (fun _ => h0) (fun _ => h1)

instance maskCoinLaw_probability (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (maskCoinLaw n p h0 h1) := by
  unfold maskCoinLaw
  infer_instance

noncomputable def mainBlockLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (MainSeedBlocks n) :=
  (maskCoinLaw n (q 0) (h0 0) (h1 0)).prod
    ((maskCoinLaw n (q 1) (h0 1) (h1 1)).prod
      ((maskCoinLaw n (q 2) (h0 2) (h1 2)).prod
        ((maskCoinLaw n (q 3) (h0 3) (h1 3)).prod
          (maskCoinLaw 2 (q 4) (h0 4) (h1 4)))))

instance mainBlockLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainBlockLaw n q h0 h1) := by
  unfold mainBlockLaw
  infer_instance

noncomputable def mainSeedLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (Seed (mainSeedBits n)) :=
  (mainBlockLaw n q h0 h1).map encodeMainSeed

instance mainSeedLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainSeedLaw n q h0 h1) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RankCost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset

variable {α : Type*} [Fintype α]

noncomputable def parityPoints (a : ℤ) (ε : Fin 2) : Finset ℤ :=
  Finset.univ.image (fun b : Pivots.ParityWindow a ε => b.val.val)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_PathStatistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def testRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h final : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (guardedPath M hE κ D C final (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Statistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset Pivots
variable {n : ℕ}

noncomputable def pathGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) : Finset (Fin n) := by
  classical
  exact (groupMask M d w univ h).toFinset

noncomputable def listedLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groups M d w).length (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (d.T : Set (Fin n)) (boolParity d.odd)

noncomputable def listedZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)

noncomputable def trueLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedLambda M hE d w ((groups M d w).idxOf i) else 0

noncomputable def trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedZ M hE d w ((groups M d w).idxOf i) else 0

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Algorithm_Worst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) : ℝ := by
  classical
  exact univ.inf' univ_nonempty (fun π : ArrivalOrder n =>
    ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e))

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Candidates
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Finset Set

namespace MatroidProphet
namespace Candidates

variable {n : ℕ}

def prior (time : Fin n → ℕ) (H : Finset (Fin n)) (e : Fin n) : Set (Fin n) :=
  {f | f ∈ H ∧ time f < time e}

noncomputable def greedy (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact H.filter fun e => e ∉ M.closure (prior time H e)

noncomputable def candidates (M : Matroid (Fin n)) (time : Fin n → ℕ)
    (V H : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact (V \ H).filter fun e => e ∉ M.closure (prior time H e)

end Candidates
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Basic
attribute [-instance] _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Maximum

open MeasureTheory Finset Set

variable {n bits : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K]

noncomputable def firstRule (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop) : OnlineRule n bits := by
  classical
  exact discreteOnlineRule key hkey (fun k r s hist => decide
    (allowed r s (hist ⟨k.val, Nat.lt_succ_self _⟩) ∧
      ∀ j : Fin (k.val + 1), j.val < k.val → ¬ allowed r s (hist j)))

def higher [LinearOrder K] (x y : Fin n × K) : Prop :=
  y.2 < x.2 ∨ (x.2 = y.2 ∧ x.1 < y.1)

def threshold [LinearOrder K] (M : Matroid (Fin n)) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (r : Seed bits) (s : Fin n → K)
    (x : Fin n × K) : Prop :=
  x.1 ∉ mask r ∧ M.Indep ({x.1} : Set (Fin n)) ∧ active x.2 ∧
    ∀ f ∈ mask r, M.Indep ({f} : Set (Fin n)) → active (s f) → higher x (f, s f)

noncomputable def maximumRule [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : OnlineRule n bits :=
  firstRule key hkey (threshold M active mask)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_irrefl [LinearOrder K] (x : Fin n × K) : ¬ higher x x := by
  simp [higher]

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_trans [LinearOrder K] {x y z : Fin n × K}
    (hxy : higher x y) (hyz : higher y z) : higher x z := by
  rcases hxy with hxy | ⟨hxy, hxy'⟩ <;> rcases hyz with hyz | ⟨hyz, hyz'⟩
  · exact Or.inl (hyz.trans hxy)
  · exact Or.inl (hyz ▸ hxy)
  · exact Or.inl (hxy ▸ hyz)
  · exact Or.inr ⟨hxy.trans hyz, hxy'.trans hyz'⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_total [LinearOrder K] {x y : Fin n × K} (h : x ≠ y) :
    higher x y ∨ higher y x := by
  rcases lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · have hn : x.1 ≠ y.1 := fun hxy => h (Prod.ext hxy heq)
    rcases lt_or_gt_of_ne hn with hxy | hyx
    · exact Or.inl (Or.inr ⟨heq, hxy⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hyx⟩)
  · exact Or.inl (Or.inl hgt)

noncomputable def maximumHidden [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  ⟨mask, maximumRule M key hkey active mask⟩

end Maximum
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Simulation
attribute [-instance] _root_.OAI.MatroidProphet.bernoulliSeedLaw_probability _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

noncomputable def glue {n : ℕ} (mask : Finset (Fin n)) (s v : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ mask then s e else v e

lemma measurable_weight_eval {n : ℕ} :
    Measurable (fun x : Weights n × Fin n => x.1 x.2) :=
  measurable_from_prod_countable_left fun e => measurable_pi_apply e

noncomputable def simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s : Weights n) {k : Fin n} (h : History n k) : History n k := by
  classical
  exact fun j => ((h j).1, if (h j).1 ∈ A.mask r then s (h j).1 else (h j).2)

lemma measurable_simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (k : Fin n) :
    Measurable (fun x : Weights n × History n k => simulationHistory A r x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro j
  have hh : Measurable (fun x : Weights n × History n k => x.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hm : MeasurableSet {x : Weights n × History n k | (x.2 j).1 ∈ A.mask r} :=
    (measurable_fst.comp hh) (by trivial)
  exact (measurable_fst.comp hh).prodMk (Measurable.ite hm
    (measurable_weight_eval.comp (measurable_fst.prodMk (measurable_fst.comp hh)))
    (measurable_snd.comp hh))

lemma measurable_observed {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits) :
    Measurable (observed A r) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ A.mask r
  · simpa [observed, he] using (measurable_pi_apply e : Measurable (fun w : Weights n => w e))
  · simp [observed, he]

def currentLabel {n : ℕ} {k : Fin n} (h : History n k) : Fin n :=
  (h ⟨k.val, Nat.lt_succ_self _⟩).1

noncomputable def sampleSimulation {n bits : ℕ} (A : HiddenRule n bits) : OnlineRule n bits where
  decide k r s h := if currentLabel h ∈ A.mask r then false
    else A.core.decide k r (observed A r s) (simulationHistory A r s h)
  measurable_decide k := by
    classical
    apply measurable_from_prod_countable_right
    intro r
    have hc : Measurable (fun x : Weights n × History n k => currentLabel x.2) :=
      measurable_fst.comp ((measurable_pi_apply (⟨k.val, Nat.lt_succ_self _⟩ : Fin (k.val + 1))).comp measurable_snd)
    have hm : MeasurableSet {x : Weights n × History n k | currentLabel x.2 ∈ A.mask r} :=
      hc (by trivial)
    exact Measurable.ite hm measurable_const
      ((A.core.measurable_decide k).comp (measurable_const.prodMk
        (((measurable_observed A r).comp measurable_fst).prodMk
          (measurable_simulationHistory A r k))))

@[simp] lemma currentLabel_history {n : ℕ} (v : Weights n)
    (π : ArrivalOrder n) (k : Fin n) : currentLabel (history v π k) = π k := by
  rfl

@[simp] lemma glue_self {n : ℕ} (mask : Finset (Fin n)) (w : Weights n) :
    glue mask w w = w := by
  classical
  funext e
  simp [glue]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GreedyOptimal
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Candidates

open Finset Set

variable {n : ℕ}

noncomputable def prefixCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ((I.filter fun e => time e < k).card : ℝ)

noncomputable def timeCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ e ∈ I, if time e = k then 1 else 0

noncomputable def orderedWeights (w : Weights n) (order : ArrivalOrder n) (i : ℕ) : ℝ :=
  if hi : i < n then w (order ⟨i, hi⟩) else 0

def priorityTime (order : ArrivalOrder n) (e : Fin n) : ℕ := (order.symm e).val

@[simp] lemma orderedWeights_priorityTime (w : Weights n) (order : ArrivalOrder n) (e : Fin n) :
    orderedWeights w order (priorityTime order e) = w e := by
  simp [orderedWeights, priorityTime]

end Candidates
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Priority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

namespace Priority

def asLevel (x : Option ℤ) : WithBot ℤ := x

@[simp] lemma asLevel_none : asLevel none = ⊥ := rfl
@[simp] lemma asLevel_some (i : ℤ) : asLevel (some i) = (i : WithBot ℤ) := rfl

open Finset Set

variable {n : ℕ}

def Higher (a : Fin n → Option ℤ) (e f : Fin n) : Prop :=
  Maximum.higher (K := WithBot ℤ) (e, asLevel (a e)) (f, asLevel (a f))

noncomputable def earlier (a : Fin n → Option ℤ) (e : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => Higher a f e

noncomputable def time (a : Fin n → Option ℤ) (e : Fin n) : ℕ := (earlier a e).card

lemma higher_trans (a : Fin n → Option ℤ) {e f g : Fin n}
    (hef : Higher a e f) (hfg : Higher a f g) : Higher a e g :=
  Maximum.higher_trans hef hfg

lemma higher_irrefl (a : Fin n → Option ℤ) (e : Fin n) : ¬ Higher a e e :=
  Maximum.higher_irrefl _

lemma higher_total (a : Fin n → Option ℤ) {e f : Fin n} (hef : e ≠ f) :
    Higher a e f ∨ Higher a f e :=
  Maximum.higher_total (fun h => hef (congrArg Prod.fst h))

lemma time_lt_of_higher (a : Fin n → Option ℤ) {e f : Fin n} (hef : Higher a e f) :
    time a e < time a f := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact higher_trans a hg hef
  · intro heq
    have he : e ∈ earlier a f := by simp [earlier, hef]
    rw [← heq] at he
    exact higher_irrefl a e (by simpa [earlier] using he)

lemma time_injective (a : Fin n → Option ℤ) : Function.Injective (time a) := by
  intro e f h
  by_contra hef
  rcases higher_total a hef with hh | hh
  · have := time_lt_of_higher a hh
    omega
  · have := time_lt_of_higher a hh
    omega

lemma time_lt_card (a : Fin n → Option ℤ) (e : Fin n) : time a e < n := by
  classical
  have hss : earlier a e ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have he : e ∈ earlier a e := heq.symm ▸ Finset.mem_univ e
    exact higher_irrefl a e (by simpa [earlier] using he)
  simpa [time] using Finset.card_lt_card hss

noncomputable def timeEquiv (a : Fin n → Option ℤ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun e => ⟨time a e, time_lt_card a e⟩)
    (by
      have hi : Function.Injective (fun e => (⟨time a e, time_lt_card a e⟩ : Fin n)) :=
        fun e f h => time_injective a (congrArg Fin.val h)
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

noncomputable def order (a : Fin n → Option ℤ) : ArrivalOrder n := (timeEquiv a).symm

@[simp] lemma priorityTime_order (a : Fin n → Option ℤ) :
    Candidates.priorityTime (order a) = time a := rfl

end Priority
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_BranchMix
attribute [-instance] _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory

noncomputable def branchOnlineRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : OnlineRule n bits) : OnlineRule n bits where
  decide k r s h := if branch r then A.decide k r s h else B.decide k r s h
  measurable_decide k := by
    have hb : Measurable (fun x : Seed bits × (Weights n × History n k) => branch x.1) :=
      (measurable_of_countable branch).comp measurable_fst
    exact Measurable.ite (hb (measurableSet_singleton true))
      (A.measurable_decide k) (B.measurable_decide k)

noncomputable def branchHiddenRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) : HiddenRule n bits where
  mask r := if branch r then A.mask r else B.mask r
  core := branchOnlineRule branch A.core B.core

instance withBotIntMeasurableSpace : MeasurableSpace (WithBot ℤ) := ⊤
instance withBotIntMeasurableSingletonClass : MeasurableSingletonClass (WithBot ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedMaximumHidden {n : ℕ} (M : Matroid (Fin n))
    {bits : ℕ} (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  Maximum.maximumHidden M (fun x => Priority.asLevel (roundedLevel weightBase x))
    ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
    (fun a => a ≠ ⊥) mask

noncomputable def completeHiddenRule {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) :=
  branchHiddenRule mainBranch (MainAlgorithm.hidden M hE)
    (roundedMaximumHidden M (fun r => (mainMasks r).H))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Score
attribute [-instance] _root_.OAI.MatroidProphet.mainBlockLaw_probability _root_.OAI.MatroidProphet.mainSeedLaw_probability _root_.OAI.MatroidProphet.maskCoinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin n) =>
    match o with
    | none => 0
    | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)

noncomputable def maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ :=
  ∫ r, hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w r
    ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CandidateFilter
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset Set

variable {n : ℕ}

noncomputable def candidateSet (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => candidate M d a e (a e)

noncomputable def candidateLabels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset (Fin n) := candidateSet M ⟨H, ∅, ∅, ∅, false⟩ a

noncomputable def positiveGreedy (M : Matroid (Fin n)) (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact (Candidates.greedy M (Priority.time a) Finset.univ).filter fun e => a e ≠ none

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_WeightGroups
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {n : ℕ}

noncomputable def weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) : Finset ℤ :=
  U.biUnion fun e => (a e).toFinset

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_AnalyzedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

noncomputable def trueLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := weightLevels a (candidateLabels M a H)

noncomputable def analyzedLevels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset ℤ := by
  classical
  exact (trueLevels M a H).filter fun i =>
    densityThreshold ≤ ((candidateLabels M a H).filter (fun e => a e = some i)).card

noncomputable def comparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ :=
  ∑ e ∈ positiveGreedy M a \ H, levelWeight weightBase (a e)

noncomputable def analyzedComparisonMass (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ i ∈ analyzedLevels M a H, weightBase ^ i *
    (((positiveGreedy M a \ H).filter (fun e => a e = some i)).card : ℝ)

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Maximum_Mask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable def maximumForMask {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (H : Finset (Fin n)) : ℝ :=
  hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w (setSeed H)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Seed
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def sourceCoinProbability (j : Fin 5) : ℝ :=
  if j.val = 0 then 1/2 else if j.val = 1 then 1/4 else if j.val = 4 then 1/2 else thinningRate

lemma sourceCoinProbability_nonneg (j : Fin 5) : 0 ≤ sourceCoinProbability j := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

lemma sourceCoinProbability_le_one (j : Fin 5) : sourceCoinProbability j ≤ 1 := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

noncomputable def sourceSeedLaw (n : ℕ) : Measure (Seed (mainSeedBits n)) :=
  mainSeedLaw n sourceCoinProbability sourceCoinProbability_nonneg sourceCoinProbability_le_one

instance sourceSeedLaw_probability (n : ℕ) : IsProbabilityMeasure (sourceSeedLaw n) := by
  unfold sourceSeedLaw
  infer_instance

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_CompletePayoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

noncomputable def mainPayoff {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) : ℝ :=
  bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (fun H =>
    mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupSafety
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) : Finset (Fin n) :=
  (groupMask M d s univ j).toFinset

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupPayoff
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def higherTrueGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_KernelModel
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite conditional seed kernels

The observation map can include the branch and the sacrificed mask. Its domain
is the *complete* source seed, so conditioning does not discard unused coins.
These definitions are independent of every proposed selection-rule proof.
-/

namespace MatroidProphet.Secretary

open scoped BigOperators

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- The source mass of a fiber of the observation map. -/
noncomputable def fiberMass (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

/-- The conditional source mass, totalized by a fixed point mass on empty fibers.
The fallback only concerns observations of source probability zero. -/
noncomputable def fiberKernel (p : α → ℝ) (f : α → β) (fallback : α)
    (b : β) (a : α) : ℝ :=
  if fiberMass p f b = 0 then
    if a = fallback then 1 else 0
  else if f a = b then p a / fiberMass p f b else 0

end MatroidProphet.Secretary

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_ConditionalLaw
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact normalization, support, and joint-law identities for finite conditional
seed reconstruction. This is supporting work for `cor:secretary`; it does not
assume a prefix law or supply the online secretary construction by itself.
-/

namespace MatroidProphet.Secretary

open scoped BigOperators

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
theorem fiberMass_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (b : β) : 0 ≤ fiberMass p f b := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

theorem fiberKernel_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (b : β) (a : α) :
    0 ≤ fiberKernel p f fallback b a := by
  unfold fiberKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (hp a) (fiberMass_nonneg p hp f b)
  · exact le_rfl

theorem fiberKernel_sum (p : α → ℝ) (f : α → β)
    (fallback : α) (b : β) : ∑ a, fiberKernel p f fallback b a = 1 := by
  by_cases hb : fiberMass p f b = 0
  · simp [fiberKernel, hb]
  · simp only [fiberKernel, hb, ite_false]
    calc
      (∑ a, if f a = b then p a / fiberMass p f b else 0) =
          (∑ a, if f a = b then p a else 0) / fiberMass p f b := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      _ = 1 := div_self hb

end MatroidProphet.Secretary

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_PrefixObservationModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

/-- The first `K` labels of a complete order, used only to specify the experiment. -/
def orderPrefix {n : ℕ} (π : ArrivalOrder n) (K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun e => (π.symm e).val < K

/-- Labels visible in the observation prefix of the currently available history. -/
def prefixLabels {n : ℕ} {k : Fin n} (K : ℕ) (h : History n k) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin (k.val + 1) => j.val < K).image fun j => (h j).1

/-- The observed weights, extended by zero away from the observation prefix.
Repeated labels in malformed histories are summed; genuine histories have none. -/
noncomputable def prefixWeights {n : ℕ} {k : Fin n} (K : ℕ)
    (h : History n k) : Weights n :=
  fun e => ∑ j : Fin (k.val + 1), if j.val < K ∧ (h j).1 = e then (h j).2 else 0

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_ProbabilityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-side arrival law for the actual random-prefix secretary experiment. -/
namespace MatroidProphet.Secretary
open MeasureTheory

instance uniformArrivalLaw_probability (n : ℕ) :
    IsProbabilityMeasure (uniformArrivalLaw n) := by
  unfold uniformArrivalLaw
  infer_instance

end MatroidProphet.Secretary

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Weights_FiniteWeightLawModel
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.FiniteLaw

open MeasureTheory
open scoped BigOperators

noncomputable def weightPMF {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a), hp1]
    exact ENNReal.ofReal_one)

noncomputable def weightMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) : Measure α :=
  (weightPMF p hp hp1).toMeasure

end MatroidProphet.FiniteLaw

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Weights_FiniteWeightLawTheorems
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite conditional-kernel bridge for the secretary transport.  The algebraic
fiber identity is a hypothesis of these reusable lemmas, not a substitute for
proving that identity for the manuscript's actual source-seed law.
-/

namespace MatroidProphet.FiniteLaw

open MeasureTheory
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

@[simp] theorem weightPMF_apply (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (a : α) :
    weightPMF p hp hp1 a = ENNReal.ofReal (p a) := rfl

instance weightMeasure_probability [MeasurableSpace α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    IsProbabilityMeasure (weightMeasure p hp hp1) := by
  unfold weightMeasure
  infer_instance

end MatroidProphet.FiniteLaw

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Initial-seed / random-prefix coupling

The complete table is drawn with the initial seed, before the independent
arrival permutation.  Reassociation here is only a proof of the joint law;
the implementation does not defer any table randomness until after the prefix.
-/

namespace MatroidProphet.Secretary

open MeasureTheory

variable {A B : Type*} [Fintype A] [Fintype B]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace B] [MeasurableSingletonClass B]
variable [DecidableEq A] [DecidableEq B]

/-- Normalize the actual source measure on each observation fiber. -/
noncomputable def conditionalSourceLaw (μ : Measure A) (obs : A → B)
    (fallback : A) (b : B) : Measure A :=
  FiniteLaw.weightMeasure
    (fiberKernel (fun a => μ.real {a}) obs fallback b)
    (fiberKernel_nonneg _ (fun _ => measureReal_nonneg) obs fallback b)
    (fiberKernel_sum _ obs fallback b)

instance conditionalSourceLaw_probability (μ : Measure A) (obs : A → B)
    (fallback : A) (b : B) : IsProbabilityMeasure (conditionalSourceLaw μ obs fallback b) := by
  unfold conditionalSourceLaw
  infer_instance

end MatroidProphet.Secretary

namespace MatroidProphet.Secretary

open MeasureTheory

abbrev SourceObservation (n : ℕ) := Bool × Finset (Fin n)

/-- The full source seed together with every conditional draw, all predrawn. -/
abbrev CouplingSeed (n : ℕ) :=
  Seed (mainSeedBits n) × (SourceObservation n → Seed (mainSeedBits n))

noncomputable def couplingObservation {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) : SourceObservation n :=
  (mainBranch r, (completeHiddenRule M hE).mask r)

noncomputable def couplingKernel {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) : Measure (Seed (mainSeedBits n)) :=
  conditionalSourceLaw (sourceSeedLaw n) (couplingObservation M hE) (fun _ => false) b

instance couplingKernel_probability {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) :
    IsProbabilityMeasure (couplingKernel M hE b) := by
  unfold couplingKernel
  infer_instance

/-- This initial seed law depends on the matroid but not on any weights. -/
noncomputable def couplingSeedLaw {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) : Measure (CouplingSeed n) :=
  (sourceSeedLaw n).prod (Measure.pi (couplingKernel M hE))

instance couplingSeedLaw_probability {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) : IsProbabilityMeasure (couplingSeedLaw M hE) := by
  unfold couplingSeedLaw
  infer_instance

/-- The cutoff is fixed before arrivals using only the first part of the seed. -/
noncomputable def couplingLength {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (q : CouplingSeed n) : Fin (n + 1) :=
  ⟨((completeHiddenRule M hE).mask q.1).card, by
    have h := Finset.card_le_univ ((completeHiddenRule M hE).mask q.1)
    simpa only [Fintype.card_fin, Nat.lt_succ_iff] using h⟩

/-- Lookup needs only the seed and the observed label set, not its weights or
the future suffix order. -/
def couplingDecode {n : ℕ} (q : CouplingSeed n) (P : Finset (Fin n)) :
    Seed (mainSeedBits n) := q.2 (mainBranch q.1, P)

noncomputable def couplingIndex {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (x : Seed (mainSeedBits n) × ArrivalOrder n) :
    SourceObservation n :=
  (mainBranch x.1, orderPrefix x.2 ((completeHiddenRule M hE).mask x.1).card)

end MatroidProphet.Secretary

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_Observation
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.uniformArrivalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Finset

namespace MatroidProphet

@[simp] lemma mem_orderPrefix {n : ℕ} (π : ArrivalOrder n) (K : ℕ) (e : Fin n) :
    e ∈ orderPrefix π K ↔ (π.symm e).val < K := by
  simp [orderPrefix]

@[simp] lemma prefixLabels_zero {n : ℕ} {k : Fin n} (h : History n k) :
    prefixLabels 0 h = ∅ := by
  simp [prefixLabels]

@[simp] lemma prefixWeights_zero {n : ℕ} {k : Fin n} (h : History n k) :
    prefixWeights 0 h = 0 := by
  funext e
  simp [prefixWeights]

/-- Prefix-label extraction is measurable despite the real-valued history entries. -/
lemma measurable_prefixLabels {n : ℕ} (k : Fin n) (K : ℕ) :
    Measurable (prefixLabels (k := k) K) := by
  classical
  have hl : Measurable (fun h : History n k => fun j => (h j).1) := by
    apply Measurable.of_eval
    intro j
    exact measurable_fst.comp (measurable_pi_apply j)
  exact (measurable_of_countable (fun l : Fin (k.val + 1) → Fin n =>
    (Finset.univ.filter fun j => j.val < K).image l)).comp hl

lemma measurable_prefixWeights {n : ℕ} (k : Fin n) (K : ℕ) :
    Measurable (prefixWeights (k := k) K) := by
  classical
  apply Measurable.of_eval
  intro e
  apply Finset.measurable_sum
  intro j _
  have hj : Measurable (fun h : History n k => h j) := measurable_pi_apply j
  have he : MeasurableSet {h : History n k | (h j).1 = e} :=
    (measurable_fst.comp hj) (measurableSet_singleton e)
  by_cases hKj : j.val < K
  · have hm : Measurable (fun h : History n k =>
        if (h j).1 = e then (h j).2 else (0 : ℝ)) :=
      Measurable.ite he (measurable_snd.comp hj) measurable_const
    simpa only [hKj, true_and] using hm
  · simp only [hKj, false_and, ite_false]
    exact measurable_const

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_ReplayRule
attribute [-instance] _root_.OAI.MatroidProphet.Secretary.couplingKernel_probability _root_.OAI.MatroidProphet.Secretary.couplingSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual history-only secretary rule reconstructed from a complete initial seed

The decoder consumes only the initial seed and the label set of the already
observed prefix. The observation vector is extracted from actual past arrivals.
A total mask-consistency guard rejects on unsupported decoder outcomes, ensuring
feasibility for every initial seed rather than merely almost surely.
-/

namespace MatroidProphet.SecretaryReplay

open MeasureTheory

/-- A concrete secretary rule from a hidden rule and a precommitted decoder.
The seed type is finite, but its law is arbitrary and need not be uniform. -/
noncomputable def reconstructedRule {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits) : SecretaryRule n Q where
  prefixLength := K
  measurable_prefixLength := measurable_of_finite K
  decide k q h :=
    let P := prefixLabels (K q).val h
    let r := decode q P
    if A.mask r = P then A.core.decide k r (prefixWeights (K q).val h) h else false
  measurable_decide k := by
    classical
    apply measurable_from_prod_countable_right
    intro q
    have hp := measurable_prefixLabels k (K q).val
    have hr : Measurable (fun h : History n k => decode q (prefixLabels (K q).val h)) :=
      (measurable_of_finite (decode q)).comp hp
    have hs : MeasurableSet {z : Seed bits × Finset (Fin n) | A.mask z.1 = z.2} :=
      (Set.toFinite _).measurableSet
    have hm : MeasurableSet {h : History n k |
        A.mask (decode q (prefixLabels (K q).val h)) = prefixLabels (K q).val h} :=
      (hr.prodMk hp) hs
    exact Measurable.ite hm
      ((A.core.measurable_decide k).comp
        (hr.prodMk ((measurable_prefixWeights k (K q).val).prodMk measurable_id)))
      measurable_const

end MatroidProphet.SecretaryReplay

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidSecretary_Secretary_SeedModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reindexing a secretary rule's complete initial seed

An arbitrary finite predrawn kernel table is represented by a single finite
index. This is a measurable bijection of the complete seed, not a statistic of it.
The rule continues to read only its initial seed and the available history.
-/

open MeasureTheory
namespace MatroidProphet

/-- Reindex a secretary rule through any measurable decoding map. -/
def reindexSecretarySeed {n : ℕ} {Q Q' : Type*}
    [MeasurableSpace Q] [MeasurableSpace Q']
    (A : SecretaryRule n Q) (f : Q' → Q) (hf : Measurable f) : SecretaryRule n Q' where
  prefixLength q := A.prefixLength (f q)
  measurable_prefixLength := A.measurable_prefixLength.comp hf
  decide k q h := A.decide k (f q) h
  measurable_decide k := (A.measurable_decide k).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

/-- Canonical finite-index representation, with no nonemptiness restriction. -/
noncomputable def secretaryFinSeed {n : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] (A : SecretaryRule n Q) :
    SecretaryRule n (Fin (Fintype.card Q)) :=
  reindexSecretarySeed A (Fintype.equivFin Q).symm (measurable_of_finite _)

/-- Push the complete finite seed law forward along the same canonical bijection. -/
noncomputable def secretaryFinSeedLaw {Q : Type*} [Fintype Q] [MeasurableSpace Q]
    (ν : Measure Q) : Measure (Fin (Fintype.card Q)) :=
  ν.map (Fintype.equivFin Q)

/-- Performance against every full-seed-aware suffix adversary, on an arbitrary
ambient probability space. The seed law is fixed before the weight vector. -/
def SecretaryGuarantee.{u} {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) (ν : Measure Q) (c : ℝ) : Prop :=
  ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Q) (σ π : Ω → ArrivalOrder n),
    Measurable R → Measurable σ → Measurable π →
    μ.map R = ν → μ.map σ = Secretary.uniformArrivalLaw n →
    ProbabilityTheory.IndepFun R σ μ →
    (∀ᵐ ω ∂μ, SamePrefix (A.prefixLength (R ω)).val (σ ω) (π ω)) →
    Integrable (fun ω => secretaryReward A (R ω) w (π ω)) μ ∧
      c * optimum M w ≤ ∫ ω, secretaryReward A (R ω) w (π ω) ∂μ

end MatroidProphet

end OAI
end


