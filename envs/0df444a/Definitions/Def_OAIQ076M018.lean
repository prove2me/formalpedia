-- Prove2me | Definitions.Def_OAIQ076M018
-- name    : OAIQ076M018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:11:59.048903+00:00
-- url     : https://prove2.me/theorems/6757860d-251b-4eed-8823-6ad391e5389c
-- title:
--   Definitions bundle OAIQ076M018 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 221 declarations of OpenAI's Lean: 61 definitions and 160 theorems. The definitions and types are `OAI.MinUncut.FiniteGaussian.gridPoint`, `OAI.MinUncut.FiniteGaussian.sourceTable`, `OAI.MinUncut.Outer.TupleCoordinateData`, `OAI.MinUncut.Outer.backgroundMean`, `OAI.MinUncut.Outer.firstFormCoordinates`, `OAI.MinUncut.Outer.firstTwo`, `OAI.MinUncut.Outer.formsTransport`, `OAI.MinUncut.Outer.rawPositions`, `OAI.MinUncut.Outer.tupleCoordinateGenerator`, `OAI.MinUncut.Outer.tupleCoordinateSlice`, `OAI.MinUncut.Outer.unpackFunctional`, `OAI.MinUncut.OuterSmoothness.JointForms.FullRaw`, `OAI.MinUncut.OuterSmoothness.JointForms.Raw`, `OAI.MinUncut.OuterSmoothness.JointForms.affineOutput`, `OAI.MinUncut.OuterSmoothness.JointForms.fullPull`, `OAI.MinUncut.OuterSmoothness.JointForms.hiddenLaw`, `OAI.MinUncut.OuterSmoothness.JointForms.hiddenPull`, `OAI.MinUncut.OuterSmoothness.JointForms.offset`, `OAI.MinUncut.OuterSmoothness.JointForms.output`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.RectangleSeed`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.SharedProfileSeed`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.rectangleAccept`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.rectangleDistribution`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.rectangleWeight`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.sharedProfileLeft`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.sharedProfileReject`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.sharedProfileRight`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.splitAll`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.splitRight`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.sumOnIntervals`, `OAI.MinUncutGames.Foundations.CorrelatedSampling.thresholdPartition`, `OAI.MinUncutGames.Foundations.Games.Game.coordinateGame`, `OAI.MinUncutGames.Foundations.Games.Game.localEmbeddingLaw`, `OAI.MinUncutGames.Foundations.Games.KernelSampling.seedLaw`, `OAI.MinUncutGames.Foundations.PCP.AssignmentTester.singleMask`, `OAI.MinUncutGames.Foundations.PCP.CayleySpectral.eigenvalue`, `OAI.MinUncutGames.Foundations.PCP.CayleySpectral.powerGenerators`, `OAI.MinUncutGames.Foundations.PCP.CayleySpectral.xorTranslation`, `OAI.MinUncutGames.Foundations.Repetition.CompletedSampling.completionKernel`, `OAI.MinUncutGames.Foundations.Repetition.CompletedSampling.coordinateOutputLaw` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FiniteGaussianLaw`, `MinUncut_Analysis_GaussianDensityError`, `MinUncut_Analysis_GaussianQuadrature`, `MinUncut_Analysis_GaussianRounding`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Analysis_LiteralGaussian`, `MinUncut_Encoding_ArbitraryProductWeights`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_TableLawPacking`, `MinUncut_Games_Basic`, `MinUncut_Games_JointHintBound`, `MinUncut_Games_JointHintSampling`, `MinUncut_Games_KernelSampling`, `MinUncut_Games_LabelBound`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_TotalVariation`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_HonestBudgets`, `MinUncut_Graphs_HonestComparisons`, `MinUncut_Graphs_HonestRows`, `MinUncut_Machines_OuterAlphabets`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_CompletedSampling`, `MinUncut_PCP_Completion`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_DistributionMaps`, `MinUncut_PCP_Overlap`, `MinUncut_PCP_SelectedLikelihood`, `MinUncut_PCP_SelectionSequence`.
--
--   **Imports.** It imports the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M009` and `OAIQ076M010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M023` and `OAIQ076M026`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M008
import Definitions.Def_OAIQ076M009
import Definitions.Def_OAIQ076M010

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

open scoped BigOperators
open MeasureTheory

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

lemma midpoint_distance {T : ℚ} {L : ℕ} (i : Fin L) {x : ℝ} (hx : x ∈ cell T L i) :
    |x-(midpoint T L i:ℝ)| ≤ (T:ℝ)/L := by
  have he : (endpoint T L (i.val+1):ℝ)-(endpoint T L i.val:ℝ)=2*((T:ℝ)/L) := by
    unfold endpoint
    push_cast
    ring
  have hm : (midpoint T L i:ℝ)=((endpoint T L i:ℝ)+(endpoint T L (i.val+1):ℝ))/2 := by
    unfold midpoint
    push_cast
    rfl
  rw [hm]
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

variable {ι : Type*} [Fintype ι]
def gridPoint (T : ℚ) (L : ℕ) (j : ι → Fin L) : ι → ℝ := fun i => midpoint T L (j i)

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

lemma score_grid_distance (v : ι → ℝ) {T : ℚ} {L : ℕ} {j : ι → Fin L}
    {x : ι → ℝ} (hx : x ∈ cubeCell T L j) :
    |score v x-score v (gridPoint T L j)| ≤ (∑ i, |v i|)*((T:ℝ)/L) := by
  unfold score
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |v i*x i-v i*gridPoint T L j i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| *((T:ℝ)/L) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (midpoint_distance (j i) (hx i (by simp))) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma tableTest_rounding_pointwise (v : S → ι → ℝ) {A : ℝ}
    (hA : ∀ s, (∑ i, |v s i|) ≤ A) {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
    {x : ι → ℝ} (hx : x ∈ cube T) :
    |F (thresholdTable v x)-gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x| ≤
      ∑ s, {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x := by
  rw [← cube_union hT hL] at hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  rw [gridStep_of_mem hT _ hj]
  by_cases he : thresholdTable v x=thresholdTable v (gridPoint T L j)
  · rw [he,sub_self,abs_zero]
    exact Finset.sum_nonneg (fun s _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  · obtain ⟨s,hs⟩ := Function.ne_iff.mp he
    have hdist : |score (v s) x-score (v s) (gridPoint T L j)| ≤ A*((T:ℝ)/L) :=
      (score_grid_distance (v s) hj).trans (mul_le_mul_of_nonneg_right (hA s) (by positivity))
    have hb := threshold_change_small hdist hs
    have hone : {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x=1 :=
      Set.indicator_of_mem (show x ∈ {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)} from hb) _
    have hsum := Finset.single_le_sum (s := Finset.univ) (a := s)
      (f := fun s => {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x)
      (fun _ _ => Set.indicator_nonneg (fun _ _ => by norm_num) x) (Finset.mem_univ s)
    rw [hone] at hsum
    exact (abs_le.mpr ⟨by linarith [(hF (thresholdTable v x)).1,(hF (thresholdTable v (gridPoint T L j))).2],
      by linarith [(hF (thresholdTable v x)).2,(hF (thresholdTable v (gridPoint T L j))).1]⟩).trans hsum

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

open scoped BigOperators
open MeasureTheory

lemma gCell_nonneg {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (i : Fin L) :
    0 ≤ gCell T L i := by
  exact (gIntegral_pos (by exact_mod_cast endpoint_lt hT hL i)).le

lemma gCell_le_qCell {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (r : ℕ) (i : Fin L) :
    gCell T L i ≤ qCell r T L i := by
  unfold gCell qCell gIntegral
  rw [qIntegral_cast]
  apply intervalIntegral.integral_mono (by exact_mod_cast (endpoint_lt hT hL i).le)
    (continuous_baseDensity.intervalIntegrable _ _) ((continuous_density r).intervalIntegrable _ _)
  intro v
  have hh := (evenExp_error (by positivity : 0 ≤ v^2/2) r).1
  dsimp [densityPolynomial,baseDensity]
  simpa only [neg_div] using (sub_nonneg.mp hh)

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

lemma gaussian_cubeCell {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 < T)
    {L : ℕ} (hL : 0 < L) (j : ι → Fin L) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cubeCell T L j)=
      gaussianConstant^(Fintype.card ι)*∏ i, gCell T L (j i) := by
  unfold cubeCell cell Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ i, (gaussianReal 0 1).real (Ioc (endpoint T L (j i):ℝ) (endpoint T L (j i+1))))=_
  simp only [gaussian_Ioc (endpoint_lt hT hL _).le]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,gCell]

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianRounding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace MinUncut.FiniteGaussian
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

lemma setIntegral_tableTest_rounding (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    (∫ x in cube T, |F (thresholdTable v x)-
      gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x| ∂gaussianLaw ι) ≤
      2*(Fintype.card S)*A*((T:ℝ)/L) := by
  let B (s : S) := {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ))
  have hB (s : S) : Integrable (B s) (gaussianLaw ι) := smallBall_indicator_integrable _ _
  have hi := ((tableTest_integrable v F hF).sub (gridStep_integrable T L
    (fun j => F (thresholdTable v (gridPoint T L j))))).abs
  have hnonneg (x : ι → ℝ) : 0 ≤ ∑ s, B s x :=
    Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  calc
    _ ≤ ∫ x in cube T, ∑ s, B s x ∂gaussianLaw ι :=
      setIntegral_mono_on hi.integrableOn (integrable_finsetSum _ (fun s _ => hB s)).integrableOn
        (cube_measurable T) (fun x hx => tableTest_rounding_pointwise v hA hT hL F hF hx)
    _ ≤ ∫ x, ∑ s, B s x ∂gaussianLaw ι :=
      setIntegral_le_integral (integrable_finsetSum _ (fun s _ => hB s)) (Filter.Eventually.of_forall hnonneg)
    _ = ∑ s, (gaussianLaw ι).real {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)} := by
      rw [integral_finsetSum _ (fun s _ => hB s)]
      apply Finset.sum_congr rfl
      intro s _
      rw [show B s={x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) by rfl,
        integral_indicator (measurableSet_le (by unfold score; fun_prop) measurable_const),
        setIntegral_const,smul_eq_mul,mul_one]
    _ ≤ ∑ _ : S, 2*(A*((T:ℝ)/L)) :=
      Finset.sum_le_sum (fun s _ => score_small_ball (hv s) (by positivity))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma conditional_tableTest_bound (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    |(∫ x, F (thresholdTable v x) ∂gaussianLaw ι)-
      (∫ x in cube T, gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x ∂gaussianLaw ι)/
        (gaussianLaw ι).real (cube T)| ≤
      (Fintype.card ι:ℝ)/(T:ℝ)^2+2*(Fintype.card S)*A*((T:ℝ)/L) := by
  have h := conditional_rounding_bound (cube_measurable T) (gaussian_cube_pos hT)
    (tableTest_integrable v F hF) (gridStep_integrable T L _)
    (fun x => hF (thresholdTable v x))
    (gridStep_range hT.le hL _ (fun j => hF (thresholdTable v (gridPoint T L j))))
  exact h.trans (add_le_add (gaussian_cube_tail hT)
    (setIntegral_tableTest_rounding v hv hA0 hA hT.le hL F hF))

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_ArbitraryProductWeights
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
lemma grid_product_bound_general {ι : Type*} [Fintype ι] {T : ℚ} (hT : 1 ≤ T) {L : ℕ} (hL : 0 < L)
    (r : ℕ) (F : (ι → Fin L) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, qCell r T L (x i))*F x)/(qIntegral r (-T) T:ℝ)^(Fintype.card ι)-
      (∑ x, (∏ i, gCell T L (x i))*F x)/(gIntegral (-T) T)^(Fintype.card ι)| ≤
        2*(Fintype.card ι)*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT0 : 0 < T := by linarith
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hb := finite_product_test_bound_general (qCell r T L) (gCell T L)
    (gCell_nonneg hT0 hL) (gCell_le_qCell hT0 hL r)
    (by rw [sum_gCell T hL]; exact (gIntegral_large hT').le) F hF
  rw [sum_qCell r T hL,sum_gCell T hL] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (residual_bounds hT0.le r).2 (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))
    nlinarith)

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianQuadrature
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace MinUncut.FiniteGaussian
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

lemma conditional_gridStep {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) :
    (∫ x in cube T, gridStep T L F x ∂gaussianLaw ι)/(gaussianLaw ι).real (cube T)=
      (∑ j, (∏ i, gCell T L (j i))*F j)/(gIntegral (-T) T)^(Fintype.card ι) := by
  rw [setIntegral_gridStep hT.le hL,gaussian_cube hT.le]
  simp_rw [gaussian_cubeCell hT hL,mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (ne_of_gt gaussianConstant_pos))

lemma rational_grid_expectation (r : ℕ) (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) :
    (∑ j, ((∏ i, cellWeight r T L (j i):ℚ):ℝ)*F j)=
      (∑ j, (∏ i, qCell r T L (j i))*F j)/(qIntegral r (-T) T:ℝ)^(Fintype.card ι) := by
  simp only [cellWeight,Rat.cast_prod,Rat.cast_div,Rat.cast_pow,Finset.prod_div_distrib,Finset.prod_const,
    Finset.card_univ,div_mul_eq_mul_div,← Finset.sum_div,qCell]

lemma joint_table_error (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 1 ≤ T) {L : ℕ} (hL : 0 < L) (r : ℕ)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    |(∫ x, F (thresholdTable v x) ∂gaussianLaw ι)-
      ∑ j : ι → Fin L, ((∏ i, cellWeight r T L (j i):ℚ):ℝ)*
        F (thresholdTable v (gridPoint T L j))| ≤
      (Fintype.card ι:ℝ)/(T:ℝ)^2+2*(Fintype.card S)*A*((T:ℝ)/L)+
        2*(Fintype.card ι)*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT0 : 0 < T := by linarith
  have ht := conditional_tableTest_bound v hv hA0 hA hT0 hL F hF
  rw [conditional_gridStep hT0 hL] at ht
  have hq := grid_product_bound_general hT hL r
    (fun j => F (thresholdTable v (gridPoint T L j)))
    (fun j => hF (thresholdTable v (gridPoint T L j)))
  rw [rational_grid_expectation]
  exact (abs_sub_le _ _ _).trans (add_le_add ht (by simpa only [abs_sub_comm] using hq))

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

lemma codeVector_norm (hn : 0<n) (z : Code m n) : ‖vector (codeVector z)‖=1 := by
  have hn' : (0:ℝ)<(n^m:ℕ) := by positivity
  have he : ‖vector (codeVector z)‖^2=1 := by
    simp only [EuclideanSpace.real_norm_sq_eq,vector,codeVector,mul_pow,sign_sq,mul_one,
      Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,inv_pow]
    rw [Real.sq_sqrt hn'.le,mul_inv_cancel₀ hn'.ne']
  nlinarith [norm_nonneg (vector (codeVector z))]

lemma score_codeVector (z : Code m n) (c : Point m n → ℝ) :
    score (codeVector z) c=(Real.sqrt (n^m:ℕ))⁻¹ * ∑ x, c x*BinaryFourier.sign (z.val x) := by
  simp only [score,codeVector,mul_assoc,← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma labelFunctional_degree (a : A) (x : Point m n) : degree (labelFunctional a x) ≤ m := by
  classical
  have hs : mask (labelFunctional a x) ⊆ Finset.univ.image (fun i : Fin m => (⟨i,face x i⟩ : Row m n)) := by
    intro r hr
    by_contra h
    have hneq : ∀ i : Fin m, (⟨i,face x i⟩ : Row m n)≠r := by
      intro i hi
      exact h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
    have hz : frequency (labelFunctional a x) r=0 := by
      ext b
      simp only [frequency,LinearMap.comp_apply,labelFunctional,LinearMap.coe_mk,AddHom.coe_mk,
        LinearMap.single_apply]
      change (∑ i : Fin m, (Pi.single r b : FaceArray A m n) ⟨i,face x i⟩ a)=0
      apply Finset.sum_eq_zero
      intro i _
      rw [Pi.single_eq_of_ne (hneq i)]
      rfl
    exact (Finset.mem_filter.mp hr).2 hz
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (by simp))

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LiteralGaussian
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

lemma scoreFamily_variance (hn : 0<n) (σ η : ℝ) (s : ScoreIndex m n) :
    1 ≤ ‖vector (scoreFamily σ η s)‖^2 := by
  have h := liftVector_norm_pos (codeVector s.2) (codeVector_norm hn s.2)
    (if s.1 then σ else 0) (if s.1 then η else 0) s.2
  change 1 ≤ ‖vector (liftVector (codeVector s.2) _ _ s.2)‖^2
  nlinarith

lemma codeVector_abs_le (hn : 0<n) (z : Code m n) (x : Point m n) : |codeVector z x| ≤ 1 := by
  have hN : (1:ℝ) ≤ (n^m:ℕ) := by exact_mod_cast (Nat.one_le_pow m n hn)
  have hs : 1 ≤ Real.sqrt (n^m:ℕ) := (Real.one_le_sqrt).mpr hN
  simp only [codeVector,abs_mul,BinaryFourier.sign_abs,mul_one,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ hs

lemma scoreFamily_l1 (hn : 0<n) {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (s : ScoreIndex m n) :
    (∑ i, |scoreFamily σ η s i|) ≤ 2*(n^m:ℕ)+1 := by
  have hh : (∑ x, |codeVector s.2 x|) ≤ (n^m:ℕ) := by
    calc
      _ ≤ ∑ _ : Point m n, (1:ℝ) := Finset.sum_le_sum (fun x _ => codeVector_abs_le hn s.2 x)
      _ = _ := by simp [Point]
  have hh0 : 0 ≤ ∑ x, |codeVector s.2 x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  unfold scoreFamily
  rw [liftVector_l1]
  cases s.1 <;> simp only [Bool.false_eq_true,ite_false,ite_true,abs_zero,abs_of_nonneg hσ,abs_of_nonneg hη]
  · linarith
  · nlinarith [mul_le_mul_of_nonneg_right hσ1 hh0]

lemma scoreFamily_packed (σ η : ℝ) (s : ScoreIndex m n)
    (p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ))) :
    thresholdTable (scoreFamily σ η) (packEquiv p) s=
      if s.1 then query (p.1+σ • p.2.1) (η • p.2.2) s.2 else query p.1 0 s.2 := by
  unfold thresholdTable scoreFamily
  rw [score_packed]
  simp only [score_codeVector,query,thresholdBit]
  cases s.1
  · simp
  · simp only [ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,
      mul_assoc,← Finset.mul_sum]
    congr 1
    ring_nf

lemma qSign_cast (b : F₂) : (qSign b:ℝ)=BinaryFourier.sign b := by
  unfold qSign BinaryFourier.sign
  split_ifs <;> norm_num

lemma rationalScoreTable_correct (hn : 0<n) (σ η : ℚ) (x : TestCoordinates m n → ℚ) :
    rationalScoreTable σ η x=thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) (fun i => (x i:ℝ)) := by
  funext s
  apply Bool.eq_iff_iff.mpr
  rw [rationalScoreTable,algebraicNonneg_eq]
  simp only [thresholdTable,thresholdBit,ite_eq_left_iff,Bool.false_eq_true,imp_false,not_not]
  have hroot : 0 < Real.sqrt (n^m:ℕ) := Real.sqrt_pos.mpr (by positivity)
  have he : score (scoreFamily (σ:ℝ) (η:ℝ) s) (fun i => (x i:ℝ))=
      (Real.sqrt (n^m:ℕ))⁻¹ *
        (∑ i, ((x (.inl i):ℝ)+(if s.1 then (σ:ℝ) else 0)*(x (.inr (.inl i)):ℝ))*BinaryFourier.sign (s.2.val i))+
        (if s.1 then (η:ℝ) else 0)*(x (.inr (.inr s.2)):ℝ) := by
    cases hs : s.1 <;>
      simp only [score,scoreFamily,liftVector,codeVector,Fintype.sum_sum_type,hs,
        Bool.false_eq_true,ite_false,ite_true,zero_mul,add_zero,
        ite_mul,Finset.sum_ite_eq',Finset.mem_univ,Finset.sum_const_zero]
    · simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [add_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,← add_assoc]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he]
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,apply_ite Rat.cast,Rat.cast_zero,qSign_cast]
  have he' (a b : ℝ) : Real.sqrt (n^m:ℕ)*((Real.sqrt (n^m:ℕ))⁻¹*a+b)=a+b*Real.sqrt (n^m:ℕ) := by
    rw [mul_add,← mul_assoc,mul_inv_cancel₀ hroot.ne',one_mul,mul_comm (Real.sqrt (n^m:ℕ)) b]
  rw [← he',mul_nonneg_iff_of_pos_left hroot]

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FiniteGaussianLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

attribute [local irreducible] tableGrid scoreFamily

attribute [local instance] OAI.MinUncut.FiniteGaussian.coordsDecEq
lemma rational_table_error (hn : 0<n) {σ η : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (g : GridData) (hT : 1≤(g.T:ℚ)) (hL : 0<g.L)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x, F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      ∑ j : TestCoordinates m n → Fin g.L,
        (gridWeight g j:ℝ)*F (rationalScoreTable σ η (fun i => midpoint g.T g.L (j i)))| ≤
      (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) := by
  have hh := joint_table_error (scoreFamily (σ:ℝ) (η:ℝ)) (scoreFamily_variance hn _ _)
    (A := 2*(n^m:ℕ)+1) (by positivity)
    (scoreFamily_l1 hn (by exact_mod_cast hσ) (by exact_mod_cast hσ1)
      (by exact_mod_cast hη) (by exact_mod_cast hη1)) hT hL g.r F hF
  simp_rw [rationalScoreTable_correct hn]
  convert hh using 1 <;> simp only [gridWeight,Rat.cast_natCast]
  congr 2

end MinUncut.FiniteGaussian

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

namespace JointForms
attribute [local instance] OAI.MinUncut.OuterSmoothness.JointForms.densityDualDecidableEq
abbrev FullRaw (d : ℕ) := Fin d → Module.Dual F₂ Triple
abbrev Raw (d : ℕ) := HiddenRaw d × FullRaw d

def fullPull {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) : FullRaw d →ₗ[F₂] Block r d :=
  LinearMap.pi (fun l => T.dualMap.comp (LinearMap.proj l))

lemma fullPull_surjective {r d : ℕ} {T : (Fin r → F₂) →ₗ[F₂] Triple}
    (hT : Function.Injective T) : Function.Surjective (fullPull (d := d) T) := by
  intro b
  choose w hw using fun l => LinearMap.dualMap_surjective_of_injective hT (b l)
  exact ⟨w, funext hw⟩

def hiddenPull {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) (q : HiddenRaw d) : Block r d :=
  fun l => q.2 l • ((LinearMap.proj q.1).comp T)

attribute [local instance] OAI.MinUncut.OuterSmoothness.JointForms.dualFintype
def hiddenLaw {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) : Density (Block r d) :=
  Density.ofMap (hiddenPull T)

lemma fullPull_uniform {r d : ℕ} {T : (Fin r → F₂) →ₗ[F₂] Triple}
    (hT : Function.Injective T) (b : Block r d) : Density.ofMap (fullPull T) b = 1 :=
  Density.ofMap_surjective_hom (fullPull T).toAddMonoidHom (fullPull_surjective hT) b

variable {r : ι → ℕ} {d : ℕ}

def output (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (H : Finset ι)
    (w : ι → Raw d) : ∀ i, Block (r i) d :=
  fun i => if i ∈ H then hiddenPull (T i) (w i).1 else fullPull (T i) (w i).2

lemma output_density (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple)
    (hT : ∀ i, Function.Injective (T i)) (H : Finset ι) (b : ∀ i, Block (r i) d) :
    Density.ofMap (output T H) b = hiddenDensity (fun i => hiddenLaw (T i)) H b := by
  rw [show output T H = (fun w : ι → Raw d => fun i =>
    (fun q : Raw d => if i ∈ H then hiddenPull (T i) q.1 else fullPull (T i) q.2) (w i)) from rfl,
    Density.ofMap_pi (fun i (q : Raw d) => if i ∈ H then hiddenPull (T i) q.1 else fullPull (T i) q.2) b]
  change (∏ i, _) = ∏ i, _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ H
  · simp only [hi, ite_true]
    exact Density.ofMap_fst _ _
  · simp only [hi, ite_false]
    rw [Density.ofMap_snd]
    exact fullPull_uniform (hT i) _

def offset (o : ι → Triple) (H : Finset ι) (w : ι → Raw d) : Fin d → F₂ :=
  fun l => ∑ i, if i ∈ H then (w i).1.2 l * o i (w i).1.1 else (w i).2 l (o i)

def affineOutput (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (o : ι → Triple) {k : ℕ}
    (sample : (Fin d → F₂) × (FixedSets ι k × (ι → Raw d))) :
      (Fin d → F₂) × (∀ i, Block (r i) d) :=
  (sample.1 + offset o sample.2.1.val sample.2.2, output T sample.2.1.val sample.2.2)

lemma joint_density {k : ℕ} (hk : k ≤ Fintype.card ι)
    (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (hT : ∀ i, Function.Injective (T i))
    (o : ι → Triple) (c : Fin d → F₂) (b : ∀ i, Block (r i) d) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    Density.ofMap (affineOutput T o (k := k)) (c,b) =
      mixture (fun H : FixedSets ι k => H.val) (fun i => hiddenLaw (T i)) b := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  rw [show affineOutput T o (k := k) = (fun sample : (Fin d → F₂) × (FixedSets ι k × (ι → Raw d)) =>
      (sample.1 + (fun p : FixedSets ι k × (ι → Raw d) => offset o p.1.val p.2) sample.2,
        (fun p : FixedSets ι k × (ι → Raw d) => output T p.1.val p.2) sample.2)) from rfl,
    Density.ofMap_uniform_shift (fun p : FixedSets ι k × (ι → Raw d) => output T p.1.val p.2)
      (fun p : FixedSets ι k × (ι → Raw d) => offset o p.1.val p.2) c b,
    Density.ofMap_family (fun (H : FixedSets ι k) (w : ι → Raw d) => output T H.val w) b]
  apply Finset.expect_congr rfl
  intro H _
  exact output_density T hT H.val b

end JointForms
end MinUncut.OuterSmoothness

end

end OAI
end

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

lemma direction_parity (E : Equation Name) (v : (alphabet E).direction) :
    parity (v : Triple) = 0 := by
  obtain ⟨a,ha,b,hb,he⟩ :=
    ((alphabet E).mem_direction_iff_eq_vsub ⟨origin E,(origin E).property⟩ v.val).mp v.property
  rw [he]
  change parity (a-b)=0
  rw [map_sub,ha.1,hb.1,sub_self]

def firstTwo (E : Equation Name) : (alphabet E).direction →ₗ[F₂] (Fin 2 → F₂) :=
  LinearMap.pi (fun i => (LinearMap.proj i.castSucc).comp (alphabet E).direction.subtype)

lemma firstTwo_injective (E : Equation Name) : Function.Injective (firstTwo E) := by
  intro v w hvw
  have h0 : v.val 0=w.val 0 := congrFun hvw 0
  have h1 : v.val 1=w.val 1 := congrFun hvw 1
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · have hv := direction_parity E v
    have hw := direction_parity E w
    simp only [parity_apply,h0,h1] at hv hw
    exact add_left_cancel (hv.trans hw.symm)

lemma alphabet_dimension_le (E : Equation Name) :
    Module.finrank F₂ (alphabet E).direction ≤ 2 := by
  have h := (firstTwo E).finrank_le_finrank_of_injective (firstTwo_injective E)
  simpa only [Module.finrank_fin_fun] using h

lemma directionEmbedding_injective (E : Equation Name) :
    Function.Injective (directionEmbedding E) :=
  Subtype.val_injective.comp (coordinates E).injective

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

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*}

open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

def unpackFunctional : (v : SecondQuestion Name) → Module.Dual F₂ (secondSlot v) →
    F₂ × Module.Dual F₂ Triple
  | .inl _, l => (l (fun _ => 1),0)
  | .inr _, l => (0,l)

lemma oneSlotDual (l : Module.Dual F₂ (Fin 1 → F₂)) :
    l (fun _ => 1) • (LinearMap.proj (0 : Fin 1)) = l := by
  apply LinearMap.ext
  intro a
  have ha : a=a 0 • (fun _ : Fin 1 => (1 : F₂)) := by
    funext p
    fin_cases p
    simp
  change l (fun _ => 1)*a 0=l a
  calc
    _ = a 0 • l (fun _ => 1) := mul_comm _ _
    _ = l (a 0 • (fun _ => 1)) := (l.map_smul _ _).symm
    _ = l a := congrArg l ha.symm

lemma slotFunctional_unpack (v : SecondQuestion Name)
    (l : Module.Dual F₂ (secondSlot v)) :
    slotFunctional v (unpackFunctional v l).1 (unpackFunctional v l).2=l := by
  cases v with
  | inl x => exact oneSlotDual l
  | inr E => rfl

attribute [local instance] BinaryFourier.dualFintype

end MinUncut.Outer

end
namespace MinUncutGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

end Game

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

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

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteDistribution

end
end MinUncutGames.Foundations.Games

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

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

variable {α : Type*} [Fintype α]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

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

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

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

end

open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

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

namespace MinUncutGames.Foundations.Games

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

end KernelSampling
end
end MinUncutGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_TotalVariation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

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

theorem factorized_completion_row
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (xy : X × Y) :
    (∑ z : X × Y, c * left z.1 * right z.2) *
      ((normalizeOr left hl defaultLeft).product
        (normalizeOr right hr defaultRight)).weight xy = c * left xy.1 * right xy.2 := by
  have hm : (∑ z : X × Y, c * left z.1 * right z.2) =
      c * (∑ z, left z) * (∑ z, right z) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [productWeight_mass]
  rw [hm]
  exact local_completion_recombination left right hl hr defaultLeft defaultRight c xy.1 xy.2

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DistributionMaps
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end MinUncutGames.Foundations.Games.FiniteDistribution

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

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

theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

open scoped BigOperators
open Games
noncomputable section

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

open scoped BigOperators
open Games Information

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      Information.totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      Information.totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
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
    Information.totalVariation (selectedSamplingTarget G strategy selected positive j).weight
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
    Information.totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CompletedSampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in

theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end

end MinUncutGames.Foundations.Repetition.CompletedSampling

namespace MinUncutGames.Foundations.Games.Game

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
end MinUncutGames.Foundations.Games.Game

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end

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

open scoped BigOperators
open Games
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
        selectedCompletionScale, selectedLeftRaw, selectedRightRaw, hl, hr, hacc]; ring
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
        cases G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) <;>
          cases event (selectedQuestionTuple selected fixed u) <;> simp; ring
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
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectionSequence
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

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ListDecoding
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

variable {Name I : Type*} [Fintype I]


open scoped BigOperators
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

omit [Fintype I] in
lemma firstCoordinates_symm_apply (U : I → Equation Name) (a : FirstAlphabet U) (i : I) :
    (firstCoordinates U).symm a i = (alphabetCoordinates (U i)).symm (a i) := rfl

def formsTransport {V W A B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    [AddCommGroup W] [Module F₂ W] [AddTorsor W B] (e : A ≃ᵃ[F₂] B) :
    Forms B ≃ₗ[F₂] Forms A where
  toFun f := f.comp e.toAffineMap
  invFun f := f.comp e.symm.toAffineMap
  left_inv f := by ext b; simp
  right_inv f := by ext a; simp
  map_add' f g := by ext a; rfl
  map_smul' c f := by ext a; rfl

def firstFormCoordinates (U : I → Equation Name) :
    (F₂ × (∀ i, Module.Dual F₂ (CoordinateSlot (U i)))) ≃ₗ[F₂] Forms (FirstAlphabet U) :=
  ((LinearEquiv.refl F₂ F₂).prodCongr
    (LinearMap.lsum F₂ (fun i => CoordinateSlot (U i)) F₂)).trans
    ((AffineMap.toConstProdLinearMap F₂).symm.trans (formsTransport (firstCoordinates U)).symm)

lemma firstFormCoordinates_apply (U : I → Equation Name) (κ : F₂)
    (b : ∀ i, Module.Dual F₂ (CoordinateSlot (U i))) (a : FirstAlphabet U) :
    firstFormCoordinates U (κ,b) a =
      (∑ i, b i ((alphabetCoordinates (U i)).symm (a i)))+κ := by
  change (∑ i, (b i).comp (LinearMap.proj i)) ((firstCoordinates U).symm a)+κ=_
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    firstCoordinates_symm_apply]

abbrev TupleCoordinateData (U : I → Equation Name) (d : ℕ) :=
  (Fin d → F₂) × (∀ i, OuterSmoothness.JointForms.Block
    (Module.finrank F₂ (alphabet (U i)).direction) d)

def tupleCoordinateSlice (U : I → Equation Name) (d : ℕ) (k : Fin d) :
    TupleCoordinateData U d →ₗ[F₂] (F₂ × (∀ i, Module.Dual F₂ (CoordinateSlot (U i)))) where
  toFun z := (z.1 k,fun i => z.2 i k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tupleCoordinateGenerator (U : I → Equation Name) (d : ℕ) :
    TupleCoordinateData U d →ₗ[F₂] (Fin d → Forms (FirstAlphabet U)) :=
  LinearMap.pi (fun k => (firstFormCoordinates U).toLinearMap.comp (tupleCoordinateSlice U d k))

lemma tupleCoordinateGenerator_surjective (U : I → Equation Name) (d : ℕ) :
    Function.Surjective (tupleCoordinateGenerator U d) := by
  intro f
  let z := fun k => (firstFormCoordinates U).symm (f k)
  refine ⟨(fun k => (z k).1,fun i k => (z k).2 i),?_⟩
  funext k
  exact (firstFormCoordinates U).apply_symm_apply (f k)

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintSampling
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
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

def rawPositions {d : ℕ} (w : I → JointForms.Raw d) : I → Fin 3 := fun i => (w i).1.1

lemma origin_coordinate_decomposition (E : Equation Name) (a : alphabet E) :
    a.val=directionEmbedding E ((alphabetCoordinates E).symm a)+(origin E).val := by
  exact congrArg Subtype.val ((alphabetCoordinates E).apply_symm_apply a) |>.symm

omit [Fintype I] in
lemma raw_slot_expansion (U : I → Equation Name) {d : ℕ} (H : Finset I)
    (w : I → JointForms.Raw d) (a : FirstAlphabet U) (i : I) (k : Fin d) :
    (if i ∈ H then (w i).1.2 k*(a i).val (w i).1.1 else (w i).2 k (a i).val) =
    (JointForms.output (fun i => directionEmbedding (U i)) H w i k)
      ((alphabetCoordinates (U i)).symm (a i)) +
      (if i ∈ H then (w i).1.2 k*(origin (U i)).val (w i).1.1
        else (w i).2 k (origin (U i)).val) := by
  classical
  by_cases hi : i ∈ H
  · simp only [hi,↓reduceIte,JointForms.output,JointForms.hiddenPull]
    change (w i).1.2 k*(a i).val (w i).1.1 =
      (w i).1.2 k*(directionEmbedding (U i) ((alphabetCoordinates (U i)).symm (a i))) (w i).1.1+_
    rw [origin_coordinate_decomposition (U i) (a i)]
    simp only [Pi.add_apply,mul_add]
  · simp only [hi,↓reduceIte,JointForms.output,JointForms.fullPull,
      LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.dualMap_apply]
    rw [origin_coordinate_decomposition (U i) (a i),map_add]

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

lemma pulled_background_reindex {K : Type*} [Fintype K] [DecidableEq K]
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (e : J ≃ K) (f : (J → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 L : K → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      f (fun j => formPullback (projection U hidden pos) (L (e j)))) =
    𝔼 L : J → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      f (fun j => formPullback (projection U hidden pos) (L j)) :=
  expect_reindex e (fun L => f (fun j => formPullback (projection U hidden pos) (L j)))

lemma actual_background_reindex {K : Type*} [Fintype K] [DecidableEq K]
    (U : I → Equation Name) (k : ℕ) (e : J ≃ K)
    (f : (J → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 H : FixedSets I k, 𝔼 pos : I → Fin 3,
      𝔼 L : K → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L (e j)))) =
      𝔼 H : FixedSets I k, 𝔼 pos : I → Fin 3,
      𝔼 L : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j)) := by
  apply Finset.expect_congr rfl
  intro H _
  exact Finset.expect_congr rfl (fun pos _ => pulled_background_reindex U _ pos e f)

end MinUncut.Outer

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

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

def backgroundMean (equations : S → Equation Name) (k : ℕ)
    (F : (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) →
      (J → Forms (SecondAlphabet (secondQuestion U hidden pos))) → ℝ) : ℝ :=
  𝔼 H : FixedSets I k, 𝔼 a : I → S, 𝔼 pos : I → Fin 3,
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) (hiddenSet H.val) pos)),
      F (fun i => equations (a i)) (hiddenSet H.val) pos B

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TableLawPacking
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

def sourceTable (σ η : ℝ) (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    ScoreIndex m n → Bool := fun s => if s.1 then query (c+σ•g) (η•l) s.2 else query c 0 s.2

lemma sourceTable_packed (σ η : ℝ) (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    sourceTable σ η c g l=thresholdTable (scoreFamily σ η) (packEquiv (c,g,l)) := by
  funext s
  exact (scoreFamily_packed σ η s (c,g,l)).symm

lemma table_integral_pack (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    (∫ c, ∫ g, ∫ l, F (sourceTable σ η c g l) ∂gauss (Code m n)
      ∂gauss (Point m n) ∂gauss (Point m n))=
      ∫ x, F (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) := by
  have ht := tableTest_integrable (scoreFamily σ η) F hF
  have hp := pack_preserving (X := Point m n) (C := Code m n)
  have hi : Integrable (fun p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      F (thresholdTable (scoreFamily σ η) (packEquiv p))) (productLaw (Point m n) (Code m n)) :=
    hp.integrable_comp_of_integrable ht
  rw [← hp.integral_comp packEquiv.measurableEmbedding (fun x => F (thresholdTable (scoreFamily σ η) x))]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with c hc
  rw [integral_prod _ hc]
  apply integral_congr_ae
  filter_upwards [] with g
  apply integral_congr_ae
  filter_upwards [] with l
  rw [sourceTable_packed]

lemma sourceTest_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    Integrable (fun p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      F (sourceTable σ η p.1 p.2.1 p.2.2)) (productLaw (Point m n) (Code m n)) := by
  simp_rw [sourceTable_packed]
  exact (pack_preserving (X := Point m n) (C := Code m n)).integrable_comp_of_integrable
    (tableTest_integrable (scoreFamily σ η) F hF)

lemma sourceTest_inner_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) (c : Point m n → ℝ) :
    Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      F (sourceTable σ η c p.1 p.2)) ((gauss (Point m n)).prod (gauss (Code m n))) := by
  simp_rw [sourceTable_packed]
  apply Integrable.of_bound
    (((measurable_of_countable F).comp (thresholdTable_measurable (scoreFamily σ η))).comp
      (packEquiv.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
  filter_upwards [] with p
  simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (hF _).1]
    using (hF (thresholdTable (scoreFamily σ η) (packEquiv (c,p)))).2

lemma sourceTest_outer_integrable (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    Integrable (fun c => ∫ g, ∫ l, F (sourceTable σ η c g l) ∂gauss (Code m n)
      ∂gauss (Point m n)) (gauss (Point m n)) := by
  have hi := (sourceTest_integrable σ η F hF).integral_prod_left
  have he (c : Point m n → ℝ) := integral_prod
    (fun p : (Point m n → ℝ) × (Code m n → ℝ) => F (sourceTable σ η c p.1 p.2))
    (sourceTest_inner_integrable σ η F hF c)
  change Integrable (fun c => ∫ p : (Point m n → ℝ) × (Code m n → ℝ),
    F (sourceTable σ η c p.1 p.2) ∂(gauss (Point m n)).prod (gauss (Code m n)))
    (gauss (Point m n)) at hi
  simpa only [he] using hi

lemma table_integral_product (σ η : ℝ) (F : (ScoreIndex m n → Bool) → ℝ)
    (hF : ∀ t, 0≤F t ∧ F t≤1) :
    (∫ c, ∫ p : (Point m n → ℝ) × (Code m n → ℝ), F (sourceTable σ η c p.1 p.2)
      ∂(gauss (Point m n)).prod (gauss (Code m n)) ∂gauss (Point m n))=
      ∫ x, F (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) := by
  rw [← table_integral_pack σ η F hF]
  apply integral_congr_ae
  filter_upwards [] with c
  exact integral_prod _ (sourceTest_inner_integrable σ η F hF c)

end MinUncut.FiniteGaussian

end
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

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma mapDemand_extend {V W : Type*} (f : V → W) (hf : Function.Injective f) (s : V → Bool) (d : Demand V) :
    failure (d.map f) (extendAssignment f s)=failure d s := by
  simp only [failure,Demand.map,extendAssignment_apply f hf]

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestComparisons
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

lemma score_query (z : Code m n) (u : Point m n → ℝ) (d : Code m n → ℝ) :
    query u d z=decide (0 ≤ score (codeVector z) u+d z) := by
  rw [score_codeVector]
  rfl

omit [Fintype A] in
lemma firstFailure_evaluation (a : A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    firstFailure (evaluationProof a) B σ η c g l =
      signFailure (score (codeVector (labelCode B a)) c)
        (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) g+η*l (labelCode B a)) := by
  simp only [firstFailure,evaluationProof,pullQuery,score_query,Pi.zero_apply,add_zero,
    score_add_noise,Pi.smul_apply,smul_eq_mul,decide_eq_decide,signFailure]

omit [Fintype A] in
lemma firstRejection_evaluation_le (a : A) (B : FaceArray A m n) (hn : 0<n)
    {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) :
    (∫ c, firstRejection (evaluationProof a) B σ η c ∂gauss (Point m n))  ≤  4*(σ+η) := by
  simp only [firstRejection,firstFailure_evaluation,gauss]
  exact first_triple_bound (codeVector_norm hn _) hσ hη _

lemma firstError_evaluation_le (a : A) (hn : 0<n) {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) :
    firstError (m := m) (n := n) (evaluationProof a) σ η  ≤  4*(σ+η) := by
  exact (Finset.expect_le_expect (fun B _ => firstRejection_evaluation_le a B hn hσ hη)).trans_eq
    (Fintype.expect_const _)

omit [Fintype A] in
lemma secondFailure_evaluation (a : A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    secondFailure (evaluationProof a) B C σ η c p =
      signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) p.1+η*p.2 (labelCode B a))
        (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) p.1+η*p.2 (labelCode C a)) := by
  simp only [secondFailure,evaluationProof,pullQuery,score_query,score_add_noise,
    Pi.smul_apply,smul_eq_mul,decide_eq_decide,signFailure]

omit [Fintype A] in
lemma secondRejection_evaluation_le (a : A) (B C : FaceArray A m n) (hn : 0<n)
    {σ η : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hη : 0 ≤ η) :
    (∫ c, secondRejection (evaluationProof a) B C σ η c ∂gauss (Point m n))  ≤
      4*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖+4*η := by
  unfold secondRejection
  simp only [secondFailure_evaluation,gauss]
  have he (c : Point m n → ℝ) :
      (∫ p : (Point m n → ℝ) × (Code m n → ℝ),
        signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) p.1+η*p.2 (labelCode B a))
          (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) p.1+η*p.2 (labelCode C a))
        ∂(Measure.pi (fun _ : Point m n => gaussianReal 0 1)).prod (Measure.pi (fun _ : Code m n => gaussianReal 0 1))) =
      ∫ g, ∫ l,
        signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) g+η*l (labelCode B a))
          (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) g+η*l (labelCode C a))
        ∂Measure.pi (fun _ : Code m n => gaussianReal 0 1) ∂Measure.pi (fun _ : Point m n => gaussianReal 0 1) := by
    apply integral_prod
    apply signFailure_integrable <;> unfold score <;> fun_prop
  simp_rw [he]
  exact second_triple_bound (codeVector_norm hn _) (codeVector_norm hn _) hσ hσ1 hη _ _

omit [Fintype A] in
lemma thirdFailure_evaluation (a : A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdFailure (evaluationProof a) B η u l z=if z=labelCode B a then 1 else 0 := by
  unfold thirdFailure evaluationProof
  by_cases h : z=labelCode B a
  · subst z; simp
  · simp [Function.update_of_ne (Ne.symm h),h]

omit [Fintype A] in
lemma thirdRejection_evaluation (a : A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : thirdRejection (evaluationProof a) B σ η c=(Fintype.card (Code m n):ℝ)⁻¹ := by
  simp only [thirdRejection,thirdFailure_evaluation,integral_const,probReal_univ,one_smul,
    Fintype.expect_eq_sum_div_card]
  simp

lemma thirdError_evaluation (a : A) (σ η : ℝ) :
    thirdError (m := m) (n := n) (evaluationProof a) σ η=(Fintype.card (Code m n):ℝ)⁻¹ := by
  simp only [thirdError,thirdRejection_evaluation,integral_const,probReal_univ,one_smul,Fintype.expect_const]
end MinUncut.Inner

end
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma codeVector_distance_sq (hn : 0<n) (z w : Code m n) :
    ‖vector (codeVector z)-vector (codeVector w)‖^2=
      ((n^m:ℕ):ℝ)⁻¹*∑ x, (BinaryFourier.sign (z.val x)-BinaryFourier.sign (w.val x))^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,codeVector,← mul_sub,mul_pow]
  rw [← Finset.mul_sum,inv_pow,Real.sq_sqrt (by positivity)]

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestBudgets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma honest_first_budget (a : A) (hn : 0 < n) {J : ℝ} (hJ : 1 ≤ J) :
    firstError (m := m) (n := n) (evaluationProof a) (sourceSigma J) (sourceEta J) ≤
      10*sourceSigma J := by
  have h := firstError_evaluation_le (m := m) a hn (sourceSigma_pos hJ).le (sourceEta_pos hJ).le
  have := sourceEta_le_sigma hJ
  have := sourceSigma_pos hJ
  linarith

end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B] {m n : ℕ}

omit [Fintype A] [Fintype B] in
lemma labelCode_pullback (π : A →ᵃ[F₂] B) (C : FaceArray B m n) (a : A) :
    labelCode (pullbackFaces π C) a=labelCode C (π a) := by
  apply Subtype.ext
  funext x
  rfl

omit [Fintype A] in
lemma fourthError_evaluation (π : A →ᵃ[F₂] B) (a : A) (σ η : ℝ) :
    fourthError (m := m) (n := n) π (evaluationProof a) (evaluationProof (π a)) σ η=0 := by
  simp only [fourthError,comparisonRejection,comparisonFailure,evaluationProof,pullQuery,
    labelCode_pullback,ite_true,integral_zero,Finset.expect_const_zero]

end MinUncut.Inner

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
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def singleMask (i : A) : Cube A := fun j => decide (j = i)

end MinUncutGames.Foundations.PCP.AssignmentTester

end
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

namespace MinUncutGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))


variable [Fintype I] [DecidableEq I] [Fintype D]

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl


end MinUncutGames.Foundations.PCP.CayleySpectral


end

end OAI
end


