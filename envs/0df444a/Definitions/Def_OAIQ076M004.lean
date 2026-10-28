-- Prove2me | Definitions.Def_OAIQ076M004
-- name    : OAIQ076M004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:01:46.72555+00:00
-- url     : https://prove2.me/theorems/d5ff71bb-c1a4-4dc8-a5b1-89d4cc90e3ed
-- title:
--   Definitions bundle OAIQ076M004 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 702 declarations of OpenAI's Lean: 336 definitions, 33 inductive types or structures, 20 instances and 313 theorems. The definitions and types are `OAI.MinUncut.FiniteGaussian.baseDensity`, `OAI.MinUncut.FiniteGaussian.cube`, `OAI.MinUncut.FiniteGaussian.gIntegral`, `OAI.MinUncut.FiniteGaussian.gaussianConstant`, `OAI.MinUncut.FiniteGaussian.gaussianLaw`, `OAI.MinUncut.FiniteGaussian.thresholdBit`, `OAI.MinUncut.FiniteGaussian.thresholdTable`, `OAI.MinUncut.GaussianBudget.betweenIndicator`, `OAI.MinUncut.GaussianBudget.productLaw`, `OAI.MinUncut.GaussianBudget.score`, `OAI.MinUncut.GaussianBudget.signFailure`, `OAI.MinUncut.GaussianBudget.vector`, `OAI.MinUncut.Outer.tupleProductEquiv`, `OAI.MinUncut.OuterSmoothness.Density`, `OAI.MinUncut.OuterSmoothness.Density.ofMap`, `OAI.MinUncut.OuterSmoothness.Density.tvUniform`, `OAI.MinUncut.PathRealization.extendAssignment`, `OAI.MinUncut.PathRealization.localCost`, `OAI.MinUncut.PathRealization.mono`, `OAI.MinUncutGames.BinaryEncoding.bitsValue`, `OAI.MinUncutGames.BinaryEncoding.clauseNameSize`, `OAI.MinUncutGames.BinaryFormula.clauseNames`, `OAI.MinUncutGames.BinaryFormula.sourceNames`, `OAI.MinUncutGames.BinaryHeaderMachine.Alphabet`, `OAI.MinUncutGames.BinaryHeaderMachine.State`, `OAI.MinUncutGames.BinaryHeaderMachine.delimiter`, `OAI.MinUncutGames.BinaryHeaderMachine.tapes`, `OAI.MinUncutGames.BinaryLiteralMachine.Alphabet`, `OAI.MinUncutGames.BinaryLiteralMachine.Label`, `OAI.MinUncutGames.BinaryLiteralMachine.State`, `OAI.MinUncutGames.BinaryLiteralMachine.clean`, `OAI.MinUncutGames.BinaryLiteralMachine.emitSign`, `OAI.MinUncutGames.BinaryLiteralMachine.finish`, `OAI.MinUncutGames.BinaryLiteralMachine.index`, `OAI.MinUncutGames.BinaryLiteralMachine.readSign`, `OAI.MinUncutGames.BinaryLiteralMachine.searchTapes`, `OAI.MinUncutGames.BinaryLiteralMachine.steps`, `OAI.MinUncutGames.BinaryNameCompare.Alphabet`, `OAI.MinUncutGames.BinaryNameCompare.Label`, `OAI.MinUncutGames.BinaryNameCompare.Label.enumList` and 329 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianDensityError`, `MinUncut_Analysis_GaussianPacking`, `MinUncut_Analysis_GaussianRounding`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Encoding_ArbitraryProductWeights`, `MinUncut_Estimates_Basic2`, `MinUncut_Estimates_ConditionalRounding`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_InputData`, `MinUncut_Estimates_LiftedVectors`, `MinUncut_Estimates_NormalizedWeights`, `MinUncut_Estimates_PatchDensity`, `MinUncut_Games_Basic`, `MinUncut_Games_FinalCNFHeader`, `MinUncut_Games_FinalCNFOutput`, `MinUncut_Games_FinalCNFStream`, `MinUncut_Games_GraphCounterModel`, `MinUncut_Games_JointHintBound`, `MinUncut_Games_KernelSampling`, `MinUncut_Games_LabelBound`, `MinUncut_Games_Parameters`, `MinUncut_Games_Pinsker`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_GraphOutput`, `MinUncut_Graphs_HonestComparisons`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Machines_Alphabet`, `MinUncut_Machines_Input`, `MinUncut_Machines_LoopInitialization`, `MinUncut_Machines_MachineBinaryFormula`, `MinUncut_Machines_MachineBinaryLiteralMachine`, `MinUncut_Machines_MachineBinaryNameMachine`, `MinUncut_Machines_MachineBinaryOccurrenceRename`, `MinUncut_Machines_MachineBinaryParsing`, `MinUncut_Machines_MachineBinaryRenameMachine`, `MinUncut_Machines_MachineCanonicalOutput`, `MinUncut_Machines_MachineCloudCount`, `MinUncut_Machines_MachineCloudPadding`, `MinUncut_Machines_MachineCloudPrefix`, `MinUncut_Machines_MachineCloudSelect`, `MinUncut_Machines_MachineDummyRows`, `MinUncut_Machines_MachineExpanderFamilyAffine`, `MinUncut_Machines_MachineExpanderFamilyCycle`, `MinUncut_Machines_MachineExpanderRowFrames`, `MinUncut_Machines_MachineExpanderTableRows`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineInitialHeaders`, `MinUncut_Machines_MachineLazyTableRuntime`, `MinUncut_Machines_MachineLookup`, `MinUncut_Machines_MachinePaddedExpanderFamilyBounds`, `MinUncut_Machines_MachineRegularLift`, `MinUncut_Machines_MachineRegularMetadata`, `MinUncut_Machines_MachineRegularOriginalBody`, `MinUncut_Machines_MachineRegularOwnerProgram`, `MinUncut_Machines_MachineRegularVertexBlock`, `MinUncut_Machines_MachineTransducer`, `MinUncut_Machines_MachineUnaryAdd`, `MinUncut_Machines_PCPIterationMachine`, `MinUncut_Machines_PreprocessingMachineBounds`, `MinUncut_Machines_RawInitialMachineBudget`, `MinUncut_Machines_RawInitialMachineFinish`, `MinUncut_Machines_RawInitialMachinePhases`, `MinUncut_Machines_Relations`, `MinUncut_Machines_Runtime`, `MinUncut_Machines_RuntimeModel2`, `MinUncut_Machines_SelectorMachine`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_CompletedSampling`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_Folding`, `MinUncut_PCP_Game`, `MinUncut_PCP_Gap`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTableComplexity`, `MinUncut_PCP_HonestTest`, `MinUncut_PCP_Occurrences`, `MinUncut_PCP_Overlap`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PreprocessingRegularLoopWords`, `MinUncut_PCP_ProfileCorrection`, `MinUncut_PCP_RawInitialPredicate`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SelectedInformation`, `MinUncut_PCP_SelectedLikelihood`, `MinUncut_Search_FiniteAverageBounds`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M009`, `OAIQ076M010`, `OAIQ076M011` and `OAIQ076M012`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.FoldedEquation

open scoped BigOperators

variable {I J : Type}

theorem xor_corrections (a b c u v w : Bool) :
    ((a ^^ b ^^ c) == (u ^^ v ^^ w)) =
      !((a ^^ u) ^^ (b ^^ v) ^^ (c ^^ w)) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases w <;> rfl

end MinUncutGames.Foundations.Hastad.FoldedEquation

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HonestTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad.SourceTape

open scoped BigOperators

section Expectations

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_prod (H : X × Y → ℝ) :
    (𝔼 p : X × Y, H p) = 𝔼 x : X, 𝔼 y : Y, H (x, y) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset X) (Finset.univ : Finset Y) H)

end Expectations

end MinUncutGames.Foundations.Hastad.SourceTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Occurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceOccurrences

open scoped BigOperators

theorem countP_cast_eq_sum {α : Type} (xs : List α) (p : α → Bool) :
    (xs.countP p : ℝ) = (xs.map (fun x => if p x then (1 : ℝ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_comm]

end MinUncutGames.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
namespace MinUncut.GaussianBudget

lemma pdf_le_one {v : ℝ≥0} (hv : 1≤v) (x : ℝ) : gaussianPDFReal 0 v x≤1 := by
  have hvR : (1:ℝ)≤v := by exact_mod_cast hv
  have hs : 1≤Real.sqrt (2*Real.pi*(v:ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x-0)^2/(2*(v:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  rw [gaussianPDFReal]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs))

lemma small_ball {v : ℝ≥0} (hv : 1≤v) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianReal 0 v).real {x : ℝ | |x| ≤ r} ≤ 2*r := by
  have hv0 : v≠0 := by linarith
  have he : {x : ℝ | |x| ≤ r}=Set.Icc (-r) r := by ext x; simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  rw [he,Measure.real,gaussianReal_apply_eq_integral 0 hv0]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 v x))]
  calc
    _ ≤ ∫ _ : ℝ in Set.Icc (-r) r, (1:ℝ) :=
      integral_mono (integrable_gaussianPDFReal 0 v).integrableOn (integrable_const 1) (fun x => pdf_le_one hv x)
    _ = 2*r := by simp only [setIntegral_const,smul_eq_mul,mul_one,Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring

def betweenIndicator (x y : ℝ) : ℝ := if |x|≤|y| then 1 else 0

lemma between_measurable : Measurable (fun p : ℝ×ℝ => betweenIndicator p.1 p.2) := by
  unfold betweenIndicator
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const

lemma between_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => betweenIndicator (X ω) (Y ω)) μ := by
  apply Integrable.of_bound (between_measurable.comp (hX.prodMk hY)).aestronglyMeasurable 1
  filter_upwards [] with x
  change |betweenIndicator (X x) (Y x)|≤1
  unfold betweenIndicator
  split_ifs <;> norm_num

lemma integral_between {v : ℝ≥0} (hv : 1≤v) (y : ℝ) :
    (∫ x, betweenIndicator x y ∂gaussianReal 0 v) ≤ 2*|y| := by
  have he : (fun x => betweenIndicator x y) = Set.indicator {x : ℝ | |x|≤|y|} (fun _ => (1:ℝ)) := by
    ext x; simp only [betweenIndicator,Set.indicator_apply,Set.mem_ofPred_eq]
  rw [he,integral_indicator (measurableSet_le (by fun_prop) measurable_const),setIntegral_const]
  simpa using small_ball hv (abs_nonneg y)

lemma independent_small_ball {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω→ℝ} (hX : Measurable X) (hY : Measurable Y) (hYI : Integrable Y μ)
    (hXY : IndepFun X Y μ) {v : ℝ≥0} (hv : 1≤v) (hlaw : μ.map X=gaussianReal 0 v) :
    (∫ ω, betweenIndicator (X ω) (Y ω) ∂μ) ≤ 2*(∫ ω, |Y ω| ∂μ) := by
  have hmap := hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hi : Integrable (fun p : ℝ×ℝ => betweenIndicator p.1 p.2) ((μ.map X).prod (μ.map Y)) :=
    between_integrable measurable_fst measurable_snd
  have he : (∫ ω, betweenIndicator (X ω) (Y ω) ∂μ) =
      ∫ y, ∫ x, betweenIndicator x y ∂(μ.map X) ∂(μ.map Y) := by
    rw [← integral_map (hX.prodMk hY).aemeasurable between_measurable.aestronglyMeasurable,hmap,
      integral_prod_symm _ hi]
  rw [he,hlaw]
  have hiY : Integrable (fun y : ℝ => 2*|y|) (μ.map Y) := by
    rw [integrable_map_measure (by fun_prop) hY.aemeasurable]
    exact hYI.abs.const_mul 2
  have hiB : Integrable (fun y => ∫ x, betweenIndicator x y ∂gaussianReal 0 v) (μ.map Y) := by
    rw [hlaw] at hi
    exact hi.integral_prod_right
  calc
    _ ≤ ∫ y, 2*|y| ∂(μ.map Y) := integral_mono hiB hiY (integral_between hv)
    _ = _ := by rw [integral_const_mul,integral_map hY.aemeasurable (by fun_prop)]

attribute [local instance] Classical.propDecidable

def signFailure (x y : ℝ) : ℝ := if (0 ≤ x ↔ 0 ≤ y) then 0 else 1

lemma signFailure_range (x y : ℝ) : 0 ≤ signFailure x y ∧ signFailure x y ≤ 1 := by
  unfold signFailure
  split_ifs <;> norm_num

lemma signFailure_measurable : Measurable (fun p : ℝ×ℝ => signFailure p.1 p.2) := by
  unfold signFailure
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le measurable_const measurable_fst).iff
    (measurableSet_le measurable_const measurable_snd)

lemma signFailure_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => signFailure (X ω) (Y ω)) μ := by
  apply Integrable.of_bound (signFailure_measurable.comp (hX.prodMk hY)).aestronglyMeasurable 1
  filter_upwards [] with ω
  change ‖signFailure (X ω) (Y ω)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (signFailure_range _ _).1]
  exact (signFailure_range _ _).2

lemma signFailure_sumdiff_le (x y : ℝ) : signFailure x y ≤ betweenIndicator (x+y) (x-y) := by
  unfold signFailure betweenIndicator
  split_ifs with h h' h'
  all_goals try norm_num
  exfalso
  apply h'
  have hh : (x < 0 ∧ 0 ≤ y) ∨ (0 ≤ x ∧ y < 0) := by
    by_cases hx : 0 ≤ x
    · right; refine ⟨hx,lt_of_not_ge ?_⟩; intro hy; exact h (iff_of_true hx hy)
    · left; refine ⟨lt_of_not_ge hx,?_⟩; by_contra hy; exact h (iff_of_false hx hy)
  rcases hh with hh|hh
  · rw [abs_of_neg (by linarith : x-y < 0)]
    rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
    rw [abs_le]; constructor <;> linarith

lemma integral_abs_le_sqrt_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ ω, |X ω| ∂μ) ≤ Real.sqrt (∫ ω, X ω^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hX) (by simpa using (memLp_const (1:ℝ) (p := 2) (μ := μ)))
  simpa only [Real.norm_eq_abs,abs_one,mul_one,Real.rpow_two,sq_abs,
    one_pow,integral_const,probReal_univ,one_smul,Real.one_rpow,← Real.sqrt_eq_rpow,Real.sqrt_one,mul_one] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma inner_hasGaussianLaw (v : E) : HasGaussianLaw (fun c : E => ⟪v,c⟫) (stdGaussian E) := by
  exact IsGaussian.hasGaussianLaw_id.map (innerSL ℝ v)

lemma inner_law (v : E) : (stdGaussian E).map (fun c : E => ⟪v,c⟫) =
    gaussianReal 0 ⟨‖v‖^2,sq_nonneg _⟩ := by
  have h := (inner_hasGaussianLaw v).map_eq_gaussianReal
  have hm : (∫ c : E, ⟪v,c⟫ ∂stdGaussian E)=0 := integral_strongDual_stdGaussian (innerSL ℝ v)
  have hv : Var[fun c : E => ⟪v,c⟫;stdGaussian E]=‖v‖^2 := by
    change Var[⇑(innerSL ℝ v);stdGaussian E]=‖v‖^2
    rw [variance_dual_stdGaussian,innerSL_apply_norm]
  rw [hm,hv] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Subtype.ext
  simp

lemma inner_second_moment (v : E) : (∫ c : E, ⟪v,c⟫^2 ∂stdGaussian E)=‖v‖^2 := by
  have h := variance_eq_sub (inner_hasGaussianLaw v).memLp_two
  have hm : (∫ c : E, ⟪v,c⟫ ∂stdGaussian E)=0 := integral_strongDual_stdGaussian (innerSL ℝ v)
  have hv : Var[fun c : E => ⟪v,c⟫;stdGaussian E]=‖v‖^2 := by
    change Var[⇑(innerSL ℝ v);stdGaussian E]=‖v‖^2
    rw [variance_dual_stdGaussian,innerSL_apply_norm]
  simpa only [hm,hv,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,Pi.pow_apply] using h.symm

lemma orthogonal_indep {v w : E} (hvw : ⟪v,w⟫=0) :
    IndepFun (fun c : E => ⟪v,c⟫) (fun c : E => ⟪w,c⟫) (stdGaussian E) := by
  have hj : HasGaussianLaw (fun c : E => (⟪v,c⟫,⟪w,c⟫)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map ((innerSL ℝ v).prod (innerSL ℝ w))
  apply hj.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  exact hvw

lemma sign_inner_le {v w : E} (hv : ‖v‖=1) (hw : ‖w‖=1) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 2*‖v-w‖ := by
  by_cases hd : 1 ≤ ‖v-w‖
  · have h := integral_mono (signFailure_integrable (μ := stdGaussian E) (X := fun c => ⟪v,c⟫) (Y := fun c => ⟪w,c⟫) (by fun_prop) (by fun_prop))
        (integrable_const (1:ℝ)) (fun c : E => (signFailure_range ⟪v,c⟫ ⟪w,c⟫).2)
    simp only [integral_const,probReal_univ,one_smul] at h
    linarith
  have hd1 : ‖v-w‖ < 1 := lt_of_not_ge hd
  have horth : ⟪v+w,v-w⟫=0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm w v,hv,hw]
    ring
  have hsum : (1:ℝ) ≤ ‖v+w‖^2 := by
    have h := parallelogram_law_with_norm ℝ v w
    simp only [hv,hw,one_pow] at h
    nlinarith [norm_nonneg (v-w)]
  have hh := independent_small_ball (μ := stdGaussian E)
    (X := fun c : E => ⟪v+w,c⟫) (Y := fun c : E => ⟪v-w,c⟫)
    (by fun_prop) (by fun_prop) (inner_hasGaussianLaw (v-w)).integrable
    (orthogonal_indep horth) (v := ⟨‖v+w‖^2,sq_nonneg _⟩) (by exact_mod_cast hsum) (inner_law _)
  have hi := integral_abs_le_sqrt_sq (inner_hasGaussianLaw (v-w)).memLp_two
  rw [inner_second_moment,Real.sqrt_sq (norm_nonneg _)] at hi
  have hb := integral_mono (signFailure_integrable (μ := stdGaussian E) (X := fun c => ⟪v,c⟫) (Y := fun c => ⟪w,c⟫) (by fun_prop) (by fun_prop))
    (between_integrable (μ := stdGaussian E) (X := fun c => ⟪v+w,c⟫) (Y := fun c => ⟪v-w,c⟫)
      (by fun_prop) (by fun_prop)) (fun c => by
      simpa only [inner_add_left,inner_sub_left] using signFailure_sumdiff_le ⟪v,c⟫ ⟪w,c⟫)
  linarith

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι]

def score (v c : ι → ℝ) : ℝ := ∑ i, v i*c i
abbrev vector (v : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 v

lemma score_inner (v c : ι → ℝ) : score v c=⟪vector v,vector c⟫ := by
  simp [score,PiLp.inner_apply,vector,mul_comm]

lemma toLp_preserving : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) (stdGaussian (EuclideanSpace ℝ ι)) :=
  ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable,map_pi_eq_stdGaussian⟩

lemma integral_score_sign (v w : ι → ℝ) :
    (∫ c, signFailure (score v c) (score w c) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ c : EuclideanSpace ℝ ι, signFailure ⟪vector v,c⟫ ⟪vector w,c⟫ ∂stdGaussian (EuclideanSpace ℝ ι) := by
  simpa only [score_inner,MeasurableEquiv.toLp_apply] using toLp_preserving.integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
    (fun c : EuclideanSpace ℝ ι => signFailure ⟪vector v,c⟫ ⟪vector w,c⟫)

lemma signFailure_mul_right {r : ℝ} (hr : 0 < r) (x y : ℝ) : signFailure x (r*y)=signFailure x y := by
  simp only [signFailure,mul_nonneg_iff_of_pos_left hr]

lemma signFailure_mul {r : ℝ} (hr : 0 < r) (x y : ℝ) : signFailure (r*x) (r*y)=signFailure x y := by
  simp only [signFailure,mul_nonneg_iff_of_pos_left hr]

section Norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma norm_unit (v : E) (hv : 0<‖v‖) : ‖(‖v‖⁻¹:ℝ) • v‖=1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv),inv_mul_cancel₀ hv.ne']

lemma distance_normalize {u v : E} (hu : ‖u‖=1) (hv : 0<‖v‖) :
    ‖u-(‖v‖⁻¹:ℝ) • v‖ ≤ 2*‖u-v‖ := by
  have he : v-(‖v‖⁻¹:ℝ) • v=(1-‖v‖⁻¹:ℝ) • v := by rw [sub_smul,one_smul]
  have hn : ‖v-(‖v‖⁻¹:ℝ) • v‖=|‖v‖-1| := by
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      |1-‖v‖⁻¹| *‖v‖ = |(1-‖v‖⁻¹)*‖v‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg v)]
      _ = |‖v‖-1| := by congr 1; field_simp

  have h := dist_triangle u v ((‖v‖⁻¹:ℝ) • v)
  simp only [dist_eq_norm] at h
  have hb := abs_norm_sub_norm_le v u
  rw [hu,norm_sub_rev v u] at hb
  rw [hn] at h
  linarith
end Norm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
lemma sign_inner_normalize_le {v w : E} (hv : ‖v‖=1) (hw : 0<‖w‖) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 4*‖v-w‖ := by
  have h := sign_inner_le hv (norm_unit w hw)
  simp only [real_inner_smul_left,
    signFailure_mul_right (inv_pos.mpr hw)] at h
  exact h.trans (by have := distance_normalize hv hw; linarith)

lemma sign_inner_common_norm {v w : E} {s : ℝ} (hs : 0 < s) (hv : ‖v‖=s) (hw : ‖w‖=s) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 2/s*‖v-w‖ := by
  have hv1 : ‖s⁻¹ • v‖=1 := by simpa only [hv] using norm_unit v (by rw [hv]; exact hs)
  have hw1 : ‖s⁻¹ • w‖=1 := by simpa only [hw] using norm_unit w (by rw [hw]; exact hs)
  have h := sign_inner_le hv1 hw1
  simp only [real_inner_smul_left,signFailure_mul (inv_pos.mpr hs)] at h
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)] at h
  convert h using 1 <;> first | rfl | ring
end MinUncut.GaussianBudget

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

open scoped BigOperators
open MeasureTheory

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]
def cube (T : ℚ) : Set (ι → ℝ) := Set.pi Set.univ (fun _ => Ioc (-(T:ℝ)) T)

lemma cube_measurable (T : ℚ) : MeasurableSet (cube (ι := ι) T) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioc)

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

abbrev gaussianLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

lemma coordinate_sq_integrable (i : ι) : Integrable (fun x : ι → ℝ => x i^2) (gaussianLaw ι) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).integrable_sq
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable h

lemma coordinate_second_moment (i : ι) : (∫ x : ι → ℝ, x i^2 ∂gaussianLaw ι)=1 := by
  have hp := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have h : (∫ x : ℝ, x^2 ∂gaussianReal 0 1)=1 := by
    have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    change Var[id; gaussianReal 0 1] = (1:ℝ) at hh
    rw [variance_eq_integral measurable_id.aemeasurable] at hh
    simpa only [id_eq,integral_id_gaussianReal,sub_zero,NNReal.coe_one] using hh
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable (by fun_prop)] at h
  exact h

lemma gaussian_cube_tail {T : ℚ} (hT : 0 < T) :
    (gaussianLaw ι).real (cube T)ᶜ ≤ (Fintype.card ι:ℝ)/(T:ℝ)^2 := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  let F : (ι → ℝ) → ℝ := (cube (ι := ι) T)ᶜ.indicator (fun _ => 1)
  have hi : Integrable F (gaussianLaw ι) := (integrable_const (1:ℝ)).indicator (cube_measurable T).compl
  have hacc : Integrable (fun x : ι → ℝ => (∑ i, x i^2)/(T:ℝ)^2) (gaussianLaw ι) :=
    (integrable_finsetSum _ (fun i _ => coordinate_sq_integrable i)).div_const _
  have hpoint (x : ι → ℝ) : F x ≤ (∑ i, x i^2)/(T:ℝ)^2 := by
    by_cases hx : x ∈ cube (ι := ι) T
    · simp only [F,Set.indicator_of_notMem (show x ∉ (cube T)ᶜ from fun hh => hh hx)]
      positivity
    · rw [show F x=1 by exact Set.indicator_of_mem hx _]
      apply (le_div_iff₀ (sq_pos_of_pos hT')).mpr
      obtain ⟨i,hi⟩ : ∃ i : ι, ¬ (-(T:ℝ)<x i ∧ x i ≤ T) := by
        simpa only [cube,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Ioc,not_forall] using hx
      have hs : (T:ℝ)^2 ≤ x i^2 := by
        rcases not_and_or.mp hi with h|h
        · have := le_of_not_gt h; nlinarith
        · have := lt_of_not_ge h; nlinarith
      have hb := Finset.single_le_sum (s := Finset.univ) (a := i) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      simpa only [one_mul] using hs.trans hb
  have hh := integral_mono hi hacc hpoint
  have hleft : (∫ x, F x ∂gaussianLaw ι)=(gaussianLaw ι).real (cube T)ᶜ := by
    change (∫ x, (cube (ι := ι) T)ᶜ.indicator (fun _ => (1:ℝ)) x ∂gaussianLaw ι)=_
    rw [integral_indicator (cube_measurable T).compl,setIntegral_const,smul_eq_mul,mul_one]
  have hright : (∫ x : ι → ℝ, (∑ i, x i^2)/(T:ℝ)^2 ∂gaussianLaw ι)=(Fintype.card ι:ℝ)/(T:ℝ)^2 := by
    rw [integral_div,integral_finsetSum _ (fun i _ => coordinate_sq_integrable i)]
    simp only [coordinate_second_moment,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  simpa only [hleft,hright] using hh

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

def thresholdBit (x : ℝ) : Bool := if 0 ≤ x then true else false

def thresholdTable (v : S → ι → ℝ) (x : ι → ℝ) : S → Bool :=
  fun s => thresholdBit (score (v s) x)

lemma thresholdBit_measurable : Measurable thresholdBit :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma score_law (v : ι → ℝ) : (gaussianLaw ι).map (score v)=
    gaussianReal 0 ⟨‖vector v‖^2,sq_nonneg _⟩ := by
  rw [← inner_law (vector v),← toLp_preserving.map_eq]
  rw [Measure.map_map (by fun_prop) toLp_preserving.measurable]
  congr 1
  ext x
  exact score_inner v x

lemma score_small_ball {v : ι → ℝ} (hv : 1 ≤ ‖vector v‖^2) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianLaw ι).real {x | |score v x| ≤ r} ≤ 2*r := by
  have hh := small_ball (by exact_mod_cast hv : (1:ℝ≥0) ≤ ⟨‖vector v‖^2,sq_nonneg _⟩) hr
  rw [← score_law v,Measure.real,Measure.map_apply (by unfold score; fun_prop)
    (measurableSet_le (by fun_prop) measurable_const)] at hh
  exact hh

lemma threshold_change_small {a b r : ℝ} (hr : |a-b| ≤ r)
    (hab : thresholdBit a ≠ thresholdBit b) : |a| ≤ r := by
  unfold thresholdBit at hab
  split_ifs at hab with ha hb hb
  · exact False.elim (hab rfl)
  · rw [abs_of_nonneg ha] at ⊢
    have hh : b < 0 := lt_of_not_ge hb
    have := (abs_le.mp hr).2
    linarith
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have := (abs_le.mp hr).1
    linarith
  · exact False.elim (hab rfl)

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_NormalizedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.FiniteGaussian

lemma normalized_test_bound {G E X Y : ℝ} (hG : 0 < G) (hE : 0 ≤ E)
    (hX : 0 ≤ X) (hXG : X ≤ G) (hY : 0 ≤ Y) (hYE : Y ≤ E) :
    |(X+Y)/(G+E)-X/G| ≤ E/(G+E) := by
  have hGE : 0 < G+E := by linarith
  have he : (X+Y)/(G+E)-X/G=(G*Y-E*X)/(G*(G+E)) := by
    field_simp
    ring
  have he' : E/(G+E)=(E*G)/(G*(G+E)) := by
    field_simp
  rw [he,he',abs_div,abs_of_pos (mul_pos hG hGE),div_le_div_iff_of_pos_right (mul_pos hG hGE)]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hG.le hY,mul_nonneg hE (sub_nonneg.mpr hXG)]
  · nlinarith [mul_nonneg hE hX,mul_nonneg hG.le (sub_nonneg.mpr hYE)]

lemma finite_normalized_test_bound {ι : Type*} [Fintype ι] (q g F : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hqg : ∀ i, g i ≤ q i)
    (hG : 0 < ∑ i, g i) (hF : ∀ i, 0 ≤ F i ∧ F i ≤ 1) :
    |(∑ i, q i*F i)/(∑ i, q i)-(∑ i, g i*F i)/(∑ i, g i)| ≤
      ((∑ i, q i)-(∑ i, g i))/(∑ i, q i) := by
  have residual : 0 ≤ ∑ i, (q i-g i) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hqg i))
  have hx : 0 ≤ ∑ i, g i*F i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hg i) (hF i).1)
  have hxg : (∑ i, g i*F i) ≤ ∑ i, g i :=
    Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (hg i) (sub_nonneg.mpr (hF i).2)])
  have hy : 0 ≤ ∑ i, (q i-g i)*F i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hqg i)) (hF i).1)
  have hye : (∑ i, (q i-g i)*F i) ≤ ∑ i, (q i-g i) :=
    Finset.sum_le_sum (fun i _ => by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hqg i)) (sub_nonneg.mpr (hF i).2)])
  have hh := normalized_test_bound hG residual hx hxg hy hye
  have he : (∑ i, g i*F i)+(∑ i, (q i-g i)*F i)=∑ i, q i*F i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he' : (∑ i, g i)+(∑ i, (q i-g i))=∑ i, q i := by
    rw [Finset.sum_sub_distrib]; ring
  rw [he,he'] at hh
  simpa only [Finset.sum_sub_distrib] using hh

end MinUncut.FiniteGaussian

end
section
open scoped BigOperators
namespace MinUncut.FiniteGaussian

lemma product_residual_bound {G Q : ℝ} (hG : 1 ≤ G) (hGQ : G ≤ Q) (d : ℕ) :
    (Q^d-G^d)/Q^d ≤ (d:ℝ)*(Q-G) := by
  have hG0 : 0 < G := by linarith
  have hQ : 0 < Q := hG0.trans_le hGQ
  have hratio : 0 ≤ G/Q := by positivity
  have hbern := one_add_mul_sub_le_pow (by linarith : (-1:ℝ) ≤ G/Q) d
  have he : (Q^d-G^d)/Q^d=1-(G/Q)^d := by
    rw [div_pow,sub_div,div_self (pow_ne_zero _ hQ.ne')]
  have hr : (Q-G)/Q ≤ Q-G := div_le_self (sub_nonneg.mpr hGQ) (hG.trans hGQ)
  have hh : 1-(G/Q)^d ≤ (d:ℝ)*((Q-G)/Q) := by
    rw [sub_div,div_self hQ.ne']
    nlinarith
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg d))

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDensityError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace MinUncut.FiniteGaussian

def baseDensity (v : ℝ) : ℝ := Real.exp (-v^2/2)
def gIntegral (a b : ℝ) : ℝ := ∫ v in a..b, baseDensity v

lemma continuous_baseDensity : Continuous baseDensity := by unfold baseDensity; fun_prop

lemma gIntegral_pos {a b : ℝ} (hab : a < b) : 0 < gIntegral a b := by
  apply intervalIntegral.integral_pos hab continuous_baseDensity.continuousOn
  · intro v _; exact (Real.exp_pos _).le
  · exact ⟨a,⟨le_rfl,hab.le⟩,Real.exp_pos _⟩

lemma gIntegral_large {T : ℝ} (hT : 1 ≤ T) : 1 < gIntegral (-T) T := by
  have hbase : (5/3:ℝ) ≤ gIntegral (-1) 1 := by
    have hh := intervalIntegral.integral_mono (a := (-1:ℝ)) (b := 1) (by norm_num)
      (show IntervalIntegrable (fun v : ℝ => 1-v^2/2) volume (-1) 1 from
        (by fun_prop : Continuous (fun v : ℝ => 1-v^2/2)).intervalIntegrable _ _)
      (continuous_baseDensity.intervalIntegrable _ _)
      (fun v => (show 1-v^2/2 ≤ baseDensity v by
        have := Real.add_one_le_exp (-v^2/2)
        dsimp [baseDensity]; linarith))
    have he : (∫ v in (-1:ℝ)..1, 1-v^2/2)=(5/3:ℝ) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const)
        ((show Continuous (fun v : ℝ => v^2/2) by fun_prop).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_div,integral_pow]
      norm_num
    simpa only [he,gIntegral] using hh
  have hle : gIntegral (-1) 1 ≤ gIntegral (-T) T := by
    exact intervalIntegral.integral_mono_interval (by linarith) (by norm_num) hT
      (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))
      (continuous_baseDensity.intervalIntegrable _ _)
  linarith

open scoped BigOperators
open MeasureTheory

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

abbrev gaussianConstant : ℝ := (Real.sqrt (2*Real.pi))⁻¹

lemma gaussianConstant_pos : 0 < gaussianConstant := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

lemma gaussian_Ioc {a b : ℚ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Ioc (a:ℝ) b)=gaussianConstant*gIntegral a b := by
  rw [Measure.real,gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  have he : gaussianPDFReal 0 1=fun x => gaussianConstant*baseDensity x := by
    ext x
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,baseDensity]
  rw [he,integral_const_mul]
  congr 1
  exact (intervalIntegral.integral_of_le (by exact_mod_cast hab)).symm

lemma gaussian_cube_pos {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 < T) :
    0 < (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cube T) := by
  unfold cube Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_pos
  intro i _
  change 0 < (gaussianReal 0 1).real (Ioc (-(T:ℝ)) T)
  rw [show -(T:ℝ)=((-T:ℚ):ℝ) by norm_cast,gaussian_Ioc (by linarith)]
  exact mul_pos gaussianConstant_pos (gIntegral_pos (by exact_mod_cast (show -T<T by linarith)))

lemma gaussian_cube {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 ≤ T) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cube T)=
      gaussianConstant^(Fintype.card ι)*(gIntegral (-T) T)^(Fintype.card ι) := by
  unfold cube Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ _ : ι, (gaussianReal 0 1).real (Ioc (-(T:ℝ)) T))=_
  simp only [show -(T:ℝ)=((-T:ℚ):ℝ) by norm_cast,gaussian_Ioc (by linarith : -T≤T),
    Finset.prod_const,Finset.card_univ,mul_pow]

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiftedVectors
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

lemma delta_distance_le (η : ℝ) (z w : C) :
    (∑ c : C, ((if c=z then η else 0)-(if c=w then η else 0))^2) ≤ 4*η^2 := by
  calc
    _ ≤ ∑ c : C, (2*(if c=z then η^2 else 0)+2*(if c=w then η^2 else 0)) := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> nlinarith [sq_nonneg η]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true]; ring

end MinUncut.GaussianBudget

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianPacking
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

abbrev productLaw (X C : Type*) [Fintype X] [Fintype C] :=
  (Measure.pi (fun _ : X => gaussianReal 0 1)).prod
    ((Measure.pi (fun _ : X => gaussianReal 0 1)).prod (Measure.pi (fun _ : C => gaussianReal 0 1)))

end MinUncut.GaussianBudget

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ConditionalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

lemma conditional_rounding_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (hp : 0 < μ.real s) {F G : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hFrange : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hGrange : ∀ x, 0 ≤ G x ∧ G x ≤ 1) :
    |(∫ x, F x ∂μ)-(∫ x in s, G x ∂μ)/μ.real s| ≤
      μ.real sᶜ+∫ x in s, |F x-G x| ∂μ := by
  let p := μ.real s
  let a := μ.real sᶜ
  let B := ∫ x in sᶜ, F x ∂μ
  let C := ∫ x in s, G x ∂μ
  let A := ∫ x in s, F x-G x ∂μ
  have ha : 0 ≤ a := measureReal_nonneg
  have hpa : p+a=1 := by simpa only [p,a,probReal_univ] using measureReal_add_measureReal_compl (μ := μ) hs
  have hB0 : 0 ≤ B := integral_nonneg (fun x => (hFrange x).1)
  have hBa : B ≤ a := by
    have hh := integral_mono hF.integrableOn (integrable_const (1:ℝ)) (fun x => (hFrange x).2) (μ := μ.restrict sᶜ)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh
  have hC0 : 0 ≤ C := integral_nonneg (fun x => (hGrange x).1)
  have hCp : C ≤ p := by
    have hh := integral_mono hG.integrableOn (integrable_const (1:ℝ)) (fun x => (hGrange x).2) (μ := μ.restrict s)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh
  have hratio : 0 ≤ a*C/p := by dsimp [p]; positivity
  have hratiole : a*C/p ≤ a := by
    apply (div_le_iff₀ hp).mpr
    exact mul_le_mul_of_nonneg_left hCp ha
  have hbound : |B-a*C/p| ≤ a := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : (∫ x, F x ∂μ)-C/p=A+(B-a*C/p) := by
    have hsplit := integral_add_compl hs hF
    have hsub := integral_sub hF.integrableOn hG.integrableOn (μ := μ.restrict s)
    change A=(∫ x in s, F x ∂μ)-C at hsub
    have hx : C-C/p= -(a*C/p) := by
      have hp0 : p ≠ 0 := ne_of_gt hp
      apply (mul_right_cancel₀ hp0)
      field_simp [hp0]
      nlinarith
    rw [← hsplit]
    change (∫ x in s, F x ∂μ)+B-C/p=A+(B-a*C/p)
    rw [hsub]
    linear_combination hx
  change |(∫ x, F x ∂μ)-C/p| ≤ a+_
  rw [he]
  have hA : |A| ≤ ∫ x in s, |F x-G x| ∂μ := abs_integral_le_integral_abs
  exact (abs_add_le _ _).trans (by linarith)

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianRounding
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

lemma smallBall_indicator_integrable (v : ι → ℝ) (r : ℝ) :
    Integrable ({x : ι → ℝ | |score v x| ≤ r}.indicator (fun _ => (1:ℝ))) (gaussianLaw ι) := by
  apply (integrable_const (1:ℝ)).indicator
  apply measurableSet_le _ measurable_const
  unfold score
  fun_prop

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_ArbitraryProductWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
lemma finite_product_test_bound_general {ι α : Type*} [Fintype ι] [Fintype α] (q g : α → ℝ)
    (hg : ∀ a, 0 ≤ g a) (hqg : ∀ a, g a ≤ q a)
    (hG : 1 ≤ ∑ a, g a) (F : (ι → α) → ℝ)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, q (x i))*F x)/(∑ a, q a)^(Fintype.card ι)-
      (∑ x, (∏ i, g (x i))*F x)/(∑ a, g a)^(Fintype.card ι)| ≤
      (Fintype.card ι:ℝ)*((∑ a, q a)-(∑ a, g a)) := by
  classical
  have hg0 : 0 < ∑ a, g a := by linarith
  have hq0 (a : α) : 0 ≤ q a := (hg a).trans (hqg a)
  have hgprod (x : ι → α) : 0 ≤ ∏ i, g (x i) :=
    Finset.prod_nonneg (fun i _ => hg (x i))
  have hprod (x : ι → α) : (∏ i, g (x i)) ≤ ∏ i, q (x i) :=
    Finset.prod_le_prod (fun index _ => hg (x index)) (fun index _ => hqg (x index))
  have hsum (w : α → ℝ) : (∑ x : ι → α, ∏ i, w (x i))=(∑ a, w a)^(Fintype.card ι) :=
    by simpa only [Finset.prod_const,Finset.card_univ] using (Fintype.prod_sum (fun _ : ι => w)).symm
  have htotal : 0 < ∑ x : ι → α, ∏ i, g (x i) := by
    rw [hsum]; exact pow_pos hg0 (Fintype.card ι)
  have hh := finite_normalized_test_bound (fun x : ι → α => ∏ i, q (x i))
    (fun x => ∏ i, g (x i)) F hgprod hprod htotal hF
  rw [hsum,hsum] at hh
  exact hh.trans (product_residual_bound hG (Finset.sum_le_sum (fun a _ => hqg a)) (Fintype.card ι))

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end MinUncutGames.Foundations.Complexity.Runtime

namespace MinUncutGames.Foundations.Complexity.MachineComposition

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

end MinUncutGames.Foundations.Complexity.MachineComposition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Density
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

structure Density (A : Type*) [Fintype A] where
  val : A → ℝ
  nonneg : ∀ a, 0 ≤ val a
  mean_one : (𝔼 a, val a) = 1

namespace Density
variable {A : Type*} [Fintype A]
instance instCoeFunForallReal : CoeFun (Density A) (fun _ => A → ℝ) := ⟨val⟩

lemma pointwise_le_card (p : Density A) (a : A) : p a ≤ Fintype.card A := by
  have h := p.mean_one
  rw [Fintype.expect_eq_sum_div_card] at h
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    have : Nonempty A := ⟨a⟩
    positivity
  have hs : ∑ a, p a = Fintype.card A := by simpa using (div_eq_iff hc).mp h
  rw [← hs]
  exact Finset.single_le_sum (fun a _ => p.nonneg a) (Finset.mem_univ a)

def tvUniform (p : Density A) : ℝ := (𝔼 a, |p a - 1|) / 2

lemma tvUniform_le_sqrt [Nonempty A] (p : Density A) :
    p.tvUniform ≤ Real.sqrt (𝔼 a, (p a - 1)^2) / 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => |p a - 1|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const, sq_abs] at h
  have hp : 0 ≤ 𝔼 a, (p a - 1)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hg : (𝔼 a, |p a - 1|) ≤ Real.sqrt (𝔼 a, (p a - 1)^2) := by
    refine (sq_le_sq₀ (Finset.expect_nonneg (fun _ _ => abs_nonneg _))
      (Real.sqrt_nonneg _)).mp ?_
    rwa [Real.sq_sqrt hp]
  exact div_le_div_of_nonneg_right hg (by norm_num)

def ofMap {B : Type*} [Fintype B] [Nonempty B] [DecidableEq A] (f : B → A) : Density A where
  val a := (Fintype.card A : ℝ) * 𝔼 b, if f b = a then 1 else 0
  nonneg a := mul_nonneg (Nat.cast_nonneg _) (Finset.expect_nonneg (fun _ _ => by positivity))
  mean_one := by
    have : Nonempty A := ⟨f (Classical.choice (inferInstance : Nonempty B))⟩
    have hc : (Fintype.card A : ℝ) ≠ 0 := by positivity
    rw [← Finset.mul_expect, Finset.expect_comm]
    simp only [Fintype.expect_eq_sum_div_card]
    simp [hc]

lemma expect_ofMap {B : Type*} [Fintype B] [Nonempty B] [DecidableEq A]
    (f : B → A) (g : A → ℝ) :
    (𝔼 a, ofMap f a * g a) = 𝔼 b, g (f b) := by
  have : Nonempty A := ⟨f (Classical.choice (inferInstance : Nonempty B))⟩
  have hc : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp only [ofMap]
  simp_rw [mul_assoc, Finset.expect_mul, Finset.mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro b _
  rw [Fintype.expect_eq_sum_div_card]
  simp [mul_ite, hc]

lemma ofMap_eq_of_invariant {B : Type*} [Fintype B] [Nonempty B]
    [DecidableEq A] {f : B → A} (h : ∀ a a', ofMap f a = ofMap f a') (a : A) :
    ofMap f a = 1 := by
  have : Nonempty A := ⟨a⟩
  calc ofMap f a = 𝔼 a', ofMap f a := (Fintype.expect_const _).symm
       _ = 𝔼 a', ofMap f a' := Finset.expect_congr rfl (fun a' _ => h a a')
       _ = 1 := (ofMap f).mean_one

lemma ofMap_surjective_hom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (y : H) : ofMap f y = 1 := by
  apply ofMap_eq_of_invariant
  intro a a'
  obtain ⟨x, hx⟩ := hf (a' - a)
  unfold ofMap
  dsimp only
  congr 1
  apply Fintype.expect_equiv (Equiv.addLeft x)
  intro z
  change (if f z = a then (1 : ℝ) else 0) = (if f (x+z) = a' then 1 else 0)
  rw [map_add, hx]
  have ht : a' - a + f z = a' + (f z - a) := by abel
  have heq : a' - a + f z = a' ↔ f z = a := by rw [ht]; simp [sub_eq_zero]
  simp only [heq]

end Density

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

omit [Fintype ι] in
lemma overlap_union_bound (H K : Finset ι) :
    (if ¬Disjoint H K then (1 : ℝ) else 0) ≤
      ∑ i ∈ H, if i ∈ K then (1 : ℝ) else 0 := by
  by_cases h : Disjoint H K
  · simp only [h, not_true_eq_false, ite_false]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  · simp only [h, not_false_eq_true, ite_true]
    obtain ⟨i, hi, hik⟩ := Finset.not_disjoint_iff.mp h
    have hh := Finset.single_le_sum (s := H)
      (f := fun i => if i ∈ K then (1 : ℝ) else 0) (fun _ _ => by positivity) hi
    simpa [hik] using hh

end MinUncut.OuterSmoothness

namespace MinUncut.OuterSmoothness.Density
variable {A : Type*} [Fintype A]

lemma abs_expect_le (f : A → ℝ) : |𝔼 a, f a| ≤ 𝔼 a, |f a| := by
  simp only [Fintype.expect_eq_sum_div_card, abs_div, abs_of_nonneg (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

lemma expect_difference (p : Density A) (g : A → ℝ) {M : ℝ}
    (_hM : 0 ≤ M) (hg : ∀ a, |g a| ≤ M) :
    |(𝔼 a, p a * g a) - (𝔼 a, g a)| ≤ 2 * p.tvUniform * M := by
  have heq : (𝔼 a, p a * g a) - (𝔼 a, g a) = 𝔼 a, (p a - 1) * g a := by
    simp only [sub_mul, one_mul, Finset.expect_sub_distrib]
  rw [heq]
  calc _ ≤ 𝔼 a, |(p a - 1) * g a| := abs_expect_le _
       _ ≤ 𝔼 a, |p a - 1| * M := by
         apply Finset.expect_le_expect
         intro a _
         rw [abs_mul]
         exact mul_le_mul_of_nonneg_left (hg a) (abs_nonneg _)
       _ = _ := by rw [← Finset.expect_mul]; unfold tvUniform; ring

end MinUncut.OuterSmoothness.Density

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

open scoped BigOperators

end MinUncutGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Game
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Soundness.RepetitionUpper

theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero =>
      simp only [Rat.pow_zero, Rat.natCast_ofNat, Rat.zero_mul, Rat.add_zero, Rat.one_mul]
      exact Rat.le_refl
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

end MinUncutGames.Soundness.RepetitionUpper

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

noncomputable section

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) (c : ℝ) :
    traceAverage w n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

variable {α : Type*} [Fintype α]

theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

theorem max_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : max x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [max_def, h, hx, hy]

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_LabelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

end

open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_KernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

variable {I A B S : Type*} [DecidableEq I]

def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

end KernelSampling
end
end MinUncutGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Pinsker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

end MinUncutGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ProfileCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

end

end MinUncutGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedInformation
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

noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

open scoped BigOperators
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

theorem abs_half_sub_half_mul (a b c : ℝ) :
    |a / 2 - b / 2 * c| = |a - b * c| / 2 := by
  rw [show a / 2 - b / 2 * c = (a - b * c) / 2 by ring, abs_div]
  norm_num

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Information

theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem discount_le_self {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

theorem discount_loss_le_mul {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

open scoped BigOperators
open Games
noncomputable section

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

open CorrelatedSampling

open scoped BigOperators
open Games Information

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CompletedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

end

end MinUncutGames.Foundations.Repetition.CompletedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedLikelihood
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

open scoped BigOperators
open Games
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def completionTupleEquiv : (I → X × Y) ≃ ((I → X) × (I → Y)) where
  toFun u := (fun i => (u i).1, fun i => (u i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv u := by funext i; rfl
  right_inv z := by cases z; rfl

end LocalNormalization

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

def sourceThreshold (D : Nat) (δ : ℚ) : ℚ := 4 * (D : ℚ)⁻¹ * δ ^ 2

theorem sourceThreshold_pos {D : Nat} (hD : 0 < D) {δ : ℚ} (hδ : 0 < δ) :
    0 < sourceThreshold D δ := by
  unfold sourceThreshold
  positivity

theorem exists_repetition_length {gap δ : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) {D : Nat} (hD : 0 < D) :
    ∃ u : Nat, 0 < u ∧ (rate gap) ^ u < sourceThreshold D δ :=
  MinUncutGames.Soundness.RepetitionUpper.exists_power_lt (rate gap) (sourceThreshold D δ)
    (rate_bounds hgap hgap1).1.le (rate_bounds hgap hgap1).2 (sourceThreshold_pos hD hδ)

def repetitionLength (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) : Nat :=
  Nat.find (exists_repetition_length hgap hgap1 hδ hD)

end MinUncutGames.Integration.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Reduction.MachineTransducer

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {Q : Type} [Fintype Q]

def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

end MinUncutGames.Reduction.MachineTransducer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineUnaryAddAt

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end MinUncutGames.Foundations.Complexity.MachineUnaryAddAt

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Gap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceGap

open SourceOccurrences
open MinUncutGames.Integration.SourceParameters
open MinUncutGames.Reduction

theorem third_pos {η : ℚ} (hη : 0 < η) : 0 < η / 3 := by positivity

theorem third_le_one {η : ℚ} (hη : η ≤ 1) : η / 3 ≤ 1 := by linarith

def repetitionCount (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) : ℕ :=
  repetitionLength (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD

end MinUncutGames.Foundations.Hastad.SourceGap

namespace MinUncutGames.Foundations.Hastad.SourceNoiseParameter

def noiseDenominator (ξ : ℚ) : ℕ := ξ.den + 2

theorem noiseDenominator_ge_two (ξ : ℚ) : 2 ≤ noiseDenominator ξ := by
  unfold noiseDenominator
  omega

theorem noiseDenominator_pos (ξ : ℚ) : 0 < noiseDenominator ξ :=
  lt_of_lt_of_le (by decide) (noiseDenominator_ge_two ξ)

theorem noiseDenominator_inv_le {ξ : ℚ} (hξ : 0 < ξ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ ξ := by
  have hn : (1 : ℤ) ≤ ξ.num := by
    have h := Rat.num_pos.mpr hξ
    omega
  have hnq : (1 : ℚ) ≤ (ξ.num : ℚ) := by exact_mod_cast hn
  have hd : (0 : ℚ) < (ξ.den : ℚ) := by exact_mod_cast ξ.den_pos
  calc
    (noiseDenominator ξ : ℚ)⁻¹ = 1 / (noiseDenominator ξ : ℚ) := inv_eq_one_div _
    _ ≤ 1 / (ξ.den : ℚ) := by
      apply one_div_le_one_div_of_le hd
      exact_mod_cast (show ξ.den ≤ noiseDenominator ξ by
        unfold noiseDenominator
        omega)
    _ ≤ (ξ.num : ℚ) / (ξ.den : ℚ) := div_le_div_of_nonneg_right hnq hd.le
    _ = ξ := ξ.num_div_den

end MinUncutGames.Foundations.Hastad.SourceNoiseParameter

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DegreeReplacement
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

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

variable {K : Type*} [Fintype K] [Nonempty K]

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end MinUncutGames.Foundations.PCP.CayleySampling

end
end
section
namespace MinUncutGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in

theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

theorem ratio_le_of_weight (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance instDecidableBadWord (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

end MinUncutGames.Foundations.PCP.CayleyTailCount

end
section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

end Averages

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
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

variable {I D : Type*}

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl


end MinUncutGames.Foundations.PCP.CayleySpectral


end
namespace MinUncutGames.Foundations.PCP.GraphTransport

open SpectralReturn

variable {V W D E : Type*}


variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)


end MinUncutGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudCount

open _root_.Turing
open MachineComposition

abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {Λ σ : Type}

def hit (flag : Bool) (x v : Nat) : Nat := if flag = false ∧ x = v then 1 else 0

inductive Label
  | copyFirst | copySecond | headerFirst | headerSecond | row | field | restore
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : Label :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

abbrev Row := Nat × List Nat

def rowWords (r : Row) : List Nat := r.1 :: r.2

def rowsHits (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => (if r.1 = v then 1 else 0) + rowsHits v rs

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudCount

end
section
namespace MinUncutGames.Foundations.Complexity.MachineCeilingPower

open _root_.Turing
open MachineComposition
open MinUncutGames.Foundations.PCP

variable {σ : Type}

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem appendTrace {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

end MinUncutGames.Foundations.Complexity.MachineCeilingPower

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudPadding

open _root_.Turing
open MachineComposition
open MinUncutGames.Foundations.PCP

abbrev State (σ : Type) := (σ × Bool) × Option Bool

end MinUncutGames.Foundations.Complexity.MachineCloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end MinUncutGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Relations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

end MinUncutGames.Foundations.PCP.AlphabetGraphBounds

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {K : Type}

variable {Λ σ : Type} {h bound : Nat} [DecidableEq K]

def resultTapes (output : K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem resultTapes_output (output : K) (base : K → List Bool) (bits : List Bool) :
    resultTapes output base bits output = bits.reverse ++ base output := by
  simp [resultTapes]

def affineValue (terms : List (Fin h × Nat)) (values : Fin h → Nat) (offset : Nat) : Nat :=
  (terms.map (fun term => term.2 * values term.1)).sum + offset

end MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLookupSpec

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

end MinUncutGames.Foundations.Complexity.MachineLookupSpec

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

end MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_LoopInitialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRepeat
open _root_.Turing

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

omit M input output in

theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

omit M input output in

theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i < count → budgets i ≤ bodyBound)
    (hl : ∀i, i ≤ count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end MinUncutGames.Foundations.Complexity.MachineRepeat

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

open _root_.Turing

theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

end MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCloudPrefix

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP
open scoped BigOperators

abbrev State (σ : Type) := (σ × Bool) × Option Bool

end MinUncutGames.Foundations.Complexity.MachineCloudPrefix

namespace MinUncutGames.Foundations.Complexity.MachineAppendAt

open _root_.Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

end MinUncutGames.Foundations.Complexity.MachineAppendAt

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudRank

open _root_.Turing MachineComposition MachineCloudCount

variable {σ : Type}

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudRank

end
section
namespace MinUncutGames.Foundations.Complexity.MachineTableRows

open _root_.Turing

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore, .reverseRead,
  .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

end MinUncutGames.Foundations.Complexity.MachineTableRows

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

open _root_.Turing MachineComposition
open PCP

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool

def lookupTape (i : Fin 5) : Tape := ⟨i.val + 1, by omega⟩

def fields : Fin 3 → Tape := Fin.cases 0 (Fin.cases 6 (fun _ => 7))

@[simp] theorem fields_zero : fields 0 = 0 := rfl
@[simp] theorem fields_one : fields 1 = 6 := rfl
@[simp] theorem fields_two : fields 2 = 7 := rfl

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (4 * q + 17) * inputLength + 2 * outputLength + 4 * q + 32795

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularMetadata

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP


abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

def querySteps (v x : Nat) : Nat := 2 * (x + 2) + 2 * (v + 2) + 1

end MinUncutGames.Foundations.Complexity.MachineRegularMetadata

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudSelect

open _root_.Turing MachineComposition
open MachineCloudCount (Row rowWords rowsHits )

abbrev BaseState (σ : Type) := MachineCloudCount.State σ

inductive BaseLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | field | restore | done | clearWork | clearRank
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : BaseLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .done

variable {σ : Type}

inductive Phase
  | checking | advancing | finishing
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.checking, .advancing, .finishing]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Control
  | initialize_ | dispatch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .dispatch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Label := BaseLabel ⊕ Control
abbrev State (σ : Type) := BaseState σ × Phase

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudSelect

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open _root_.Turing
open PCP.AlphabetTable

def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

variable {ρ : Type} [Fintype ρ] {d : Nat}

open _root_.Turing
open MachineComposition

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

open _root_.Turing MachineComposition

variable {K Λ ρ : Type} [DecidableEq K]

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderRowFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

variable {v d : Nat}

open _root_.Turing MachineComposition
open PCP.AlphabetTable

theorem concatenate {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing

def singleStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

def sequence {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

def widen {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (bound : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

variable {ρ : Type} [Fintype ρ] {v d : Nat}

open _root_.Turing MachineComposition

def boundarySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

open _root_.Turing
open MachineComposition

open _root_.Turing MachineComposition

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing

open _root_.Turing

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

open _root_.Turing

def familySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

open _root_.Turing

def singleFamilyStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePaddedExpanderFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularFamily

open _root_.Turing MachineComposition
open MachineCloudPadding


abbrev CoreTape := Fin 27

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MinUncutGames.Foundations.Complexity.MachineRegularFamily

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

end MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Alphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularInternalRow

open _root_.Turing MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive FinishLabel
  | seedReturn | copyReturn | restoreReturn | affine | restoreTarget | equality
  | row (stage : MachineTableRows.Label)
  | clearReverse | clearEquality
  deriving DecidableEq, Fintype

def finishFields (tape : Fin 8 → K) : Fin 3 → K := fun i =>
  if i = 0 then tape 0 else if i = 1 then tape 4 else tape 5

omit [DecidableEq K] in
@[simp] theorem finishFields_zero (tape : Fin 8 → K) : finishFields tape 0 = tape 0 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_one (tape : Fin 8 → K) : finishFields tape 1 = tape 4 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_two (tape : Fin 8 → K) : finishFields tape 2 = tape 5 := rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def rotorLookupTapes (tape : Fin 8 → K) (j : Fin 5) : K :=
  tape ⟨j.val + 1, by omega⟩

omit [DecidableEq K] in
theorem rotorLookupTapes_injective (tape : Fin 8 → K) (h : Function.Injective tape) :
    Function.Injective (rotorLookupTapes tape) := by
  intro i j hij
  have hv := congrArg Fin.val (h hij)
  apply Fin.ext
  simpa only [Fin.val_mk, Nat.add_left_inj] using hv

inductive SelectExtraTape
  | localIndex | owner | cloudSize | prefixOffset | darts
  | savedLeft | savedRight | localWork | sizeWork
  deriving DecidableEq

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

protected abbrev SelectCopy.enumList : List SelectCopy := [.oldLocal, .oldOwner, .dummyLocal,
  .dummySize, .dummyDifference]

protected theorem SelectCopy.enumList_nodup : SelectCopy.enumList.Nodup := by decide

instance instFintypeSelectCopy : Fintype SelectCopy where
  elems := ⟨SelectCopy.enumList, SelectCopy.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

protected abbrev SelectAdd.enumList : List SelectAdd := [.prefixOffset, .darts]

protected theorem SelectAdd.enumList_nodup : SelectAdd.enumList.Nodup := by decide

instance instFintypeSelectAdd : Fintype SelectAdd where
  elems := ⟨SelectAdd.enumList, SelectAdd.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAddStage
  | scan | restore
  deriving DecidableEq

protected abbrev SelectAddStage.enumList : List SelectAddStage := [.scan, .restore]

protected theorem SelectAddStage.enumList_nodup : SelectAddStage.enumList.Nodup := by decide

instance instFintypeSelectAddStage : Fintype SelectAddStage where
  elems := ⟨SelectAddStage.enumList, SelectAddStage.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev CoreTape := Fin 27

def dummySelectSteps (j k o m : Nat) : Nat :=
  (2 * (j + 1) + 1) + (2 * (k + 1) + 1) + (k + 1) +
    (2 * (j - k + 1) + 1) + 2 * (o + 1) + 2 * (m + 1) + (j + k + 7)

end MinUncutGames.Foundations.Complexity.MachineRegularInternalRow
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_SelectorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularInternalRow
open _root_.Turing MachineComposition
open PCP
variable {K Λ σ : Type} [DecidableEq K]

def coreRotorTapes : Fin 8 → CoreTape := ![3, 7, 10, 11, 12, 9, 13, 14]

def coreFinishTapes : Fin 8 → CoreTape := ![1, 15, 14, 9, 24, 25, 26, 8]

def coreCleanupTape : Fin 10 → CoreTape := ![10, 11, 12, 13, 14, 15, 9, 16, 17, 18]

end MinUncutGames.Foundations.Complexity.MachineRegularInternalRow

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

open _root_.Turing MachineComposition PCP

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineDummyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineDummyRows

open _root_.Turing

abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

end MinUncutGames.Foundations.Complexity.MachineDummyRows

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularDummyRow

open _root_.Turing MachineComposition

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

end MinUncutGames.Foundations.Complexity.MachineRegularDummyRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

open _root_.Turing MachineComposition PCP MachineRegularInternalRow

variable {σ Λ : Type}

def portBits {q : Nat} (bits : Fin q → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => portBits bits k ++ if h : k < q then bits ⟨k, h⟩ else []

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

open _root_.Turing MachineComposition PCP
abbrev MetaState := MachineRegularMetadata.State Unit

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularLoopWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularLoopWords

def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

end MinUncutGames.Foundations.PCP.PreprocessingRegularLoopWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

open _root_.Turing MachineComposition PCP
open PreprocessingRegularLoopWords

abbrev MetaState := MachineRegularOriginalBody.MetaState

open _root_.Turing MachineComposition PCP
open PreprocessingRegularLoopWords

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PreprocessingMachineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingMachineBounds
open MinUncutGames.Foundations.Complexity
open scoped BigOperators

noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

end MinUncutGames.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP


namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.m, .index, .work, .scratch, .vertices, .darts,
  .emit, .output]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := MachineCloudPrefix.State σ

inductive Field
  | vertices | darts
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.vertices, .darts]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.count, .rEmit, .nEmit]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

end Fuel

namespace Top

def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

inductive CopyPhase
  | old | owner
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.old, .owner]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

end Top
end MinUncutGames.Foundations.Complexity.MachineRegularTable
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PatchDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.OuterSmoothness.Density
lemma tv_ofMap_instances {A B : Type*} (a₁ a₂ : Fintype A) (b₁ b₂ : Fintype B)
    (h₁ h₂ : Nonempty B) (d₁ d₂ : DecidableEq A) (f : B → A) :
    @tvUniform A a₁ (@ofMap A a₁ B b₁ h₁ d₁ f) =
      @tvUniform A a₂ (@ofMap A a₂ B b₂ h₂ d₂ f) := by
  cases Subsingleton.elim a₁ a₂
  cases Subsingleton.elim b₁ b₂
  cases Subsingleton.elim d₁ d₂
  rfl
end MinUncut.OuterSmoothness.Density

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MinUncut.Outer
open OuterSmoothness
attribute [local instance] Classical.propDecidable 

lemma expect_reindex {J K A : Type*} [Fintype J] [Fintype K] [Fintype A] [DecidableEq J] [DecidableEq K]
    (e : J ≃ K) (f : (J → A) → ℝ) :
    (𝔼 L : K → A, f (fun j => L (e j))) = 𝔼 L : J → A, f L := by
  exact Fintype.expect_equiv (Equiv.arrowCongr e.symm (Equiv.refl A)) _ _ (fun _ => rfl)

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IndexedLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable 

def tupleProductEquiv {I A B : Type*} : (I → A × B) ≃ ((I → A) × (I → B)) where
  toFun w := (fun i => (w i).1,fun i => (w i).2)
  invFun z := fun i => (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InputData
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

def counterStacks (old owners dummy work : List Bool) : Fin 4 → List Bool :=
  ![old, owners, dummy, work]

end Top

end MinUncutGames.Foundations.Complexity.MachineRegularTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss

end MinUncutGames.Foundations.PCP.FinalConstants

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

end MinUncutGames.Foundations.PCP.RoundTables

end
section
namespace MinUncutGames.Foundations.PCP.AmplificationIteration

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

def rounds (n : Nat) : Nat := Nat.log2 n + 1

end MinUncutGames.Foundations.PCP.AmplificationIteration

end
section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalBooleanVerifier

variable {V E : Type*} {n m : Nat}

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

end MinUncutGames.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialPredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialRows

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

theorem orderedList_prod {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.prodCongr f).trans finProdFinEquiv) =
      (orderedList e).flatMap (fun a => (orderedList f).map (fun b => (a, b))) := by
  change List.ofFn (fun q : Fin (m * n) =>
    (e.symm (finProdFinEquiv.symm q).1, f.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [orderedList, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val * n + j.val, by
      calc
        i.val * n + j.val < (i.val + 1) * n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem orderedList_sum {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.sumCongr f).trans finSumFinEquiv) =
      (orderedList e).map Sum.inl ++ (orderedList f).map Sum.inr := by
  change List.ofFn (fun q : Fin (m + n) =>
    (e.sumCongr f).symm (finSumFinEquiv.symm q)) = _
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin m =>
    (e.sumCongr f).symm (finSumFinEquiv.symm (i.castAdd n)))) ++
    (List.ofFn (fun i : Fin n =>
      (e.sumCongr f).symm (finSumFinEquiv.symm (i.natAdd m)))) = _
  simp [orderedList, List.map_ofFn]
  rfl

end MinUncutGames.Foundations.PCP.RawInitialRows

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineInitialHeaders

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineInitialHeaders

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineModel

open _root_.Turing Complexity Hastad

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

end MinUncutGames.Foundations.PCP.RawInitialMachineModel

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineStart

open _root_.Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]


end MinUncutGames.Foundations.PCP.RawInitialMachineStart

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineLoopData

open Complexity RawInitialMachineModel

theorem mapIdx_ofFn {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

end MinUncutGames.Foundations.PCP.RawInitialMachineLoopData

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTableComplexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.GraphTableComplexity

open MinUncutGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

end MinUncutGames.Foundations.PCP.GraphTableComplexity

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineBudget

open Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

end MinUncutGames.Foundations.PCP.RawInitialMachineBudget

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RawInitialMachinePhases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialMachineReadClause

open _root_.Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineReadClause

namespace MinUncutGames.Foundations.PCP.RawInitialMachineRows

open _root_.Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineRows

namespace MinUncutGames.Foundations.PCP.RawInitialMachineCleanup

open _root_.Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineCleanup

namespace MinUncutGames.Foundations.PCP.RawInitialMachineBody

open _root_.Turing Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineFinish

open _root_.Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineFinish

end
section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineLoop

open _root_.Turing Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.RawInitialMachineLoop

end
section
namespace MinUncutGames.Foundations.PCP.MachineRawInitialTable

open _root_.Turing Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.PCP.MachineRawInitialTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open _root_.Turing
open PCP.AlphabetTable

noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

open _root_.Turing PCP PCP.AlphabetTable

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFTemplate

open PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

end MinUncutGames.Foundations.Complexity.FinalCNFTemplate

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringFinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalTableFormula

open Complexity

noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

end MinUncutGames.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

open PCP

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MinUncutGames.Foundations.Complexity.FinalCNFCleanup

open _root_.Turing MachineComposition

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

end MinUncutGames.Foundations.Complexity.FinalCNFCleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCanonicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCanonicalOutput

open _root_.Turing MachineComposition

structure Program (K Λ σ : Type) where
  input : K
  output : K
  main : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

def extendedStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ →
      TM2.Stmt (fun _ : K => Bool) Λ' (σ × Option Bool)
  | .push k f next => .push k (fun state => f state.1)
      (extendedStmt labels haltTarget next)
  | .peek k f next => .peek k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .pop k f next => .pop k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .load f next => .load (fun state => (f state.1, state.2))
      (extendedStmt labels haltTarget next)
  | .branch test yes no => .branch (fun state => test state.1)
      (extendedStmt labels haltTarget yes) (extendedStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_extended (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (register : Option Bool) (tapes : K → List Bool) :
    TM2.stepAux (extendedStmt labels haltTarget stmt) (state, register) tapes =
      extendedCfg labels haltTarget register (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Structural

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def sourceMachine (P : Program K Λ σ) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Λ
  main := P.main
  σ := σ
  initialState := P.initial
  m := P.code

end MinUncutGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLogCounter

open _root_.Turing


def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

theorem update_input (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

end MinUncutGames.Foundations.Complexity.MachineLogCounter

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_GraphCounterModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.GraphCounterModel

open _root_.Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance instFintypeExtraLabel : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

open _root_.Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

end MinUncutGames.Foundations.Complexity.GraphCounterModel

namespace MinUncutGames.Foundations.Complexity.GraphCounterFinish

open _root_.Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
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

def mono (x y : Bool) : ℕ := if x=y then 1 else 0

def localCost (equal x y a b c : Bool) : ℕ :=
  mono x a + mono a b + if equal then mono b c+mono c y else mono b y

lemma local_lower (equal x y a b c : Bool) :
    (if (x==y) = equal then 0 else 1) ≤ localCost equal x y a b c := by
  cases equal <;> cases x <;> cases y <;> cases a <;> cases b <;> cases c <;>
    decide

lemma local_extension (equal x y : Bool) :
    localCost equal x y (!x) x (!x) = (if (x==y)=equal then 0 else 1) := by
  cases equal <;> cases x <;> cases y <;> decide

end MinUncut.PathRealization

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphOutput
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

lemma output_opt_le (G : MinUncut.Output) (s : Fin G.vertices → Bool) : G.opt ≤ G.uncut s := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)

lemma le_output_opt (G : MinUncut.Output) (r : ℕ) (h : ∀ s, r ≤ G.uncut s) : r ≤ G.opt := by
  apply Finset.le_min'
  intro x hx
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hx
  exact h s

end MinUncut.PathRealization

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncutGames.Foundations.Hastad.SourceOccurrences

noncomputable def extendAssignment {V W : Type*} (f : V → W) (s : V → Bool) (w : W) : Bool :=
  by
    classical
    exact if h : ∃ v, f v=w then s (Classical.choose h) else false

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*}
  [AddCommGroup V]
  [AddTorsor V A]
  [Fintype A]
variable {m n : ℕ}

lemma weighted_expect_sq {T : Type*} [Fintype T] (w f : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : (𝔼 t, w t)=1) :
    (𝔼 t, w t*f t)^2 ≤ 𝔼 t, w t*(f t)^2 := by
  let M := 𝔼 t, w t*f t
  have hz : 0 ≤ 𝔼 t, w t*(f t-M)^2 :=
    Finset.expect_nonneg (fun t _ => mul_nonneg (hw t) (sq_nonneg _))
  have he (t : T) : w t*(f t-M)^2=w t*(f t)^2-2*M*(w t*f t)+M^2*w t := by ring
  simp_rw [he,Finset.expect_add_distrib,Finset.expect_sub_distrib,← Finset.mul_expect,hw1,mul_one] at hz
  change 0 ≤ (𝔼 t, w t*(f t)^2)-2*M*M+M^2 at hz
  change M^2 ≤ _
  nlinarith only [hz]

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryFormula

open MinUncutGames.Foundations

def clauseNames (c : Clause) : List Nat :=
  [(c)[0].name, (c)[1].name, (c)[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

end MinUncutGames.BinaryFormula

end
section
namespace MinUncutGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

end MinUncutGames.BinaryEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryNameMachine
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

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

end Program

end MinUncutGames.BinaryNameMachine

end
section
namespace MinUncutGames.BinaryNameCompare

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copyOut, .copyBack, .compare]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.BinaryNameCompare

end
section
namespace MinUncutGames.BinaryNameSearch

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def afterMatch : List Token → List Bool → List Token
  | [], _ => []
  | token :: tokens, key => if token.2 = key then tokens else afterMatch tokens key

def steps : List Token → List Bool → Nat
  | [], _ => 0
  | token :: tokens, key =>
      1 + BinaryNameCompare.steps token.2.length key.length +
        if token.2 = key then 0 else 1 + steps tokens key

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A

abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | sign
  | comparison (label : BinaryNameCompare.Label)
  | increment
  deriving DecidableEq, Fintype

def compareTapes (tape : Fin 6 → K) : Fin 5 → K := fun i => tape i.castSucc

omit [DecidableEq K] in
theorem compareTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (compareTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 6 => i.val) (distinct h)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt exit)

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end MinUncutGames.BinaryNameSearch

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryLiteralMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.BinaryLiteralMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State (A × Bool)
abbrev clean (ambient : A) (sign : Bool := false) : State A :=
  BinaryNameCompare.clean (ambient, sign)

inductive Label
  | readSign | scanKey | copyOut | copyBack
  | search (label : BinaryNameSearch.Label)
  | drainSearch | drainKey | emitIndex | emitSign
  deriving DecidableEq, Fintype

def searchTapes (tape : Fin 9 → K) : Fin 6 → K
  | 0 => tape 3
  | 1 => tape 2
  | 2 => tape 4
  | 3 => tape 5
  | 4 => tape 6
  | 5 => tape 7

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [searchTapes] at h
  all_goals first | rfl | have heq := congrArg Fin.val (distinct h); norm_num at heq

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def readSign (tape : Fin 9 → K) (next : Λ) (malformed : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push (tape 7) (fun _ => false)
    (.pop (tape 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.load (fun state => clean state.1.1.1 (state.2.getD false)) (.goto fun _ => next))
        (finish malformed)))

def emitSign (output : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => state.1.1.2)
    (.push output (fun _ => true) (.push output (fun _ => false) (finish exit)))
    (.push output (fun _ => false) (finish exit))

def index (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads tokens).idxOf bits

def steps (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  1 + (bits.length + 1) + 2 * ((BinaryNameSearch.stream tokens).length + 1) +
    BinaryNameSearch.steps tokens bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length + 1) +
    (bits.length + 1) + (index tokens bits + 2) + 1

theorem afterMatch_length_le (tokens : List BinaryNameSearch.Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

theorem steps_le (tokens : List BinaryNameSearch.Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    steps tokens bits ≤
      3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9 := by
  have search := BinaryNameSearch.steps_le_stream tokens bits
  have suffix := afterMatch_length_le tokens bits
  have idx : index tokens bits < tokens.length := by
    have h := List.idxOf_lt_length_iff.mpr present
    simpa [index, BinaryNameSearch.payloads] using h
  have count : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  unfold steps
  nlinarith [Nat.zero_le ((BinaryNameSearch.stream tokens).length * bits.length)]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.BinaryLiteralMachine

namespace MinUncutGames.BinaryRenameLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

abbrev Token := BinaryNameSearch.Token

def nextSlot (slot : Fin 3) : Fin 3 := if slot = 0 then 1 else if slot = 1 then 2 else 0

def clauseIncrement (slot : Fin 3) : Nat := if slot = 2 then 1 else 0

def finalSlot : Nat → Fin 3 → Fin 3
  | 0, slot => slot
  | n + 1, slot => finalSlot n (nextSlot slot)

def completedClauses : Nat → Fin 3 → Nat
  | 0, _ => 0
  | n + 1, slot => completedClauses n (nextSlot slot) + clauseIncrement slot

theorem finalSlot_three (n : Nat) : finalSlot (n + 3) 0 = finalSlot n 0 := by
  simp [finalSlot, nextSlot]

theorem completedClauses_three (n : Nat) :
    completedClauses (n + 3) 0 = completedClauses n 0 + 1 := by
  simp [completedClauses, nextSlot, clauseIncrement]

@[simp] theorem finalSlot_triples (n : Nat) : finalSlot (3 * n) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, finalSlot_three, ih]

@[simp] theorem completedClauses_triples (n : Nat) : completedClauses (3 * n) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, completedClauses_three, ih]

def perLiteralBound (streamLength : Nat) : Nat :=
  12 * streamLength ^ 2 + 26 * streamLength + 11

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryLiteralMachine.State (A × Fin 3)
abbrev clean (ambient : A) (slot : Fin 3) : State A :=
  BinaryLiteralMachine.clean (ambient, slot)

inductive Label
  | entry
  | literal (label : BinaryLiteralMachine.Label)
  | tally
  deriving DecidableEq, Fintype

def literalTapes (tape : Fin 11 → K) : Fin 9 → K := fun i => tape i.castSucc.castSucc

omit [DecidableEq K] in
theorem literalTapes_injective (tape : Fin 11 → K) (distinct : Function.Injective tape) :
    Function.Injective (literalTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 11 => i.val) (distinct h)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 state.1.1.1.2)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def next (again : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 (nextSlot state.1.1.1.2))
    (.goto fun _ => again)

def loopTapes (tape : Fin 11 → K) (base : K → List Bool)
    (cursor output variableCounter clauses : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) cursor) (tape 8) output) (tape 9) variableCounter) (tape 10) clauses

theorem loopTapes_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 0) = cursor := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 9) = variableCounter := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 10) = clauses := by
  simp [loopTapes]

theorem update_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 0) replacement =
      loopTapes tape base replacement output variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_output (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 8) replacement =
      loopTapes tape base cursor replacement variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 8
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 9) replacement =
      loopTapes tape base cursor output replacement clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 9
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 10) replacement =
      loopTapes tape base cursor output variableCounter replacement := by
  simp [loopTapes]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base =
      ⟨exit, clean state.1.1.1.1 state.1.1.1.2, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.BinaryRenameLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryOccurrenceRename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryOccurrenceRename

open BinaryFormula MinUncutGames.Foundations

def nameIndex (F : Formula) (name : Nat) (mem : name ∈ sourceNames F) :
    Fin (sourceNames F).length :=
  ⟨(sourceNames F).idxOf name, List.idxOf_lt_length_of_mem mem⟩

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (sourceNames F).length → Bool :=
  fun i => A (sourceNames F)[i.val]

def extendAssignment (F : Formula) (A : Fin (sourceNames F).length → Bool) : Nat → Bool :=
  fun name => if mem : name ∈ sourceNames F then A (nameIndex F name mem) else false

@[simp] theorem nameIndex_reads_name (F : Formula) (name : Nat)
    (mem : name ∈ sourceNames F) : (sourceNames F)[(nameIndex F name mem).val] = name :=
  List.getElem_idxOf _

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b same
  have decoded := congrArg BinaryEncoding.bitsValue same
  simpa only [BinaryEncoding.bitsValue_bits] using decoded

theorem idxOf_binary_payloads (names : List Nat) (name : Nat) :
    (names.map Nat.bits).idxOf name.bits = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first names ih =>
      by_cases same : first = name
      · subst first
        simp
      · have different : first.bits ≠ name.bits := fun h => same (nat_bits_injective h)
        simp only [List.map_cons, List.idxOf_cons, beq_false_of_ne same,
          beq_false_of_ne different, ih]

end MinUncutGames.BinaryOccurrenceRename

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryParsing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.BinaryParsing

open BinaryEncoding BinaryFormula

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

end MinUncutGames.BinaryParsing

namespace MinUncutGames.BinaryTokenMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open BinaryFormula BinaryEncoding

abbrev Tape := Fin 3
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label where
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3)
  | restore
  | accept
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Label :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

@[simp] theorem afterName_zero : afterName 0 = .sign 1 := rfl
@[simp] theorem afterName_one : afterName 1 = .sign 2 := rfl
@[simp] theorem afterName_two : afterName 2 = .clause := rfl

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def clauseInstruction : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (jump (.sign 0)) (jump .restore)))

def signInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
      (jump .reject))

def nameInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true)
          (.pop 0 (fun state head => (state.1, head))
            (.branch (fun state => state.2.isSome)
              (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
              (jump .reject))))
        (.push 1 (fun _ => false) (jump (afterName slot)))))

def tapes (input reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then reversed else output

@[simp] theorem tapes_zero (input reversed output : List Bool) :
    tapes input reversed output 0 = input := rfl

@[simp] theorem tapes_one (input reversed output : List Bool) :
    tapes input reversed output 1 = reversed := rfl

@[simp] theorem tapes_two (input reversed output : List Bool) :
    tapes input reversed output 2 = output := rfl

theorem update_zero (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 0 replacement =
      tapes replacement reversed output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_one (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 1 replacement =
      tapes input replacement output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.BinaryTokenMachine

namespace MinUncutGames.BinaryHeaderMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem update_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

theorem update_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

theorem update_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Placement

end MinUncutGames.BinaryHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryRenameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryRenameMachine


open _root_.Turing MinUncutGames.Foundations
open Complexity Complexity.MachineComposition

abbrev Tape := Fin 12
abbrev Alphabet (_ : Tape) := Bool
abbrev State := BinaryRenameLoop.State Unit

inductive Label
  | copyOut | copyBack
  | loop (label : BinaryRenameLoop.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop
  | cleanup | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 11 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def tapes (permanent cursor reversed variableCounter clauseCounter output : List Bool) :
    Tape → List Bool := fun k =>
  if k = 0 then cursor
  else if k = 1 then permanent
  else if k = 8 then reversed
  else if k = 9 then variableCounter
  else if k = 10 then clauseCounter
  else if k = 11 then output
  else []

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 35 * Polynomial.X ^ 2 +
    Polynomial.C 28 * Polynomial.X + Polynomial.C 11

end MinUncutGames.BinaryRenameMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PCPIterationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PCPIterationMachine

open _root_.Turing

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

end MinUncutGames.Foundations.Complexity.PCPIterationMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteAverageBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
variable {A : Type*} [Fintype A] [Nonempty A]

lemma expect_abs_difference (f g : A → ℝ) {ε : ℝ} (h : ∀ a, |f a-g a|≤ε) :
    |(𝔼 a,f a)-(𝔼 a,g a)|≤ε := by
  rw [← Finset.expect_sub_distrib]
  exact (OuterSmoothness.Density.abs_expect_le _).trans
    ((Finset.expect_le_expect (fun a _ => h a)).trans_eq (Fintype.expect_const _))

omit [Nonempty A] in
lemma weighted_expect_abs_difference (w f g : A → ℝ) (hw : ∀ a, 0≤w a)
    (hs : (𝔼 a,w a)=1) {ε : ℝ} (h : ∀ a, |f a-g a|≤ε) :
    |(𝔼 a,w a*f a)-(𝔼 a,w a*g a)|≤ε := by
  rw [← Finset.expect_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ 𝔼 a, |w a*(f a-g a)| := OuterSmoothness.Density.abs_expect_le _
    _ ≤ 𝔼 a, w a*ε := Finset.expect_le_expect (fun a _ => by
      rw [abs_mul,abs_of_nonneg (hw a)]
      exact mul_le_mul_of_nonneg_left (h a) (hw a))
    _ = ε := by rw [← Finset.expect_mul,hs,one_mul]
end MinUncut.FiniteGaussian

end
end

end OAI
end


