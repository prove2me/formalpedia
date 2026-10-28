-- Prove2me | Definitions.Def_OAIQ076M006
-- name    : OAIQ076M006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:03:31.033796+00:00
-- url     : https://prove2.me/theorems/6a0cc009-6c03-457d-9c27-172ac1ec8c82
-- title:
--   Definitions bundle OAIQ076M006 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 615 declarations of OpenAI's Lean: 268 definitions, 5 inductive types or structures, 4 instances and 338 theorems. The definitions and types are `OAI.MinUncut.Costed.AExpr.program`, `OAI.MinUncut.Costed.Arena.Action`, `OAI.MinUncut.Costed.Arena.Action.Safe`, `OAI.MinUncut.Costed.Arena.Action.eval`, `OAI.MinUncut.Costed.Arena.Action.program`, `OAI.MinUncut.Costed.Arena.CodeAt`, `OAI.MinUncut.Costed.Arena.Extends`, `OAI.MinUncut.Costed.Arena.Init.base`, `OAI.MinUncut.Costed.Arena.Init.baseLength`, `OAI.MinUncut.Costed.Arena.Init.canvas`, `OAI.MinUncut.Costed.Arena.Init.header`, `OAI.MinUncut.Costed.Arena.Init.input`, `OAI.MinUncut.Costed.Arena.Init.newHeap`, `OAI.MinUncut.Costed.Arena.Init.oldWords`, `OAI.MinUncut.Costed.Arena.ListRep`, `OAI.MinUncut.Costed.Arena.Simulates`, `OAI.MinUncut.Costed.Arena.Small`, `OAI.MinUncut.Costed.Arena.State.tick`, `OAI.MinUncut.Costed.Arena.Trace`, `OAI.MinUncut.Costed.Arena.alloc`, `OAI.MinUncut.Costed.Arena.c`, `OAI.MinUncut.Costed.Arena.dataCells`, `OAI.MinUncut.Costed.Arena.evalAction`, `OAI.MinUncut.Costed.Arena.evalCase`, `OAI.MinUncut.Costed.Arena.evalComp`, `OAI.MinUncut.Costed.Arena.evalCons`, `OAI.MinUncut.Costed.Arena.evalFix`, `OAI.MinUncut.Costed.Arena.evalSucc`, `OAI.MinUncut.Costed.Arena.evalTail`, `OAI.MinUncut.Costed.Arena.evalZero`, `OAI.MinUncut.Costed.Arena.expressionList`, `OAI.MinUncut.Costed.Arena.fresh`, `OAI.MinUncut.Costed.Arena.groupWords`, `OAI.MinUncut.Costed.Arena.halt`, `OAI.MinUncut.Costed.Arena.initialState`, `OAI.MinUncut.Costed.Arena.listCells`, `OAI.MinUncut.Costed.Arena.put`, `OAI.MinUncut.Costed.Arena.rawTick`, `OAI.MinUncut.Costed.Arena.retComp`, `OAI.MinUncut.Costed.Arena.retCons1` and 233 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianDistance`, `MinUncut_Analysis_Gradient`, `MinUncut_Analysis_LowGradient`, `MinUncut_Analysis_OddAtom`, `MinUncut_Analysis_SmoothingRho`, `MinUncut_Encoding_LocalDecoder`, `MinUncut_Encoding_Serialization`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_CodeComputability`, `MinUncut_Estimates_CodeContinuations`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FiberPrefix`, `MinUncut_Estimates_FourthTest`, `MinUncut_Estimates_HeapInitializationMath`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_IterationMagnitude`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_Rest`, `MinUncut_Estimates_ReversePrefixProgram`, `MinUncut_Estimates_RowListBridge`, `MinUncut_Games_JointInner`, `MinUncut_Games_OuterQuestions`, `MinUncut_Graphs_GeneratedGraph`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_AlphabetReduction`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineTupleOdometer`, `MinUncut_Machines_OuterAlphabets`, `MinUncut_Machines_Relations`, `MinUncut_Machines_Runtime`, `MinUncut_Machines_RuntimeModel`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ContextClear`, `MinUncut_PCP_ContextLoad`, `MinUncut_PCP_ContextPrepare`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_DescriptorEmission`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_Folding`, `MinUncut_PCP_Game`, `MinUncut_PCP_Gap`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_HeaderCounts`, `MinUncut_PCP_InitialGraph`, `MinUncut_PCP_LoopOrder`, `MinUncut_PCP_Occurrences`, `MinUncut_PCP_Overlay`, `MinUncut_PCP_PoweringOpinionTables`, `MinUncut_PCP_PoweringReturn`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_ProfileBridge`, `MinUncut_PCP_RawInitialPredicate`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_TupleBody`, `MinUncut_PCP_TupleBound`, `MinUncut_PCP_Walsh`, `MinUncut_Search_ArithmeticExpression`, `MinUncut_Search_BlockEnumeration`, `MinUncut_Search_PolynomialArithmetic`.
--
--   **Imports.** It imports the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002` and `OAIQ076M003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M016`, `OAIQ076M017`, `OAIQ076M018`, `OAIQ076M019`, `OAIQ076M020` and `OAIQ076M021`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite

variable {ι : Type*} [Fintype ι]

lemma measurable_score (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (i : ι) :
    Measurable (score ρ s Q i) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact (by fun_prop : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
    z.2 i * Q (ρ • z.1+s • z.2))).stronglyMeasurable

lemma score_bound (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) (x : ι → ℝ) :
    |score ρ s Q i x| ≤ ∫ g, |g i| ∂γpi ι := by
  have hi : Integrable (fun g : ι → ℝ => g i * Q (ρ • x+s • g)) (γpi ι) :=
    (coordinate_integrable i).mul_bdd (hQ.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  calc
    _ ≤ ∫ g, |g i * Q (ρ • x+s • g)| ∂γpi ι := by
      simpa only [score, Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun g : ι → ℝ => g i * Q (ρ • x+s • g))
    _ ≤ _ := integral_mono_ae hi.abs (coordinate_integrable i).abs <|
      ae_of_all _ fun g => by
        change |g i * Q (ρ • x+s • g)| ≤ |g i|
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

lemma memLp_score (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) : MemLp (score ρ s Q i) 2 (γpi ι) :=
  MemLp.of_bound (measurable_score ρ s hQ i).aestronglyMeasurable _
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using score_bound ρ s hQ hb i x)

end MinUncut.GaussianHermite
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_Gradient
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι]

def gradient (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  (ρ/s)*score ρ s Q i x

lemma memLp_gradient (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) : MemLp (gradient ρ s Q i) 2 (γpi ι) :=
  (memLp_score ρ s hQ hb i).const_mul (ρ/s)

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
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

namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {m n : ℕ}

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

instance gauss_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gauss ι) := by
  unfold gauss
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable [Fintype A]

lemma measurable_query (z : Code m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 p.2 z) := by
  apply measurable_to_bool
  have heq : (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 p.2 z) ⁻¹'
      {true} = {p | 0 ≤ (Real.sqrt (n^m : ℕ))⁻¹ *
        (∑ x : Point m n, p.1 x * BinaryFourier.sign (z.val x)) + p.2 z} := by
    ext p; simp [query]
  rw [heq]
  apply measurableSet_le measurable_const
  fun_prop

omit [Fintype A] in
lemma measurable_pullQuery (B : FaceArray A m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => pullQuery B p.1 p.2) := by
  apply Measurable.of_eval
  intro a
  exact measurable_query (labelCode B a)

lemma measurable_answer (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      bitSign (f.answer (pullQuery B p.1 (η • p.2)))) := by
  exact (measurable_of_finite bitSign).comp ((measurable_of_finite f.answer).comp
    ((measurable_pullQuery B).comp (by fun_prop : Measurable
      (fun pair : (Point m n → ℝ) × (Code m n → ℝ) => (pair.1, η • pair.2)))))

noncomputable def tableSmooth (f : FoldedProof A) (B : FaceArray A m n)
    (η : ℝ) (u : Point m n → ℝ) : ℝ :=
  ∫ l : Code m n → ℝ, bitSign (f.answer (pullQuery B u (η • l))) ∂gauss (Code m n)

lemma measurable_tableSmooth (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) :
    Measurable (tableSmooth f B η) := by
  exact ((measurable_answer f B η).stronglyMeasurable.integral_prod_right).measurable

omit [Fintype A] in
lemma tableSmooth_abs_le (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) : |tableSmooth f B η u| ≤ 1 := by
  simpa [tableSmooth, ← Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := gauss (Code m n))
      (ae_of_all _ fun l => (by simp only [Real.norm_eq_abs, bitSign_abs, le_refl] :
        ‖bitSign (f.answer (pullQuery B u (η • l)))‖ ≤ 1)))

lemma smooth_coordinate_derivative (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    HasDerivAt (fun t => smooth f B σ η (Function.update c x t))
      (σ⁻¹ * ∫ g : Point m n → ℝ, g x * tableSmooth f B η (c + σ • g)
        ∂gauss (Point m n)) (c x) := by
  exact GaussianSmoothing.product_convolution_derivative
    (measurable_tableSmooth f B η) (tableSmooth_abs_le f B η) hσ c x

noncomputable def spatialEnergy (v : Point m n → ℝ) : ℝ :=
  ((n^m : ℕ) : ℝ)⁻¹ * ∑ x : Point m n, v x ^ 2

lemma gradient_score (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) / σ *
      ∫ g : Point m n → ℝ, g x * tableSmooth f B η (c + σ • g) ∂gauss (Point m n) := by
  rw [gradient, (smooth_coordinate_derivative f B hσ η c x).deriv]
  ring

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Convolution
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def convolutionGradient (σ : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  σ⁻¹ * ∫ g, g i * Q (x + σ • g) ∂γpi ι

omit [DecidableEq ι] in
lemma convolutionGradient_as_noise {ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (Q : (ι → ℝ) → ℝ) (i : ι) :
    convolutionGradient σ Q i = gradient ρ (σ*ρ) (fun v => Q (ρ⁻¹ • v)) i := by
  funext x
  unfold convolutionGradient gradient score
  have hc : ρ/(σ*ρ) = σ⁻¹ := by field_simp
  rw [hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  ext j
  dsimp
  field_simp

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SmoothingRho
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma convolutionGradient_memLp {σ : ℝ} (hσ : σ ≠ 0) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (i : ι) :
    MemLp (convolutionGradient σ Q i) 2 (γpi ι) := by
  rw [convolutionGradient_as_noise (ρ := 1) one_ne_zero hσ]
  exact memLp_gradient 1 (σ*1) (hQ.comp (by fun_prop)) (fun x => hb _) i

end MinUncut.GaussianHermite

namespace MinUncut.Inner
open GaussianHermite
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [Fintype A] {m n : ℕ}

lemma gradient_as_convolutionGradient (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) *
      convolutionGradient σ (tableSmooth f B η) x c := by
  rw [gradient_score f B hσ]
  unfold GaussianHermite.convolutionGradient
  simp only [div_eq_mul_inv, mul_assoc]
  rfl

lemma gradient_memLp (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) :
    MemLp (fun c => gradient f B σ η c x) 2 (gauss (Point m n)) := by
  simp_rw [gradient_as_convolutionGradient f B hσ]
  exact (convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
    (tableSmooth_abs_le f B η) x).const_mul _

end MinUncut.Inner

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace

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
abbrev Triple := Fin 3 → F₂

end JointForms
end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Rest
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma expect_splitRow (r : R) (f : (R → W) → ℝ) :
    (𝔼 B, f B) = 𝔼 b, 𝔼 D, f (joinRow r b D) := by
  calc
    _ = 𝔼 p : W × Rest (W := W) r, f (joinRow r p.1 p.2) :=
      Fintype.expect_equiv (Equiv.funSplitAt r W) _ _ (fun B => congrArg f ((Equiv.funSplitAt r W).symm_apply_apply B).symm)
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_OddAtom
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

attribute [local instance] OAI.MinUncut.RowNoise.oddAtomDualFintype
omit [Fintype R] [DecidableEq W] in
lemma rowCoefficient_le_oddAtom (r : R) (one : W) (f : (R → W) → ℝ)
    (α : Module.Dual F₂ W) (hα : α one=1) (D : Rest (W := W) r) :
    |rowCoefficient r f α D| ≤ oddAtom r one f D := by
  have h := Finset.le_sup' (fun β : Module.Dual F₂ W =>
    if β one=1 then |rowCoefficient r f β D| else 0) (Finset.mem_univ α)
  rw [ite_eq_left hα] at h
  exact h

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointInner
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def jointEnergy (u : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, (u B c)^2 ∂γpi ι

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LowGradient
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
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def averagedEnergy (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ) : ℝ :=
  𝔼 B, ∫ c, spatialEnergy (u B c) ∂gauss (Point m n)

lemma averagedEnergy_eq_jointEnergy
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (hu : ∀ B x, MemLp (fun c => u B c x) 2 (gauss (Point m n))) :
    averagedEnergy u = ((n^m:ℕ):ℝ)⁻¹*∑ x, jointEnergy (fun B c => u B c x) := by
  simp only [averagedEnergy,spatialEnergy,integral_const_mul,
    integral_finsetSum _ (fun x _ => (hu _ x).integrable_sq),
    ← Finset.mul_expect,Finset.expect_sum_comm,jointEnergy]
  rfl

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_LocalDecoder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]

lemma labelList_card (f : Forms A → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0<u)
    (hf : ∀ a, |f a| ≤ M) : ((labelList f u).card : ℝ) ≤ M^2/u^2 := by
  have hsub : (labelList f u).image labelFrequency ⊆ largeSpectrum f u := by
    intro α hα
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hα
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_labelList f u a).mp ha⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ labelFrequency_injective] at hcard
  exact (Nat.cast_le.mpr hcard).trans (largeSpectrum_card f hM hu hf)

end MinUncut.Composition

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FourthTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

omit [Fintype A] [Fintype A'] in
lemma pullbackFaces_joinRow (π : A →ᵃ[F₂] A') (r : Row m n) (b : Forms A')
    (D : Rest (W := Forms A') r) :
    pullbackFaces π (joinRow r b D) =
      joinRow r (formPullback π b) (fun t => formPullback π (D t)) := by
  funext t
  by_cases ht : t=r
  · subst t
    simp [pullbackFaces]
  · simp only [pullbackFaces, joinRow_other r b D ⟨t,ht⟩,
      joinRow_other r (formPullback π b) (fun s => formPullback π (D s)) ⟨t,ht⟩]

def comparisonRow (f : FoldedProof A) (σ η : ℝ) (c : Point m n → ℝ)
    (x : Point m n) (r : Row m n) (D : Rest (W := Forms A) r) (b : Forms A) : ℝ :=
  gradient f (joinRow r b D) σ η c x

omit [Fintype A] [Fintype A'] in
lemma comparisonRow_pullback (π : A →ᵃ[F₂] A') (f : FoldedProof A)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (D : Rest (W := Forms A') r) (b : Forms A') :
    comparisonRow f σ η c x r (fun t => formPullback π (D t)) (formPullback π b) =
      gradient f (pullbackFaces π (joinRow r b D)) σ η c x := by
  rw [pullbackFaces_joinRow]
  rfl

omit [Fintype A] in
lemma comparisonRow_average (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms A') r, 𝔼 b : Forms A',
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)) (formPullback π b) -
        comparisonRow g σ η c x r D b)^2) =
    𝔼 C : FaceArray A' m n,
      (gradient f (pullbackFaces π C) σ η c x-gradient g C σ η c x)^2 := by
  simp_rw [comparisonRow_pullback]
  rw [Finset.expect_comm, expect_splitRow r]
  rfl

end MinUncut.Inner

open scoped BigOperators

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
abbrev Triple := Fin 3 → F₂

structure Equation (Name : Type*) where
  names : Fin 3 → Name
  rhs : F₂
  deriving DecidableEq

variable {Name : Type*}

def parity : Triple →ₗ[F₂] F₂ where
  toFun a := a 0+a 1+a 2
  map_add' a b := by simp only [Pi.add_apply]; ring
  map_smul' c a := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

@[simp] lemma parity_apply (a : Triple) : parity a = a 0+a 1+a 2 := rfl

def Valid (E : Equation Name) (a : Triple) : Prop :=
  parity a = E.rhs ∧ ∀ p p', E.names p=E.names p' → a p=a p'

def alphabet (E : Equation Name) : AffineSubspace F₂ Triple where
  carrier := {a | Valid E a}
  smul_vsub_vadd_mem' c a b d ha hb hd := by
    change parity (c • (a-b)+d)=E.rhs ∧ _
    constructor
    · rw [map_add,map_smul,map_sub,ha.1,hb.1,hd.1,sub_self,smul_zero,zero_add]
    · intro p p' he
      change c*(a p-b p)+d p=c*(a p'-b p')+d p'
      rw [ha.2 p p' he,hb.2 p p' he,hd.2 p p' he]

@[simp] lemma mem_alphabet (E : Equation Name) (a : Triple) :
    a ∈ alphabet E ↔ Valid E a := Iff.rfl

def origin (E : Equation Name) : alphabet E :=
  ⟨fun _ => E.rhs, ⟨by simp only [parity_apply,CharTwo.add_self_eq_zero,zero_add],
    fun _ _ _ => rfl⟩⟩

instance alphabetNonempty (E : Equation Name) : Nonempty (alphabet E) := ⟨origin E⟩

def coordinates (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) ≃ₗ[F₂] (alphabet E).direction :=
  (Module.finBasis F₂ (alphabet E).direction).equivFun.symm

def directionEmbedding (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) →ₗ[F₂] Triple :=
  (alphabet E).direction.subtype.comp (coordinates E).toLinearMap

def alphabetCoordinates (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) ≃ᵃ[F₂] alphabet E :=
  (coordinates E).toAffineEquiv.trans (AffineEquiv.vaddConst F₂ (origin E))

@[simp] lemma alphabetCoordinates_val (E : Equation Name)
    (v : Fin (Module.finrank F₂ (alphabet E).direction) → F₂) :
    ((alphabetCoordinates E v : alphabet E) : Triple) =
      directionEmbedding E v + (origin E : Triple) := rfl

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

abbrev SecondQuestion (Name : Type*) := Name ⊕ Equation Name

def secondSlotCount : SecondQuestion Name → ℕ
  | .inl _ => 1
  | .inr _ => 3
abbrev secondSlot (v : SecondQuestion Name) := Fin (secondSlotCount v) → F₂

abbrev FirstAlphabet (U : I → Equation Name) := ∀ j, alphabet (U j)
abbrev SecondAlphabet (V : I → SecondQuestion Name) := ∀ j, secondSlot (V j)

def slotQuestion (E : Equation Name) (hidden : Bool) (p : Fin 3) : SecondQuestion Name :=
  if hidden then .inl (E.names p) else .inr E

def slotProjection (E : Equation Name) (hidden : Bool) (p : Fin 3) :
    alphabet E →ᵃ[F₂] secondSlot (slotQuestion E hidden p) := by
  cases hidden
  · exact (alphabet E).subtype
  · exact (LinearMap.pi (fun _ : Fin 1 => (LinearMap.proj p : Triple →ₗ[F₂] F₂))).toAffineMap.comp (alphabet E).subtype

def secondQuestion (U : I → Equation Name) (hidden : I → Bool) (position : I → Fin 3) :
    I → SecondQuestion Name := fun j => slotQuestion (U j) (hidden j) (position j)

def projection (U : I → Equation Name) (hidden : I → Bool) (position : I → Fin 3) :
    FirstAlphabet U →ᵃ[F₂] SecondAlphabet (secondQuestion U hidden position) :=
  AffineMap.pi (fun j => (slotProjection (U j) (hidden j) (position j)).comp (AffineMap.proj j))

@[simp] lemma projection_apply (U : I → Equation Name) (hidden : I → Bool)
    (position : I → Fin 3) (a : FirstAlphabet U) (j : I) :
    projection U hidden position a j=slotProjection (U j) (hidden j) (position j) (a j) := rfl

open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

def slotFunctional (v : SecondQuestion Name) (β : F₂) (l : Module.Dual F₂ Triple) :
    Module.Dual F₂ (secondSlot v) := by
  cases v with
  | inl x => exact β • (LinearMap.proj (0 : Fin 1))
  | inr E => exact l

def directLinear (V : I → SecondQuestion Name) (β : I → F₂)
    (l : I → Module.Dual F₂ Triple) : Module.Dual F₂ (SecondAlphabet V) :=
  ∑ j, (slotFunctional (V j) (β j) (l j)).comp (LinearMap.proj j)

def directHint (V : I → SecondQuestion Name) (κ : F₂) (β : I → F₂)
    (l : I → Module.Dual F₂ Triple) : Forms (SecondAlphabet V) :=
  (directLinear V β l).toAffineMap + AffineMap.const F₂ _ κ

@[simp] lemma directHint_apply (V : I → SecondQuestion Name) (κ : F₂) (β : I → F₂)
    (l : I → Module.Dual F₂ Triple) (a : SecondAlphabet V) :
    directHint V κ β l a = (∑ j, slotFunctional (V j) (β j) (l j) (a j))+κ := by
  simp [directHint,directLinear]

attribute [local instance] BinaryFourier.dualFintype

end MinUncut.Outer

end

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

abbrev CoordinateSlot (E : Equation Name) := Fin (Module.finrank F₂ (alphabet E).direction) → F₂
abbrev FirstCoordinateSpace (U : I → Equation Name) := ∀ i, CoordinateSlot (U i)

def firstCoordinates (U : I → Equation Name) :
    FirstCoordinateSpace U ≃ᵃ[F₂] FirstAlphabet U :=
  (LinearEquiv.piCongrRight (fun i => coordinates (U i))).toAffineEquiv.trans
    (AffineEquiv.vaddConst F₂ (fun i => origin (U i)))

omit [Fintype I] in
@[simp] lemma firstCoordinates_apply (U : I → Equation Name)
    (v : FirstCoordinateSpace U) (i : I) :
    (firstCoordinates U v i).val = directionEmbedding (U i) (v i) + (origin (U i)).val := rfl

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma averagedEnergy_eq_expect_joint
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (hu : ∀ B x, MemLp (fun c => u B c x) 2 (γpi (Point m n))) :
    averagedEnergy u = 𝔼 x, jointEnergy (fun B c => u B c x) := by
  rw [averagedEnergy_eq_jointEnergy u hu]
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Point, Fintype.card_fin]
  ring

end MinUncut.Inner

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_RowListBridge
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner RowNoise
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

attribute [local irreducible] MinUncut.Inner.gradient

lemma oddAtom_iff_labelList {R : Type*} [Fintype R] [DecidableEq R]
    (r : R) (F : (R → Forms A) → ℝ) (D : Rest (W := Forms A) r)
    {θ : ℝ} (hθ : 0<θ) :
    θ≤oddAtom r (AffineMap.const F₂ A 1) F D ↔
      (labelList (fun b => F (joinRow r b D)) θ).Nonempty := by
  constructor
  · intro h
    have he : ∃ α : Module.Dual F₂ (Forms A),
        oddAtom r (AffineMap.const F₂ A 1) F D =
          if α (AffineMap.const F₂ A 1)=1 then |rowCoefficient r F α D| else 0 := by
      obtain ⟨α,_,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
        (fun α : Module.Dual F₂ (Forms A) =>
          if α (AffineMap.const F₂ A 1)=1 then |rowCoefficient r F α D| else 0)
      exact ⟨α,he⟩
    obtain ⟨α,he⟩ := he
    rw [he] at h
    split_ifs at h with ho
    · obtain ⟨a,rfl⟩ := oddFrequency_exists_label α ho
      exact ⟨a, (mem_labelList _ θ a).mpr h⟩
    · linarith
  · rintro ⟨a,ha⟩
    exact ((mem_labelList _ θ a).mp ha).trans
      (rowCoefficient_le_oddAtom r (AffineMap.const F₂ A 1)
        F (labelFrequency a) (labelFrequency_odd a) D)

lemma rowAtom_iff_list (f : FoldedProof A) (σ η : ℝ) {θ : ℝ} (hθ : 0<θ)
    (x : Point m n) (i : Fin m)
    (D : Rest (W := Forms A) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) :
    θ ≤ rowAtom f σ η x i D c ↔
      (labelList (comparisonRow f σ η c x ⟨i,face x i⟩ D) θ).Nonempty :=
  oddAtom_iff_labelList (⟨i,face x i⟩ : Row m n) (fun B => gradient f B σ η c x) D hθ

lemma rowAtomIndicator_eq_list (f : FoldedProof A) (σ η : ℝ) {θ : ℝ} (hθ : 0<θ)
    (x : Point m n) (i : Fin m)
    (D : Rest (W := Forms A) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) :
    rowAtomIndicator f σ η θ x i D c =
      if (labelList (comparisonRow f σ η c x ⟨i,face x i⟩ D) θ).Nonempty then 1 else 0 := by
  simp only [rowAtomIndicator,rowAtom_iff_list f σ η hθ]

end MinUncut.Composition

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDistance
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open MinUncut.Inner RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B] {m n : ℕ}

lemma comparisonRow_distance_integrable (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n)
    (D : Rest (W := Forms B) r) :
    Integrable (fun c => rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D)) (gauss (Point m n)) := by
  apply integrable_expect
  intro z
  exact ((gradient_memLp g _ hσ η x).sub (gradient_memLp f _ hσ η x)).integrable_sq

omit [Fintype A] in
lemma comparisonRow_distance_mean (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms B) r, rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D)) =
    𝔼 C : FaceArray B m n,
      (MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-MinUncut.Inner.gradient g C σ η c x)^2 := by
  simpa only [rowDistance,sub_sq_comm] using comparisonRow_average π f g σ η c x r

lemma comparisonRow_distance_integral (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms B) r, ∫ c, rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D) ∂gauss (Point m n)) =
    jointEnergy (fun C c => MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-
      MinUncut.Inner.gradient g C σ η c x) := by
  rw [← integral_expect _ (fun D => comparisonRow_distance_integrable π f g hσ η x r D)]
  simp_rw [comparisonRow_distance_mean]
  exact integral_expect _ (fun C => ((gradient_memLp f _ hσ η x).sub
    (gradient_memLp g C hσ η x)).integrable_sq)

lemma comparisonRow_distance_total (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    (hm : 0 < m) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,
      𝔼 D : Rest (W := Forms B) (⟨i,face x i⟩ : Row m n), ∫ c, rowDistance π
        (comparisonRow f σ η c x ⟨i,face x i⟩ (fun t => formPullback π (D t)))
        (comparisonRow g σ η c x ⟨i,face x i⟩ D) ∂gauss (Point m n)) =
      averagedEnergy (m := m) (n := n) (fun C c x => MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-
        MinUncut.Inner.gradient g C σ η c x) := by
  let : NeZero m := ⟨hm.ne'⟩
  simp_rw [comparisonRow_distance_integral π f g hσ,Fintype.expect_const]
  exact (averagedEnergy_eq_expect_joint _ (fun C x => (gradient_memLp f _ hσ η x).sub
    (gradient_memLp g C hσ η x))).symm
end MinUncut.Composition

open scoped BigOperators

end

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

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

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

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

end MinUncutGames.Foundations.Hastad

end

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
namespace MinUncutGames.Reduction.SourceEncoding

open MinUncutGames.Foundations.Complexity

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

end MinUncutGames.Reduction.SourceEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeComputability
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

namespace PolyProgram
variable {f g : List ℕ → List ℕ}

open Turing.ToPartrec Polynomial

variable {f g e : List ℕ → List ℕ}

def branch (E : PolyProgram e) (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>if (e v).headI=0 then f v else g v) where
  code := .comp (.case F.code (.comp G.code .tail)) (.cons E.code .id)
  bound := E.bound+F.bound+G.bound+C 300*(X+E.bound+1)+1
  run v := by
    have hp := run_cons (E.run v) (run_id v)
    have hs := (magnitude_head (e v)).trans (E.size v)
    by_cases he : (e v).headI=0
    · simp only [ite_eq_left he]
      have hb := run_caseZero (g:=.comp G.code .tail) (v := (e v).headI::v) (by simpa using he) (F.run v)
      have hh := run_comp hp hb
      apply hh.mono
      simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,magnitude_cons]
      have hh := E.size v
      omega
    · simp only [ite_eq_right he]
      obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero he
      have hb := run_caseSucc (f:=F.code) (run_comp (run_tail (a::v)) (G.run v))
      change Runs _ ((a+1)::v) _ _ at hb
      rw [← show (e v).headI=a+1 from ha] at hb
      have hh := run_comp hp hb
      apply hh.mono
      have heq : (e v).headI=a+1 := ha
      simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,magnitude_cons]
      have hh := E.size v
      omega
  size v := by
    have hf := F.size v
    have hg := G.size v
    split_ifs <;> simp only [eval_add,eval_mul,eval_C,eval_X,eval_one] <;> omega

end PolyProgram
end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_PolynomialArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def eqOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[if (f v).headI=(g v).headI then 1 else 0]) :=
  (branch (addOf (subOf F G) (subOf G F)) (const 1) (const 0)).ofEq (by
    intro v
    simp only [List.headI_cons]
    have h : (f v).headI-(g v).headI+((g v).headI-(f v).headI)=0 ↔
        (f v).headI=(g v).headI := by omega
    simp only [h]
    split_ifs <;> rfl)

def leOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[if (f v).headI≤(g v).headI then 1 else 0]) :=
  (branch (subOf F G) (const 1) (const 0)).ofEq (by
    intro v
    simp only [List.headI_cons,Nat.sub_eq_zero_iff_le]
    split_ifs <;> rfl)

end MinUncut.Costed.PolyProgram

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed

noncomputable def Expr.program : (e : Expr) → PolyProgram (fun v=>[e.eval v])
  | .const n => PolyProgram.const n
  | .reg i => PolyProgram.projection i
  | .add a b => PolyProgram.addOf a.program b.program
  | .sub a b => PolyProgram.subOf a.program b.program
  | .mul a b => PolyProgram.mulOf a.program b.program
  | .eq a b => PolyProgram.eqOf a.program b.program
  | .le a b => PolyProgram.leOf a.program b.program
  | .at a => PolyProgram.dynamic.comp (a.program.cons PolyProgram.id)
  | .cond e a b => (PolyProgram.branch e.program a.program b.program).ofEq (by
      intro v
      change (if e.eval v=0 then [a.eval v] else [b.eval v])=
        [if e.eval v=0 then a.eval v else b.eval v]
      by_cases h : e.eval v=0 <;> simp only [h,ite_true,ite_false])

end MinUncut.Costed

namespace MinUncut.Costed.Arena

lemma words_drop (h : Heap) (i : ℕ) :
    (words h).drop (4*i)=words (h.drop i) := by
  induction i generalizing h with
  | zero => simp
  | succ i ih =>
    cases h with
    | nil => simp
    | cons n h =>
      rw [words_cons,show 4*(i+1)=4+4*i by omega,← List.drop_drop]
      simpa using ih h

lemma words_at (h : Heap) (i : ℕ) (j : Fin 4) :
    ((words h).drop (4*i+j.val)).headI=((h.drop i).headD (fun _=>0)) j := by
  rw [← List.drop_drop,words_drop]
  cases h.drop i with
  | nil => simp
  | cons n hs =>
    rw [words_cons]
    fin_cases j <;> rfl

lemma read_words (h : Heap) (a : ℕ) (j : Fin 4) :
    read h a j=if a=0 then 0 else ((words h).drop (4*(h.length-a)+j.val)).headI := by
  simp only [read,words_at]

lemma read_old (h : Heap) (n : Node) (a : ℕ) (ha : a≤h.length) (j : Fin 4) :
    read (n::h) a j=read h a j := by
  by_cases hz : a=0
  · simp [hz]
  · simp only [read,hz,ite_false,List.length_cons]
    rw [show h.length+1-a=(h.length-a)+1 by omega]
    rfl

lemma readExpr_eval (regs : List ℕ) (len : ℕ) (h : Heap) (addr : Expr) (field : Fin 4)
    (hlen : ((regs++words h).drop len).headI=h.length) :
    (readExpr regs.length len addr field).eval (regs++words h)=
      read h (addr.eval (regs++words h)) field := by
  rw [read_words]
  simp only [readExpr,Expr.eval,hlen]
  by_cases he : addr.eval (regs++words h)=0
  · simp [he]
  · simp only [he,ite_false,ite_true]
    rw [show regs.length+field.val+4*(h.length-addr.eval (regs++words h))=
        regs.length+(4*(h.length-addr.eval (regs++words h))+field.val) by omega]
    simp only [← List.drop_drop, List.drop_left]

open Turing.ToPartrec

inductive ListRep (h : Heap) : ℕ → List ℕ → Prop
  | nil : ListRep h 0 []
  | cons {p a q v} : 0<p → p≤h.length → read h p 0=a → read h p 1=q →
      ListRep h q v → ListRep h p (a::v)

lemma ListRep.head {h p v} (hv : ListRep h p v) : read h p 0=v.headI := by
  cases hv with
  | nil => simp
  | cons _ _ he => exact he

lemma ListRep.tail {h p v} (hv : ListRep h p v) : ListRep h (read h p 1) v.tail := by
  cases hv with
  | nil => simpa using ListRep.nil (h:=h)
  | cons _ _ _ he ht => simpa only [he,List.tail_cons] using ht

lemma ListRep.extend {h p v} (hv : ListRep h p v) (n : Node) : ListRep (n::h) p v := by
  induction hv with
  | nil => exact .nil
  | cons hpos hp ha hq hv ih =>
    exact .cons hpos (by simp only [List.length_cons]; omega)
      ((read_old h n _ hp 0).trans ha) ((read_old h n _ hp 1).trans hq) ih

lemma ListRep.push {h p v} (hv : ListRep h p v) (a : ℕ) :
    ListRep (node a p 0 0::h) (h.length+1) (a::v) := by
  refine .cons (by omega) (by simp) ?_ ?_ (hv.extend _)
  · simp [node]
  · simp [node]

inductive CodeAt (h : Heap) : ℕ → Code → Prop
  | zero {p} : 0<p → p≤h.length → read h p 0=0 → CodeAt h p .zero'
  | succ {p} : 0<p → p≤h.length → read h p 0=1 → CodeAt h p .succ
  | tail {p} : 0<p → p≤h.length → read h p 0=2 → CodeAt h p .tail
  | cons {p f fs} : 0<p → p≤h.length → read h p 0=3 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) fs → CodeAt h p (.cons f fs)
  | comp {p f g} : 0<p → p≤h.length → read h p 0=4 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) g → CodeAt h p (.comp f g)
  | case {p f g} : 0<p → p≤h.length → read h p 0=5 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) g → CodeAt h p (.case f g)
  | fix {p f} : 0<p → p≤h.length → read h p 0=6 →
      CodeAt h (read h p 1) f → CodeAt h p (.fix f)

lemma CodeAt.extend {h p c} (hc : CodeAt h p c) (n : Node) : CodeAt (n::h) p c := by
  induction hc with
  | zero hpos hp ht => exact .zero hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | succ hpos hp ht => exact .succ hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | tail hpos hp ht => exact .tail hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | cons hpos hp ht _ _ ih ih' =>
    exact .cons hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | comp hpos hp ht _ _ ih ih' =>
    exact .comp hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | case hpos hp ht _ _ ih ih' =>
    exact .case hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | fix hpos hp ht _ ih =>
    exact .fix hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)

lemma ListRep.prepend {h p v} (hv : ListRep h p v) (hs : Heap) : ListRep (hs++h) p v := by
  induction hs with
  | nil => exact hv
  | cons n hs ih => exact ih.extend n

lemma CodeAt.prepend {h p c} (hc : CodeAt h p c) (hs : Heap) : CodeAt (hs++h) p c := by
  induction hs with
  | nil => exact hc
  | cons n hs ih => exact ih.extend n

lemma codeCells_spec (c : Code) (h : Heap) :
    CodeAt (codeCells c h.length++h) (h.length+(codeCells c h.length).length) c := by
  induction c generalizing h with
  | zero' => simpa [codeCells,node] using
      (CodeAt.zero (h := node 0 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | succ => simpa [codeCells,node] using
      (CodeAt.succ (h := node 1 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | tail => simpa [codeCells,node] using
      (CodeAt.tail (h := node 2 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | cons f g ih ih' =>
    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 3 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.cons f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .cons (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 3 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 3 (h.length+l.length) (h.length+l.length+r.length) 0)
  | comp f g ih ih' =>

    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 4 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.comp f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .comp (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 4 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 4 (h.length+l.length) (h.length+l.length+r.length) 0)
  | case f g ih ih' =>
    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 5 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.case f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .case (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 5 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 5 (h.length+l.length) (h.length+l.length+r.length) 0)
  | fix f ih =>
    simp only [codeCells,List.cons_append,List.length_cons]
    let l := codeCells f h.length
    change CodeAt (node 6 (h.length+l.length) 0 0::(l++h)) (h.length+(l.length+1)) (.fix f)
    rw [show h.length+(l.length+1)=(l++h).length+1 by simp; omega]
    refine .fix (by omega) (by simp) (by rw [read_new]; rfl) ?_
    simpa only [read_new,node_one] using (ih h).extend (node 6 (h.length+l.length) 0 0)

def State.tick (s : State) : State :=
  let h := s.heap
  let n := h.length
  let get := read h
  if s.mode=0 then
    match get s.pc 0 with
    | 0 => ⟨1,0,n+1,s.kont,node 0 s.env 0 0::h⟩
    | 1 => ⟨1,0,n+1,s.kont,node (get s.env 0+1) 0 0 0::h⟩
    | 2 => ⟨1,0,get s.env 1,s.kont,h⟩
    | 3 => ⟨0,get s.pc 1,s.env,n+1,node 0 (get s.pc 2) s.env s.kont::h⟩
    | 4 => ⟨0,get s.pc 2,s.env,n+1,node 2 (get s.pc 1) 0 s.kont::h⟩
    | 5 => if get s.env 0=0 then ⟨0,get s.pc 1,get s.env 1,s.kont,h⟩
        else ⟨0,get s.pc 2,n+1,s.kont,node (get s.env 0-1) (get s.env 1) 0 0::h⟩
    | 6 => ⟨0,get s.pc 1,s.env,n+1,node 3 s.pc 0 s.kont::h⟩
    | _ => ⟨2,0,s.env,0,h⟩
  else if s.mode=1 then
    if s.kont=0 then ⟨2,0,s.env,0,h⟩
    else match get s.kont 0 with
      | 0 => ⟨0,get s.kont 1,get s.kont 2,n+1,
          node 1 (get s.env 0) 0 (get s.kont 3)::h⟩
      | 1 => ⟨1,0,n+1,get s.kont 3,node (get s.kont 1) s.env 0 0::h⟩
      | 2 => ⟨0,get s.kont 1,s.env,get s.kont 3,h⟩
      | 3 => if get s.env 0=0 then ⟨1,0,get s.env 1,get s.kont 3,h⟩
          else ⟨0,get s.kont 1,get s.env 1,get s.kont 3,h⟩
      | _ => ⟨2,0,s.env,0,h⟩
  else s

inductive Action where
  | put (regs : List Expr)
  | test (e : Expr) (yes no : Action)

def Action.eval : Action → List ℕ → List ℕ
  | .put es,v => es.map (fun e=>e.eval v)++v.drop 5
  | .test e yes no,v => if e.eval v=0 then yes.eval v else no.eval v

noncomputable def expressionList (es : List Expr) :
    PolyProgram (fun v=>es.map (fun e=>e.eval v)++v.drop 5) :=
  match es with
  | [] => (PolyProgram.drop 5).ofEq (fun _=>rfl)
  | e::es => (e.program.cons (expressionList es)).ofEq (fun _=>rfl)

noncomputable def Action.program : (a : Action) → PolyProgram a.eval
  | .put es => expressionList es
  | .test e yes no => (PolyProgram.branch e.program yes.program no.program).ofEq (by
      intro v
      simp only [Action.eval,List.headI_cons]
      rfl)

abbrev c (i : ℕ) : Expr := .const i
abbrev fresh : Expr := .add n (c 1)

def put (md pc env kont : Expr) : Action := .put [md,pc,env,kont,n]
def alloc (md pc env kont a b d e : Expr) : Action :=
  .put [md,pc,env,kont,fresh,a,b,d,e]

def halt : Action := put (c 2) (c 0) (r 2) (c 0)

def evalZero : Action := alloc (c 1) (c 0) fresh (r 3) (c 0) (r 2) (c 0) (c 0)
def evalSucc : Action := alloc (c 1) (c 0) fresh (r 3) (.add (g (r 2) 0) (c 1)) (c 0) (c 0) (c 0)
def evalTail : Action := put (c 1) (c 0) (g (r 2) 1) (r 3)
def evalCons : Action := alloc (c 0) (g (r 1) 1) (r 2) fresh (c 0) (g (r 1) 2) (r 2) (r 3)
def evalComp : Action := alloc (c 0) (g (r 1) 2) (r 2) fresh (c 2) (g (r 1) 1) (c 0) (r 3)
def evalCase : Action := .test (g (r 2) 0)
  (put (c 0) (g (r 1) 1) (g (r 2) 1) (r 3))
  (alloc (c 0) (g (r 1) 2) fresh (r 3) (.sub (g (r 2) 0) (c 1)) (g (r 2) 1) (c 0) (c 0))
def evalFix : Action := alloc (c 0) (g (r 1) 1) (r 2) fresh (c 3) (r 1) (c 0) (r 3)

def switch (e : Expr) : ℕ → List Action → Action
  | _,[] => halt
  | j,a::as => .test (.eq e (c j)) (switch e (j+1) as) a

def evalAction : Action := switch (g (r 1) 0) 0
  [evalZero,evalSucc,evalTail,evalCons,evalComp,evalCase,evalFix]

def retCons1 : Action := alloc (c 0) (g (r 3) 1) (g (r 3) 2) fresh
  (c 1) (g (r 2) 0) (c 0) (g (r 3) 3)
def retCons2 : Action := alloc (c 1) (c 0) fresh (g (r 3) 3)
  (g (r 3) 1) (r 2) (c 0) (c 0)
def retComp : Action := put (c 0) (g (r 3) 1) (r 2) (g (r 3) 3)
def retFix : Action := .test (g (r 2) 0)
  (put (c 1) (c 0) (g (r 2) 1) (g (r 3) 3))
  (put (c 0) (g (r 3) 1) (g (r 2) 1) (g (r 3) 3))
def returnAction : Action := .test (r 3) halt
  (switch (g (r 3) 0) 0 [retCons1,retCons2,retComp,retFix])

def tickAction : Action := .test (r 0) evalAction
  (.test (.eq (r 0) (c 1)) (put (r 0) (r 1) (r 2) (r 3)) returnAction)

def rawTick : List ℕ → List ℕ := tickAction.eval

lemma expr_read_encode (s : State) (addr : Expr) (j : Fin 4) :
    (g addr j).eval s.encode=read s.heap (addr.eval s.encode) j := by
  exact readExpr_eval [s.mode,s.pc,s.env,s.kont,s.heap.length] 4 s.heap addr j rfl

lemma put_encode (s : State) (md pc env kont : Expr) :
    (put md pc env kont).eval s.encode=
      (State.mk (md.eval s.encode) (pc.eval s.encode) (env.eval s.encode) (kont.eval s.encode) s.heap).encode := by
  simp only [put,Action.eval,List.map_cons,List.map_nil,State.encode,Expr.eval]
  rfl

lemma alloc_encode (s : State) (md pc env kont a b d e : Expr) :
    (alloc md pc env kont a b d e).eval s.encode=
      (State.mk (md.eval s.encode) (pc.eval s.encode) (env.eval s.encode) (kont.eval s.encode)
        (node (a.eval s.encode) (b.eval s.encode) (d.eval s.encode) (e.eval s.encode)::s.heap)).encode := by
  simp only [alloc,Action.eval,List.map_cons,List.map_nil,State.encode,words_cons,List.length_cons,
    Expr.eval,node,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  rfl

lemma rawTick_encode (s : State) : rawTick s.encode=s.tick.encode := by
  simp only [rawTick,tickAction,Action.eval,Expr.eval]
  change (if s.mode=0 then _ else if (if s.mode=1 then 1 else 0)=0 then _ else _)=_
  by_cases hm : s.mode=0
  · simp only [hm,ite_true,State.tick]
    generalize he : read s.heap s.pc 0=a
    rcases Nat.lt_or_ge a 7 with ha | ha
    · interval_cases a <;> simp [evalAction,switch,Action.eval,Expr.eval,expr_read_encode,
      he,put_encode,alloc_encode,evalZero,evalSucc,evalTail,evalCons,
      evalComp,evalCase,evalFix,halt]
      all_goals split_ifs <;> rfl
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le ha
      rw [hb, Nat.add_comm 7 b] at he ⊢
      simp [evalAction,switch,Action.eval,Expr.eval,expr_read_encode,he,put_encode,halt]
  · by_cases hm1 : s.mode=1
    · simp only [hm1,ite_true,State.tick]
      by_cases hk : s.kont=0
      · simp [returnAction,Action.eval,Expr.eval,hk,halt,put_encode, -List.drop_one]
      · simp only [returnAction,Action.eval,Expr.eval]
        change (if s.kont=0 then _ else _)=_
        simp only [hk,ite_false]
        generalize he : read s.heap s.kont 0=a
        rcases Nat.lt_or_ge a 4 with ha | ha
        · interval_cases a <;> simp [switch,Action.eval,Expr.eval,expr_read_encode,
          he,put_encode,alloc_encode,retCons1,retCons2,retComp,retFix,halt]
          all_goals split_ifs <;> rfl
        · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le ha
          rw [hb,Nat.add_comm 4 b] at he ⊢
          simp [switch,Action.eval,Expr.eval,expr_read_encode,he,put_encode,halt]
    · simp [hm,hm1,State.tick,put_encode,Expr.eval]

lemma reg_le_maximum (v : List ℕ) (i : ℕ) : (r i).eval v≤ maximum v :=
  (head_le_maximum (v.drop i)).trans (maximum_drop v i)

def Small (e : Expr) : Prop := ∀v,e.eval v≤ maximum v+3

def Action.Safe (a : Action) : Prop := ∀v,
    (a.eval v).length≤v.length+9 ∧ maximum (a.eval v)≤ maximum v+3

lemma maximum_map_small (es : List Expr) (hs : ∀e∈es,Small e) (v : List ℕ) :
    maximum (es.map (fun e=>e.eval v))≤ maximum v+3 := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,maximum_cons]
    exact max_le (hs e (by simp) v) (ih (fun f hf=>hs f (by simp [hf])))

lemma Action.Safe.put {es : List Expr} (hl : es.length≤9) (hs : ∀e∈es,Small e) :
    Action.Safe (.put es) := by
  intro v
  constructor
  · simp only [Action.eval,List.length_append,List.length_map,List.length_drop]
    omega
  · simp only [Action.eval,maximum_append]
    exact max_le (maximum_map_small es hs v) ((maximum_drop v 5).trans (by omega))

lemma Action.Safe.test {e a b} (ha : Action.Safe a) (hb : Action.Safe b) :
    Action.Safe (.test e a b) := by
  intro v
  simp only [Action.eval]
  split_ifs <;> [exact ha v; exact hb v]

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IterationMagnitude
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Division
open Arena

noncomputable def stepProgram : PolyProgram step :=
  (PolyProgram.branch (Expr.eq (.add (.reg 1) (.const 1)) (.reg 2)).program
    ((Expr.reg 0).program.cons ((Expr.add (.reg 1) (.const 1)).program.cons
      ((Expr.reg 2).program.cons (PolyProgram.drop 3))))
    ((Expr.add (.reg 0) (.const 1)).program.cons ((PolyProgram.const 0).cons
      ((Expr.reg 2).program.cons (PolyProgram.drop 3))))).ofEq (by
    intro v
    simp only [Expr.eval,List.headI_cons,step]
    by_cases h : (v.drop 1).headI+1=(v.drop 2).headI <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero])

lemma step_safe (v : List ℕ) :
    (step v).length≤v.length+3 ∧ maximum (step v) ≤ maximum v+1 := by
  have h0 := reg_le_maximum v 0
  have h1 := reg_le_maximum v 1
  have h2 := reg_le_maximum v 2
  have h3 := maximum_drop v 3
  change (v.drop 0).headI≤_ at h0
  change (v.drop 1).headI≤_ at h1
  change (v.drop 2).headI≤_ at h2
  dsimp only [step]
  split_ifs <;> simp only [List.length_cons,List.length_drop,maximum_cons] <;>
    constructor <;> omega

noncomputable def pair : PolyProgram (fun v=>[v.headI/v.tail.headI,v.headI%v.tail.headI]) := by
  let pack := PolyProgram.head.cons ((PolyProgram.const 0).cons ((PolyProgram.const 0).cons
    ((PolyProgram.head.comp PolyProgram.tail).cons PolyProgram.nil)))
  let run := (PolyProgram.safeIterate stepProgram 3 1 step_safe).comp pack
  let take := (PolyProgram.projection 0).cons ((PolyProgram.projection 1).cons PolyProgram.nil)
  exact (take.comp run).ofEq (by
    intro v
    simp only [Function.comp_apply,List.headI_cons,List.tail_cons,iterate_exact,List.drop_zero,List.drop_one])

noncomputable def quotient : PolyProgram (fun v=>[v.headI/v.tail.headI]) :=
  (PolyProgram.head.comp pair).ofEq (by intro v; rfl)
noncomputable def remainder : PolyProgram (fun v=>[v.headI%v.tail.headI]) :=
  (PolyProgram.projection 1 |>.comp pair).ofEq (by intro v; rfl)

end MinUncut.Costed.Division

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticExpression
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed

noncomputable def AExpr.program : (a : AExpr) → PolyProgram (fun v=>[a.eval v])
  | .const n => PolyProgram.const n
  | .reg i => PolyProgram.projection i
  | .add a b => PolyProgram.addOf a.program b.program
  | .sub a b => PolyProgram.subOf a.program b.program
  | .mul a b => PolyProgram.mulOf a.program b.program
  | .div a b => Division.quotient.comp (a.program.cons (b.program.cons PolyProgram.nil))
  | .mod a b => Division.remainder.comp (a.program.cons (b.program.cons PolyProgram.nil))
  | .eq a b => PolyProgram.eqOf a.program b.program
  | .le a b => PolyProgram.leOf a.program b.program
  | .at a => PolyProgram.dynamic.comp (a.program.cons PolyProgram.id)
  | .cond e a b => (PolyProgram.branch e.program a.program b.program).ofEq (by
      intro v
      change (if e.eval v=0 then [a.eval v] else [b.eval v])=[if e.eval v=0 then a.eval v else b.eval v]
      split_ifs <;> rfl)

end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_BlockEnumeration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

namespace PolyProgram

def expressions {g : List ℕ → List ℕ} (G : PolyProgram g) :
    (es : List AExpr) → PolyProgram (fun v=>es.map (fun e=>e.eval v)++g v)
  | [] => G
  | e::es => e.program.cons (expressions G es)

end PolyProgram

namespace Blocks

def stepProgram (es : List AExpr) : PolyProgram (step es) :=

  let pref : PolyProgram (fun v=>block es v.headI (source v)++v.drop 2) := by
    let rec go (l : List AExpr) : PolyProgram (fun v=> l.map (fun e=>e.eval (v.headI::source v))++v.drop 2) :=
      match l with
      | [] => PolyProgram.drop 2
      | e::l => (e.program.comp extractor).cons (go l)
    exact go es
  (PolyProgram.succ.cons
    ((PolyProgram.addOf (PolyProgram.projection 1) (PolyProgram.const es.length)).cons pref)).ofEq
      (by intro v; simp only [List.headI_cons,List.drop_one,step])

lemma iterate_size (es : List AExpr) (v : List ℕ) (n i : ℕ) (hi : i≤n) :
    magnitude ((step es)^[i] v)≤ magnitude v+
      i*(es.length+3+((PolyProgram.expressions PolyProgram.nil es).bound).eval
        (n+1+2*magnitude v)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hh := ih (by omega)
    have hs := magnitude_step es ((step es)^[i] v)
    have hb := (PolyProgram.expressions PolyProgram.nil es).size
      (((step es)^[i] v).headI::source ((step es)^[i] v))
    change magnitude (block es _ _++[])≤_ at hb
    rw [List.append_nil,iterate_head,iterate_source] at hb
    have hm : magnitude ((v.headI+i)::source v)≤n+1+2*magnitude v := by
      have h1 := magnitude_head v
      have h2 := magnitude_drop (v.tail.headI+2) v
      simp only [magnitude_cons,source]
      omega
    have hb' := hb.trans (evalNat_mono _ hm)
    rw [iterate_head,iterate_source] at hs
    rw [Function.iterate_succ_apply']
    nlinarith

def iterationProgram (es : List AExpr) :
    PolyProgram (fun v=>(step es)^[v.headI] v.tail) :=
  PolyProgram.iterate (stepProgram es)
    (X+X*(C (es.length+3)+(PolyProgram.expressions PolyProgram.nil es).bound.comp (C 3*X+1))) (by
      intro n v i hi
      have h := iterate_size es v n i hi
      have hv : magnitude v≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have hi' : i≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have hn : n+1+2*magnitude v≤3*magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      have hb := evalNat_mono (PolyProgram.expressions PolyProgram.nil es).bound hn
      simp only [eval_add,eval_mul,eval_C,eval_comp,eval_X,eval_one]
      exact h.trans (Nat.add_le_add hv (Nat.mul_le_mul hi' (Nat.add_le_add_left hb _))))

def enumerate (es : List AExpr) (N : AExpr) : PolyProgram (fun v=>
    N.eval v::(N.eval v*es.length)::
      ((List.range (N.eval v)).reverse.flatMap (fun i=>block es i v)++v)) :=
  ((iterationProgram es).comp (N.program.cons ((PolyProgram.const 0).cons
    ((PolyProgram.const 0).cons PolyProgram.id)))).ofEq (by
      intro v
      change (step es)^[N.eval v] (0::0::v)=_
      exact iterate_accumulator es v (N.eval v))

end Blocks
end MinUncut.Costed

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ReversePrefixProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec Polynomial Arena

noncomputable def prefixStepProgram : PolyProgram prefixStep :=
  PolyProgram.succ.cons (((Expr.at (.add (.mul (.const 2) (.reg 0)) (.const 1))).program).cons PolyProgram.tail)

noncomputable def reversePrefixProgram : PolyProgram
    (fun v=>(prefixStep^[v.headI] (0::v.tail)).tail) :=
  PolyProgram.tail.comp ((Arena.PolyProgram.safeIterate prefixStepProgram 2 1 prefixStep_safe).comp
    (PolyProgram.head.cons ((PolyProgram.const 0).cons PolyProgram.tail)))

end MinUncut.Costed

namespace MinUncut.Costed.Blocks
noncomputable section

def forward (es : List AExpr) (N : AExpr) : PolyProgram (fun v=>
    emitted es (N.eval v) v++retained es (N.eval v) v) :=
  (reversePrefixProgram.comp (PolyProgram.tail.comp (enumerate es.reverse N))).ofEq (by
    intro v
    simp only [Function.comp_def,List.tail_cons,enumerate_reverse,List.length_reverse,
      List.headI_cons]
    rw [←show (emitted es (N.eval v) v).reverse.length=N.eval v*es.length by
      simp only [List.length_reverse,length_emitted]]
    rw [reversePrefix_spec,List.reverse_reverse]
    exact List.append_assoc _ _ _)

end
end MinUncut.Costed.Blocks

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

section ConcreteSource

open SourceContexts
open MinUncutGames.Reduction.FiniteNoise

def emptyFormulaEquation (F : Target.Formula) (u : ℕ) : Equation (Fin (nBits F u)) :=
  ⟨dummyIndex F u, dummyIndex F u, dummyIndex F u, false⟩

def sourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  if F.clauses.isEmpty then [emptyFormulaEquation F u] else rawSourceList F u D

theorem sourceList_empty (F : Target.Formula) (u D : ℕ) (h : F.clauses = []) :
    sourceList F u D = [emptyFormulaEquation F u] := by simp [sourceList, h]

theorem sourceList_nonempty (F : Target.Formula) (u D : ℕ) (h : F.clauses ≠ []) :
    sourceList F u D = rawSourceList F u D := by
  unfold sourceList
  rw [List.isEmpty_eq_false_iff.mpr h]
  rfl

theorem sourceList_ne_nil (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    sourceList F u D ≠ [] := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    simp
  · rw [sourceList_nonempty F u D h]
    apply List.length_pos_iff.mp
    rw [rawSourceList_length]
    have hc : 0 < F.clauses.length := List.length_pos_iff.mpr h
    positivity

def sourceInput (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    MinUncutGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

end ConcreteSource

end MinUncutGames.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Runtime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Reduction.MachineTransfer

open _root_.Turing

variable {α β : Type} [Fintype α] [Fintype β]

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

theorem tapesAt_other (src dst k : K) (notSrc : k ≠ src) (notDst : k ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output k = base k := by
  simp [tapesAt, notSrc, notDst]

theorem update_tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input replacement : List (Γ src))
    (output : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) src replacement =
      tapesAt src dst base replacement output := by
  funext k
  by_cases hs : k = src
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = dst
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src))
    (output replacement : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) dst replacement =
      tapesAt src dst base input replacement := by
  funext k
  by_cases hd : k = dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

theorem stepAt_empty (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program ⟨some loopLabel, (ambient, register), tapesAt src dst base [] output⟩ =
      some ⟨exit, (ambient, none), tapesAt src dst base [] output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base [] output)) = _
  rw [atLoop]
  cases exit <;>
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src]

theorem stepAt_cons (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (head : Γ src) (input : List (Γ src))
    (output : List (Γ dst)) (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some (f head)),
        tapesAt src dst base input (f head :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base (head :: input) output)) = _
  rw [atLoop]
  simp [loopAt, TM2.stepAux, tapesAt_src, tapesAt_dst, distinct,
    update_tapesAt_src, update_tapesAt_dst]

theorem transferAt_steps (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register), tapesAt src dst base input output⟩) =
      some ⟨exit, (ambient, none), tapesAt src dst base [] (input.reverse.map f ++ output)⟩ := by
  induction input generalizing output register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, nextAt,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using stepAt_empty src dst distinct f fallback loopLabel exit program atLoop base output
        ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (nextAt dst program)^[input.length + 1]
      (TM2.step program
        ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩) = _
    rw [stepAt_cons src dst distinct f fallback loopLabel exit program atLoop, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem transferAt_fromTapes (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[(base src).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩ := by
  simpa only [tapesAt_self] using
    transferAt_steps src dst distinct f fallback loopLabel exit program atLoop base
      (base src) (base dst) ambient register

end MinUncutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Game
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceHonest

open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise
open scoped BigOperators


open SourceContexts
open SourceOccurrences

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl


end MinUncutGames.Foundations.Hastad.SourceHonest

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

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

end Transport

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

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

def stageTapes (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then
      coordinateOutput ⟨r, h⟩ F.clauses[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (p : Tape u Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

end MinUncutGames.Foundations.Hastad.SourceContextLoad

namespace MinUncutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise

abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

end MinUncutGames.Foundations.Hastad.SourceLocalEquation

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ProfileBridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def positionEncoding (u : ℕ) : Encoding (Position u) :=
  (Encoding.fin u).prod slotEncoding

def names (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → ℕ :=
  fun i => (occurrenceName F c ((positionEncoding u).code.symm i)).val

def nameWords (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → List Bool :=
  fun i => encodeWord (names F c i)

end MinUncutGames.Foundations.Hastad.SourceProfileBridge

namespace MinUncutGames.Foundations.Hastad.SourceSignaturePrepare

open _root_.Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open MinUncutGames.Foundations.Complexity

abbrev Width (u : ℕ) := (positionEncoding u).size
abbrev Arena (u : ℕ) (Extra : Type) := SourceContextLoad.Tape u Extra
abbrev ProfileState (u : ℕ) := MachineCompare.State (MachineFieldProfile.Profile (Width u))
abbrev State (u : ℕ) (τ : Type) := ProfileState u × (Signature u × τ)

variable {u : ℕ} {Extra τ : Type}

def variableField (p : Position u) : Arena u Extra :=
  SourceContextLoad.variableField p.1 (slotEncoding.code p.2)

def place : MachineFieldProfile.Tape (Width u) → Arena u Extra
  | .inl i => variableField ((positionEncoding u).code.symm i)
  | .inr w => if w = 0 then .index else if w = 1 then .work else .scratch

def unplace : Arena u Extra → Option (MachineFieldProfile.Tape (Width u))
  | .index => some (.inr 0)
  | .work => some (.inr 1)
  | .scratch => some (.inr 2)
  | .field t s =>
    if s = 0 then some (.inl ((positionEncoding u).code (t, .first)))
    else if s = 2 then some (.inl ((positionEncoding u).code (t, .second)))
    else if s = 4 then some (.inl ((positionEncoding u).code (t, .third))) else none
  | _ => none

@[simp] theorem unplace_place (k : MachineFieldProfile.Tape (Width u)) :
    unplace (place (Extra := Extra) k) = some k := by
  cases k with
  | inl i =>
    obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
    rcases p with ⟨t, s⟩
    simp only [place, Equiv.symm_apply_apply]
    cases s <;> rfl
  | inr w =>
    obtain ⟨w, hw⟩ := w
    have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases h with rfl | rfl | rfl <;> rfl

theorem place_unplace (a : Arena u Extra) (k : MachineFieldProfile.Tape (Width u))
    (h : unplace a = some k) : place k = a := by
  cases a with
  | formula => simp [unplace] at h
  | index => cases Option.some.inj h; rfl
  | work => cases Option.some.inj h; rfl
  | scratch => cases Option.some.inj h; rfl
  | copyScratch => simp [unplace] at h
  | current t => simp [unplace] at h
  | remaining t => simp [unplace] at h
  | extra e => simp [unplace] at h
  | field t s =>
    by_cases h0 : s = 0
    · subst s
      simp only [unplace, ↓reduceIte] at h
      cases Option.some.inj h
      simp only [place, Equiv.symm_apply_apply]
      rfl
    · by_cases h2 : s = 2
      · subst s
        simp only [unplace, ↓reduceIte] at h
        cases Option.some.inj h
        simp only [place, Equiv.symm_apply_apply]
        rfl
      · by_cases h4 : s = 4
        · subst s
          simp only [unplace, ↓reduceIte] at h
          cases Option.some.inj h
          simp only [place, Equiv.symm_apply_apply]
          rfl
        · simp [unplace, h0, h2, h4] at h

def fill (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) : Arena u Extra → List Bool :=
  fun a => match unplace a with
    | some k => localTapes k
    | none => base a

@[simp] theorem fill_place (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) : fill base localTapes (place k) = localTapes k := by
  simp only [fill, unplace_place]

@[simp] theorem fill_self (base : Arena u Extra → List Bool) :
    fill base (base ∘ place) = base := by
  funext a
  cases h : unplace a with
  | none => simp only [fill, h]
  | some k =>
    simp only [fill, h, Function.comp_apply, place_unplace a k h]

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

abbrev PrepareState (u : Nat) (τ : Type) := SourceSignaturePrepare.State u τ
abbrev State (u : Nat) (τ : Type) := LoadState × PrepareState u τ

variable {u : Nat} {Extra τ : Type}

variable [DecidableEq Extra]

def finalState (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
    (ofContext F c selected, ambient)))

end MinUncutGames.Foundations.Hastad.SourceContextPrepare

end
section

namespace MinUncutGames.Foundations.Hastad.SourceLoopInit

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem headerOutput_frame (F : Target.Formula) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader) :
    headerOutput F base p = base p := by simp [headerOutput, hw, hn, hm]

theorem output_frame (F : Target.Formula) (base : Tape u Extra → List Bool) (p : Tape u Extra)
    (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader)
    (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    outputTapes F base p = base p := by
  rw [outputTapes, stageTapes_frame _ _ _ _ hc hr, headerOutput_frame _ _ _ hw hn hm]

@[simp] theorem output_formula (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .formula = base .formula :=
  output_frame F base .formula (by simp) (by simp [variableHeader])
    (by simp [clauseHeader]) (by simp) (by simp)

end MinUncutGames.Foundations.Hastad.SourceLoopInit

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

namespace MinUncutGames.Foundations.Hastad.SourceTestEmit

open _root_.Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open MinUncutGames.Reduction.CloneGap
open Complexity

abbrev State (u D : ℕ) := LocalInput u D × Option Bool

end MinUncutGames.Foundations.Hastad.SourceTestEmit

namespace MinUncutGames.Foundations.Hastad.SourceTestAppend

open _root_.Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceTestEmit

abbrev State (u D : Nat) := SourceTestEmit.State u D

end MinUncutGames.Foundations.Hastad.SourceTestAppend

namespace MinUncutGames.Foundations.Hastad.SourceQueryLoop

open _root_.Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev Query (u D : Nat) := SourceTape.TestTape (I u) (J u) D
abbrev State (u D : Nat) := SourceTestAppend.State u D

end MinUncutGames.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeModel

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev BodyExtra (Extra : Type) := SourceLoopInit.HeaderTape ⊕ BodyWork Extra
abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (BodyExtra Extra)
abbrev QueryState (u D : Nat) := SourceQueryLoop.State u D
abbrev State (u D : Nat) := SourceContextPrepare.State u (QueryState u D × ArithmeticState)
abbrev QueryMetadata (u : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × ArithmeticState))
abbrev ArithmeticMetadata (u D : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × QueryState u D))

variable {u D : Nat} {Extra : Type}

def workTape (role : BodyWork Extra) : Arena u Extra := .extra (.inr role)
def variableHeader : Arena u Extra := SourceLoopInit.variableHeader
def clauseHeader : Arena u Extra := SourceLoopInit.clauseHeader

def queryStateEquiv (u D : Nat) : QueryState u D × QueryMetadata u ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.1, x.2.2.2.2))))
  invFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def arithmeticStateEquiv (u D : Nat) : ArithmeticState × ArithmeticMetadata u D ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2, x.1))))
  invFun x := (x.2.2.2.2, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1))))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem initializer_arena :
    SourceLoopInit.Tape u (BodyWork Extra) = Arena u Extra := rfl

end MinUncutGames.Foundations.Hastad.SourceRuntimeModel

end

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

def dummyValue (u n m : Nat) : Nat := leftValue u n + rightValue u m
def bitValue (u n m : Nat) : Nat := dummyValue u n m + 1

variable {u D : Nat} {K Λ σ : Type}

@[simp] theorem evalSlots_digit (slots : Layout u D ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial u D kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock u D kind i)) := rfl

@[simp] theorem control_eq_iff (slots : Layout u D ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by
  simp [control, slots.injective.eq_iff]

variable [DecidableEq K]

def resultTapes (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (control slots .leftBlockSize) (encodeWord (leftValue u n)))
    (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m)))
    (control slots .dummyIndex) (encodeWord (dummyValue u n m)))
    (control slots .bitCount) (encodeWord (bitValue u n m))

@[simp] theorem result_left (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
  simp [resultTapes]
@[simp] theorem result_occurrences (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .occurrenceCount) = encodeWord (occurrenceValue u D m) := by
  simp [resultTapes]
@[simp] theorem result_dummy (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
  simp [resultTapes]
@[simp] theorem result_bits (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .bitCount) = encodeWord (bitValue u n m) := by
  simp [resultTapes]

end

end MinUncutGames.Foundations.Hastad.SourceHeaderCounts

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorModel

open _root_.Turing Complexity SourceRuntimeModel

abbrev Extra (u D : Nat) := SourceHeaderCounts.Coefficients u D ⊕ Unit
abbrev Tape (u D : Nat) := SourceRuntimeModel.Arena u (Extra u D)
def accumulatorTape (u D : Nat) : Tape u D := workTape .accumulator

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
namespace MinUncutGames.Foundations.Hastad.SourceHeaderAccumulate

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

def statement (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ) :
    Bool → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | false => loopAt layout.bits layout.accumulator id false (labels false) (some (labels true))
  | true => loopAt layout.count layout.accumulator id false (labels true) exit

def resultTapes (layout : Layout K) (base : K → List Bool) (nBits count : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base layout.bits []) layout.count [])
    layout.accumulator ((encodeWords [nBits, count]).reverse ++ base layout.accumulator)

@[simp] theorem result_bits (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.bits = [] := by
  simp [resultTapes, layout.bits_count, layout.bits_accumulator]

@[simp] theorem result_count (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.count = [] := by
  simp [resultTapes, layout.count_accumulator]

@[simp] theorem result_accumulator (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.accumulator =
      (encodeWords [nBits, count]).reverse ++ base layout.accumulator := by
  simp [resultTapes]

theorem trace (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[nBits + count + 4]
      (some ⟨some (labels false), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩ := by
  let middle := tapesAt layout.bits layout.accumulator base []
    ((encodeWord nBits).reverse ++ base layout.accumulator)
  have firstRun := transferAt_fromTapes layout.bits layout.accumulator layout.bits_accumulator
    id false (labels false) (some (labels true)) program (by simpa only [statement] using atLabels false) base ambient register
  change (advance (TM2.step program))^[(base layout.bits).length + 1]
    (some ⟨some (labels false), (ambient, register), base⟩) = _ at firstRun
  simp only [hbits, List.map_id, encodeWord_length] at firstRun
  have hc : middle layout.count = encodeWord count := by
    dsimp only [middle]
    rw [tapesAt_other _ _ _ layout.bits_count.symm layout.count_accumulator]
    exact hcount
  have ha : middle layout.accumulator =
      (encodeWord nBits).reverse ++ base layout.accumulator := by
    exact tapesAt_dst _ _ _ _ _
  have secondRun := transferAt_fromTapes layout.count layout.accumulator layout.count_accumulator
    id false (labels true) exit program (by simpa only [statement] using atLabels true) middle ambient none
  change (advance (TM2.step program))^[(middle layout.count).length + 1]
    (some ⟨some (labels true), (ambient, none), middle⟩) = _ at secondRun
  simp only [hc, ha, List.map_id, encodeWord_length] at secondRun
  have he : tapesAt layout.count layout.accumulator middle []
      ((encodeWord count).reverse ++ ((encodeWord nBits).reverse ++ base layout.accumulator)) =
      resultTapes layout base nBits count := by
    funext k
    by_cases hk : k = layout.accumulator
    · subst k
      simp [resultTapes, tapesAt, encodeWords, List.reverse_append, List.append_assoc]
    · by_cases hc : k = layout.count
      · subst k; simp [tapesAt, resultTapes, layout.count_accumulator]
      · by_cases hb : k = layout.bits
        · subst k
          simp [middle, tapesAt, resultTapes, layout.bits_count, layout.bits_accumulator]
        · simp [middle, tapesAt, resultTapes, hk, hc, hb]
  rw [he] at secondRun
  rw [show nBits + count + 4 = (count + 1 + 1) + (nBits + 1 + 1) by omega,
    Function.iterate_add_apply, firstRun]
  exact secondRun

def inTime (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels false), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩)
      (nBits + count + 4) where
  steps := nBits + count + 4
  evals_in_steps := trace layout labels exit program atLabels base nBits count hbits hcount ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem inTime_steps (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (inTime layout labels exit program atLabels base nBits count hbits hcount ambient register).steps =
      nBits + count + 4 := rfl

end MinUncutGames.Foundations.Hastad.SourceHeaderAccumulate

end
section
namespace MinUncutGames.Foundations.Hastad.SourceStartup

open _root_.Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def initialTapes (F : Target.Formula) : Tape u D → List Bool :=
  Function.update (fun _ => []) .formula (formulaBits F)

def initializedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceLoopInit.outputTapes F (initialTapes F)

def readyTapes (F : Target.Formula) : Tape u D → List Bool
  | .extra (.inr .leftBlock) => encodeWord (SourceHeaderCounts.leftValue u F.«variables»)
  | .extra (.inr .dummy) => encodeWord (SourceHeaderCounts.dummyValue u F.«variables» F.clauses.length)
  | .extra (.inr .accumulator) =>
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse
  | p => initializedTapes F p

@[simp] theorem initialized_formula (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F .formula = formulaBits F := by
  simp [initializedTapes, initialTapes]

@[simp] theorem initialized_current (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.current j) = encodeWord 0 := by
  simp [initializedTapes]

@[simp] theorem initialized_remaining (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp [initializedTapes]

@[simp] theorem initialized_variableHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F variableHeader = encodeWord F.«variables» := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.variableHeader = _
  rw [SourceLoopInit.output_variableHeader]
  simp [initialTapes, SourceLoopInit.variableHeader]

@[simp] theorem initialized_clauseHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.clauseHeader = _
  rw [SourceLoopInit.output_clauseHeader]
  simp [initialTapes, SourceLoopInit.clauseHeader]

@[simp] theorem initialized_work (F : Target.Formula) (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (workTape role) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (workTape role)
    (by simp [workTape]) (by simp [workTape, SourceLoopInit.variableHeader])
    (by simp [workTape, SourceLoopInit.clauseHeader]) (by simp [workTape]) (by simp [workTape])]
  simp [initialTapes, workTape]

@[simp] theorem initialized_work_raw (F : Target.Formula)
    (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (.extra (.inr role)) = [] := initialized_work F role

@[simp] theorem initialized_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    initializedTapes (D := D) F (.field j s) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (.field j s)
    (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
    (by simp) (by simp)]
  simp [initialTapes]

@[simp] theorem ready_formula (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .formula = formulaBits F := initialized_formula F

@[simp] theorem ready_current (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.current j) = encodeWord 0 := initialized_current F j

@[simp] theorem ready_remaining (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := initialized_remaining F j

@[simp] theorem ready_variableHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F variableHeader = encodeWord F.«variables» := initialized_variableHeader F

@[simp] theorem ready_clauseHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := initialized_clauseHeader F

@[simp] theorem ready_leftBlock (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .leftBlock) =
      encodeWord (SourceHeaderCounts.leftValue u F.«variables») := rfl

@[simp] theorem ready_dummy (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .dummy) =
      encodeWord (SourceHeaderCounts.dummyValue u F.«variables» F.clauses.length) := rfl

@[simp] theorem ready_accumulator (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (accumulatorTape u D) =
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse := rfl

@[simp] theorem ready_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    readyTapes (D := D) F (.field j s) = [] := initialized_field F j s

@[simp] theorem ready_sharedWork (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .work = [] := by
  simp [readyTapes, initializedTapes]

end

end MinUncutGames.Foundations.Hastad.SourceStartup

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

abbrev digitTapes (current remaining : K) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) : K → List Bool :=
  MachineUnaryAddAt.unaryTapes current remaining base d r currentSuffix remainingSuffix

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

abbrev Tape := SourceContextLoad.Tape

variable {u : Nat} {Extra : Type}

def fieldAt (i : Fin (u * 6)) : Tape u Extra :=
  .field (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def fields : List (Tape u Extra) := List.ofFn fieldAt

@[simp] theorem fields_length : (fields (u := u) (Extra := Extra)).length = 6 * u := by
  simp [fields, Nat.mul_comm]

def outputTapes (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .field _ _ => []
  | p => base p

@[simp] theorem output_field (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 6) :
    outputTapes base (.field j s) = [] := rfl

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
namespace MinUncutGames.Foundations.Hastad.SourceTupleTape

open _root_.Turing Complexity SourceContexts SourceRuntimeModel

variable {u : Nat} {Extra : Type}

def tapes (base : Arena u Extra → List Bool) (s : Snapshot) : Arena u Extra → List Bool
  | .extra (.inr .rank) => s.rank
  | .extra (.inr .rightBase) => s.rightBase
  | .extra (.inr .leftBase) => s.leftBase
  | .extra (.inr .zero) => s.zero
  | .extra (.inr .accumulator) => s.emitted.reverse ++ base (workTape .accumulator)
  | k => base k

@[simp] theorem tapes_rank (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rank) = s.rank := rfl
@[simp] theorem tapes_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rightBase) = s.rightBase := rfl
@[simp] theorem tapes_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBase) = s.leftBase := rfl
@[simp] theorem tapes_zero (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .zero) = s.zero := rfl
@[simp] theorem tapes_accumulator (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .accumulator) = s.emitted.reverse ++ base (workTape .accumulator) := rfl
@[simp] theorem tapes_coefficient (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .coefficient) = base (workTape .coefficient) := rfl
@[simp] theorem tapes_dummy (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .dummy) = base (workTape .dummy) := rfl
@[simp] theorem tapes_leftBlock (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBlock) = base (workTape .leftBlock) := rfl
@[simp] theorem tapes_queryTemporary (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryTemporary) = base (workTape .queryTemporary) := rfl
@[simp] theorem tapes_queryScratch (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryScratch) = base (workTape .queryScratch) := rfl
@[simp] theorem tapes_field (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) (k : Fin 6) :
    tapes base s (.field j k) = base (.field j k) := rfl
@[simp] theorem tapes_current (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) :
    tapes base s (.current j) = base (.current j) := rfl
@[simp] theorem tapes_formula (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .formula = base .formula := rfl
@[simp] theorem tapes_index (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .index = base .index := rfl
@[simp] theorem tapes_work (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .work = base .work := rfl
@[simp] theorem tapes_variableHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s variableHeader = base variableHeader := rfl
@[simp] theorem tapes_clauseHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s clauseHeader = base clauseHeader := rfl

end MinUncutGames.Foundations.Hastad.SourceTupleTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TupleBody
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleBody

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape

abbrev SlotCount (u : Nat) := (slotContextEncoding u).size
abbrev Query (u D : Nat) := SourceQueryLoop.Query u D

variable {u D : Nat} {Extra : Type}

def selected (index : Fin (SlotCount u)) : SlotContext u :=
  (slotContextEncoding u).code.symm index

variable [DecidableEq Extra]

def selectState (initialQuery : Query u D) (index : Fin (SlotCount u))
    (state : State u D) : State u D :=
  (state.1, (state.2.1, (state.2.2.1,
    ((({state.2.2.1 with selected := selected index}, initialQuery), none), state.2.2.2.2))))

def contextSignature (F : Target.Formula) (c : ClauseContext F u) : Signature u :=
  ofContext F c (fun _ => .first)

def workingState (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : State u D :=
  SourceContextPrepare.finalState F c (fun _ => .first)
    (((signature, query), none), (((), ()), none))

@[simp] theorem workingState_loader (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    (((), none), (workingState F c signature query).2) = workingState F c signature query := rfl

def arithmeticMetadata (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : ArithmeticMetadata u D :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, ((signature, query), none))))

def queryMetadata (F : Target.Formula) (c : ClauseContext F u) : QueryMetadata u :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, (((), ()), none))))

@[simp] theorem arithmeticState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    arithmeticStateEquiv u D ((((), ()), none), arithmeticMetadata F c signature query) =
      workingState F c signature query := rfl

@[simp] theorem queryState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    queryStateEquiv u D (((signature, query), none), queryMetadata F c) =
      workingState F c signature query := rfl

@[simp] theorem select_workingState (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery query : Query u D) (signature : Signature u) :
    selectState initialQuery index (workingState F c signature query) =
      workingState F c (ofContext F c (selected index)) initialQuery := rfl

omit [DecidableEq Extra] in
@[simp] theorem loaded_extra (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (extra : BodyExtra Extra) :
    SourceContextLoad.stageTapes F c base u (.extra extra) = base (.extra extra) :=
  SourceContextLoad.stageTapes_frame F c base u _ (by simp) (by simp) (by simp)

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

namespace MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

open _root_.Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

abbrev Tape := SourceContextLoad.Tape

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .current i => if h : i.val < q then encodeWord (digits ⟨i.val, h⟩)
      else base (.current i)
  | .remaining i => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.remaining i)
  | k => base k

def setAcc (accumulator : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    Tape u Extra → List Bool := Function.update base (.extra accumulator) bits

def putDigit (i : Fin u) (base : Tape u Extra → List Bool) (d r : ℕ) :
    Tape u Extra → List Bool := digitTapes (.current i) (.remaining i) base d r [] []

omit [DecidableEq Extra] in
@[simp] theorem setDigits_zero (m : ℕ) (digits : Fin 0 → ℕ)
    (base : Tape u Extra → List Bool) : setDigits m digits base = base := by
  funext k
  cases k <;> simp [setDigits]

omit [DecidableEq Extra] in
@[simp] theorem setDigits_extra (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (a : Extra) :
    setDigits m digits base (.extra a) = base (.extra a) := rfl

@[simp] theorem setAcc_self (a : Extra) (base : Tape u Extra → List Bool) :
    setAcc a base (base (.extra a)) = base := by
  simp [setAcc]

@[simp] theorem setAcc_setAcc (a : Extra) (base : Tape u Extra → List Bool)
    (first second : List Bool) : setAcc a (setAcc a base first) second = setAcc a base second := by
  simp [setAcc]

@[simp] theorem setAcc_apply (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setAcc a base bits (.extra a) = bits := by simp [setAcc]

@[simp] theorem putDigit_extra (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) : putDigit i base d r (.extra a) = base (.extra a) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

def configuration (label : Λ) (canonical : σ) (tapes : Tape u Extra → List Bool) :
    Configuration (Tape u Extra) Λ σ := ⟨some label, (canonical, none), tapes⟩

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape u Extra → List Bool) : Configuration (Tape u Extra) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape u Extra) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc accumulator base ((allBits bits).reverse ++ base (.extra accumulator))))

omit [DecidableEq Extra] in
@[simp] theorem initial_current (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.current i) =
      encodeWord 0 := by simp [initialConfiguration, configuration, setDigits]

omit [DecidableEq Extra] in
@[simp] theorem initial_remaining (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.remaining i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration, setDigits]

@[simp] theorem final_current (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.current i) =
      encodeWord 0 := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_remaining (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.remaining i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

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
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

open _root_.Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

local instance tupleBoundExtraDecidableEq (u D : Nat) :
    DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def accumulatorRole (u D : Nat) : BodyExtra (SourceGeneratorModel.Extra u D) :=
  .inr .accumulator

def leafTapes (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceGeneratorModel.Tape u D → List Bool :=
  setDigits F.clauses.length (fun i => (c i).val)
    (setAcc (accumulatorRole u D) (SourceStartup.readyTapes F) output)

@[simp] theorem leaf_accumulator (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    leafTapes (D := D) F c output (accumulatorTape u D) = output := by
  exact setAcc_apply (accumulatorRole u D) (SourceStartup.readyTapes F) output

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (MinUncutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

end

end MinUncutGames.Foundations.Hastad.SourceGeneratorTraversal

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

def tableBits (table : Table) : List Bool := encodeWords (tableWords table)

def decodeTableBits (bits : List Bool) : Option Table :=
  decodeWords bits >>= decodeTableWords

@[simp] theorem decodeTableBits_encoded (table : Table) :
    decodeTableBits (tableBits table) = some table := by
  simp [decodeTableBits, tableBits]

@[simp] theorem tableWords_length (table : Table) :
    (tableWords table).length = 2 + 4098 * table.darts := by
  simp only [tableWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, rowList_length]

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
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

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

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl


variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]


end MinUncutGames.Foundations.PCP.CayleySpectral


end
namespace MinUncutGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]


end MinUncutGames.Foundations.PCP.GraphTransport

namespace MinUncutGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

end MinUncutGames.Foundations.PCP.ZigzagGraphs

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

namespace MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

def cloudRank (t : Table) (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    Fin (cloudSize t v) :=
  ⟨(cloudDarts t v).idxOf e.val,
    List.idxOf_lt_length_of_mem ((mem_cloudDarts t v e.val).2 e.property)⟩

@[simp] theorem cloudSelect_val (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) :
    (cloudSelect t v i).val = (cloudDarts t v).get i := rfl

@[simp] theorem cloudRank_val (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) :
    (cloudRank t v e).val = (cloudDarts t v).idxOf e.val := rfl

@[simp] theorem cloudSelect_cloudRank (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : cloudSelect t v (cloudRank t v e) = e := by
  apply Subtype.ext
  exact List.idxOf_get (cloudRank t v e).isLt

@[simp] theorem cloudRank_cloudSelect (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) : cloudRank t v (cloudSelect t v i) = i := by
  apply Fin.ext
  exact List.get_idxOf (cloudDarts_nodup t v) i

def cloudEquiv (t : Table) (v : Fin t.vertices) :
    Cloud (semantics t) v ≃ Fin (cloudSize t v) where
  toFun := cloudRank t v
  invFun := cloudSelect t v
  left_inv := cloudSelect_cloudRank t v
  right_inv := cloudRank_cloudSelect t v

def oldCloudIndex (t : Table) (e : Fin t.darts) :
    Fin (cloudSize t t.rows[e].tail) := cloudRank t t.rows[e].tail ⟨e, rfl⟩

@[simp] theorem cloudSelect_oldCloudIndex (t : Table) (e : Fin t.darts) :
    (cloudSelect t t.rows[e].tail (oldCloudIndex t e)).val = e :=
  congrArg Subtype.val (cloudSelect_cloudRank t t.rows[e].tail ⟨e, rfl⟩)

abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

def paddedCloudEquiv (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) : PaddedCloud t padding v ≃ Fin (cloudSize t v + padding v) :=
  (CloudPadding.paddedCloudEquiv (semantics t) (fun u => Fin (padding u)) v).trans
    ((Equiv.sumCongr (cloudEquiv t v) (Equiv.refl (Fin (padding v)))).trans
      finSumFinEquiv)

def paddedCloudRank (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    PaddedCloud t padding v → Fin (cloudSize t v + padding v) :=
  paddedCloudEquiv t padding v

def paddedCloudSelect (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    Fin (cloudSize t v + padding v) → PaddedCloud t padding v :=
  (paddedCloudEquiv t padding v).symm

@[simp] theorem paddedCloudSelect_rank (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : PaddedCloud t padding v) :
    paddedCloudSelect t padding v (paddedCloudRank t padding v e) = e :=
  (paddedCloudEquiv t padding v).symm_apply_apply e

@[simp] theorem paddedCloudRank_select (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    paddedCloudRank t padding v (paddedCloudSelect t padding v i) = i :=
  (paddedCloudEquiv t padding v).apply_symm_apply i

@[simp] theorem paddedCloudRank_old (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    paddedCloudRank t padding v (paddedOld t padding v e) =
      Fin.castAdd (padding v) (cloudRank t v e) := rfl

@[simp] theorem paddedCloudRank_new (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudRank t padding v (paddedNew t padding v i) =
      Fin.natAdd (cloudSize t v) i := rfl

@[simp] theorem paddedCloudRank_old_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    (paddedCloudRank t padding v (paddedOld t padding v e)).val =
      (cloudRank t v e).val := rfl

@[simp] theorem paddedCloudRank_new_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    (paddedCloudRank t padding v (paddedNew t padding v i)).val =
      cloudSize t v + i.val := rfl

@[simp] theorem paddedCloudSelect_castAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    paddedCloudSelect t padding v (Fin.castAdd (padding v) i) =
      paddedOld t padding v (cloudSelect t v i) := by
  apply (paddedCloudEquiv t padding v).injective
  change (paddedCloudEquiv t padding v)
      ((paddedCloudEquiv t padding v).symm (Fin.castAdd (padding v) i)) = _
  rw [Equiv.apply_symm_apply]
  change Fin.castAdd (padding v) i =
    Fin.castAdd (padding v) (cloudRank t v (cloudSelect t v i))
  rw [cloudRank_cloudSelect]

@[simp] theorem paddedCloudSelect_natAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudSelect t padding v (Fin.natAdd (cloudSize t v) i) =
      paddedNew t padding v i :=
  (paddedCloudEquiv t padding v).symm_apply_apply (paddedNew t padding v i)

end MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

namespace MinUncutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

theorem graph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext (lookup_ofGraph G)

end MinUncutGames.Foundations.PCP.ExpanderTables

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

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

end MinUncutGames.Foundations.PCP.Overlay

end
section
namespace MinUncutGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def lazyRotate (G : PortGraph V D) : Edge V (Bool × D) → Edge V (Bool × D)
  | (v, (false, d)) => (v, (false, d))
  | (v, (true, d)) => ((G.rot (v, d)).1, (true, (G.rot (v, d)).2))

theorem lazyRotate_involutive (G : PortGraph V D) :
    Function.Involutive (lazyRotate G) := by
  rintro ⟨v, b, d⟩
  cases b with
  | false => rfl
  | true =>
    exact congrArg (fun e : V × D => (e.1, (true, e.2))) (rot_rot G (v, d))

def lazyGraph (G : PortGraph V D) : PortGraph V (Bool × D) where
  rot := {
    toFun := lazyRotate G
    invFun := lazyRotate G
    left_inv := lazyRotate_involutive G
    right_inv := lazyRotate_involutive G }
  rot_involutive := lazyRotate_involutive G

@[simp] theorem lazyGraph_rot_false (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (false, d)) = (v, (false, d)) := rfl

@[simp] theorem lazyGraph_rot_true (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (true, d)) = ((G.rot (v, d)).1, (true, (G.rot (v, d)).2)) := rfl

end MinUncutGames.Foundations.PCP.PoweringWalks

end
section
namespace MinUncutGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a c
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a c

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

end MinUncutGames.Foundations.PCP.LazyConstraint

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

namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

def materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) : PortTables.Table n d :=
  PortTables.ofPortGraph
    (GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports)
    (fun x a b => G.accepts (x.1, ports.symm x.2) a b)
    (by
      intro x a b
      simp only [GraphTransport.reindex, Overlay.originalPortGraph,
        Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map]
      convert G.reverse_accepts (x.1, ports.symm x.2) a b using 1
      all_goals try with_reducible_and_instances rfl
      rfl)

@[simp] theorem accepts_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (x : Fin n × Fin d) (a b : PortTables.Label) :
    PortTables.accepts (materialize G ports) x a b =
      G.accepts (x.1, ports.symm x.2) a b := by
  exact PortTables.accepts_ofPortGraph _ _ _ x a b

end MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

namespace MinUncutGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

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

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

abbrev Vertex (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :=
  PaddedDart (GraphTables.semantics t) (fun v => Fin (padding v))

def vertexCount (t : GraphTables.Table) (padding : Fin t.vertices → Nat) : Nat :=
  t.darts + ∑ v, padding v

def vertexOrder (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :
    Vertex t padding ≃ Fin (vertexCount t padding) :=
  (Equiv.sumCongr (Equiv.refl _) (paddingOrder padding)).trans finSumFinEquiv

@[simp] theorem vertexOrder_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    (vertexOrder t padding (Sum.inl e)).val = e.val := rfl

@[simp] theorem vertexOrder_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (z : Σ v, Fin (padding v)) :
    (vertexOrder t padding (Sum.inr z)).val =
      t.darts + (paddingOrder padding z).val := rfl

def cloudGraphs (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) (v : Fin t.vertices) :
    PortGraph (Cloud (paddedGraph (GraphTables.semantics t)
      (fun w => Fin (padding w))) v) (Fin q) :=
  GraphTransport.reindex (ExpanderTables.graph (tables v))
    (PreprocessingCloudIndex.paddedCloudEquiv t padding v).symm (Equiv.refl _)

def sourcePortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Vertex t padding) (Fin q ⊕ Unit) :=
  paddedReplacementPortGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def sourceGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    ConstraintGraph (Vertex t padding) (Vertex t padding × (Fin q ⊕ Unit))
      GraphTables.Label :=
  paddedReplacementGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def numberedPortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Fin (vertexCount t padding)) (Fin (q + 1)) :=
  GraphTransport.reindex (sourcePortGraph t padding tables)
    (vertexOrder t padding) (portOrder q)

def numberedAccepts (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1))
    (a b : GraphTables.Label) : Bool :=
  (sourceGraph t padding tables).accepts
    ((vertexOrder t padding).symm e.1, (portOrder q).symm e.2) a b

theorem numberedAccepts_transpose (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1)) (a b : GraphTables.Label) :
    numberedAccepts t padding tables ((numberedPortGraph t padding tables).rot e) b a =
      numberedAccepts t padding tables e a b := by
  obtain ⟨z, rfl⟩ := (Equiv.prodCongr (vertexOrder t padding) (portOrder q)).surjective e
  rcases z with ⟨v, p⟩
  simp only [numberedPortGraph, Equiv.prodCongr_apply, Prod.map_apply,
    GraphTransport.reindex_rot, numberedAccepts, Equiv.symm_apply_apply]
  exact (sourceGraph t padding tables).reverse_accepts (v, p) a b

def ofCloudTables (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortTables.Table (vertexCount t padding) (q + 1) :=
  PortTables.ofPortGraph (numberedPortGraph t padding tables)
    (numberedAccepts t padding tables) (numberedAccepts_transpose t padding tables)

@[simp] theorem rotation_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) =
      (vertexOrder t padding ((sourcePortGraph t padding tables).rot (v, p)).1,
        portOrder q ((sourcePortGraph t padding tables).rot (v, p)).2) := by
  rw [ofCloudTables, PortTables.rotation_ofPortGraph]
  exact GraphTransport.reindex_rot _ _ _ _ _

@[simp] theorem accepts_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) a b =
      (sourceGraph t padding tables).accepts (v, p) a b := by
  simp only [ofCloudTables, PortTables.accepts_ofPortGraph,
    numberedAccepts, Equiv.symm_apply_apply]

@[simp] theorem accepts_internal (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q (Sum.inl p)) a b = decide (a = b) := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin t.darts) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inl e), portOrder q (Sum.inr ())) a b =
      GraphTables.acceptsAt t.rows e a b := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (z : Σ v, Fin (padding v)) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inr z), portOrder q (Sum.inr ())) a b = true := by
  rw [accepts_ofCloudTables]
  rfl

end MinUncutGames.Foundations.PCP.PreprocessingRegularTables

namespace MinUncutGames.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

end MinUncutGames.Foundations.PCP.VertexPadding

namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

def sumGraph (table : Table n d) (m : Nat) :
    ConstraintGraph (Fin n ⊕ Fin (m - n))
      ((Fin n ⊕ Fin (m - n)) × Fin d) Label :=
  VertexPadding.pad (baseGraph table) (m - n)

def paddedGraph (table : Table n d) (h : n ≤ m) :
    ConstraintGraph (Fin m) (Fin m × Fin d) Label where
  reverse := ((dartEquiv h).symm.trans (sumGraph table m).reverse).trans (dartEquiv h)
  reverse_involutive e := by
    change dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h ((sumGraph table m).reverse
        ((dartEquiv h).symm e))))) = e
    rw [Equiv.symm_apply_apply, (sumGraph table m).reverse_involutive,
      Equiv.apply_symm_apply]
  tail := Prod.fst
  accepts e a b := (sumGraph table m).accepts ((dartEquiv h).symm e) a b
  reverse_accepts e a b := by
    change (sumGraph table m).accepts ((dartEquiv h).symm
      (dartEquiv h ((sumGraph table m).reverse ((dartEquiv h).symm e)))) b a = _
    rw [Equiv.symm_apply_apply]
    exact (sumGraph table m).reverse_accepts _ _ _

theorem paddedGraph_reverse_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).reverse (dartEquiv h e) =
      dartEquiv h ((sumGraph table m).reverse e) := by
  change dartEquiv h ((sumGraph table m).reverse
    ((dartEquiv h).symm (dartEquiv h e))) = _
  rw [Equiv.symm_apply_apply]

theorem paddedGraph_accepts_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) (a b : Label) :
    (paddedGraph table h).accepts (dartEquiv h e) a b =
      (sumGraph table m).accepts e a b := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e)) a b = _
  rw [Equiv.symm_apply_apply]

def pad (table : Table n d) (h : n ≤ m) : Table m d :=
  ofPortGraph
    { rot := (paddedGraph table h).reverse
      rot_involutive := (paddedGraph table h).reverse_involutive }
    (paddedGraph table h).accepts (paddedGraph table h).reverse_accepts

@[simp] theorem rotation_pad (table : Table n d) (h : n ≤ m) (e : Fin m × Fin d) :
    rotation (pad table h) e = (paddedGraph table h).reverse e := by
  exact rotation_ofPortGraph _ _ _ e

@[simp] theorem accepts_pad (table : Table n d) (h : n ≤ m)
    (e : Fin m × Fin d) (a b : Label) :
    PortTables.accepts (pad table h) e a b = (paddedGraph table h).accepts e a b := by
  exact accepts_ofPortGraph _ _ _ e a b

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem baseGraph_pad (table : Table n d) (h : n ≤ m) :
    baseGraph (pad table h) = paddedGraph table h := by
  apply constraintGraph_ext
  · exact rotation_pad table h
  · rfl
  · funext e a b
    exact accepts_pad table h e a b

theorem rotation_pad_equiv (table : Table n d) (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h v, p) =
      (vertexEquiv h ((sumGraph table m).reverse (v, p)).1,
        ((sumGraph table m).reverse (v, p)).2) := by
  rw [rotation_pad]
  exact paddedGraph_reverse_equiv table h (v, p)

@[simp] theorem rotation_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    rotation (pad table h) (v.castLE h, p) =
      ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inl, baseGraph_reverse,
    vertexEquiv_inl] using rotation_pad_equiv table h (Sum.inl v) p

@[simp] theorem rotation_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h (Sum.inr v), p) =
      (vertexEquiv h (Sum.inr v), p) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inr] using
    rotation_pad_equiv table h (Sum.inr v) p

@[simp] theorem accepts_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (v.castLE h, p) a b = PortTables.accepts table (v, p) a b := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inl v, p) a b

@[simp] theorem accepts_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (vertexEquiv h (Sum.inr v), p) a b = true := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inr v, p) a b

theorem paddedGraph_edgeSatisfied_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e))
    (labeling (dartEquiv h e).1)
    (labeling (dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h e)))).1) =
    (sumGraph table m).accepts e (labeling (vertexEquiv h e.1))
      (labeling (vertexEquiv h ((sumGraph table m).reverse e).1))
  simp only [Equiv.symm_apply_apply]
  rfl

theorem edgeSatisfied_pad_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  rw [baseGraph_pad]
  exact paddedGraph_edgeSatisfied_equiv table h labeling e

@[simp] theorem edgeSatisfied_pad_old (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin n) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (v.castLE h, p) =
      (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) (v, p) := by
  simpa only [dartEquiv_apply, vertexEquiv_inl, sumGraph,
    VertexPadding.edgeSatisfied_inl (baseGraph table) rfl] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inl v, p)

@[simp] theorem edgeSatisfied_pad_new (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin (m - n)) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (vertexEquiv h (Sum.inr v), p) = true := by
  simpa only [dartEquiv_apply, sumGraph, VertexPadding.edgeSatisfied_inr] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inr v, p)

end MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

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
namespace MinUncutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

end MinUncutGames.Foundations.PCP.PoweringLabels

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
namespace MinUncutGames.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end MinUncutGames.Foundations.PCP.PoweringReach

end
section
namespace MinUncutGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach

variable {V D A : Type*}

def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

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
namespace MinUncutGames.Foundations.PCP.GenericGraphTables

open MinUncutGames.Foundations.Complexity

variable {q : Nat}

def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

end MinUncutGames.Foundations.PCP.GenericGraphTables

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

noncomputable section

namespace MinUncutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MinUncutGames.Foundations.Hastad

def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

end MinUncutGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetReduction
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AlphabetReduction

open MinUncutGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev InputCoordinate (A : Type*) := Bool × Cube A

end MinUncutGames.Foundations.PCP.AlphabetReduction

end
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

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

end MinUncutGames.Foundations.PCP.AlphabetGraph

end
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Enumeration

open MinUncutGames.Foundations.Hastad
open scoped BigOperators

def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

end MinUncutGames.Foundations.PCP.AlphabetTable.Enumeration

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Queries

open MinUncutGames.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

end MinUncutGames.Foundations.PCP.AlphabetTable.Queries

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

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

def relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable :=
  GraphTables.relationOf fun a b =>
    predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
      slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)

@[simp] theorem relationAt_relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot orientation) a b =
      predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
        slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  exact GraphTables.relationAt_relationOf _ _ _

@[simp] theorem oldPredicate_relationAt (old : GraphTables.RelationTable)
    (a b : GraphTables.Label) : oldPredicate old a b = GraphTables.relationAt old a b := rfl

end MinUncutGames.Foundations.PCP.AlphabetTable.Relations

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

abbrev Vertex (F : Formula) := (Fin F.«variables» ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.«variables» + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end MinUncutGames.Foundations.PCP.InitialGraph

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

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

end MinUncutGames.Foundations.PCP.RawInitialTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialPredicate
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

end MinUncutGames.Foundations.PCP.RawInitialRows

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
namespace MinUncut.Costed.Arena
open Turing.ToPartrec

def Extends (h h' : Heap) : Prop := ∃g,h'=g++h
lemma Extends.refl (h : Heap) : Extends h h := ⟨[],rfl⟩
lemma Extends.cons (h : Heap) (n : Node) : Extends h (n::h) := ⟨[n],rfl⟩
lemma Extends.trans {h h' h''} (he : Extends h h') (he' : Extends h' h'') : Extends h h'' := by
  obtain ⟨a,rfl⟩ := he
  obtain ⟨b,rfl⟩ := he'
  exact ⟨b++a,(List.append_assoc _ _ _).symm⟩
lemma Extends.read {h h'} (he : Extends h h') (p : ℕ) (hp : p≤h.length) (j : Fin 4) :
    read h' p j=read h p j := by
  obtain ⟨a,rfl⟩ := he
  induction a with
  | nil => rfl
  | cons n a ih =>
    rw [List.cons_append,read_old (a++h) n p (by simp; omega),ih]
lemma ListRep.mono {h h' p v} (hv : ListRep h p v) (he : Extends h h') : ListRep h' p v := by
  obtain ⟨a,rfl⟩ := he
  exact hv.prepend a
lemma CodeAt.mono {h h' p c} (hc : CodeAt h p c) (he : Extends h h') : CodeAt h' p c := by
  obtain ⟨a,rfl⟩ := he
  exact hc.prepend a

def Trace (s s' : State) (n : ℕ) : Prop := State.tick^[n] s=s'
lemma Trace.one {s s'} (he : s.tick=s') : Trace s s' 1 := he
lemma Trace.trans {s s' s'' n m} (h : Trace s s' n) (h' : Trace s' s'' m) :
    Trace s s'' (n+m) := by
  unfold Trace at *
  rw [Nat.add_comm n m,Function.iterate_add_apply,h,h']

def Simulates (c : Code) (v w : List ℕ) (B : ℕ) : Prop :=
  ∀h pc env kont,CodeAt h pc c → ListRep h env v →
    ∃h' out n,n≤B ∧ Extends h h' ∧ ListRep h' out w ∧
      Trace ⟨0,pc,env,kont,h⟩ ⟨1,0,out,kont,h'⟩ n

lemma simulate_zero (v : List ℕ) : Simulates .zero' v (0::v) 1 := by
  intro h pc env k hc hv
  cases hc with
  | zero hp hb ht =>
    refine ⟨node 0 env 0 0::h,h.length+1,1,le_rfl,Extends.cons h _,hv.push 0,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true]

lemma simulate_succ (v : List ℕ) : Simulates .succ v [v.headI+1] 1 := by
  intro h pc env k hc hv
  cases hc with
  | succ hp hb ht =>
    refine ⟨node (v.headI+1) 0 0 0::h,h.length+1,1,le_rfl,Extends.cons h _,ListRep.nil.push _,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true,hv.head]

lemma simulate_tail (v : List ℕ) : Simulates .tail v v.tail 1 := by
  intro h pc env k hc hv
  cases hc with
  | tail hp hb ht =>
    refine ⟨h,read h env 1,1,le_rfl,Extends.refl h,hv.tail,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true]

lemma simulate_comp {f g v u w A B} (hg : Simulates g v u A) (hf : Simulates f u w B) :
    Simulates (.comp f g) v w (A+B+2) := by
  intro h pc env k hc hv
  cases hc with
  | comp hp hb ht hcf hcg =>
    let frame := node 2 (read h pc 1) 0 k
    let h₁ := frame::h
    have hv₁ : ListRep h₁ env v := hv.extend frame
    have hc₁ := hcg.extend frame
    obtain ⟨h₂,out,n,hn,he,ho,htrace⟩ := hg h₁ (read h pc 2) env (h.length+1) hc₁ hv₁
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have hs : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 2,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have hs' : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,read h pc 1,out,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_one,node_three]
    obtain ⟨h₃,out',m,hm,he',ho',htrace'⟩ := hf h₂ (read h pc 1) out k (hcf.mono hh) ho
    refine ⟨h₃,out',1+n+1+m,by omega,hh.trans he',ho',?_⟩
    exact ((hs.trans htrace).trans hs').trans htrace'

lemma simulate_caseZero {f g v w A} (hz : v.headI=0) (hf : Simulates f v.tail w A) :
    Simulates (.case f g) v w (A+1) := by
  intro h pc env k hc hv
  cases hc with
  | case hp hb ht hcf hcg =>
    obtain ⟨h',out,n,hn,he,ho,tr⟩ := hf h (read h pc 1) (read h env 1) k hcf hv.tail
    refine ⟨h',out,1+n,by omega,he,ho,(Trace.one ?_).trans tr⟩
    simp only [State.tick,ht,ite_true,hv.head,hz]

lemma simulate_caseSucc {f g v a w A} (hg : Simulates g (a::v) w A) :
    Simulates (.case f g) ((a+1)::v) w (A+1) := by
  intro h pc env k hc hv
  cases hc with
  | case hp hb ht hcf hcg =>
    let cell := node a (read h env 1) 0 0
    have hh := hv.tail.push a
    obtain ⟨h',out,n,hn,he,ho,tr⟩ := hg (cell::h) (read h pc 2) (h.length+1) k
      (hcg.extend cell) hh
    refine ⟨h',out,1+n,by omega,(Extends.cons h cell).trans he,ho,(Trace.one ?_).trans tr⟩
    simp only [State.tick,ht,ite_true,hv.head,List.headI_cons,show a+1≠0 by omega,ite_false,
      Nat.add_sub_cancel,cell]

end MinUncut.Costed.Arena

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeContinuations
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena
open Turing.ToPartrec

lemma simulate_cons {f fs v u w A B} (hf : Simulates f v u A) (hfs : Simulates fs v w B) :
    Simulates (.cons f fs) v (u.headI::w) (A+B+3) := by
  intro h pc env k hc hv
  cases hc with
  | cons hp hb ht hcf hcfs =>
    let frame₁ := node 0 (read h pc 2) env k
    let h₁ := frame₁::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame₁) (hv.extend frame₁)
    have hh : Extends h h₂ := (Extends.cons h frame₁).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame₁ j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame₁]
    let frame₂ := node 1 u.headI 0 k
    let h₃ := frame₂::h₂
    have hh₃ : Extends h h₃ := hh.trans (Extends.cons h₂ frame₂)
    have next : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,read h pc 2,env,h₂.length+1,h₃⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame₁,node_zero,node_one,node_two,node_three,
        ho.head,h₃,frame₂]
    obtain ⟨h₄,out',m,hm,he',ho',tr'⟩ := hfs h₃ (read h pc 2) env (h₂.length+1)
      (hcfs.mono hh₃) (hv.mono hh₃)
    have hr' (j : Fin 4) : read h₄ (h₂.length+1) j=frame₂ j := by
      rw [he'.read _ (by simp [h₃]),read_new]
    let h₅ := node u.headI out' 0 0::h₄
    have finish : Trace ⟨1,0,out',h₂.length+1,h₄⟩ ⟨1,0,h₄.length+1,k,h₅⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h₂.length+1≠0 by omega,hr',frame₂,node_zero,node_one,node_three,h₅]
    refine ⟨h₅,h₄.length+1,1+n+1+m+1,by omega,
      hh₃.trans (he'.trans (Extends.cons h₄ _)),ho'.push _,?_⟩
    exact (((start.trans tr).trans next).trans tr').trans finish

lemma simulate_fixDone {f v u A} (hf : Simulates f v u A) (hz : u.headI=0) :
    Simulates (.fix f) v u.tail (A+2) := by
  intro h pc env k hc hv
  cases hc with
  | fix hp hb ht hcf =>
    let frame := node 3 pc 0 k
    let h₁ := frame::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame) (hv.extend frame)
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have finish : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨1,0,read h₂ out 1,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_three,ho.head,hz]
    exact ⟨h₂,read h₂ out 1,1+n+1,by omega,hh,ho.tail,(start.trans tr).trans finish⟩

lemma simulate_fixMore {f v u a w A B} (hf : Simulates f v ((a+1)::u) A)
    (hfix : Simulates (.fix f) u w B) : Simulates (.fix f) v w (A+B+2) := by
  intro h pc env k hc hv
  have hc₀ := hc
  cases hc with
  | fix hp hb ht hcf =>
    let frame := node 3 pc 0 k
    let h₁ := frame::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame) (hv.extend frame)
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have next : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,pc,read h₂ out 1,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_one,node_three,ho.head,
        List.headI_cons,show a+1≠0 by omega]
    obtain ⟨h₃,out',m,hm,he',ho',tr'⟩ := hfix h₂ pc (read h₂ out 1) k (hc₀.mono hh) ho.tail
    exact ⟨h₃,out',1+n+1+m,by omega,hh.trans he',ho',((start.trans tr).trans next).trans tr'⟩

lemma Simulates.mono {c v w A B} (h : Simulates c v w A) (hAB : A≤B) : Simulates c v w B := by
  intro heap pc env k hc hv
  obtain ⟨h',out,n,hn,he,ho,tr⟩ := h heap pc env k hc hv
  exact ⟨h',out,n,hn.trans hAB,he,ho,tr⟩

lemma CodeRun.simulates {c v w t} (h : CodeRun c v w t) : Simulates c v w (3*t) := by
  induction h with
  | zero v => exact (simulate_zero v).mono (by omega)
  | succ v => exact (simulate_succ v).mono (by omega)
  | tail v => exact (simulate_tail v).mono (by omega)
  | cons _ _ ih ih' => exact (simulate_cons ih ih').mono (by omega)
  | comp _ _ ih ih' => exact (simulate_comp ih ih').mono (by omega)
  | caseZero hz _ ih => exact (simulate_caseZero hz ih).mono (by omega)
  | caseSucc _ ih => exact (simulate_caseSucc ih).mono (by omega)
  | fixDone _ hz ih => exact (simulate_fixDone ih hz).mono (by omega)
  | fixMore _ _ ih ih' => exact (simulate_fixMore ih ih').mono (by omega)

open Turing.ToPartrec

def listCells : List ℕ → Heap → ℕ × Heap
  | [],h => (0,h)
  | a::v,h =>
    let r := listCells v h
    (r.2.length+1,node a r.1 0 0::r.2)

lemma listCells_spec (v : List ℕ) (h : Heap) :
    Extends h (listCells v h).2 ∧ ListRep (listCells v h).2 (listCells v h).1 v := by
  induction v with
  | nil => exact ⟨Extends.refl h,ListRep.nil⟩
  | cons a v ih =>
    exact ⟨ih.1.trans (Extends.cons _ _),ih.2.push a⟩

def initialState (c : Code) (v : List ℕ) (base : Heap := []) : State :=
  let hc := codeCells c base.length++base
  let r := listCells v hc
  ⟨0,base.length+(codeCells c base.length).length,r.1,0,r.2⟩

lemma initialState_spec (c : Code) (v : List ℕ) (base : Heap) :
    CodeAt (initialState c v base).heap (initialState c v base).pc c ∧
    ListRep (initialState c v base).heap (initialState c v base).env v := by
  exact ⟨(codeCells_spec c base).mono (listCells_spec v _).1,(listCells_spec v _).2⟩

lemma State.tick_halted (pc env k : ℕ) (h : Heap) :
    (State.mk 2 pc env k h).tick=State.mk 2 pc env k h := by
  simp [State.tick]

lemma Trace.pad_halted {s : State} (env : ℕ) (h : Heap) {n B : ℕ}
    (ht : Trace s ⟨2,0,env,0,h⟩ n) (hn : n≤B) : Trace s ⟨2,0,env,0,h⟩ B := by
  have hs : ∀i,State.tick^[i] (State.mk 2 0 env 0 h)=State.mk 2 0 env 0 h := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply',ih,State.tick_halted]
  have hh := ht.trans (show Trace (State.mk 2 0 env 0 h) _ (B-n) from hs (B-n))
  simpa only [Nat.add_sub_of_le hn] using hh

lemma CodeRun.interpreted {c v w t} (hr : CodeRun c v w t) (base : Heap) {B : ℕ} (hB : t≤B) :
    ∃h out,ListRep h out w ∧
      rawTick^[3*B+1] (initialState c v base).encode=(State.mk 2 0 out 0 h).encode := by
  have hi := initialState_spec c v base
  obtain ⟨h,out,n,hn,he,ho,tr⟩ := CodeRun.simulates hr _ _ _ 0 hi.1 hi.2
  have last : Trace (State.mk 1 0 out 0 h) (State.mk 2 0 out 0 h) 1 := by
    apply Trace.one
    simp [State.tick]
  have tr' := (tr.trans last).pad_halted out h (by omega : n+1≤3*B+1)
  refine ⟨h,out,ho,?_⟩
  have interp (s : State) (i : ℕ) : rawTick^[i] s.encode=(State.tick^[i] s).encode := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply',ih,rawTick_encode,Function.iterate_succ_apply']
  rw [interp]
  exact congrArg State.encode tr'

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_HeapInitializationMath
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.Arena
open Turing.ToPartrec

lemma words_append (h g : Heap) : words (h++g)=words h++words g := by
  simp only [words,List.flatMap_append]

def groupWords (v : List ℕ) : Heap :=
  (List.range (v.length/4)).map (fun i j=>((v.drop (4*i+j.val)).headI))
lemma groupWords_length (v : List ℕ) : (groupWords v).length=v.length/4 := by
  simp [groupWords]
lemma groupWords_words (v : List ℕ) (h : 4∣v.length) : words (groupWords v)=v := by
  apply List.ext_getElem
  · simp only [length_words,groupWords_length]
    omega
  · intro i hi hv
    have hq : i/4<v.length/4 := by omega
    have hr : i%4<4 := Nat.mod_lt _ (by decide)
    have hat:=words_at (groupWords v) (i/4) ⟨i%4,hr⟩
    have he : 4*(i/4)+i%4=i := by omega
    rw [he,List.drop_eq_getElem_cons hi] at hat
    simp only [List.headI_cons] at hat
    rw [hat]
    have hn : i/4<(groupWords v).length := by simpa only [groupWords_length] using hq
    rw [List.drop_eq_getElem_cons hn,List.headD_cons]
    simp only [groupWords]
    erw [List.getElem_map,List.getElem_range]
    rw [he,List.drop_eq_getElem_cons hv]
    rfl

end MinUncut.Costed.Arena

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FiberPrefix
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena

def dataCells (v : List ℕ) (b : ℕ) : Heap :=
  (List.range v.length).map (fun i=> node ((v.drop i).headI)
    (if i+1=v.length then 0 else b+v.length-i-1) 0 0)
lemma dataCells_length (v : List ℕ) (b : ℕ) : (dataCells v b).length=v.length := by simp [dataCells]
end MinUncut.Costed.Arena

namespace MinUncut.Costed.Arena.Init
open Turing.ToPartrec

def input (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  (codeCells c 0).length::(words (codeCells c 0)++K::rest.length::xs.length::(xs.reverse++rest))

lemma input_drop (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (input c xs K rest).drop (4*(codeCells c 0).length+1)=K::rest.length::xs.length::(xs.reverse++rest) := by
  simp only [input,List.drop_succ_cons]
  rw [←length_words,List.drop_left]
lemma input_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (input c xs K rest).length=4*(codeCells c 0).length+4+xs.length+rest.length := by
  simp only [input,List.length_cons,List.length_append,length_words,List.length_reverse]; omega

def canvas (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  [(codeCells c 0).length,xs.length,(input c xs K rest).length,0]++quadruple (input c xs K rest)
lemma canvas_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (canvas c xs K rest).length=4*((input c xs K rest).length+1) := by
  simp only [canvas,List.length_append,List.length_cons,List.length_nil,quadruple_length]; omega
lemma canvas_drop (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (canvas c xs K rest).drop (4+(input c xs K rest).length)=
      input c xs K rest++(input c xs K rest).reverse++input c xs K rest := by
  simp only [canvas,quadruple]
  rw [←List.drop_drop]
  simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]
  rw [List.append_assoc,List.append_assoc,show (input c xs K rest).length=(input c xs K rest).reverse.length from List.length_reverse.symm,List.drop_left]
  simp only [List.append_assoc]
lemma canvas_at (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<(input c xs K rest).length) :
    ((canvas c xs K rest).drop (4+(input c xs K rest).length+i)).headI=
      ((input c xs K rest).drop i).headI := by
  rw [←List.drop_drop,canvas_drop]
  rw [List.append_assoc,List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

open Turing.ToPartrec

def baseLength (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : ℕ :=
  (codeCells c 0).length+xs.length+(input c xs K rest).length+1
lemma cExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    cExpr.eval (i::canvas c xs K rest)=(codeCells c 0).length := rfl
lemma mExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    mExpr.eval (i::canvas c xs K rest)=xs.length := rfl
lemma lExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    lExpr.eval (i::canvas c xs K rest)=(input c xs K rest).length := rfl
lemma iExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    iExpr.eval (i::canvas c xs K rest)=i := rfl
lemma bExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    bExpr.eval (i::canvas c xs K rest)=baseLength c xs K rest := rfl

lemma rawCell_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i-xs.length<(codeCells c 0).length) (j : Fin 4) :
    (rawCell j.val).eval (i::canvas c xs K rest)=
      (((codeCells c 0).drop (i-xs.length)).headD (fun _=>0)) j := by
  simp only [rawCell,AExpr.eval,lExpr_eval,iExpr_eval,mExpr_eval]
  rw [show (input c xs K rest).length+6+4*(i-xs.length)+j.val=
    (4+(input c xs K rest).length+(1+4*(i-xs.length)+j.val))+1 by omega,List.drop_succ_cons]
  rw [canvas_at c xs K rest _ (by rw [input_length]; omega)]
  rw [show 1+4*(i-xs.length)+j.val=(4*(i-xs.length)+j.val)+1 by omega]
  simp only [input,List.drop_succ_cons]
  rw [at_append _ _ _ (by rw [length_words]; omega),words_at]

lemma rawData_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<xs.length) :
    rawData.eval (i::canvas c xs K rest)=xs[i] := by
  simp only [rawData,AExpr.eval,lExpr_eval,iExpr_eval,mExpr_eval,cExpr_eval]
  rw [show (input c xs K rest).length+4*(codeCells c 0).length+9+(xs.length-1-i)=
    (4+(input c xs K rest).length+(4*(codeCells c 0).length+4+(xs.length-1-i)))+1 by omega,List.drop_succ_cons]
  rw [canvas_at c xs K rest _ (by rw [input_length]; omega)]
  rw [show 4*(codeCells c 0).length+4+(xs.length-1-i)=
    (4*(codeCells c 0).length+1)+(3+(xs.length-1-i)) by omega,←List.drop_drop,input_drop]
  simp only [show 3+(xs.length-1-i)=(xs.length-1-i)+3 by omega,
    List.drop_succ_cons]
  have hr : xs.length-1-i<xs.reverse.length := by simp only [List.length_reverse]; omega
  rw [at_append _ _ _ hr,List.drop_eq_getElem_cons hr]
  simp only [List.headI_cons,List.getElem_reverse]
  congr 1
  omega

lemma pointerExpr_eval (a : AExpr) (v : List ℕ) :
    (pointerExpr a).eval v=rebasePointer (bExpr.eval v) (a.eval v) := by
  simp only [pointerExpr,AExpr.eval,rebasePointer]
  by_cases h : a.eval v=0 <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]

lemma row_data (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<xs.length) :
    Blocks.block rowExpressions i (canvas c xs K rest)=
      [xs[i],if i+1=xs.length then 0 else baseLength c xs K rest+(codeCells c 0).length+xs.length-i-1,0,0] := by
  have hdata : isData.eval (i::canvas c xs K rest)=1 := by
    simp only [isData,AExpr.eval,iExpr_eval,mExpr_eval]
    exact ite_eq_left (by omega)
  have hp : dataPointer.eval (i::canvas c xs K rest)=
      if i+1=xs.length then 0 else baseLength c xs K rest+(codeCells c 0).length+xs.length-i-1 := by
    unfold dataPointer
    by_cases h : i+1=xs.length <;>
      simp only [AExpr.eval,iExpr_eval,mExpr_eval,cExpr_eval,bExpr_eval,h,ite_true,ite_false,Nat.one_ne_zero]
  simp only [Blocks.block,rowExpressions,List.map_cons,List.map_nil,AExpr.eval,hdata,
    Nat.one_ne_zero,ite_false,rawData_eval c xs K rest i hi,hp]
lemma row_code (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hm : xs.length ≤ i) (hi : i-xs.length<(codeCells c 0).length) :
    Blocks.block rowExpressions i (canvas c xs K rest)=
      List.ofFn (rebaseNode (baseLength c xs K rest)
        (((codeCells c 0).drop (i-xs.length)).headD (fun _=>0))) := by
  have hd : isData.eval (i::canvas c xs K rest)=0 := by
    simp only [isData,AExpr.eval,iExpr_eval,mExpr_eval]
    exact ite_eq_right (by omega)
  have h0 := rawCell_eval c xs K rest i hi (0:Fin 4)
  have h1 := rawCell_eval c xs K rest i hi (1:Fin 4)
  have h2 := rawCell_eval c xs K rest i hi (2:Fin 4)
  have h3 := rawCell_eval c xs K rest i hi (3:Fin 4)
  change (rawCell 0).eval (i::canvas c xs K rest)=_ at h0
  change (rawCell 1).eval (i::canvas c xs K rest)=_ at h1
  change (rawCell 2).eval (i::canvas c xs K rest)=_ at h2
  change (rawCell 3).eval (i::canvas c xs K rest)=_ at h3
  simp only [Blocks.block,rowExpressions,List.map_cons,List.map_nil,AExpr.eval,hd,ite_true,
    pointerExpr_eval,h0,h1,h2,h3,bExpr_eval]
  rfl

open Turing.ToPartrec

def newHeap (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : Heap :=
  dataCells xs (baseLength c xs K rest+(codeCells c 0).length)++
    codeCells c (baseLength c xs K rest)

lemma countRows_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    countRows.eval (canvas c xs K rest)=(codeCells c 0).length+xs.length := rfl

lemma map_drop_head (h : Heap) :
    (List.range h.length).map (fun i=>(h.drop i).headD (fun _=>0))=h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    rw [List.drop_eq_getElem_cons hj]
    rfl

lemma emitted_data (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (List.range xs.length).flatMap (fun i=>Blocks.block rowExpressions i (canvas c xs K rest))=
      words (dataCells xs (baseLength c xs K rest+(codeCells c 0).length)) := by
  simp only [words,dataCells,List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  have hi' : i<xs.length := List.mem_range.mp hi
  rw [row_data c xs K rest i hi',List.drop_eq_getElem_cons hi']
  rfl

lemma emitted_code (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (List.range (codeCells c 0).length).flatMap
      (fun i=>Blocks.block rowExpressions (xs.length+i) (canvas c xs K rest))=
      words (codeCells c (baseLength c xs K rest)) := by
  have he := codeCells_rebase c 0 (baseLength c xs K rest)
  simp only [Nat.zero_add] at he
  conv_rhs => rw [he,←map_drop_head (codeCells c 0)]
  simp only [words,List.map_map,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  have hi' : i<(codeCells c 0).length := List.mem_range.mp hi
  convert row_code c xs K rest (xs.length+i) (by omega) (by omega) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.add_sub_cancel_left]

lemma emitted_spec (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    Blocks.emitted rowExpressions (countRows.eval (canvas c xs K rest)) (canvas c xs K rest)=
      words (newHeap c xs K rest) := by
  rw [countRows_eval,show (codeCells c 0).length+xs.length=xs.length+(codeCells c 0).length by omega]
  simp only [Blocks.emitted,List.range_add,List.flatMap_append,List.flatMap_map]
  rw [emitted_data,emitted_code,newHeap,words_append]

lemma newHeap_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (newHeap c xs K rest).length=(codeCells c 0).length+xs.length := by
  simp only [newHeap,List.length_append,dataCells_length,codeCells_length_eq c (baseLength c xs K rest) 0]
  omega

open Turing.ToPartrec

def oldWords (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  Blocks.retained rowExpressions (countRows.eval (canvas c xs K rest)) (canvas c xs K rest)
def base (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : Heap :=
  groupWords (oldWords c xs K rest)
lemma oldWords_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (oldWords c xs K rest).length=4*baseLength c xs K rest := by
  simp only [oldWords,Blocks.retained,List.length_append,List.length_reverse,emitted_spec,
    length_words,newHeap_length,canvas_length,baseLength]
  omega
lemma base_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (base c xs K rest).length=baseLength c xs K rest := by
  rw [base,groupWords_length,oldWords_length]
  omega
lemma base_words (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    words (base c xs K rest)=oldWords c xs K rest := by
  exact groupWords_words _ (by rw [oldWords_length]; exact dvd_mul_right _ _)
def header : List AExpr := [.const 0,canvasPc,canvasEnv,.const 0,canvasTotal]
lemma canvasPc_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasPc.eval (canvas c xs K rest)=baseLength c xs K rest+(codeCells c 0).length := rfl
lemma canvasTotal_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasTotal.eval (canvas c xs K rest)=baseLength c xs K rest+((codeCells c 0).length+xs.length) := rfl
lemma canvasEnv_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasEnv.eval (canvas c xs K rest)=
      if xs=[] then 0 else baseLength c xs K rest+((codeCells c 0).length+xs.length) := by
  change (if (if xs.length=0 then 1 else 0)=0 then canvasTotal.eval (canvas c xs K rest) else 0)=_
  by_cases h : xs=[]
  · simp only [h,List.length_nil,ite_true,Nat.one_ne_zero,ite_false]
  · have hl : xs.length≠0 := fun hh=>h (List.length_eq_zero_iff.mp hh)
    simp only [hl,ite_false,ite_true,canvasTotal_eval,h]

end MinUncut.Costed.Arena.Init

end OAI
end


