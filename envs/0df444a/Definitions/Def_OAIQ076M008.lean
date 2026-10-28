-- Prove2me | Definitions.Def_OAIQ076M008
-- name    : OAIQ076M008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:04:07.050704+00:00
-- url     : https://prove2.me/theorems/a5244d91-d7c6-40cc-b85b-3cace6c17be0
-- title:
--   Definitions bundle OAIQ076M008 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 251 declarations of OpenAI's Lean: 39 definitions and 212 theorems. The definitions and types are `OAI.MinUncut.Enumeration.encoding`, `OAI.MinUncut.FiniteProof.expanded`, `OAI.MinUncut.GaussianHermite.convolution`, `OAI.MinUncut.GaussianHermite.heSequence`, `OAI.MinUncut.GaussianHermite.noise`, `OAI.MinUncut.GaussianHermite.orthPolyMap`, `OAI.MinUncut.GaussianHermite.parity`, `OAI.MinUncut.GaussianHermite.productHermiteBasis`, `OAI.MinUncut.GaussianHermite.project`, `OAI.MinUncut.GaussianHermite.psiVec`, `OAI.MinUncut.IndependentSquares.restrictLinear`, `OAI.MinUncut.Inner.addConstantArray`, `OAI.MinUncut.Inner.arraySum`, `OAI.MinUncut.Inner.averagedCorrelation`, `OAI.MinUncut.Inner.constantArray`, `OAI.MinUncut.Inner.coupledAnswer`, `OAI.MinUncut.Inner.cylinderArray`, `OAI.MinUncut.Inner.diagonal`, `OAI.MinUncut.Inner.gaussianProject`, `OAI.MinUncut.Inner.jointCoefficient`, `OAI.MinUncut.Inner.pairField`, `OAI.MinUncut.Inner.rowCode`, `OAI.MinUncut.Inner.rowProjectedGradient`, `OAI.MinUncut.Inner.singleRow`, `OAI.MinUncut.Inner.tableCoefficient`, `OAI.MinUncut.Inner.tableMass`, `OAI.MinUncut.PathRealization.demandList`, `OAI.MinUncut.RowNoise.convolutionDualFintype`, `OAI.MinUncut.RowNoise.degree`, `OAI.MinUncut.RowNoise.frequency`, `OAI.MinUncut.RowNoise.jointInner`, `OAI.MinUncut.RowNoise.jointL1`, `OAI.MinUncut.RowNoise.mask`, `OAI.MinUncut.RowNoise.maskRowKernelDualFintype`, `OAI.MinUncut.RowNoise.project`, `OAI.MinUncut.SourceTemplate.keyAddress`, `OAI.MinUncut.SourceTemplate.keyNumber`, `OAI.MinUncutGames.Foundations.Target.Clause.eval`, `OAI.MinUncutGames.Foundations.Target.Literal.eval`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FaceCorrelation`, `MinUncut_Analysis_FreshCorrelation`, `MinUncut_Analysis_GaussNegPreserving`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Analysis_Gradient`, `MinUncut_Analysis_LowGradient`, `MinUncut_Analysis_MaskHermite`, `MinUncut_Analysis_RationalRowNoise`, `MinUncut_Analysis_RowProjectedGradient`, `MinUncut_Analysis_SmoothingRho`, `MinUncut_Encoding_SignatureEncoding`, `MinUncut_Estimates_ArraySum`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_CollisionIndicator`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_CoupledAnswer`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_EuclideanInvariantScore`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_ExpressionOutput`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FaceUpdateSelf`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_MemLpMaskProject`, `MinUncut_Estimates_SecondFailureIndicator`, `MinUncut_Estimates_SelectedProject`, `MinUncut_Estimates_SingleRow`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Games_JointCoefficient`, `MinUncut_Games_JointInner`, `MinUncut_Games_MaskRowKernel`, `MinUncut_Games_Target`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_GraphOutput`, `MinUncut_PCP_ContextClear`, `MinUncut_PCP_Parity`, `MinUncut_Search_FiniteEnumeration`, `MinUncut_Search_TemplateArithmetic`.
--
--   **Imports.** It imports the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002` and `OAIQ076M003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M015`, `OAIQ076M016`, `OAIQ076M017`, `OAIQ076M018`, `OAIQ076M019` and `OAIQ076M020`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003

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
namespace MinUncut.GaussianSmoothing

section FiniteProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma coordinate_memLp_two (i : ι) : MemLp (fun g : ι → ℝ => g i) 2 (gamma ι) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

lemma coordinate_second_moment (i j : ι) :
    (∫ g : ι → ℝ, g i * g j ∂gamma ι) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hm := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    have hs : (∫ x : ℝ, x * x ∂gaussianReal 0 1) = 1 := by
      simpa [variance_id_gaussianReal, integral_id_gaussianReal, sq] using hm.symm
    exact (integral_comp_eval (i := i) (μ := fun _ : ι => gaussianReal 0 1) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => x*x) (gaussianReal 0 1))).trans hs
  · rw [ite_eq_right hij]
    have hi : (fun g : ι → ℝ => g i) ⟂ᵢ[gamma ι] (fun g : ι → ℝ => g j) :=
      (iIndepFun_pi (X := fun (_ : ι) (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)).indepFun hij
    simpa [gamma, integral_eval, integral_id_gaussianReal] using
      hi.integral_mul_eq_mul_integral (coordinate_memLp_two i).aestronglyMeasurable
        (coordinate_memLp_two j).aestronglyMeasurable

end FiniteProduct

lemma gaussian_score_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i, (∫ g, g i * f g ∂gamma ι)^2) ≤ 1 := by
  have hlp : MemLp f 2 (gamma ι) := MemLp.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  refine (integral_bessel (fun i => coordinate_memLp_two i) coordinate_second_moment hlp).trans ?_
  have hs : ∀ x, f x ^ 2 ≤ 1 := fun x => by
    have := hb x
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  simpa using integral_mono_ae (hlp.integrable_sq) (integrable_const (1 : ℝ))
    (ae_of_all _ hs)

end MinUncut.GaussianSmoothing

open scoped BigOperators

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

omit [DecidableEq ι] in
lemma fixedSets_nonempty {k : ℕ} (hk : k ≤ Fintype.card ι) : Nonempty (FixedSets ι k) := by
  obtain ⟨H, _, hH⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hk
  exact ⟨⟨H, hH⟩⟩

end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EuclideanInvariantScore
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

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

lemma query_shift_cancel (x : Point m n) (u : Point m n → ℝ)
    (d : Code m n → ℝ) (t : ℝ) :
    query (u + t • Pi.single x 1)
      (fun z => d z - (Real.sqrt (n^m : ℕ))⁻¹ * t * BinaryFourier.sign (z.val x)) =
      query u d := by
  classical
  funext z
  unfold query
  congr 1
  have hs : (∑ j : Point m n, (u + t • (Pi.single x (1 : ℝ) : Point m n → ℝ)) j * BinaryFourier.sign (z.val j)) =
      (∑ j : Point m n, u j * BinaryFourier.sign (z.val j)) + t*BinaryFourier.sign (z.val x) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hs]
  ring_nf

omit [Fintype A] in
lemma answer_coupled_shift (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) (c g : Point m n → ℝ) (l : Code m n → ℝ)
    (x : Point m n) (t : ℝ) :
    bitSign (f.answer (pullQuery B (c + σ • (g + t • Pi.single x 1))
      (η • (l - t • (fun z : Code m n =>
        σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x)))))) =
    bitSign (f.answer (pullQuery B (c+σ • g) (η • l))) := by
  have hu : c + σ • (g + t • Pi.single x 1) =
      (c+σ • g)+(σ*t) • Pi.single x 1 := by module
  have hl : η • (l - t • (fun z : Code m n =>
        σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x))) =
      (fun z => (η • l) z - (Real.sqrt (n^m : ℕ))⁻¹ * (σ*t) * BinaryFourier.sign (z.val x)) := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  rw [hu, hl]
  congr 1
  congr 1
  funext a
  change query _ _ (labelCode B a) = query _ _ (labelCode B a)
  rw [query_shift_cancel]

def tableCoefficient (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (z : Code m n) : ℝ :=
  η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    l z * bitSign (f.answer (pullQuery B (c+σ • g) (η • l)))
      ∂gauss (Code m n) ∂gauss (Point m n)

end MinUncut.Inner
namespace MinUncut.GaussianSmoothing
open MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integral_split_other (i : ι) {f : (ι → ℝ) → ℝ} (hf : Integrable f (gamma ι)) :
    (∫ g, f g ∂gamma ι) =
    ∫ h, ∫ t, f ((split i).symm (t,h)) ∂gaussianReal 0 1 ∂gamma {j : ι // j ≠ i} := by
  let hm := (split_measurePreserving i).symm (split i)
  rw [← hm.integral_comp' f, integral_prod_symm]
  exact (hm.integrable_comp hf.aestronglyMeasurable).mpr hf
end MinUncut.GaussianSmoothing

namespace MinUncut.GaussianKernel
open MeasureTheory ProbabilityTheory GaussianSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_thresholdTable (T : ι → ℝ) (η : ℝ) :
    Measurable (thresholdTable T η) := by
  apply Measurable.of_eval
  intro z
  apply measurable_to_bool
  have heq : (fun l => thresholdTable T η l z) ⁻¹' {true} = {l : ι → ℝ | 0 ≤ T z + η*l z} := by
    ext l
    simp [thresholdTable]
  rw [heq]
  exact measurableSet_le measurable_const (by fun_prop)

lemma measurable_tableSensitivity (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) :
    Measurable (tableSensitivity H T η z) := by
  let D : (ι → Bool) → ℝ := fun P =>
    if H (Function.update P z true) = H (Function.update P z false) then 0 else 1
  exact (measurable_of_finite D).comp (measurable_thresholdTable T η)

lemma tableSensitivity_integrable (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) :
    Integrable (tableSensitivity H T η z) (gamma ι) :=
  (integrable_const (1 : ℝ)).mono' (measurable_tableSensitivity H T η z).aestronglyMeasurable
    (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using tableSensitivity_abs_le H T η z l)

omit [Fintype ι] in
lemma forced_threshold_split (T : ι → ℝ) (η : ℝ) (z : ι)
    (h : {j : ι // j ≠ z} → ℝ) (t : ℝ) (b : Bool) :
    Function.update (thresholdTable T η ((split z).symm (t,h))) z b =
      Function.update (thresholdTable T η ((split z).symm (0,h))) z b := by
  funext j
  by_cases hj : j = z
  · subst j; simp
  · simp [thresholdTable, split_symm_apply, hj]

omit [Fintype ι] in
lemma tableSensitivity_split (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι)
    (h : {j : ι // j ≠ z} → ℝ) (t : ℝ) :
    tableSensitivity H T η z ((split z).symm (t,h)) =
      tableSensitivity H T η z ((split z).symm (0,h)) := by
  simp only [tableSensitivity, forced_threshold_split T η z h t]

lemma conditional_table_score (H : (ι → Bool) → ℝ) (hH : ∀ P, |H P| ≤ 1)
    (T : ι → ℝ) (η : ℝ) (z : ι) (h : {j : ι // j ≠ z} → ℝ) :
    |∫ t : ℝ, t*H (thresholdTable T η ((split z).symm (t,h))) ∂gaussianReal 0 1| ≤
      tableSensitivity H T η z ((split z).symm (0,h)) := by
  unfold tableSensitivity
  split_ifs with he
  · have hv (t : ℝ) : H (thresholdTable T η ((split z).symm (t,h))) =
        H (Function.update (thresholdTable T η ((split z).symm (0,h))) z true) := by
      rw [equal_forced_value H _ z (by simpa only [forced_threshold_split] using he),
        forced_threshold_split]
    simp only [hv, integral_mul_const, integral_id_gaussianReal, zero_mul, abs_zero, le_refl]
  · apply bounded_scalar_score
    · exact (measurable_of_finite H).comp ((measurable_thresholdTable T η).comp
        ((split z).symm.measurable.comp (show Measurable (fun t : ℝ => (t,h)) by fun_prop)))
    · intro t; exact hH _

theorem table_score_le (H : (ι → Bool) → ℝ) (hH : ∀ P, |H P| ≤ 1)
    (T : ι → ℝ) (η : ℝ) (z : ι) :
    |∫ l : ι → ℝ, l z * H (thresholdTable T η l) ∂gamma ι| ≤
      ∫ l : ι → ℝ, tableSensitivity H T η z l ∂gamma ι := by
  have hf : Measurable (fun l => H (thresholdTable T η l)) :=
    (measurable_of_finite H).comp (measurable_thresholdTable T η)
  have hint : Integrable (fun l : ι → ℝ => l z * H (thresholdTable T η l)) (gamma ι) :=
    (integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using hH _)
  have hsint := tableSensitivity_integrable H T η z
  let hm := (split_measurePreserving z).symm (split z)
  have hi := ((hm.integrable_comp hint.aestronglyMeasurable).mpr hint).integral_prod_right
  have hsi := ((hm.integrable_comp hsint.aestronglyMeasurable).mpr hsint).integral_prod_right
  dsimp only [Function.comp_def] at hi hsi
  rw [integral_split_other z hint, integral_split_other z hsint]
  simp only [split_symm_apply]
  calc
    _ ≤ ∫ h, |∫ t : ℝ, t * H (thresholdTable T η ((split z).symm (t,h)))
        ∂gaussianReal 0 1| ∂gamma {j : ι // j ≠ z} := abs_integral_le_integral_abs
    _ ≤ ∫ h, ∫ t : ℝ, tableSensitivity H T η z ((split z).symm (t,h))
        ∂gaussianReal 0 1 ∂gamma {j : ι // j ≠ z} := by
      apply integral_mono (by simpa [split_symm_apply] using hi.abs) hsi
      intro h
      simpa only [tableSensitivity_split, integral_const, probReal_univ, one_smul]
        using conditional_table_score H hH T η z h
    _ = _ := rfl
end MinUncut.GaussianKernel
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

@[simp] lemma bitSign_eq_iff (b c : Bool) : bitSign b = bitSign c ↔ b = c := by
  cases b <;> cases c <;> norm_num [bitSign]

omit [Fintype A] in
lemma thirdFailure_abs_le (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    |thirdFailure f B η u l z| ≤ 1 := by unfold thirdFailure; split <;> norm_num

lemma query_eq_threshold (η : ℝ) (u : Point m n → ℝ) (l : Code m n → ℝ) :
    query u (η • l) = GaussianKernel.thresholdTable
      (fun z : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) η l := rfl

omit [Fintype A] in
lemma thirdFailure_eq_sensitivity (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdFailure f B η u l z = GaussianKernel.tableSensitivity
      (fun P : Code m n → Bool => bitSign (f.answer (fun a => P (labelCode B a))))
      (fun w : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (w.val x)) η z l := by
  simp only [thirdFailure, GaussianKernel.tableSensitivity, bitSign_eq_iff, query_eq_threshold]
  rfl

omit [Fintype A] in
lemma table_score_le_thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (z : Code m n) :
    |∫ l : Code m n → ℝ, l z * bitSign (f.answer (pullQuery B u (η • l))) ∂gauss (Code m n)| ≤
      ∫ l : Code m n → ℝ, thirdFailure f B η u l z ∂gauss (Code m n) := by
  change |∫ l : Code m n → ℝ, l z * bitSign (f.answer (fun a => query u (η • l) (labelCode B a))) ∂gauss (Code m n)| ≤ _
  simpa only [thirdFailure_eq_sensitivity, query_eq_threshold, gauss, GaussianSmoothing.gamma]
    using GaussianKernel.table_score_le
      (fun P : Code m n → Bool => bitSign (f.answer (fun a => P (labelCode B a))))
      (fun P => by simp only [bitSign_abs, le_refl])
      (fun w : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (w.val x)) η z

def tableMass (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  ∑ z : Code m n, |tableCoefficient f B σ η c z|

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FaceCorrelation
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
namespace MinUncut.Inner
open scoped BigOperators

variable {m n : ℕ}

lemma code_correlation_le (v : Point m n → ℝ) (z : Code m n) :
    |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| ≤ faceCorrelation v := by
  exact Finset.le_sup' (fun w : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (w.val x)|) (Finset.mem_univ z)

lemma faceCorrelation_nonneg (v : Point m n → ℝ) : 0 ≤ faceCorrelation v :=
  (abs_nonneg _).trans (code_correlation_le v 0)

lemma faceCorrelation_le {v : Point m n → ℝ} {a : ℝ}
    (ha : ∀ z : Code m n, |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| ≤ a) :
    faceCorrelation v ≤ a := Finset.sup'_le _ _ (fun z _ => ha z)

lemma faceCorrelation_le_l1 (v : Point m n → ℝ) :
    faceCorrelation v ≤ 𝔼 x : Point m n, |v x| := by
  apply faceCorrelation_le
  intro z
  calc
    _ ≤ 𝔼 x : Point m n, |v x * BinaryFourier.sign (z.val x)| :=
      Finset.abs_expect_le _ _
    _ = _ := by simp only [abs_mul, BinaryFourier.sign_abs, mul_one]

lemma representation_correlation (v : Point m n → ℝ) (μ : Code m n → ℝ) :
    |𝔼 x : Point m n, v x * (∑ z : Code m n, μ z * BinaryFourier.sign (z.val x))| ≤
      (∑ z : Code m n, |μ z|)*faceCorrelation v := by
  simp_rw [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ z : Code m n, |𝔼 x : Point m n, v x * (μ z * BinaryFourier.sign (z.val x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : Code m n, |μ z| * |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| := by
      apply Finset.sum_congr rfl
      intro z _
      simp_rw [mul_left_comm (v _), ← Finset.mul_expect]
      rw [abs_mul]
    _ ≤ ∑ z : Code m n, |μ z| * faceCorrelation v :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (code_correlation_le v z) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end MinUncut.Inner

end

end OAI
end

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

lemma integrable_poly (p : ℝ[X]) : Integrable (fun x => p.eval x) γ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add] using hp.fun_add hq
  | monomial n a =>
    have hn : Integrable (fun x : ℝ => x^n) γ :=
      integrable_pow_of_mem_interior_integrableExpSet (by simp [γ]) n
    simpa only [eval_monomial] using hn.const_mul a

lemma stein_poly (p : ℝ[X]) :
    (∫ x, x * p.eval x ∂γ) = ∫ x, p.derivative.eval x ∂γ := by
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => p.eval x) (v := gaussianPDFReal 0 1)
    (u' := fun x => p.derivative.eval x) (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x) (fun x _ => density_derivative x)
    (by convert (integrable_poly_density (-(X*p))) using 1
        funext x; simp only [Pi.mul_apply, eval_neg, eval_mul, eval_X]; ring)
    (integrable_poly_density p.derivative)
    (integrable_poly_density p)
  have hleft : (∫ x, p.eval x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x, x * p.eval x ∂γ) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_neg]
    congr 1
    funext x
    simp only [smul_eq_mul]
    ring
  rw [hleft] at hi
  rw [integral_gaussianReal_eq_integral_smul (f := fun x => p.derivative.eval x)
    (by norm_num : (1:NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have hr : (∫ x, p.derivative.eval x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * p.derivative.eval x := by
    congr 1; funext x; ring
  rw [hr] at hi
  linarith

lemma derivative_hePoly (n : ℕ) : (hePoly (n+1)).derivative = (n+1 : ℝ) • hePoly n := by
  induction n with
  | zero => simp [hePoly_succ]
  | succ n ih =>
    rw [hePoly_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, hePoly_succ n]
    simp only [Nat.cast_add, Nat.cast_one, smul_eq_C_mul, map_add, map_one]
    ring

lemma hePoly_adjoint (n : ℕ) (p : ℝ[X]) :
    (∫ x, he (n+1) x * p.eval x ∂γ) = ∫ x, he n x * p.derivative.eval x ∂γ := by
  have hi := stein_poly (hePoly n * p)
  have ha : Integrable (fun x => (hePoly n).derivative.eval x * p.eval x) γ := by
    simpa using integrable_poly ((hePoly n).derivative * p)
  have hb : Integrable (fun x => (hePoly n).eval x * p.derivative.eval x) γ := by
    simpa using integrable_poly (hePoly n * p.derivative)
  have hc : Integrable (fun x => x * (hePoly n).eval x * p.eval x) γ := by
    convert integrable_poly (X * hePoly n * p) using 1
    all_goals try with_reducible_and_instances rfl
    funext x; simp only [eval_mul, eval_X]
  simp only [eval_mul, derivative_mul, eval_add] at hi
  rw [integral_add ha hb] at hi
  have heq : (fun x => he (n+1) x * p.eval x) = fun x =>
      x * (hePoly n).eval x * p.eval x - (hePoly n).derivative.eval x * p.eval x := by
    funext x
    rw [← hePoly_eval, hePoly_succ]
    simp [sub_mul]
  rw [heq, integral_sub hc ha]
  simp only [hePoly_eval] at *
  simp only [mul_assoc] at *
  linarith

lemma he_mean_succ (n : ℕ) : (∫ x, he (n+1) x ∂γ) = 0 := by
  simpa using hePoly_adjoint n 1

lemma he_product (n m : ℕ) :
    (∫ x, he n x * he m x ∂γ) = if n = m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [γ]
    | succ m => simp [he_mean_succ]
  | succ n ih =>
    cases m with
    | zero => simp [he_mean_succ]
    | succ m =>
      have h := hePoly_adjoint n (hePoly (m+1))
      rw [derivative_hePoly] at h
      simp only [hePoly_eval, eval_smul, smul_eq_mul] at h
      rw [show (fun x => he n x * ((m+1:ℝ) * he m x)) =
        fun x => (m+1:ℝ) * (he n x * he m x) by funext x; ring,
        integral_const_mul, ih] at h
      rw [h]
      by_cases hnm : n = m
      · subst m; simp [Nat.factorial_succ]
      · simp [hnm]

lemma memLp_poly (p : ℝ[X]) : MemLp (fun x => p.eval x) 2 γ := by
  apply (memLp_two_iff_integrable_sq (p.continuous.aestronglyMeasurable)).mpr
  convert integrable_poly (p^2) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [Polynomial.eval_pow]

lemma memLp_exp (t : ℝ) : MemLp (fun x => Real.exp (t*x)) 2 γ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2*t) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [← Real.exp_nat_mul]
  congr 1
  ring

def heSequence : Polynomial.Sequence ℝ where
  elems' := hePoly
  degree_eq' n := by
    rw [hePoly, (hermite_monic n).degree_map, degree_hermite]

lemma memLp_H (n : ℕ) : MemLp (H n) 2 γ := by
  change MemLp (fun x => he n x / Real.sqrt (n.factorial : ℝ)) 2 γ
  simpa only [ div_eq_mul_inv, hePoly_eval] using (memLp_poly (hePoly n)).mul_const
    (Real.sqrt (n.factorial : ℝ))⁻¹

lemma H_product (n m : ℕ) :
    (∫ x, H n x * H m x ∂γ) = if n = m then 1 else 0 := by
  simp only [H, div_mul_div_comm]
  rw [integral_div, he_product]
  split_ifs with h
  · subst m
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    exact div_self (by positivity)
  · exact zero_div _

section Product
variable {ι : Type*} [Fintype ι]

lemma memLp_polyProd (p : ι → ℝ[X]) :
    MemLp (fun x : ι → ℝ => ∏ i, (p i).eval (x i)) 2 (γpi ι) := by
  apply (memLp_two_iff_integrable_sq
    (continuous_finsetProd _ (fun i _ => (p i).continuous.comp (continuous_apply i))).aestronglyMeasurable).mpr
  simpa only [Finset.prod_pow, Function.comp_def] using Integrable.fintype_prod
    (fun i => (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_poly (p i)))

def orthPolyMap {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    MultilinearMap ℝ (fun _ : ι => ℝ[X]) ℝ where
  toFun p := ∫ x, f x * polyProdMap p x ∂γpi ι
  map_update_add' p i a b := by
    rw [polyProdMap.map_update_add]
    simp only [Pi.add_apply, mul_add]
    apply integral_add <;>
      simpa only [polyProdMap_apply, Pi.mul_def] using hf.integrable_mul (memLp_polyProd _)
  map_update_smul' p i a b := by
    rw [polyProdMap.map_update_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => f x * (a * polyProdMap (Function.update p i b) x)) =
      fun x => a * (f x * polyProdMap (Function.update p i b) x) by funext x; ring]
    exact integral_const_mul _ _

lemma heLeadingUnit (n : ℕ) : IsUnit (heSequence n).leadingCoeff := by
  change IsUnit (hePoly n).leadingCoeff
  rw [show (hePoly n).leadingCoeff = 1 from ((hermite_monic n).map _).leadingCoeff]
  exact isUnit_one

lemma ortho_polyProd_of_heProd {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (h : ∀ a : ι → ℕ, (∫ x, f x * ∏ i, he (a i) (x i) ∂γpi ι) = 0)
    (p : ι → ℝ[X]) : (∫ x, f x * ∏ i, (p i).eval (x i) ∂γpi ι) = 0 := by
  have heq : orthPolyMap hf = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => heSequence.basis heLeadingUnit)
    intro a
    simpa only [orthPolyMap, MultilinearMap.coe_mk, polyProdMap_apply,
      Sequence.basis_eq_self, show (fun i => heSequence (a i)) = fun i => hePoly (a i) from rfl,
      hePoly_eval, zero_apply] using h a
  simpa only [orthPolyMap, MultilinearMap.coe_mk, polyProdMap_apply, zero_apply] using
    congrArg (fun q => q p) heq

lemma memLp_exp_linear (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    MemLp (fun x => Real.exp (t * L x)) 2 (γpi ι) := by
  classical
  have heq (x : ι → ℝ) : Real.exp (t * L x) =
      ∏ i, Real.exp ((t * L (Pi.single i 1)) * x i) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
    rw [show Pi.single i (x i) = x i • Pi.single i (1:ℝ) by
      simpa only [smul_eq_mul, mul_one] using (Pi.single_smul (f := fun _ : ι => ℝ) i (x i) (1:ℝ))]
    simp [mul_comm, mul_left_comm]
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simp_rw [heq, ← Finset.prod_pow]
  exact Integrable.fintype_prod (fun i =>
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_exp (t * L (Pi.single i 1))))

lemma memLp_mvpoly (p : MvPolynomial ι ℝ) :
    MemLp (fun x => MvPolynomial.eval x p) 2 (γpi ι) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simpa only [MvPolynomial.eval_add, Pi.add_def] using hp.add hq
  | monomial m a =>
    simpa only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Polynomial.eval_pow, Polynomial.eval_X] using
      (memLp_polyProd (fun i : ι => (X : ℝ[X])^(m i))).const_mul a

lemma ortho_mvpoly_of_polyProd {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (h : ∀ p : ι → ℝ[X], (∫ x, f x * ∏ i, (p i).eval (x i) ∂γpi ι) = 0)
    (p : MvPolynomial ι ℝ) : (∫ x, f x * MvPolynomial.eval x p ∂γpi ι) = 0 := by
  have hi (p : MvPolynomial ι ℝ) : Integrable (fun x => f x * MvPolynomial.eval x p) (γpi ι) := by
    simpa only [Pi.mul_def] using hf.integrable_mul (memLp_mvpoly p)
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [show (fun x => f x * MvPolynomial.eval x (p+q)) =
        fun x => f x * MvPolynomial.eval x p + f x * MvPolynomial.eval x q by
          funext x; simp [mul_add], integral_add (hi p) (hi q), hp, hq, add_zero]
  | monomial m a =>
    simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [show (fun x => f x * (a * ∏ i, x i ^ m i)) =
        fun x => a * (f x * ∏ i, x i ^ m i) by funext x; ring, integral_const_mul]
    have hh := h (fun i => (X : ℝ[X]) ^ m i)
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at hh
    rw [hh, mul_zero]

lemma weighted_linear_expSet {w : (ι → ℝ) → ℝ} (hw : MemLp w 2 (γpi ι))
    (hwn : ∀ x, 0 ≤ w x) (L : (ι → ℝ) →L[ℝ] ℝ) :
    integrableExpSet id ((γpi ι).withDensity (fun x => ENNReal.ofReal (w x)) |>.map L) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  show Integrable (fun x => Real.exp (t*x)) _
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  rw [integrable_withDensity_iff_integrable_smul₀'
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (hwn _), smul_eq_mul, Pi.mul_def] using
    hw.integrable_mul (memLp_exp_linear L t)

lemma ae_zero_of_integral_mvpoly_eq_zero {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (horth : ∀ p : MvPolynomial ι ℝ, (∫ x, f x * MvPolynomial.eval x p ∂γpi ι) = 0) :
    f =ᵐ[γpi ι] 0 := by
  classical
  let p := fun x => max (f x) 0
  let n := fun x => max (-f x) 0
  have hp : MemLp p 2 (γpi ι) := memLp_positivePart hf
  have hn : MemLp n 2 (γpi ι) := memLp_positivePart hf.neg
  have hpn : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hnn : ∀ x, 0 ≤ n x := fun x => le_max_right _ _
  let μ := (γpi ι).withDensity (fun x => ENNReal.ofReal (p x))
  let ν := (γpi ι).withDensity (fun x => ENNReal.ofReal (n x))
  let : IsFiniteMeasure μ := weighted_finite hp
  let : IsFiniteMeasure ν := weighted_finite hn
  have hμν : μ = ν := by
    apply Measure.ext_of_charFunDual
    funext L
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
    have hh : μ.map L = ν.map L := by
      apply measure_eq_of_moments (weighted_linear_expSet hp hpn L)
        (weighted_linear_expSet hn hnn L)
      intro k
      rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
      rw [integral_weighted hp hpn, integral_weighted hn hnn]
      have hi := horth ((linearPoly L)^k)
      have hk := memLp_mvpoly ((linearPoly L)^k)
      simp only [map_pow, eval_linearPoly] at hi hk
      have heq : (fun x => f x * (L x)^k) = fun x => p x * (L x)^k - n x * (L x)^k := by
        funext x
        dsimp [p,n]
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      have hip : Integrable (fun x => p x * (L x)^k) (γpi ι) := by
        simpa only [Pi.mul_def] using hp.integrable_mul hk
      have hin : Integrable (fun x => n x * (L x)^k) (γpi ι) := by
        simpa only [Pi.mul_def] using hn.integrable_mul hk
      rw [heq, integral_sub hip hin] at hi
      exact sub_eq_zero.mp hi
    rw [hh]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hμν
  filter_upwards [hae] with x hx
  have heq := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal (hpn x), ENNReal.toReal_ofReal (hnn x)] at heq
  have hd : p x - n x = f x := by dsimp [p,n]; exact max_zero_sub_max_neg_zero_eq_self _
  change f x = 0
  linarith

lemma continuous_H (n : ℕ) : Continuous (H n) := by
  change Continuous (fun x => he n x / Real.sqrt (n.factorial : ℝ))
  simpa only [hePoly_eval] using (hePoly n).continuous.div_const _

lemma memLp_psi (a : ι → ℕ) : MemLp (psi a) 2 (γpi ι) := by
  apply (memLp_two_iff_integrable_sq
    (continuous_finsetProd _ (fun i _ => (continuous_H (a i)).comp (continuous_apply i))).aestronglyMeasurable).mpr
  simpa only [psi, Function.comp_def, Finset.prod_pow] using Integrable.fintype_prod
    (fun i => (memLp_two_iff_integrable_sq (continuous_H (a i)).aestronglyMeasurable).mp (memLp_H (a i)))

lemma psi_product (a b : ι → ℕ) :
    (∫ x, psi a x * psi b x ∂γpi ι) = if a = b then 1 else 0 := by
  classical
  simp only [psi, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => H (a i) t * H (b i) t)
    (μ := fun _ => γ)]
  simp only [H_product]
  by_cases hab : a = b
  · simp [hab]
  · rw [ite_eq_right hab]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma heProd_eq (a : ι → ℕ) (x : ι → ℝ) :
    (∏ i, he (a i) (x i)) = (∏ i, Real.sqrt ((a i).factorial : ℝ)) * psi a x := by
  rw [psi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [H, mul_div_cancel₀ _ (ne_of_gt (sqrt_factorial_pos _))]

lemma ae_zero_of_integral_psi_eq_zero {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (horth : ∀ a, (∫ x, f x * psi a x ∂γpi ι) = 0) : f =ᵐ[γpi ι] 0 := by
  apply ae_zero_of_integral_mvpoly_eq_zero hf
  apply ortho_mvpoly_of_polyProd hf
  apply ortho_polyProd_of_heProd hf
  intro a
  simp only [heProd_eq]
  rw [show (fun x => f x * ((∏ i, Real.sqrt ((a i).factorial : ℝ)) * psi a x)) =
      fun x => (∏ i, Real.sqrt ((a i).factorial : ℝ)) * (f x * psi a x) by funext x; ring,
    integral_const_mul, horth a, mul_zero]

def psiVec (a : ι → ℕ) : Lp ℝ 2 (γpi ι) := (memLp_psi a).toLp (psi a)

lemma psiVec_orthonormal : Orthonormal ℝ (psiVec (ι := ι)) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa only [psiVec, integral_inner_toLp] using psi_product a b

lemma eq_zero_of_inner_psiVec_eq_zero (f : Lp ℝ 2 (γpi ι))
    (h : ∀ a, inner ℝ f (psiVec a) = 0) : f = 0 := by
  have hae : (f : (ι → ℝ) → ℝ) =ᵐ[γpi ι] 0 := by
    apply ae_zero_of_integral_psi_eq_zero (Lp.memLp f)
    intro a
    have hi := h a
    rw [L2.inner_def] at hi
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [(memLp_psi a).coeFn_toLp] with x hx
    simp only [psiVec, hx, RCLike.inner_apply, conj_trivial, mul_comm]
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℝ 2 (γpi ι)).symm

def productHermiteBasis : HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (γpi ι)) :=
  HilbertBasis.mkOfOrthogonalEqBot psiVec_orthonormal (by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply eq_zero_of_inner_psiVec_eq_zero f
    intro a
    exact (Submodule.mem_orthogonal' _ f).mp hf _
      (Submodule.subset_span (Set.mem_range_self a)))

end Product

lemma integrable_he_affine (n : ℕ) (r s : ℝ) :
    Integrable (fun x => he n (r+s*x)) γ := by
  simpa only [eval_comp, eval_affinePoly, hePoly_eval] using
    integrable_poly ((hePoly n).comp (affinePoly r s))

lemma integrable_mul_he_affine (n : ℕ) (r s : ℝ) :
    Integrable (fun x => x * he n (r+s*x)) γ := by
  convert integrable_poly (X * (hePoly n).comp (affinePoly r s)) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Polynomial.eval_mul, eval_X, eval_comp, eval_affinePoly, hePoly_eval]

lemma stein_he_affine (n : ℕ) (r s : ℝ) :
    (∫ x, x * he (n+1) (r+s*x) ∂γ) = ((n+1:ℝ)*s) * ∫ x, he n (r+s*x) ∂γ := by
  have h := stein_poly ((hePoly (n+1)).comp (affinePoly r s))
  simp only [derivative_comp, derivative_hePoly, derivative_affinePoly, eval_comp,
    eval_affinePoly, hePoly_eval, eval_mul, eval_C, eval_smul, smul_eq_mul] at h
  rw [h, show (fun x => s * ((n+1:ℝ) * he n (r+s*x))) =
    fun x => ((n+1:ℝ)*s) * he n (r+s*x) by funext x; ring, integral_const_mul]

lemma he_recurrence (n : ℕ) (x : ℝ) :
    he (n+2) x = x * he (n+1) x - (n+1:ℝ) * he n x := by
  rw [← hePoly_eval, show n+2 = (n+1)+1 by omega, hePoly_succ, derivative_hePoly]
  simp

lemma he_noise (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, he n (ρ*c+s*g) ∂γ) = ρ^n * he n c := by
  induction n using Nat.twoStepInduction with
  | zero => simp [γ]
  | one =>
    have hi : Integrable (fun x : ℝ => x) γ := by simpa using integrable_poly X
    simp only [he_one, pow_one]
    rw [integral_add (integrable_const _) (hi.const_mul s), integral_const_mul]
    rw [integral_const_mul s]
    simp [γ]
  | more n ih0 ih1 =>
    have hi0 := integrable_he_affine n (ρ*c) s
    have hi1 := integrable_he_affine (n+1) (ρ*c) s
    have hig := integrable_mul_he_affine (n+1) (ρ*c) s
    have heq : (fun g => he (n+2) (ρ*c+s*g)) = fun g =>
        (ρ*c) * he (n+1) (ρ*c+s*g) + s*(g * he (n+1) (ρ*c+s*g)) -
        (n+1:ℝ)*he n (ρ*c+s*g) := by
      funext g
      rw [he_recurrence]
      ring
    rw [heq, integral_sub ((hi1.const_mul (ρ*c)).fun_add (hig.const_mul s)) (hi0.const_mul (n+1:ℝ)),
      integral_add (hi1.const_mul _) (hig.const_mul _)]
    simp only [integral_const_mul, stein_he_affine, ih0, ih1, he_recurrence, pow_succ]
    have hh : s*s = 1-ρ*ρ := by nlinarith [h]
    calc
      _ = ρ^n*ρ*ρ*c*he (n+1) c + ((s*s)-1)*((n+1:ℝ)*ρ^n*he n c) := by ring
      _ = _ := by rw [hh]; ring

lemma H_noise (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, H n (ρ*c+s*g) ∂γ) = ρ^n * H n c := by
  simp only [H, integral_div, he_noise ρ s c h, mul_div_assoc]

variable {ι : Type*} [Fintype ι]

lemma psi_noise (ρ s : ℝ) (h : ρ^2+s^2=1) (a : ι → ℕ) (c : ι → ℝ) :
    (∫ g, psi a (fun i => ρ*c i+s*g i) ∂γpi ι) = ρ^(∑ i, a i)*psi a c := by
  simp only [psi]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => H (a i) (ρ*c i+s*t))]
  simp only [H_noise ρ s _ h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma charFunDual_gamma (L : ℝ →L[ℝ] ℝ) :
    charFunDual γ L = Complex.exp ((-(L 1)^2 / 2 : ℝ) : ℂ) := by
  rw [charFunDual_eq_charFun_map_one, γ, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  simp [Real.coe_toNNReal _ (sq_nonneg _), neg_div]

lemma charFunDual_gammaPi [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) :
    charFunDual (γpi ι) L =
      Complex.exp ((-(∑ i, (L (Pi.single i 1))^2) / 2 : ℝ) : ℂ) := by
  classical
  rw [γpi, charFunDual_pi]
  simp only [charFunDual_gamma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma rotation_preserves (ρ s : ℝ) (h : ρ^2+s^2=1) :
    MeasurePreserving (rotation (ι := ι) ρ s) ((γpi ι).prod (γpi ι))
      ((γpi ι).prod (γpi ι)) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod]
  simp only [charFunDual_gammaPi, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  have h1 (i : ι) : L (rotation ρ s (Pi.single i 1, 0)) =
      ρ * L (Pi.single i 1, 0) + s * L (0, Pi.single i 1) := by
    rw [show rotation ρ s (Pi.single i 1, 0) =
        ρ • (Pi.single i 1, 0) + s • (0, Pi.single i 1) by
          ext j <;> simp [rotation_apply]]
    simp only [map_add, map_smul, smul_eq_mul]
  have h2 (i : ι) : L (rotation ρ s (0, Pi.single i 1)) =
      s * L (Pi.single i 1, 0) - ρ * L (0, Pi.single i 1) := by
    rw [show rotation ρ s (0, Pi.single i 1) =
        s • (Pi.single i 1, 0) - ρ • (0, Pi.single i 1) by
          ext j <;> simp [rotation_apply]]
    simp only [map_sub, map_smul, smul_eq_mul]
  simp only [h1, h2]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 1
  apply congrArg Complex.ofReal
  have hsum : (∑ i, (ρ * L (Pi.single i 1, 0) + s * L (0, Pi.single i 1))^2) +
      (∑ i, (s * L (Pi.single i 1, 0) - ρ * L (0, Pi.single i 1))^2) =
      (∑ i, (L (Pi.single i 1, 0))^2) + (∑ i, (L (0, Pi.single i 1))^2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (ρ^2+s^2)*((L (Pi.single i 1, 0))^2+(L (0, Pi.single i 1))^2) := by ring
      _ = _ := by rw [h, one_mul]
  linarith

def noise (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ y, Q (ρ • x + s • y) ∂γpi ι

lemma measurable_noise (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) :
    Measurable (noise ρ s Q) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact (hQ.comp (by fun_prop : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
    ρ • z.1+s • z.2))).stronglyMeasurable

lemma psi_integrable (a : ι → ℕ) : Integrable (psi a) (γpi ι) :=
  (memLp_psi a).integrable (by norm_num)

lemma noise_bound (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : ∀ x, |Q x| ≤ 1) (x : ι → ℝ) :
    |noise ρ s Q x| ≤ 1 := by
  simpa [noise, ← Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := γpi ι) (f := fun y => Q (ρ • x+s • y)) (C := 1)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hQ _)

lemma he_rotation_moment (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, (s*c-ρ*g) * he n (ρ*c+s*g) ∂γ) = s*ρ^n*he (n+1) c := by
  have hi := integrable_he_affine n (ρ*c) s
  have hig := integrable_mul_he_affine n (ρ*c) s
  rw [show (fun g => (s*c-ρ*g)*he n (ρ*c+s*g)) = fun g =>
      (s*c)*he n (ρ*c+s*g)-ρ*(g*he n (ρ*c+s*g)) by funext g; ring,
    integral_sub (hi.const_mul _) (hig.const_mul _), integral_const_mul,
    integral_const_mul, he_noise ρ s c h]
  cases n with
  | zero => simp [γ, integral_id_gaussianReal]
  | succ n =>
    rw [stein_he_affine, he_noise ρ s c h, he_recurrence]
    simp only [pow_succ]
    ring

lemma H_rotation_moment (ρ s c : ℝ) (h : ρ^2+s^2=1) (n : ℕ) :
    (∫ g, (s*c-ρ*g) * H n (ρ*c+s*g) ∂γ) =
      s*Real.sqrt (n+1:ℝ)*ρ^n*H (n+1) c := by
  simp only [H, ← mul_div_assoc, integral_div, he_rotation_moment ρ s c h]
  rw [sqrt_factorial_succ]
  have h1 : Real.sqrt (n+1:ℝ) ≠ 0 := by positivity
  have h2 := ne_of_gt (sqrt_factorial_pos n)
  field_simp

lemma psi_rotation_moment [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (a : ι → ℕ) (c : ι → ℝ) (i : ι) :
    (∫ g, (s*c i-ρ*g i) * psi a (ρ • c+s • g) ∂γpi ι) =
      s*Real.sqrt (a i+1:ℝ)*ρ^(∑ j,a j) * psi (Function.update a i (a i+1)) c := by
  have heq (g : ι → ℝ) : (s*c i-ρ*g i)*psi a (ρ • c+s • g) =
      ∏ j, (if j=i then s*c j-ρ*g j else 1)*H (a j) (ρ*c j+s*g j) := by
    rw [Finset.prod_mul_distrib]
    simp [psi, Finset.prod_ite_eq', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [heq]
  rw [integral_fintype_prod_eq_prod (f := fun j (t : ℝ) =>
    (if j=i then s*c j-ρ*t else 1)*H (a j) (ρ*c j+s*t))]
  have hfactor (j : ι) :
      (∫ t, (if j=i then s*c j-ρ*t else 1)*H (a j) (ρ*c j+s*t) ∂γ) =
        (if j=i then s*Real.sqrt (a i+1:ℝ) else 1)*
          (ρ^(a j)*H ((Function.update a i (a i+1)) j) (c j)) := by
    by_cases hj : j=i
    · subst j
      simp only [ite_true, Function.update_self, H_rotation_moment ρ s _ h]
      ring
    · simp only [hj, ite_false, one_mul, Function.update_of_ne hj, H_noise ρ s _ h]
  simp only [hfactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp [Finset.prod_ite_eq', psi, mul_assoc]

lemma degree_bump [DecidableEq ι] (i : ι) (a : ι → ℕ) :
    degree (bump i a) = degree a+1 := by
  have heq (j : ι) : bump i a j = a j + if j=i then 1 else 0 := by
    by_cases hj : j=i <;> simp [bump, hj, Function.update_of_ne]
  simp only [degree, heq, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

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

lemma productHermiteBasis_apply (a : ι → ℕ) :
    productHermiteBasis a = psiVec a := by
  simp only [productHermiteBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma coeff_eq_inner {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) (a : ι → ℕ) :
    coeff f a = inner ℝ (productHermiteBasis a) (hf.toLp f) := by
  rw [productHermiteBasis_apply]
  exact (integral_inner_toLp (memLp_psi a) hf).symm

lemma hasSum_coeff_sq {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    HasSum (fun a => (coeff f a)^2) (∫ x, (f x)^2 ∂γpi ι) := by
  have hs := productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have hc (a : ι → ℕ) : inner ℝ (hf.toLp f) (productHermiteBasis a) = coeff f a := by
    rw [real_inner_comm]
    exact (coeff_eq_inner hf a).symm
  simp only [hc, ← coeff_eq_inner hf, ← pow_two] at hs
  simpa only [integral_inner_toLp hf hf, ← pow_two] using hs

lemma coeff_const_mul (r : ℝ) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (fun x => r*f x) a = r*coeff f a := by
  unfold coeff
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma memLp_noise (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) : MemLp (noise ρ s Q) 2 (γpi ι) :=
  MemLp.of_bound (measurable_noise ρ s hQ).aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using noise_bound ρ s hb x)

lemma degree_eq_zero_iff (a : ι → ℕ) : degree a = 0 ↔ a = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    funext_iff, Pi.zero_apply]

def project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ a ∈ low d, coeff f a * psi a x

lemma memLp_project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) :
    MemLp (project d f) 2 (γpi ι) := by
  exact memLp_finsetSum _ (fun a _ => (memLp_psi a).const_mul _)

lemma coeff_project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (project d f) a = if degree a ≤ d then coeff f a else 0 := by
  unfold coeff project
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun b _ =>
    ((memLp_psi a).integrable_mul (memLp_psi b)).const_mul (coeff f b) |>.congr
      (ae_of_all _ fun x => by dsimp; ring))]
  simp_rw [show ∀ b : ι → ℕ, (fun x => psi a x * (coeff f b * psi b x)) =
    (fun x => coeff f b * (psi a x * psi b x)) by intro b; funext x; ring,
    integral_const_mul, psi_product]
  simp [coeff, mem_low]

lemma coeff_sub {f g : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (hg : MemLp g 2 (γpi ι)) (a : ι → ℕ) :
    coeff (fun x => f x-g x) a = coeff f a-coeff g a := by
  unfold coeff
  simp_rw [mul_sub]
  exact integral_sub ((memLp_psi a).integrable_mul hf) ((memLp_psi a).integrable_mul hg)

lemma coeff_residual [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (d : ℕ) (a : ι → ℕ) :
    coeff (fun x => f x-project d f x) a = if d < degree a then coeff f a else 0 := by
  rw [coeff_sub hf (memLp_project d f), coeff_project]
  split_ifs <;> simp_all; omega

end MinUncut.GaussianHermite

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

def convolution (σ : ℝ) (Q : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ g, Q (x + σ • g) ∂γpi ι

omit [DecidableEq ι] in
lemma convolution_as_noise {ρ σ : ℝ} (hρ : ρ ≠ 0) (Q : (ι → ℝ) → ℝ) :
    convolution σ Q = noise ρ (σ*ρ) (fun v => Q (ρ⁻¹ • v)) := by
  funext x
  unfold convolution noise
  congr 1
  funext g
  congr 1
  ext i
  dsimp
  field_simp

end MinUncut.GaussianHermite

namespace MinUncut.RowNoise
open BinaryFourier
local instance convolutionDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

omit [Module F₂ W] in
lemma rowDensity_mean (a : ℝ) (b : W) : (𝔼 c, rowDensity a b c) = 1 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rowDensity, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

omit [AddCommGroup W] [Module F₂ W] in
lemma rowDensity_symmetric (a : ℝ) (b c : W) : rowDensity a b c = rowDensity a c b := by
  simp [rowDensity, eq_comm]

omit [Module F₂ W] in
lemma rowDensity_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b c : W) :
    0 ≤ rowDensity a b c := by
  unfold rowDensity
  split_ifs <;> positivity

def frequency (α : Module.Dual F₂ (R → W)) (r : R) : Module.Dual F₂ W :=
  α.comp (LinearMap.single F₂ (fun _ : R => W) r)

omit [Fintype W] [DecidableEq W] in
lemma dual_apply (α : Module.Dual F₂ (R → W)) (B : R → W) :
    α B = ∑ r, frequency α r (B r) := by
  change α B = ∑ r, α (Pi.single r (B r))
  rw [← map_sum]
  congr 1
  ext r
  simp

lemma sign_sum {S : Type*} (s : Finset S) (f : S → F₂) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, sign_add, ih]

omit [Fintype W] [DecidableEq W] in
lemma character_product (α : Module.Dual F₂ (R → W)) (B : R → W) :
    character α B = ∏ r, character (frequency α r) (B r) := by
  simp only [character, dual_apply, sign_sum]

def mask (α : Module.Dual F₂ (R → W)) : Finset R :=
  Finset.univ.filter (fun r => frequency α r ≠ 0)

def degree (α : Module.Dual F₂ (R → W)) : ℕ := (mask α).card

lemma row_character_eigen (a : ℝ) (b : W) (α : Module.Dual F₂ W) :
    (𝔼 c, rowDensity a b c * character α c) =
      (if α=0 then 1 else 1-a)*character α b := by
  unfold rowDensity
  simp only [add_mul, Finset.expect_add_distrib, mul_assoc, ← Finset.mul_expect]
  have hh : (𝔼 c, (if c=b then (Fintype.card W : ℝ) else 0) * character α c) =
      character α b := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hh, character_mean]
  split_ifs with hα
  · subst α; simp
  · ring

def project (D : ℕ) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  ∑ α ∈ Finset.univ.filter (fun α => degree α ≤ D), coefficient f α * character α B

omit [DecidableEq W] in
lemma coefficient_project (D : ℕ) (f : (R → W) → ℝ) (β : Module.Dual F₂ (R → W)) :
    coefficient (project D f) β = if degree β ≤ D then coefficient f β else 0 := by
  unfold coefficient project
  simp_rw [Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect,
    character_orthogonality]
  simp [Finset.mem_filter, coefficient]

omit [DecidableEq W] in
lemma coefficient_residual (D : ℕ) (f : (R → W) → ℝ) (β : Module.Dual F₂ (R → W)) :
    coefficient (fun B => f B-project D f B) β =
      if degree β ≤ D then 0 else coefficient f β := by
  have he : coefficient (fun B => f B-project D f B) β =
      coefficient f β - coefficient (project D f) β := by
    simp only [coefficient, sub_mul, Finset.expect_sub_distrib]
  rw [he, coefficient_project]
  split_ifs <;> ring

omit [DecidableEq W] in
lemma residual_energy (D : ℕ) (f : (R → W) → ℝ) :
    (𝔼 B, (f B-project D f B)^2) =
      ∑ α, if D < degree α then (coefficient f α)^2 else 0 := by
  rw [← parseval]
  apply Finset.sum_congr rfl
  intro α _
  rw [coefficient_residual]
  split_ifs <;> simp_all
  omega

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CoupledAnswer
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
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def coupledAnswer (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  bitSign (f.answer (pullQuery B (c+σ•p.1) (η•p.2)))

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_RowProjectedGradient
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def rowProjectedGradient (D : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  RowNoise.project D (fun C => gradient f C σ η c x) B

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussNegPreserving
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
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory

variable {m n : ℕ}

lemma gauss_neg_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (fun g : ι → ℝ => -g) (gauss ι) (gauss ι) := by
  apply measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => -x)
  intro i
  exact ⟨by fun_prop, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

lemma gauss_integral_neg (ι : Type*) [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ g, f (-g) ∂gauss ι) = ∫ g, f g ∂gauss ι := by
  exact (gauss_neg_preserving ι).integral_comp (Homeomorph.neg _).measurableEmbedding f

lemma query_neg (u : Point m n → ℝ) (d : Code m n → ℝ) (z : Code m n)
    (h : (Real.sqrt (n^m : ℕ))⁻¹ *
      (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + d z ≠ 0) :
    query (-u) (-d) z = !(query u d z) := by
  simp only [query, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro ht hpos
    apply h
    linarith
  · intro ht
    linarith

lemma query_no_ties (u : Point m n → ℝ) {η : ℝ} (hη : η ≠ 0) :
    ∀ᵐ l ∂gauss (Code m n), ∀ z : Code m n,
      (Real.sqrt (n^m : ℕ))⁻¹ *
        (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + (η • l) z ≠ 0 := by
  rw [ae_all_iff]
  intro z
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let t := (Real.sqrt (n^m : ℕ))⁻¹ *
    (∑ x : Point m n, u x * BinaryFourier.sign (z.val x))
  have he := (measurePreserving_eval (fun _ : Code m n => gaussianReal 0 1) z).quasiMeasurePreserving.ae
    (Measure.ae_ne (gaussianReal 0 1) (-t / η))
  filter_upwards [he] with l hl
  change t + η * l z ≠ 0
  intro hh
  apply hl
  change l z = -t / η
  apply (eq_div_iff hη).mpr
  linarith

end MinUncut.Inner

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

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
lemma project_const_mul (d : ℕ) (a : ℝ) (f : (ι → ℝ) → ℝ) :
    project d (fun x => a*f x) = fun x => a*project d f x := by
  funext x
  simp only [project, coeff_const_mul, Finset.mul_sum, mul_assoc]

end MinUncut.GaussianHermite

namespace MinUncut.Inner
open GaussianHermite
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [Fintype A] {m n : ℕ}

def gaussianProject (d : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  GaussianHermite.project d (fun c => gradient f B σ η c x) c

end MinUncut.Inner

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_MaskRowKernel
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
local instance maskRowKernelDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

lemma maskRowKernel_character (active : Bool) (b : W) (α : Module.Dual F₂ W) :
    (𝔼 c, maskRowKernel active b c * character α c) =
      if active = decide (α ≠ 0) then character α b else 0 := by
  cases active
  · simp [maskRowKernel, character_mean]
    split_ifs with h
    · simp [h]
    · rfl
  · simp only [maskRowKernel, ↓reduceIte, sub_mul, one_mul,
      Finset.expect_sub_distrib, row_character_eigen, character_mean]
    by_cases h : α=0 <;> simp [h]

lemma maskKernel_character (S : Finset R) (B : R → W) (α : Module.Dual F₂ (R → W)) :
    (𝔼 C, maskKernel S B C * character α C) = if mask α=S then character α B else 0 := by
  simp only [maskKernel, character_product, ← Finset.prod_mul_distrib]
  rw [expect_prod (f := fun r (c : W) => maskRowKernel (decide (r ∈ S)) (B r) c * character (frequency α r) c)]
  simp only [maskRowKernel_character]
  have he (r : R) : (decide (r ∈ S) = decide (frequency α r ≠ 0)) ↔
      (r ∈ S ↔ r ∈ mask α) := by
    by_cases h₁ : r ∈ S <;> by_cases h₂ : frequency α r=0 <;> simp [mask, h₁, h₂]
  by_cases hs : mask α=S
  · rw [ite_eq_left hs]
    apply Finset.prod_congr rfl
    intro r _
    rw [ite_eq_left ((he r).mpr (by rw [hs]))]
  · rw [ite_eq_right hs]
    have hh : ∃ r, ¬(r ∈ S ↔ r ∈ mask α) := by
      by_contra hn
      push Not at hn
      exact hs (Finset.ext (fun r => (hn r).symm))
    obtain ⟨r,hr⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right (fun h => hr ((he r).mp h)))

lemma maskProject_expansion (S : Finset R) (f : (R → W) → ℝ) (B : R → W) :
    maskProject S f B = ∑ α : Module.Dual F₂ (R → W),
      if mask α=S then coefficient f α * character α B else 0 := by
  unfold maskProject
  conv_lhs => arg 2; ext C; rw [← inversion f C]
  simp only [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [mul_left_comm _ (coefficient f α), ← Finset.mul_expect, maskKernel_character]
  split_ifs <;> simp

lemma coefficient_maskProject (S : Finset R) (f : (R → W) → ℝ) (α : Module.Dual F₂ (R → W)) :
    coefficient (maskProject S f) α = if mask α=S then coefficient f α else 0 := by
  have he (B : R → W) : maskProject S f B =
      ∑ β ∈ Finset.univ.filter (fun β : Module.Dual F₂ (R → W) => mask β=S), coefficient f β*character β B := by
    rw [maskProject_expansion, Finset.sum_filter]
  unfold coefficient
  simp_rw [he, Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect,
    character_orthogonality]
  simp [Finset.mem_filter, coefficient]

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_MemLpMaskProject
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
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_maskProject (S : Finset R) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (B : R → W) :
    MemLp (fun c => maskProject S (fun D => u D c) B) 2 (γpi ι) :=
  memLp_expect _ (fun D => (hu D).const_mul _)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_MaskHermite
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
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_maskHermite (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) : MemLp (maskHermite S I u B) 2 (γpi ι) :=
  memLp_maskProject S _ (fun _ => (memLp_psi I).mul_const _) B

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SelectedProject
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
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma memLp_selectedProject (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) :
    MemLp (selectedProject J u B) 2 (γpi ι) :=
  memLp_finsetSum _ (fun j _ => memLp_maskHermite j.1 j.2 u B)

end MinUncut.RowNoise
open scoped BigOperators

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

local instance jointInnerDualFintype_r5d4563_1 {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
lemma maskProject_selfadjoint (S : Finset R) (f g : (R → W) → ℝ) :
    (𝔼 B, f B * maskProject S g B) = 𝔼 B, maskProject S f B * g B := by
  rw [← parseval_inner, ← parseval_inner]
  simp only [coefficient_maskProject]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs <;> ring

lemma maskProject_idempotent (S T : Finset R) (f : (R → W) → ℝ) (B : R → W) :
    maskProject S (maskProject T f) B = if S=T then maskProject S f B else 0 := by
  rw [maskProject_expansion]
  simp only [coefficient_maskProject]
  by_cases h : S=T
  · subst T
    simp only [↓reduceIte]
    rw [maskProject_expansion]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro α _
    split_ifs with hS hT
    · exact (h (hS.symm.trans hT)).elim
    · simp
    · rfl

lemma maskProject_inner (S T : Finset R) (f g : (R → W) → ℝ) :
    (𝔼 B, maskProject S f B * maskProject T g B) =
      if S=T then (𝔼 B, f B * maskProject S g B) else 0 := by
  rw [← maskProject_selfadjoint]
  simp_rw [maskProject_idempotent]
  split_ifs with h
  · rfl
  · simp

omit [AddCommGroup W] [Module F₂ W] in
lemma maskHermite_eq (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) :
    maskHermite S I u B c = psi I c * maskProject S (fun D => GaussianHermite.coeff (u D) I) B := by
  unfold maskHermite maskProject hermiteComponent GaussianHermite.coeff
  simp only [mul_left_comm _ (psi I c), ← Finset.mul_expect]

def jointInner (u v : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, u B c * v B c ∂γpi ι

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_symm (u v : (R → W) → (ι → ℝ) → ℝ) : jointInner u v = jointInner v u := by
  simp only [jointInner, mul_comm]

lemma jointInner_maskHermite (S T : Finset R) (I J : ι → ℕ)
    (u v : (R → W) → (ι → ℝ) → ℝ) :
    jointInner (maskHermite S I u) (maskHermite T J v) =
      if I=J then if S=T then
        (𝔼 B, GaussianHermite.coeff (u B) I * maskProject S (fun D => GaussianHermite.coeff (v D) J) B) else 0 else 0 := by
  classical
  unfold jointInner
  simp only [maskHermite_eq]
  have h (B : R → W) : (∫ c, (psi I c * maskProject S (fun D => GaussianHermite.coeff (u D) I) B) *
      (psi J c * maskProject T (fun D => GaussianHermite.coeff (v D) J) B) ∂γpi ι) =
      (if I=J then 1 else 0) * (maskProject S (fun D => GaussianHermite.coeff (u D) I) B *
        maskProject T (fun D => GaussianHermite.coeff (v D) J) B) := by
    simp_rw [mul_mul_mul_comm (psi I _) _ (psi J _) _]
    rw [integral_mul_const, psi_product]
  simp_rw [h, ← Finset.mul_expect, maskProject_inner]
  split_ifs <;> simp_all

lemma components_orthogonal (a b : Finset R × (ι → ℕ)) (hab : a ≠ b)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointInner (maskHermite a.1 a.2 u) (maskHermite b.1 b.2 u) = 0 := by
  rw [jointInner_maskHermite]
  split_ifs with hI hS
  · exact (hab (Prod.ext hS hI)).elim
  · rfl
  · rfl

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_sum_right {T : Type*} (s : Finset T)
    (u : (R → W) → (ι → ℝ) → ℝ) (v : T → (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ t ∈ s, ∀ B, MemLp (v t B) 2 (γpi ι)) :
    jointInner u (fun B c => ∑ t ∈ s, v t B c) = ∑ t ∈ s, jointInner u (v t) := by
  unfold jointInner
  simp only [Finset.mul_sum]
  have hh (B) : (∫ c, ∑ t ∈ s, u B c * v t B c ∂γpi ι) =
      ∑ t ∈ s, ∫ c, u B c * v t B c ∂γpi ι :=
    integral_finsetSum s (fun t ht => (hu B).integrable_mul (hv t ht B))
  simp_rw [hh]
  rw [Finset.expect_sum_comm]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_sum_left {T : Type*} (s : Finset T)
    (u : T → (R → W) → (ι → ℝ) → ℝ) (v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ t ∈ s, ∀ B, MemLp (u t B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointInner (fun B c => ∑ t ∈ s, u t B c) v = ∑ t ∈ s, jointInner (u t) v := by
  rw [jointInner_symm, jointInner_sum_right s v u hv hu]
  exact Finset.sum_congr rfl (fun t _ => jointInner_symm _ _)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SecondFailureIndicator
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
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

local instance secondFailureDualFintype_r5d4563_1 {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
lemma project_eq_mask_sum (D : ℕ) (f : (R → W) → ℝ) (B : R → W) :
    project D f B = ∑ S ∈ Finset.univ.filter (fun S : Finset R => S.card ≤ D), maskProject S f B := by
  simp only [maskProject_expansion]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  unfold project
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_eq_single (mask α)]
  · simp [degree]
    rfl
  · intro S _ hS
    simp [Ne.symm hS]
  · simp

omit [DecidableEq W] in
lemma project_sum {T : Type*} (s : Finset T) (D : ℕ) (u : T → (R → W) → ℝ) (B : R → W) :
    project D (fun C => ∑ t ∈ s, u t C) B = ∑ t ∈ s, project D (u t) B := by
  unfold project BinaryFourier.coefficient
  simp only [Finset.sum_mul,Finset.expect_sum_comm]
  rw [Finset.sum_comm]

omit [DecidableEq W] in
lemma project_sub (D : ℕ) (f g : (R → W) → ℝ) (B : R → W) :
    project D (fun C => f C-g C) B = project D f B-project D g B := by
  simp only [project,BinaryFourier.coefficient,sub_mul,Finset.expect_sub_distrib,Finset.sum_sub_distrib]

omit [DecidableEq W] in
lemma project_energy_le (D : ℕ) (f : (R → W) → ℝ) :
    (𝔼 B, (project D f B)^2) ≤ 𝔼 B, (f B)^2 := by
  rw [← BinaryFourier.parseval,← BinaryFourier.parseval]
  simp only [coefficient_project]
  apply Finset.sum_le_sum
  intro α _
  split_ifs <;> simp [sq_nonneg]

omit [DecidableEq ι] in
lemma project_memLp (D : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (B : R → W) :
    MemLp (fun c => project D (fun C => u C c) B) 2 (γpi ι) := by
  simp_rw [project_eq_mask_sum]
  exact memLp_finsetSum _ (fun S _ => memLp_maskProject S u hu B)

lemma rectangle_eq_composition (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) :
    selectedProject (rectangle D s) u B c =
      project D (fun C => GaussianHermite.project s (u C) c) B := by
  unfold selectedProject rectangle
  have he := Finset.sum_product
    (Finset.univ.filter (fun S : Finset R => S.card≤D)) (GaussianHermite.low s)
    (fun j => maskHermite j.1 j.2 u B c)
  change (∑ j ∈ (Finset.univ.filter (fun S : Finset R => S.card≤D)) ×ˢ
    (GaussianHermite.low s), maskHermite j.1 j.2 u B c) = _
  rw [he]
  simp only [GaussianHermite.project]
  rw [project_sum]
  simp only [project_eq_mask_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro S _
  simp only [maskHermite,hermiteComponent,mul_comm]

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

lemma lowGradient_memLp (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (x : Point m n) :
    MemLp (fun c => lowGradient D s f σ η B c x) 2 (gauss (Point m n)) :=
  memLp_selectedProject _ _ _

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ArraySum
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def arraySum (B : FaceArray A m n) (x : Point m n) : Forms A := ∑ i : Fin m, B ⟨i,face x i⟩

lemma arraySum_apply (B : FaceArray A m n) (x : Point m n) (a : A) :
    arraySum B x a = ∑ i : Fin m, B ⟨i,face x i⟩ a := by
  let ev : Forms A →+ F₂ := { toFun := fun L => L a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev (fun i : Fin m => B ⟨i,face x i⟩) Finset.univ

lemma labelCode_eq_of_arraySum (B C : FaceArray A m n) (h : ∀ x, arraySum B x = arraySum C x)
    (a : A) : labelCode B a = labelCode C a := by
  apply Subtype.ext
  funext x
  have hh := congrArg (fun L : Forms A => L a) (h x)
  simpa only [arraySum_apply, labelCode_apply] using hh

lemma gradient_eq_of_arraySum (f : FoldedProof A) (B C : FaceArray A m n)
    (h : ∀ x, arraySum B x = arraySum C x) (σ η : ℝ) :
    gradient f B σ η = gradient f C σ η := by
  have hp : ∀ u d, pullQuery B u d = pullQuery C u d := by
    intros u d; funext a
    simp only [pullQuery, labelCode_eq_of_arraySum B C h]
  funext c x
  simp only [gradient, smooth, hp]

def addConstantArray (B : FaceArray A m n) (k : Row m n → F₂) : FaceArray A m n :=
  fun r => B r + AffineMap.const F₂ A (k r)

def rowCode (k : Row m n → F₂) : Code m n := ⟨faceSum m n k, ⟨k,rfl⟩⟩

lemma labelCode_addConstantArray (B : FaceArray A m n) (k : Row m n → F₂) (a : A) :
    labelCode (addConstantArray B k) a = labelCode B a + rowCode k := by
  apply Subtype.ext
  funext x
  simp [labelCode_apply, addConstantArray, rowCode, faceSum, Finset.sum_add_distrib]

def diagonal {ι : Type*} (k : ι → F₂) (u : ι → ℝ) : ι → ℝ :=
  fun x => BinaryFourier.sign (k x)*u x

lemma diagonal_involutive {ι : Type*} (k : ι → F₂) : Function.Involutive (diagonal k) := by
  intro u
  funext x
  dsimp [diagonal]
  rw [← mul_assoc, ← sq, BinaryFourier.sign_sq, one_mul]

lemma diagonal_add {ι : Type*} (k : ι → F₂) (u v : ι → ℝ) :
    diagonal k (u+v) = diagonal k u + diagonal k v := by
  funext x; exact mul_add _ _ _

lemma diagonal_smul {ι : Type*} (k : ι → F₂) (t : ℝ) (u : ι → ℝ) :
    diagonal k (t • u) = t • diagonal k u := by
  funext x; dsimp [diagonal]; ring

lemma diagonal_preserves {ι : Type*} [Fintype ι] (k : ι → F₂) :
    MeasurePreserving (diagonal k) (gauss ι) (gauss ι) := by
  apply measurePreserving_pi
  intro x
  change MeasurePreserving (fun t : ℝ => BinaryFourier.sign (k x)*t) _ _
  by_cases hk : k x = 0
  · rw [show (fun t : ℝ => BinaryFourier.sign (k x)*t) = id by funext t; simp [hk]]
    exact MeasurePreserving.id (gaussianReal 0 1)
  · rw [show (fun t : ℝ => BinaryFourier.sign (k x)*t) = (fun t => -t) by
      funext t; simp [BinaryFourier.sign, hk]]
    exact ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

lemma integral_diagonal {ι : Type*} [Fintype ι] (k : ι → F₂) (F : (ι → ℝ) → ℝ) :
    (∫ u, F (diagonal k u) ∂gauss ι) = ∫ u, F u ∂gauss ι := by
  let e : Homeomorph (ι → ℝ) (ι → ℝ) :=
    { toEquiv := (diagonal_involutive k).toPerm
      continuous_toFun := by fun_prop [diagonal]
      continuous_invFun := by fun_prop [diagonal] }
  exact (diagonal_preserves k).integral_comp e.measurableEmbedding F

lemma integral_code_translate (k : Code m n) (F : (Code m n → ℝ) → ℝ) :
    (∫ l, F (fun z => l (z+k)) ∂gauss (Code m n)) = ∫ l, F l ∂gauss (Code m n) := by
  let e := Equiv.addRight k
  let p := MeasurableEquiv.piCongrLeft (fun _ : Code m n => ℝ) e
  have hp := measurePreserving_piCongrLeft (fun _ : Code m n => gaussianReal 0 1) e
  have he (l : Code m n → ℝ) : p l = (fun z => l (z+k)) := by
    funext z
    calc p l z = p l (e (e.symm z)) := by rw [e.apply_symm_apply]
         _ = l (e.symm z) := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Code m n => ℝ) e l (e.symm z)
         _ = l (z+k) := by
           congr 1
           simp [e, Equiv.addRight, BinaryFourier.neg_eq]
  have hh := hp.integral_comp p.measurableEmbedding F
  change (∫ l, F (p l) ∂gauss (Code m n)) = ∫ l, F l ∂gauss (Code m n) at hh
  simpa only [he] using hh

lemma query_translate (k z : Code m n) (u : Point m n → ℝ) (d : Code m n → ℝ) :
    query u d (z+k) = query (diagonal k.val u) (fun w => d (w+k)) z := by
  unfold query
  congr 2
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change u x * BinaryFourier.sign (z.val x+k.val x) = _
  rw [BinaryFourier.sign_add]
  dsimp [diagonal]
  ring

lemma pullQuery_addConstantArray (B : FaceArray A m n) (k : Row m n → F₂)
    (u : Point m n → ℝ) (d : Code m n → ℝ) :
    pullQuery (addConstantArray B k) u d =
      pullQuery B (diagonal (rowCode k).val u) (fun z => d (z+rowCode k)) := by
  funext a
  dsimp only [pullQuery]
  rw [labelCode_addConstantArray, query_translate]

end MinUncut.Inner
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

lemma doubleMatch_rowFill (i j : Fin m) (q x : Point m n) (t : Fin m) (ht : t=i ∨ t=j) :
    doubleMatch i j q (rowFill q ⟨t,face x t⟩) ↔ doubleMatch i j q x := by
  unfold doubleMatch
  have hh (u : Fin m) (hui : u ≠ i) (huj : u ≠ j) : u ≠ t := by
    rcases ht with rfl | rfl <;> assumption
  simp only [rowFill, face]
  constructor
  · intro h u hui huj
    simpa only [dite_eq_right (hh u hui huj)] using h u hui huj
  · intro h u hui huj
    simpa only [dite_eq_right (hh u hui huj)] using h u hui huj

def cylinderArray (i j : Fin m) (q : Point m n) (a : Forms A) : FaceArray A m n :=
  fun r => if (r.1=i ∨ r.1=j) ∧ doubleMatch i j q (rowFill q r) then a else 0

lemma cylinderArray_local (i j : Fin m) (q x : Point m n) (a : Forms A) (t : Fin m) :
    cylinderArray i j q a ⟨t,face x t⟩ =
      if t=i ∨ t=j then (if doubleMatch i j q x then a else 0) else 0 := by
  by_cases ht : t=i ∨ t=j
  · simp only [cylinderArray, ht, true_and, ite_true, doubleMatch_rowFill i j q x t ht]
  · simp only [cylinderArray, ht, false_and, ite_false]

lemma cylinderArray_sum_zero (i j : Fin m) (hij : i ≠ j) (q x : Point m n) (a : Forms A) :
    arraySum (cylinderArray i j q a) x = 0 := by
  unfold arraySum
  simp_rw [cylinderArray_local]
  have he (t : Fin m) : (if t=i ∨ t=j then (if doubleMatch i j q x then a else 0) else 0) =
      (if t=i then (if doubleMatch i j q x then a else 0) else 0) +
      (if t=j then (if doubleMatch i j q x then a else 0) else 0) := by
    by_cases hi : t=i <;> by_cases hj : t=j <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact BinaryFourier.self_add _

lemma arraySum_add (B C : FaceArray A m n) (x : Point m n) :
    arraySum (B+C) x = arraySum B x + arraySum C x := Finset.sum_add_distrib

theorem gradient_cylinder (f : FoldedProof A) (B : FaceArray A m n)
    (i j : Fin m) (hij : i ≠ j) (q : Point m n) (a : Forms A) (σ η : ℝ) :
    gradient f (B+cylinderArray i j q a) σ η = gradient f B σ η := by
  apply gradient_eq_of_arraySum
  intro x
  rw [arraySum_add, cylinderArray_sum_zero i j hij, add_zero]

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Parity
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
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma H_neg (d : ℕ) (x : ℝ) : H d (-x) = (-1 : ℝ)^d * H d x := by
  have hh := H_noise (-1) 0 x (by norm_num) d
  simpa [γ] using hh

lemma H_sign (d : ℕ) (k : BinaryFourier.F₂) (x : ℝ) :
    H d (BinaryFourier.sign k*x) = BinaryFourier.sign (k*(d : BinaryFourier.F₂))*H d x := by
  have hs : BinaryFourier.sign (d : BinaryFourier.F₂) = (-1 : ℝ)^d := by
    induction d with
    | zero => simp
    | succ d ih => simp [Nat.cast_add, BinaryFourier.sign_add, ih, pow_succ]
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : k = 1 := by
      have h : ∀ a : BinaryFourier.F₂, a = 0 ∨ a=1 := by decide
      exact (h k).resolve_left hk
    simp only [hk1, BinaryFourier.sign_one, neg_one_mul, one_mul, H_neg, hs]

variable {ι : Type*} [Fintype ι]

def parity (k : ι → BinaryFourier.F₂) (a : ι → ℕ) : BinaryFourier.F₂ := ∑ i, k i * (a i : BinaryFourier.F₂)

lemma psi_diagonal (k : ι → BinaryFourier.F₂) (a : ι → ℕ) (c : ι → ℝ) :
    psi a (Inner.diagonal k c) = BinaryFourier.sign (parity k a) * psi a c := by
  simp only [psi, Inner.diagonal, H_sign, Finset.prod_mul_distrib, parity, RowNoise.sign_sum]

lemma coeff_diagonal (k : ι → BinaryFourier.F₂) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (fun c => f (Inner.diagonal k c)) a = BinaryFourier.sign (parity k a)*coeff f a := by
  unfold coeff
  change (∫ c, psi a c * f (Inner.diagonal k c) ∂Inner.gauss ι) =
    BinaryFourier.sign (parity k a)*(∫ c, psi a c*f c ∂Inner.gauss ι)
  rw [← Inner.integral_diagonal k (fun c => psi a c * f (Inner.diagonal k c))]
  simp only [Inner.diagonal_involutive k _, psi_diagonal, mul_assoc, integral_const_mul]

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointCoefficient
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
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def jointCoefficient (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ) : ℝ :=
  BinaryFourier.coefficient
    (fun B => GaussianHermite.coeff (fun c => gradient f B σ η c x) I) α

def constantArray (k : Row m n → F₂) : FaceArray A m n := fun r => AffineMap.const F₂ A (k r)

omit [Fintype A] in
lemma constantArray_add (B : FaceArray A m n) (k : Row m n → F₂) :
    constantArray k+B = addConstantArray B k := by
  funext r; exact add_comm _ _

lemma sign_injective : Function.Injective BinaryFourier.sign := by
  intro a b hab
  have h : ∀ x : F₂, x=0 ∨ x=1 := by decide
  rcases h a with rfl | rfl
  · rcases h b with rfl | rfl
    · rfl
    · norm_num at hab
  · rcases h b with rfl | rfl
    · norm_num at hab
    · rfl

theorem joint_cylinder_gauge (f : FoldedProof A) (σ η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0)
    (i j : Fin m) (hij : i ≠ j) (q : Point m n) (a : Forms A) :
    α (cylinderArray i j q a) = 0 := by
  have ht := BinaryFourier.coefficient_translate
    (fun B : FaceArray A m n => GaussianHermite.coeff (fun c => gradient f B σ η c x) I)
    α (cylinderArray i j q a)
  have hg (B : FaceArray A m n) : gradient f (cylinderArray i j q a+B) σ η =
      gradient f B σ η := by rw [add_comm, gradient_cylinder f B i j hij]
  simp only [hg] at ht
  by_contra hn
  have hs : BinaryFourier.character α (cylinderArray i j q a) = -1 := by
    simp [BinaryFourier.character, BinaryFourier.sign, hn]
  rw [hs] at ht
  exact hne (by change jointCoefficient f σ η x α I = -1*jointCoefficient f σ η x α I at ht; linarith)
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SingleRow
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
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def singleRow (r : Row m n) : Row m n → F₂ := Pi.single r 1

lemma rowCode_singleRow (r : Row m n) (u : Point m n) :
    (rowCode (singleRow r)).val u = if face u r.1=r.2 then 1 else 0 := by
  change (∑ i : Fin m, (Pi.single r (1:F₂) : Row m n → F₂) ⟨i,face u i⟩) = _
  rw [Finset.sum_eq_single r.1]
  · by_cases hh : face u r.1=r.2
    · simp [hh]
    · have he : (⟨r.1,face u r.1⟩ : Row m n) ≠ r := by
        intro he; cases r; simp_all
      simp [hh, Pi.single_eq_of_ne he]
  · intro i _ hi
    apply Pi.single_eq_of_ne
    intro he
    exact hi (congrArg Sigma.fst he)
  · simp

omit [Fintype A] in
lemma constantArray_singleRow (r : Row m n) :
    constantArray (singleRow r) = Pi.single r (AffineMap.const F₂ A 1) := by
  funext t
  by_cases ht : t=r
  · subst t; simp [constantArray, singleRow]
  · simp only [constantArray, singleRow, Pi.single_eq_of_ne ht]
    rfl

lemma frequency_cylinder (α : Module.Dual F₂ (FaceArray A m n))
    (x : Point m n) (i j : Fin m) (hij : i ≠ j)
    (hi : ∀ y, RowNoise.frequency α ⟨i,y⟩ ≠ 0 →
      doubleMatch i j x (rowFill x ⟨i,y⟩) → y=face x i)
    (hj : ∀ y, RowNoise.frequency α ⟨j,y⟩ ≠ 0 →
      doubleMatch j i x (rowFill x ⟨j,y⟩) → y=face x j) (a : Forms A) :
    α (cylinderArray i j x a) =
      RowNoise.frequency α ⟨i,face x i⟩ a + RowNoise.frequency α ⟨j,face x j⟩ a := by
  rw [RowNoise.dual_apply]
  have he (r : Row m n) : RowNoise.frequency α r (cylinderArray i j x a r) =
      (if r=⟨i,face x i⟩ then RowNoise.frequency α ⟨i,face x i⟩ a else 0) +
      (if r=⟨j,face x j⟩ then RowNoise.frequency α ⟨j,face x j⟩ a else 0) := by
    by_cases hr : r=⟨i,face x i⟩
    · subst r
      have hne : (⟨i,face x i⟩ : Row m n) ≠ ⟨j,face x j⟩ := by
        intro he; exact hij (congrArg Sigma.fst he)
      simp [hne, cylinderArray_local, doubleMatch]
    by_cases hr' : r=⟨j,face x j⟩
    · subst r
      simp [hr, cylinderArray_local, doubleMatch]
    simp only [ite_eq_right hr, ite_eq_right hr', zero_add]
    by_cases ha : RowNoise.frequency α r=0
    · simp [ha]
    · unfold cylinderArray
      split_ifs with hc
      · rcases r with ⟨t,y⟩
        rcases hc.1 with ht | ht
        · change t=i at ht
          subst t
          exact False.elim (hr (by rw [hi y ha hc.2]))
        · change t=j at ht
          subst t
          have hc' : doubleMatch j i x (rowFill x ⟨j,y⟩) :=
            fun u huj hui => hc.2 u hui huj
          exact False.elim (hr' (by rw [hj y ha hc']))
      · simp
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Away
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
namespace MinUncut.Subbox
open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

lemma expect_coordinate {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]
    (i : ι) (f : B i → ℝ) : (𝔼 x : ∀ j, B j, f (x i)) = 𝔼 b, f b := by
  calc
    _ = 𝔼 p : B i × (∀ j : {j // j ≠ i}, B j), f p.1 := by
      apply Fintype.expect_equiv (Equiv.piSplitAt i B)
      intro x
      rfl
    _ = _ := by rw [expect_pair]; simp

end MinUncut.Subbox
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [Fintype R] [Fintype W] [DecidableEq W] in
lemma character_single (α : Module.Dual F₂ (R → W)) (r : R) (b : W) :
    character α (Pi.single r b)=character (frequency α r) b := rfl

local instance awayRowNoiseDualFintype_r5d4563_1 {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
lemma localSlice_odd (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (F : Finset R) (r : R) (e : W)
    (ho : ∀ j ∈ J, ∀ α : Module.Dual F₂ (R → W), mask α=j.1 →
      coefficient (fun B => coeff (u B) j.2) α ≠ 0 → frequency α r e=1)
    (C : R → W) (c : ι → ℝ) (b : W) :
    localSlice J u F r C c (b+e) = -localSlice J u F r C c b := by
  unfold localSlice selectedProject
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq, maskProject_expansion]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hmask : mask α=j.1
  swap
  · simp [hmask]
  rw [ite_eq_left hmask, ite_eq_left hmask]
  by_cases hc : coefficient (fun B => coeff (u B) j.2) α=0
  · simp [hc]
  have he : character (frequency α r) e = -1 := by simp [character,ho j hj α hmask hc]
  simp only [character_add, character_single, he]
  ring

omit [DecidableEq W] in
lemma odd_coefficient_zero (v : W → ℝ) (e : W) (hv : ∀ b, v (b+e) = -v b)
    (α : Module.Dual F₂ W) (hα : α e≠1) : coefficient v α=0 := by
  have hz : α e=0 := by
    have hh : ∀ a : F₂, a=0 ∨ a=1 := by decide
    exact (hh (α e)).resolve_right hα
  have ht := coefficient_translate v α e
  have hh : (fun b => v (e+b)) = fun b => -v b := by funext b; rw [add_comm, hv]
  rw [hh] at ht
  simp only [coefficient, neg_mul, Finset.expect_neg_distrib, character, hz, BinaryFourier.sign_zero, one_mul] at ht
  change -coefficient v α=coefficient v α at ht
  linarith

end MinUncut.RowNoise
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

lemma maskClass_some (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (p : PairClass m) (hp : maskClass x I S=some p) : I x=0 ∧ PairAdmissible x I S p := by
  unfold maskClass at hp
  split_ifs at hp with hx he
  have hp' := Option.some.inj hp
  have hm := Finset.min'_mem (admissibleClasses x I S) he
  rw [hp'] at hm
  exact ⟨Nat.eq_zero_of_not_pos hx,(Finset.mem_filter.mp hm).2⟩

lemma classSelection_partition (x : Point m n)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (v : (Finset (Row m n) × (Point m n → ℕ)) → ℝ) :
    (∑ j ∈ J, v j) = ∑ a : Option (PairClass m), ∑ j ∈ classSelection x a J, v j := by
  simp only [classSelection, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp
end MinUncut.Inner
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma retained_pair_admissible (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (p : PairClass m) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j∈retainedClass x H (some p) J) :
    PairAdmissible x j.2 j.1 p := by
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  exact (maskClass_some x j.2 j.1 p hc).2

lemma pairSlice_background (f : FoldedProof A) (σ η : ℝ)
    (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (C D : FaceArray A m n) (hCD : ∀ t ∉ freePairRows x H p, C t=D t) :
    pairSlice f σ η x H p J C=pairSlice f σ η x H p J D := by
  have he : zeroFree (freePairRows x H p) C=zeroFree (freePairRows x H p) D := by
    funext t
    by_cases ht : t∈freePairRows x H p
    · simp [zeroFree,ht]
    · simp [zeroFree,ht,hCD t ht]
  funext c b
  unfold pairSlice localSlice
  rw [he]
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FaceUpdateSelf
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
open scoped BigOperators
variable {m n : ℕ}

lemma face_update_self (x : Point m n) (i : Fin m) (z : Fin n) :
    face (Function.update x i z) i = face x i := by
  funext j
  exact Function.update_of_ne j.property _ _

theorem faceCorrelation_box_cs (hm : 0 < m) (hn : 0 < n) (v : Point m n → ℝ) :
    faceCorrelation v ^ (2^m) ≤ Box.moment v := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun z : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)|)
  change faceCorrelation v = _ at hz
  obtain ⟨b, hb⟩ := z.property
  let a : Fin m → Point m n → ℝ := fun i x => BinaryFourier.sign (b ⟨i, face x i⟩)
  have ha : Box.Local a := by
    intro i x t
    simp only [a, face_update_self]
  have hc : |Box.correlation v a| = faceCorrelation v := by
    rw [hz]
    unfold Box.correlation
    congr 1
    apply Finset.expect_congr rfl
    intro x _
    congr 1
    have hbx : z.val x = ∑ i, b ⟨i, face x i⟩ := congrFun hb.symm x
    simp only [hbx, RowNoise.sign_sum, a]
  rw [← hc]
  exact Box.abs_correlation_cs hm v a ha (fun _ _ => (BinaryFourier.sign_abs _).le)
end MinUncut.Inner

namespace MinUncut.Slice
open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

lemma clip_abs_le_self {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : |clip A z| ≤ |z| := by
  unfold clip
  rcases le_total z A with hz | hz
  · rw [min_eq_left hz]
    rcases le_total (-A) z with ha | ha
    · rw [max_eq_right ha]
    · rw [max_eq_left ha, abs_neg, abs_of_nonneg hA, abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_right hz, max_eq_right (by linarith), abs_of_nonneg hA,
      abs_of_nonneg (by linarith)]
    exact hz

lemma clip_sq_le {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : clip A z ^2 ≤ z^2 := by
  have h := clip_abs_le_self hA z
  nlinarith [abs_nonneg (clip A z), abs_nonneg z, sq_abs (clip A z), sq_abs z]

omit [DecidableEq W] in
lemma coefficient_lipschitz (f g : W → ℝ) (α : Module.Dual F₂ W) :
    |coefficient f α - coefficient g α| ≤ 𝔼 w, |f w-g w| := by
  simp only [coefficient, ← Finset.expect_sub_distrib, ← sub_mul]
  calc
    _ ≤ 𝔼 w, |(f w-g w)*character α w| := by
      simp only [Finset.expect_eq_sum_div_card, abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = _ := by simp only [abs_mul, character_abs, mul_one]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma clip_mean_loss {A : ℝ} (hA : 0 < A) (f : W → ℝ) :
    (𝔼 w, |f w-clip A (f w)|) ≤ (𝔼 w, (f w)^2)/A := by
  calc
    _ ≤ 𝔼 w, (f w)^2/A := Finset.expect_le_expect (fun w _ => clip_loss hA (f w))
    _ = _ := by simp [Finset.expect_div]

attribute [local instance] OAI.MinUncut.Slice.faceUpdateSelfSliceDualFintype
omit [DecidableEq W] in
lemma oddMax_nonneg (one : W) (f : W → ℝ) : 0 ≤ oddMax one f := by
  have h := Finset.le_sup' (fun α : Module.Dual F₂ W =>
    if α one = 1 then |coefficient f α| else 0) (Finset.mem_univ 0)
  change 0 ≤ Finset.univ.sup' Finset.univ_nonempty _
  simpa only [LinearMap.zero_apply, zero_ne_one, ↓reduceIte] using h

omit [DecidableEq W] in
lemma coefficient_le_oddMax (one : W) (f : W → ℝ)
    (hodd : ∀ α : Module.Dual F₂ W, α one ≠ 1 → coefficient f α = 0)
    (α : Module.Dual F₂ W) : |coefficient f α| ≤ oddMax one f := by
  by_cases h : α one = 1
  · have h' := Finset.le_sup' (fun α : Module.Dual F₂ W =>
      if α one = 1 then |coefficient f α| else 0) (Finset.mem_univ α)
    simpa only [h, ↓reduceIte, oddMax] using h'
  · rw [hodd α h, abs_zero]
    exact oddMax_nonneg one f

omit [DecidableEq W] in
lemma processed_abs_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) (w : W) :
    |processed H γ A one f w| ≤ A := by
  unfold processed; split_ifs
  · simpa using hA
  · exact clip_abs_le hA _

omit [DecidableEq W] in
lemma processed_sq_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) (w : W) :
    (processed H γ A one f w)^2 ≤ (f w)^2 := by
  unfold processed; split_ifs
  · simpa using sq_nonneg (f w)
  · exact clip_sq_le hA _

omit [DecidableEq W] in
lemma processed_coefficient_le {H γ A : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ)
    (one : W) (f : W → ℝ)
    (hodd : ∀ α : Module.Dual F₂ W, α one ≠ 1 → coefficient f α = 0)
    (α : Module.Dual F₂ W) :
    |coefficient (processed H γ A one f) α| ≤ γ + H^2/A := by
  by_cases h : H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f
  · simp only [processed, h, ↓reduceIte, coefficient, zero_mul, Fintype.expect_const, abs_zero]
    positivity
  · have hs : Real.sqrt (𝔼 b, (f b)^2) ≤ H := le_of_not_gt (fun ht => h (Or.inl ht))
    have hq : oddMax one f ≤ γ := le_of_not_gt (fun ht => h (Or.inr ht))
    have he : 0 ≤ 𝔼 b, (f b)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
    have hE : (𝔼 b, (f b)^2) ≤ H^2 := by
      nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (𝔼 b, (f b)^2)]
    have hp : processed H γ A one f = fun w => clip A (f w) := by funext w; simp only [processed, h, ↓reduceIte]
    rw [hp]
    calc
      _ ≤ |coefficient (fun w => clip A (f w)) α - coefficient f α| + |coefficient f α| := by
        have hh := abs_add_le (coefficient (fun w => clip A (f w)) α - coefficient f α) (coefficient f α)
        simpa only [sub_add_cancel] using hh
      _ ≤ (𝔼 w, |clip A (f w)-f w|) + oddMax one f := add_le_add
        (coefficient_lipschitz _ _ _) (coefficient_le_oddMax one f hodd α)
      _ = (𝔼 w, |f w-clip A (f w)|) + oddMax one f := by simp_rw [abs_sub_comm]
      _ ≤ (𝔼 w, (f w)^2)/A + γ := add_le_add (clip_mean_loss hA f) hq
      _ ≤ γ + H^2/A := by linarith [div_le_div_of_nonneg_right hE (le_of_lt hA)]

open BinaryFourier
end MinUncut.Slice
namespace MinUncut.IndependentSquares
open BinaryFourier
variable {C W : Type*} [Fintype C] [DecidableEq C] [Fintype W]
  [DecidableEq W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq W] [Module F₂ W] in
lemma factor_squares (V : C → Bool → Bool → W → ℝ) :
    (𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, 𝔼 s₁ : C → W,
      ∏ c, V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁ c) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁ c)) =
      ∏ c, 𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀+s₀) * V c false true (r₀+s₁) *
        V c true false (r₁+s₀) * V c true true (r₁+s₁) := by
  calc
    _ = 𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, ∏ c, 𝔼 s₁,
        V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      apply Finset.expect_congr rfl; intro r₁ _
      apply Finset.expect_congr rfl; intro s₀ _
      exact expect_prod (fun c s₁ => V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁) * V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁))
    _ = 𝔼 r₀ : C → W, 𝔼 r₁ : C → W, ∏ c, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) *
        V c true false (r₁ c+s₀) * V c true true (r₁ c+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      apply Finset.expect_congr rfl; intro r₁ _
      exact expect_prod (fun c s₀ => 𝔼 s₁, V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) * V c true false (r₁ c+s₀) * V c true true (r₁ c+s₁))
    _ = 𝔼 r₀ : C → W, ∏ c, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
        V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) *
        V c true false (r₁+s₀) * V c true true (r₁+s₁) := by
      apply Finset.expect_congr rfl; intro r₀ _
      exact expect_prod (fun c r₁ => 𝔼 s₀, 𝔼 s₁, V c false false (r₀ c+s₀) * V c false true (r₀ c+s₁) * V c true false (r₁+s₀) * V c true true (r₁+s₁))
    _ = _ := expect_prod (fun c r₀ => 𝔼 r₁, 𝔼 s₀, 𝔼 s₁, V c false false (r₀+s₀) * V c false true (r₀+s₁) * V c true false (r₁+s₀) * V c true true (r₁+s₁))

omit [DecidableEq W] in
lemma independent_square_bound (V : C → Bool → Bool → W → ℝ) (ε H : ℝ)
    (hε : 0 ≤ ε)
    (hcoef : ∀ c a b α, |coefficient (V c a b) α| ≤ ε)
    (henergy : ∀ c a b, (𝔼 w, (V c a b w)^2) ≤ H^2) :
    |𝔼 r₀ : C → W, 𝔼 r₁ : C → W, 𝔼 s₀ : C → W, 𝔼 s₁ : C → W,
      ∏ c, V c false false (r₀ c+s₀ c) * V c false true (r₀ c+s₁ c) *
        V c true false (r₁ c+s₀ c) * V c true true (r₁ c+s₁ c)| ≤
      (ε^2*H^2)^Fintype.card C := by
  rw [factor_squares, Finset.abs_prod]
  calc
    _ ≤ ∏ _c : C, ε^2*H^2 := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro c _
      exact square_bound _ _ _ _ ε H hε (hcoef c false false) (hcoef c false true)
        (henergy c true false) (henergy c true true)
    _ = _ := by simp

def restrictLinear {R D : Type*} (j : D → R) : (R → W) →ₗ[F₂] (D → W) where
  toFun B := B ∘ j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype W] [DecidableEq W] in
lemma restrict_surjective {R D : Type*} (j : D → R) (hj : Function.Injective j) :
    Function.Surjective (restrictLinear (W := W) j) := by
  classical
  intro b
  refine ⟨Function.extend j b (fun _ => 0), ?_⟩
  funext d
  exact hj.extend_apply b (fun _ => 0) d

lemma expect_surjective_linear {G H : Type*} [Fintype G] [AddCommGroup G] [Module F₂ G]
    [Fintype H] [AddCommGroup H] [Module F₂ H]
    (φ : G →ₗ[F₂] H) (hφ : Function.Surjective φ) (f : H → ℝ) :
    (𝔼 g, f (φ g)) = 𝔼 h, f h := by
  have h (h : H) : (𝔼 g, f (h+φ g)) = 𝔼 g, f (φ g) := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [map_add] using expect_translate (fun a => f (φ a)) g
  calc
    _ = 𝔼 h', 𝔼 g, f (h'+φ g) := by simp_rw [h]; simp
    _ = 𝔼 g, 𝔼 h', f (h'+φ g) := Finset.expect_comm _ _ _
    _ = 𝔼 g : G, 𝔼 h', f h' := by
      apply Finset.expect_congr rfl
      intro g _
      simpa only [add_comm] using expect_translate f (φ g)
    _ = _ := by simp

omit [DecidableEq W] in
lemma expect_restrict {R D : Type*} [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D]
    (j : D → R) (hj : Function.Injective j) (f : (D → W) → ℝ) :
    (𝔼 B : R → W, f (B ∘ j)) = 𝔼 b, f b :=
  expect_surjective_linear (restrictLinear j) (restrict_surjective j hj) f
end MinUncut.IndependentSquares

namespace MinUncut.CubeRows
open BinaryFourier IndependentSquares
variable {ι A W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

variable {C : Type*} [Fintype C] [DecidableEq C]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma expect_boolSplit (f : (C → W) → (C → W) → ℝ) :
    (𝔼 t : (C × Bool) → W, f (fun c => t (c,false)) (fun c => t (c,true))) =
      𝔼 t₀ : C → W, 𝔼 t₁ : C → W, f t₀ t₁ := by
  rw [← Finset.expect_product', Finset.univ_product_univ]
  exact Fintype.expect_equiv boolSplitEquiv _ _ (fun _ => rfl)

omit [Fintype W] [DecidableEq W] [Module F₂ W] in
lemma cubeProduct_eq (i j : ι) (hij : i ≠ j) (x y : ι → A)
    (V : (ι → Bool) → W → ℝ)
    (Bj : ({k : ι // k ≠ j} → A) → W) (Bi : ({k : ι // k ≠ i} → A) → W) :
    (∏ ν : ι → Bool, V ν (Bj (face j (vertex ν x y)) + Bi (face i (vertex ν x y)))) =
      squareProduct i j V (Bj ∘ rowJ i j x y) (Bi ∘ rowI i j x y) := by
  rw [prod_split i j hij]
  simp only [face_join_J i j hij, face_join_I i j hij, squareProduct, Function.comp_apply]

omit [DecidableEq W] in
lemma cubeExpectation_restrict [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) :
    cubeExpectation i j x y V = 𝔼 r, 𝔼 s, squareProduct i j V r s := by
  unfold cubeExpectation
  simp_rw [cubeProduct_eq i j hij]
  have hBi (r) := expect_restrict (rowI i j x y) (rowI_injective i j hij x y hxy)
    (squareProduct i j V r)
  calc
    _ = 𝔼 Bj, 𝔼 s, squareProduct i j V (Bj ∘ rowJ i j x y) s := by
      apply Finset.expect_congr rfl
      intro Bj _
      exact hBi (Bj ∘ rowJ i j x y)
    _ = _ := expect_restrict (rowJ i j x y) (rowJ_injective i j hij x y hxy)
      (fun r => 𝔼 s, squareProduct i j V r s)

omit [DecidableEq W] in
lemma cubeExpectation_eq_squares [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) :
    cubeExpectation i j x y V =
    𝔼 r₀ : (Other i j → Bool) → W, 𝔼 r₁ : (Other i j → Bool) → W,
    𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r₀ c+s₀ c) * V (join i j c false true) (r₀ c+s₁ c) *
        V (join i j c true false) (r₁ c+s₀ c) * V (join i j c true true) (r₁ c+s₁ c) := by
  rw [cubeExpectation_restrict i j hij x y hxy V]
  let F := squareProduct i j V
  change (𝔼 r, 𝔼 s, F r s) = _
  have hs (r : ((Other i j → Bool) × Bool) → W) : (𝔼 s, F r s) =
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
        V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c) := expect_boolSplit (fun s₀ s₁ =>
      ∏ c : Other i j → Bool,
        V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
        V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c))
  trans 𝔼 r : ((Other i j → Bool) × Bool) → W,
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
        ∏ c : Other i j → Bool,
          V (join i j c false false) (r (c,false)+s₀ c) * V (join i j c false true) (r (c,false)+s₁ c) *
          V (join i j c true false) (r (c,true)+s₀ c) * V (join i j c true true) (r (c,true)+s₁ c)
  · exact Finset.expect_congr rfl (fun r _ => hs r)
  · exact expect_boolSplit (fun r₀ r₁ : (Other i j → Bool) → W =>
      𝔼 s₀ : (Other i j → Bool) → W, 𝔼 s₁ : (Other i j → Bool) → W,
        ∏ c : Other i j → Bool,
          V (join i j c false false) (r₀ c+s₀ c) * V (join i j c false true) (r₀ c+s₁ c) *
          V (join i j c true false) (r₁ c+s₀ c) * V (join i j c true true) (r₁ c+s₁ c))

omit [DecidableEq W] in
lemma cubeExpectation_bound [Fintype A] [DecidableEq A]
    (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k)
    (V : (ι → Bool) → W → ℝ) (ε H : ℝ) (hε : 0 ≤ ε)
    (hcoef : ∀ ν α, |coefficient (V ν) α| ≤ ε)
    (henergy : ∀ ν, (𝔼 w, (V ν w)^2) ≤ H^2) :
    |cubeExpectation i j x y V| ≤ (ε^2*H^2)^(2^Fintype.card (Other i j)) := by
  rw [cubeExpectation_eq_squares i j hij x y hxy V]
  have h := independent_square_bound (fun c a b => V (join i j c a b)) ε H hε
    (fun c a b => hcoef _) (fun c a b => henergy _)
  simpa only [Fintype.card_fun, Fintype.card_bool] using h
end MinUncut.CubeRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CollisionIndicator
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
namespace MinUncut.CubeRows
open BinaryFourier IndependentSquares
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι A W : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq ι] [Fintype A] [Nonempty A] in
lemma collision_indicator (x y : ι → A) :
    (if ∃ i, x i=y i then (1:ℝ) else 0) ≤ ∑ i, if x i=y i then (1:ℝ) else 0 := by
  by_cases h : ∃ i, x i=y i
  · obtain ⟨i,hi⟩ := h
    simpa only [ite_eq_left (show ∃ j, x j=y j from ⟨i,hi⟩),ite_eq_left hi] using
      (Finset.single_le_sum (s := Finset.univ) (f := fun i => if x i=y i then (1:ℝ) else 0)
        (fun _ _ => by positivity) (Finset.mem_univ i))
  · simp only [ite_eq_right h]; exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma collision_probability :
    (𝔼 x : ι → A, 𝔼 y : ι → A, if ∃ i, x i=y i then (1:ℝ) else 0) ≤
      (Fintype.card ι:ℝ)/Fintype.card A := by
  have hf (x : ι → A) :
      (𝔼 y : ι → A, if ∃ i, x i=y i then (1:ℝ) else 0) ≤
        (Fintype.card ι:ℝ)/Fintype.card A := by
    calc
      _ ≤ 𝔼 y : ι → A, ∑ i, if x i=y i then (1:ℝ) else 0 :=
        Finset.expect_le_expect (fun y _ => collision_indicator x y)
      _ = ∑ i : ι, 𝔼 a : A, if x i=a then (1:ℝ) else 0 := by
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        exact Subbox.expect_coordinate (B := fun _ : ι => A) i (fun a => if x i=a then (1:ℝ) else 0)
      _ = _ := by simp [div_eq_mul_inv]
  exact (Finset.expect_le_expect (fun x _ => hf x)).trans_eq (Fintype.expect_const _)

omit [Nonempty A] [Module F₂ W] in
lemma cubeExpectation_abs_bound (i j : ι) (x y : ι → A)
    (V : (ι → Bool) → W → ℝ) {C : ℝ} (hC : 0≤C) (hV : ∀ ν w, |V ν w|≤C) :
    |cubeExpectation i j x y V| ≤ C^(2^Fintype.card ι) := by
  unfold cubeExpectation
  refine (Finset.abs_expect_le _ _).trans ?_
  apply (Finset.expect_le_expect (fun Bj _ => ?_)).trans_eq (Fintype.expect_const _)
  refine (Finset.abs_expect_le _ _).trans ?_
  apply (Finset.expect_le_expect (fun Bi _ => ?_)).trans_eq (Fintype.expect_const _)
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ ν : ι → Bool, |C| := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun ν _ => (hV ν _).trans (le_abs_self C))
    _ = _ := by simp [abs_of_nonneg hC]

lemma full_cube_bound (i j : ι) (hij : i≠j) (V : (ι → A) → W → ℝ)
    (ε H C : ℝ) (hε : 0≤ε) (hC : 0≤C)
    (hcoef : ∀ x α, |coefficient (V x) α|≤ε)
    (henergy : ∀ x, (𝔼 w, (V x w)^2)≤H^2) (hV : ∀ x w, |V x w|≤C) :
    (𝔼 x : ι → A, 𝔼 y : ι → A,
      cubeExpectation i j x y (fun ν => V (vertex ν x y))) ≤
      C^(2^Fintype.card ι)*((Fintype.card ι:ℝ)/Fintype.card A) +
        (ε^2*H^2)^(2^Fintype.card (Other i j)) := by
  let D := (ε^2*H^2)^(2^Fintype.card (Other i j))
  have hD : 0≤D := by dsimp [D]; positivity
  have hpoint (x y : ι → A) :
      cubeExpectation i j x y (fun ν => V (vertex ν x y)) ≤
        C^(2^Fintype.card ι)*(if ∃ k, x k=y k then (1:ℝ) else 0)+D := by
    by_cases hxy : ∃ k, x k=y k
    · simp only [ite_eq_left hxy,mul_one]
      exact (le_abs_self _).trans ((cubeExpectation_abs_bound i j x y _ hC (fun ν => hV _)).trans (le_add_of_nonneg_right hD))
    · simp only [ite_eq_right hxy,mul_zero,zero_add]
      exact (le_abs_self _).trans (cubeExpectation_bound i j hij x y (by simpa only [not_exists] using hxy)
        _ ε H hε (fun ν => hcoef _) (fun ν => henergy _))
  calc
    _ ≤ 𝔼 x : ι → A, 𝔼 y : ι → A,
        (C^(2^Fintype.card ι)*(if ∃ k, x k=y k then (1:ℝ) else 0)+D) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun y _ => hpoint x y))
    _ = C^(2^Fintype.card ι)*(𝔼 x : ι → A, 𝔼 y : ι → A, if ∃ k, x k=y k then (1:ℝ) else 0)+D := by
      simp only [Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const]
    _ ≤ _ := by
      simpa only [D,add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left (collision_probability (ι := ι) (A := A)) (pow_nonneg hC (2^Fintype.card ι))) D
end MinUncut.CubeRows

namespace MinUncut.Inner
open BinaryFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
variable {W : Type*} [Fintype W] [AddCommGroup W] [Module F₂ W]

def pairField (i j : Fin m) (V : Point m n → W → ℝ)
    (Bj : ({k : Fin m // k≠j} → Fin n) → W)
    (Bi : ({k : Fin m // k≠i} → Fin n) → W) (x : Point m n) : ℝ :=
  V x (Bj (face x j)+Bi (face x i))

omit [Module F₂ W] in
lemma pair_moment (hn : 0 < n) (i j : Fin m) (V : Point m n → W → ℝ) :
    (𝔼 Bj, 𝔼 Bi, Box.moment (pairField i j V Bj Bi)) =
      𝔼 x : Point m n, 𝔼 y : Point m n, CubeRows.cubeExpectation i j x y (fun ν => V (Box.vertex ν x y)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold Box.moment CubeRows.cubeExpectation pairField
  conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
  rw [Finset.expect_comm]
  rfl

theorem pair_correlation_power (hm : 0 < m) (hn : 0 < n) (i j : Fin m) (hij : i≠j)
    (V : Point m n → W → ℝ) (ε H C : ℝ) (hε : 0≤ε) (hC : 0≤C)
    (hcoef : ∀ x α, |coefficient (V x) α|≤ε)
    (henergy : ∀ x, (𝔼 w, (V x w)^2)≤H^2) (hV : ∀ x w, |V x w|≤C) :
    (𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField i j V Bj Bi))^(2^m) ≤
      C^(2^m)*((m:ℝ)/n)+(ε^2*H^2)^(2^Fintype.card (CubeRows.Other i j)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  calc
    _ ≤ 𝔼 Bj, (𝔼 Bi, faceCorrelation (pairField i j V Bj Bi))^(2^m) := Box.expect_pow_two_pow _ m
    _ ≤ 𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField i j V Bj Bi)^(2^m) :=
      Finset.expect_le_expect (fun Bj _ => Box.expect_pow_two_pow _ m)
    _ ≤ 𝔼 Bj, 𝔼 Bi, Box.moment (pairField i j V Bj Bi) :=
      Finset.expect_le_expect (fun Bj _ => Finset.expect_le_expect (fun Bi _ => faceCorrelation_box_cs hm hn _))
    _ = _ := pair_moment hn i j V
    _ ≤ _ := by
      have hc := CubeRows.full_cube_bound i j hij V ε H C hε hC hcoef henergy hV
      simp only [Fintype.card_fin] at hc
      exact hc
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
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
open Subbox
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma faceEmbed_mem {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) (j : {j : Fin m // j≠i}) :
    faceEmbed Y i v j∈(Y j.val).val := (coordinateEnum Y j.val (v j)).property

lemma extendSingle_other {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i j : Fin m) (hij : i≠j)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (v : {t : Fin m // t≠j} → Fin n) :
    extendSingle Y i B ⟨j,v⟩=0 := by
  apply Function.extend_apply'
  rintro ⟨u,hu⟩
  exact hij (congrArg Sigma.fst hu)

lemma extendSingle_support {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (r : Row m n)
    (hr : extendSingle Y i B r≠0) : r.fst=i ∧ ∀ j, r.snd j∈(Y j.val).val := by
  by_cases h : ∃ u, embedSingle Y i u=r
  · obtain ⟨u,rfl⟩ := h
    exact ⟨rfl,faceEmbed_mem Y i u⟩
  · exact (hr (Function.extend_apply' _ _ _ h)).elim
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

omit [Fintype A] in
lemma extendSingle_zero_outside_pair {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (u : Point m (k+1)) (p : PairClass m) (i : Fin m) (hi : i=p.val.1 ∨ i=p.val.2)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → Forms A) (r : Row m n)
    (hr : r∉freePairRows (pointEmbed Y u) (pointBox Y u) p) : extendSingle Y i B r=0 := by
  by_contra he
  have hs := extendSingle_support Y i B r he
  apply hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · simpa only [hs.1] using hi
  · simpa only [FaceInBox, pointBox_set] using hs.2

lemma pairSlice_add_rows (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (u : Point m (k+1)) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n)
    (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A)
    (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A) :
    pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J
      (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj) =
    pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B := by
  apply pairSlice_background
  intro r hr
  simp only [Pi.add_apply, extendSingle_zero_outside_pair Y u p p.val.1 (Or.inl rfl) Bi r hr,
    extendSingle_zero_outside_pair Y u p p.val.2 (Or.inr rfl) Bj r hr, add_zero]

lemma pairProcessedOnBox_resample (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ)
    (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A)
    (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A) :
    pairProcessedOnBox f σ η Y p J H γ A₀ (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj) c =
      pairField p.val.1 p.val.2
        (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
          (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c))
        ((fun v => B ⟨p.val.2,faceEmbed Y p.val.2 v⟩)+Bj)
        ((fun v => B ⟨p.val.1,faceEmbed Y p.val.1 v⟩)+Bi) := by
  funext u
  have hij := ne_of_lt p.property
  unfold pairProcessedOnBox pairField
  rw [pairSlice_add_rows]
  simp only [Pi.add_apply,extendSingle_local,extendSingle_other Y _ _ hij,
    extendSingle_other Y _ _ hij.symm,add_zero,faceEmbed_face]
  congr 1
  abel

theorem pairProcessedOnBox_law (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) =
      𝔼 B : FaceArray A m n, 𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField p.val.1 p.val.2
        (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
          (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi) := by
  let G (B : FaceArray A m n) := faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)
  have hm : (𝔼 B : FaceArray A m n,
      𝔼 Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A,
      𝔼 Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A,
      G (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj)) = 𝔼 B, G B := by
    rw [Finset.expect_comm]
    conv_lhs => arg 2; ext Bj; rw [Finset.expect_comm]
    have ht (Bj : ({j : Fin m // j≠p.val.2} → Fin (k+1)) → Forms A)
        (Bi : ({j : Fin m // j≠p.val.1} → Fin (k+1)) → Forms A) :
        (𝔼 B : FaceArray A m n, G (B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj))=𝔼 B,G B := by
      have he (B : FaceArray A m n) :
          B+extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj=
            (extendSingle Y p.val.1 Bi+extendSingle Y p.val.2 Bj)+B := by abel
      simp_rw [he]
      exact expect_translate G _
    simp only [ht,Fintype.expect_const]
  rw [← hm]
  apply Finset.expect_congr rfl
  intro B _
  simp only [G,pairProcessedOnBox_resample]
  let P := fun Bj Bi => faceCorrelation (pairField p.val.1 p.val.2
    (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
      (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi)
  let Rj := fun v => B ⟨p.val.2,faceEmbed Y p.val.2 v⟩
  let Ri := fun v => B ⟨p.val.1,faceEmbed Y p.val.1 v⟩
  change (𝔼 Bj,𝔼 Bi,P (Rj+Bj) (Ri+Bi))=𝔼 Bj,𝔼 Bi,P Bj Bi
  calc
    _ = 𝔼 Bj, 𝔼 Bi, P (Rj+Bj) Bi := by
      apply Finset.expect_congr rfl
      intro Bj _
      exact expect_translate (fun Bi => P (Rj+Bj) Bi) Ri
    _ = _ := expect_translate (fun Bj => 𝔼 Bi,P Bj Bi) Rj

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma faceCorrelation_measurable_field {Ω : Type*} [MeasurableSpace Ω]
    (v : Ω → Point m n → ℝ) (hv : ∀ x, Measurable (fun t => v t x)) :
    Measurable (fun t => faceCorrelation (v t)) := by
  have hh : Measurable (Finset.sup' Finset.univ Finset.univ_nonempty
      (fun (z : Code m n) t => |𝔼 x, v t x * sign (z.val x)|)) := by
    apply Finset.measurable_sup'
    intro z _
    apply Measurable.abs
    simp only [Finset.expect_eq_sum_div_card]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro x _
    exact (hv x).mul measurable_const
  change Measurable (fun t => (Finset.univ.sup' Finset.univ_nonempty
    (fun (z : Code m n) t => |𝔼 x, v t x * sign (z.val x)|)) t) at hh
  simpa only [faceCorrelation,Finset.sup'_apply] using hh

attribute [local irreducible] gaussianSlice Slice.centeredClip

attribute [local irreducible] pointEmbed coordinateEnum

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairClass_dimension (p : PairClass m) : 2 ≤ m := by
  have h1 := p.property
  have h2 := p.val.2.isLt
  have h0 := p.val.1.isLt
  change p.val.1.val < p.val.2.val at h1
  omega

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FreshCorrelation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery thirdFailure
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def averagedCorrelation (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ) : ℝ :=
  𝔼 B, ∫ c, faceCorrelation (u B c) ∂gauss (Point m n)

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Target
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Target

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

end MinUncutGames.Foundations.Target

end

end OAI
end

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

lemma endpoint_lt {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (i : ℕ) :
    endpoint T L i < endpoint T L (i+1) := by
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  unfold endpoint
  simp only [add_lt_add_iff_left,div_lt_div_iff_of_pos_right hL']
  push_cast
  nlinarith

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_RationalRowNoise
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.RowNoise
attribute [local instance] Classical.propDecidable
variable {R W : Type*} [Fintype R] [Fintype W] [DecidableEq W]

lemma rationalRowDensity_cast (a : ℚ) (b c : W) :
    (rationalRowDensity a b c:ℝ)=rowDensity a b c := by
  by_cases h : c=b <;> simp [rationalRowDensity,rowDensity,h]

end MinUncut.RowNoise

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphOutput
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.FiniteProof
open PathRealization
variable {E V : Type*} [Fintype E]

def expanded (D : ℕ) (w : E → ℚ) (d : E → Demand V) : UnitDemand D w → Demand V :=
  fun p => d p.1


open scoped BigOperators
open PathRealization
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteProof

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma faceCorrelation_sum_le {T : Type*} (S : Finset T) (v : T → Point m n → ℝ) :
    faceCorrelation (fun x => ∑ t ∈ S, v t x) ≤ ∑ t ∈ S, faceCorrelation (v t) := by
  apply faceCorrelation_le
  intro z
  simp_rw [Finset.sum_mul, Finset.expect_sum_comm]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun t _ => code_correlation_le (v t) z))

lemma faceCorrelation_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (u : Ω → Point m n → ℝ) (hm : ∀ x, Measurable (fun t => u t x))
    (hi : ∀ x, Integrable (fun t => u t x) μ) :
    Integrable (fun t => faceCorrelation (u t)) μ := by
  have hh : Integrable (fun t => 𝔼 x, |u t x|) μ := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ => (hi x).abs)).div_const _
  exact hh.mono' (faceCorrelation_measurable_field u hm).aestronglyMeasurable
    (ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (faceCorrelation_nonneg _)]
      exact faceCorrelation_le_l1 _))

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma classField_memLp (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (x : Point m n) :
    MemLp (fun c => classField f σ η J a B c x) 2 (γpi (Point m n)) :=
  memLp_selectedProject _ _ _

lemma lowGradient_class_partition (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) :
    lowGradient D s f σ η B c x =
      ∑ a : Option (PairClass m), classField f σ η (rectangle D s) a B c x :=
  classSelection_partition x _ _

end MinUncut.Inner

namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [Nonempty W] [Fintype ι]

def jointL1 (u : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, |u B c| ∂γpi ι

end MinUncut.RowNoise

open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairAtomMean_nonneg (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) : 0≤pairAtomMean f σ η x Y p J :=
  Finset.expect_nonneg (fun _ _ => integral_nonneg (fun _ => Slice.oddMax_nonneg _ _))

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Assembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox BoxGaussian
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass Slice.centeredClip
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] classField pairSlice Slice.processed gaussianSlice
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] oddAtom rowAtom pairAtomMean lowGradient
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

lemma rectangle_bounds (D s : ℕ) (j : Finset (Row m n) × (Point m n → ℕ))
    (hj : j ∈ rectangle D s) : (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D := by
  obtain ⟨hS,hI⟩ := Finset.mem_product.mp hj
  exact ⟨(mem_low _ _).mp hI,(Finset.mem_filter.mp hS).2⟩

lemma rectangle_pair_room {D s : ℕ} (hroom : D < (m-s).choose 2)
    (j : Finset (Row m n) × (Point m n → ℕ)) (hj : j ∈ rectangle D s) :
    j.1.card < (m-(∑ u, j.2 u)).choose 2 := by
  obtain ⟨hi,hS⟩ := rectangle_bounds D s j hj
  exact lt_of_le_of_lt hS (lt_of_lt_of_le hroom (Nat.choose_le_choose 2 (by omega)))

end MinUncut.Inner

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

namespace MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding

variable {α β γ : Type}

theorem prod_decode_pair (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size) :
    (a.prod b).code.symm (finProdFinEquiv (i, j)) =
      (a.code.symm i, b.code.symm j) := by
  change (a.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
    b.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem prod_decode_mk (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size)
    (h : i.val * b.size + j.val < a.size * b.size) :
    (a.prod b).code.symm ⟨i.val * b.size + j.val, h⟩ =
      (a.code.symm i, b.code.symm j) := by
  have he : (⟨i.val * b.size + j.val, h⟩ : Fin (a.size * b.size)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  change (a.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).1,
    b.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).2) = _
  rw [he]
  exact prod_decode_pair a b i j

theorem enumerate_prod (a : Encoding α) (b : Encoding β) :
    (a.prod b).enumerate =
      a.enumerate.flatMap (fun x => b.enumerate.map (fun y => (x, y))) := by
  change List.ofFn (fun q : Fin (a.size * b.size) =>
    (a.code.symm (finProdFinEquiv.symm q).1,
     b.code.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [enumerate, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact prod_decode_mk a b i j _

end MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding

namespace MinUncutGames.Foundations.Hastad.SourceEnumeration

open Target SourceContexts SourceOccurrences

theorem testTapeEncoding_enumerate (u D : ℕ) :
    (testTapeEncoding u D).enumerate =
      ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
        ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
          ((jEncoding u).function Encoding.bool).enumerate.map (fun g => (f, z, g)))) := by
  simp only [testTapeEncoding, Encoding.enumerate_prod, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem sourceIndexEncoding_enumerate (F : Formula) (u D : ℕ) :
    (sourceIndexEncoding F u D).enumerate =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => ((c, s), (f, z, g))))))) := by
  simp only [sourceIndexEncoding, Encoding.enumerate_prod, testTapeEncoding_enumerate,
    List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

theorem sourceIndexEncoding_map {α : Type} (F : Formula) (u D : ℕ)
    (emit : SourceIndex F u D → α) :
    (sourceIndexEncoding F u D).enumerate.map emit =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => emit ((c, s), (f, z, g))))))) := by
  rw [sourceIndexEncoding_enumerate]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem rawSourceList_eq_nestedLoops (F : Formula) (u D : ℕ) :
    rawSourceList F u D =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.map
                (fun g => contextEquation F u D c (sampledVariables F c s) (f, z, g)))))) := by
  exact sourceIndexEncoding_map F u D (sourceEquation F u D)

theorem rawSourceList_flatMap {α : Type} (F : Formula) (u D : ℕ)
    (emit : MinUncutGames.Reduction.CloneGap.Equation (Fin (nBits F u)) → List α) :
    (rawSourceList F u D).flatMap emit =
      (clauseEncoding F u).enumerate.flatMap (fun c =>
        (slotContextEncoding u).enumerate.flatMap (fun s =>
          ((iEncoding u).function Encoding.bool).enumerate.flatMap (fun f =>
            ((jEncoding u).function (Encoding.fin D)).enumerate.flatMap (fun z =>
              ((jEncoding u).function Encoding.bool).enumerate.flatMap
                (fun g => emit (contextEquation F u D c (sampledVariables F c s) (f, z, g))))))) := by
  rw [rawSourceList_eq_nestedLoops]
  simp only [List.flatMap_assoc, List.flatMap_map]

end MinUncutGames.Foundations.Hastad.SourceEnumeration

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteEnumeration
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace Enumeration
variable {A B : Type}

def encoding [DecidableEq A] (E : Enumeration A) : Encoding A where
  size := E.values.length
  code := (List.Nodup.getEquivOfForallMemList E.values E.nodup E.complete).symm

end Enumeration
end MinUncut

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_SignatureEncoding
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.Costed
open MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma lookupValue_mem {xs : List (ℕ × ℕ)} (hn : (xs.map Prod.fst).Nodup)
    {i x : ℕ} (h : (i,x)∈xs) : AExpr.lookupValue i xs=x := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
    rcases p with ⟨j,y⟩
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp h with h|h
    · cases h
      simp [AExpr.lookupValue]
    · have hij : i≠j := by
        intro he
        subst i
        exact hn.1 (List.mem_map.mpr ⟨(j,x),h,rfl⟩)
      simp only [AExpr.lookupValue,ite_eq_right hij]
      exact ih hn.2 h

end MinUncut.Outer.LocalTemplate

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

namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

def keyAddress (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v,f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c,g)))
  | .inr (.inr _) => dummyIndex F u

lemma mapEquation_comp {A B C : Type} (f : A → B) (g : B → C) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := by
  cases e
  rfl

lemma localEquation_spec (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (t : SourceTape.TestTape (I u) (J u) D) :
    mapEquation (keyAddress F c v) (localEquation (validJ F c) (pi F c v) t) =
      contextEquation F u D c v t := by
  unfold localEquation contextEquation rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    simp only
    rw [mapEquation_comp]
    congr 1
    funext a
    cases a <;> rfl
  | some j₀ =>
    simp only
    rw [mapEquation_comp]
    unfold conditionedOccurrence
    congr 1
    funext a
    cases a <;> rfl

lemma signature_equation (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceTape.TestTape (I u) (J u) D) :
    mapEquation (keyAddress F c (sampledVariables F c s))
      ((signature F c).equation s t) = sourceEquation F u D ((c,s),t) := by
  unfold Signature.equation
  rw [signature_valid, signature_project]
  exact localEquation_spec F c _ t

end MinUncut.SourceTemplate

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_TemplateArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def keyNumber {u : ℕ} (N M c v : ℕ) (x : LocalKey u) : ℕ :=
  if keyTag x=0 then keyTable x+2^(2^u)*v else
  if keyTag x=1 then N^u*2^(2^u)+(keyTable x+2^(8^u)*c) else
    N^u*2^(2^u)+M^u*2^(8^u)

lemma keyAddress_number (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (x : LocalKey u) :
    (keyAddress F c v x).val=keyNumber F.«variables» F.clauses.length
      ((clauseEncoding F u).code c).val ((variableEncoding F u).code v).val x := by
  cases x with
  | inl f => rfl
  | inr x =>
    cases x with
    | inl g => rfl
    | inr z => cases z; rfl

lemma formula_name_word (F : Formula) (i : Fin F.clauses.length) (s : Slot) :
    ((Complexity.formulaWords F).drop (2+6*i.val+2*(slotEncoding.code s).val)).headI=
      (nameAt (clauseAt F i) s).val := by
  have h : ∀ (xs : List (Clause F.«variables»)) (j : ℕ) (hj : j<xs.length),
      ((xs.flatMap Complexity.clauseWords).drop (6*j+2*(slotEncoding.code s).val)).headI=
        (nameAt xs[j] s).val := by
    intro xs
    induction xs with
    | nil => intro j hj; simp at hj
    | cons e es ih =>
      intro j hj
      cases j with
      | zero => cases s <;> rfl
      | succ j =>
        have he : 6*(j+1)+2*(slotEncoding.code s).val=
            ((((((6*j+2*(slotEncoding.code s).val)+1)+1)+1)+1)+1)+1 := by omega
        rw [he]
        simpa only [List.flatMap_cons,Complexity.clauseWords,Complexity.literalWords,
          List.cons_append,List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using
          ih j (by simpa using hj)
  have he : 2+6*i.val+2*(slotEncoding.code s).val=(6*i.val+2*(slotEncoding.code s).val)+1+1 := by omega
  rw [he]
  exact h F.clauses i.val i.isLt

lemma formula_positive_word (F : Formula) (i : Fin F.clauses.length) (s : Slot) :
    ((Complexity.formulaWords F).drop (2+6*i.val+(2*(slotEncoding.code s).val+1))).headI=
      (positiveAt (clauseAt F i) s).toNat := by
  have h : ∀ (xs : List (Clause F.«variables»)) (j : ℕ) (hj : j<xs.length),
      ((xs.flatMap Complexity.clauseWords).drop (6*j+(2*(slotEncoding.code s).val+1))).headI=
        (positiveAt xs[j] s).toNat := by
    intro xs
    induction xs with
    | nil => intro j hj; simp at hj
    | cons e es ih =>
      intro j hj
      cases j with
      | zero =>
        cases s with
        | first => change (if e[0].positive then 1 else 0)=e[0].positive.toNat
                   cases e[0].positive <;> rfl
        | second => change (if e[1].positive then 1 else 0)=e[1].positive.toNat
                    cases e[1].positive <;> rfl
        | third => change (if e[2].positive then 1 else 0)=e[2].positive.toNat
                   cases e[2].positive <;> rfl
      | succ j =>
        have he : 6*(j+1)+(2*(slotEncoding.code s).val+1)=
            ((((((6*j+(2*(slotEncoding.code s).val+1))+1)+1)+1)+1)+1)+1 := by omega
        rw [he]
        simpa only [List.flatMap_cons,Complexity.clauseWords,Complexity.literalWords,
          List.cons_append,List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using
          ih j (by simpa using hj)
  have he : 2+6*i.val+(2*(slotEncoding.code s).val+1)=
      (6*i.val+(2*(slotEncoding.code s).val+1))+1+1 := by omega
  rw [he]
  exact h F.clauses i.val i.isLt

end MinUncut.SourceTemplate

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
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

lemma functionExpr_eval {A B : Type} (a : Encoding A) (b : Encoding B) (f : A → AExpr)
    (g : A → B) (v : List ℕ) (h : ∀x,(f x).eval v=(b.code (g x)).val) :
    (functionExpr a b.size f).eval v=((a.function b).code g).val := by
  simp only [functionExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,h]
  rfl

end MinUncut.SourceTemplate

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

def demandList {V E : Type} (D : ℕ) (w : E → ℚ) (d : E → Demand V) (enc : Encoding E) : List (Demand V) :=
  enc.enumerate.flatMap (fun e => List.replicate (multiplicity D (w e)) (d e))

lemma sum_enumerate {E : Type} [Fintype E] (enc : Encoding E) (f : E → ℕ) :
    (enc.enumerate.map f).sum=∑e, f e := by
  simp only [Encoding.enumerate,List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp enc.code.symm f

end MinUncut.PathRealization

end OAI
end


