-- Prove2me | Definitions.Def_OAIQ076M016
-- name    : OAIQ076M016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:10:04.563664+00:00
-- url     : https://prove2.me/theorems/5d9ee7da-c790-4071-b0fb-89f3aee11cd1
-- title:
--   Definitions bundle OAIQ076M016 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 11 definitions and 111 theorems. The definitions and types are `OAI.MinUncut.FiniteGaussian.finiteFirst`, `OAI.MinUncut.FiniteGaussian.finiteFourth`, `OAI.MinUncut.FiniteGaussian.finiteSecond`, `OAI.MinUncut.FiniteGaussian.finiteThird`, `OAI.MinUncut.FiniteGaussian.firstTable`, `OAI.MinUncut.FiniteGaussian.fourthTable`, `OAI.MinUncut.FiniteGaussian.secondTable`, `OAI.MinUncut.FiniteGaussian.tableAverage`, `OAI.MinUncut.FiniteGaussian.thirdTable`, `OAI.MinUncut.PathRealization.totalFailure`, `OAI.MinUncut.RowNoise.noise`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FaceCorrelation`, `MinUncut_Analysis_FiniteGaussianLaw`, `MinUncut_Analysis_FreshCorrelation`, `MinUncut_Analysis_GaussNegPreserving`, `MinUncut_Analysis_Gradient`, `MinUncut_Analysis_GradientEnergyFirstTables`, `MinUncut_Analysis_LowGradient`, `MinUncut_Analysis_LowGradientEnergyLowerWeighted`, `MinUncut_Analysis_RationalRowNoise`, `MinUncut_Analysis_RowProjectedGradient`, `MinUncut_Analysis_SmoothingRho`, `MinUncut_Estimates_ActualBoxBound`, `MinUncut_Estimates_ArraySum`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_CoupledAnswer`, `MinUncut_Estimates_EuclideanInvariantScore`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FaceUpdateSelf`, `MinUncut_Estimates_FirstError`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_SamplerAssembly`, `MinUncut_Estimates_SamplerCost`, `MinUncut_Estimates_SecondFailureIndicator`, `MinUncut_Estimates_TableTestFunctions`, `MinUncut_Games_JointInner`, `MinUncut_Graphs_GraphOutput`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Search_FiniteAverageBounds`.
--
--   **Imports.** It imports the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008` and `OAIQ076M009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M022` and `OAIQ076M023`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M008
import Definitions.Def_OAIQ076M009

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable [Fintype A]

lemma gradient_convolution (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) / σ *
      ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        g x * bitSign (f.answer (pullQuery B (c + σ • g) (η • l)))
          ∂gauss (Code m n) ∂gauss (Point m n) := by
  rw [gradient, (smooth_coordinate_derivative f B hσ η c x).deriv]
  simp only [tableSmooth, integral_const_mul, div_eq_mul_inv, mul_assoc]

lemma gradient_spatialEnergy_le (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (gradient f B σ η c) ≤ σ⁻¹ ^ 2 := by
  have hN : (0 : ℝ) < (n^m : ℕ) := by exact_mod_cast pow_pos hn m
  let S : Point m n → ℝ := fun x => ∫ g : Point m n → ℝ,
    g x * tableSmooth f B η (c + σ • g) ∂gauss (Point m n)
  have hS : (∑ x, S x ^ 2) ≤ 1 :=
    GaussianSmoothing.gaussian_score_energy
      ((measurable_tableSmooth f B η).comp (by fun_prop))
      (fun _ => tableSmooth_abs_le f B η _)
  have hE : spatialEnergy (gradient f B σ η c) = σ⁻¹^2 * ∑ x, S x ^ 2 := by
    simp only [spatialEnergy, gradient_score f B hσ, mul_pow, div_pow,
      Real.sq_sqrt hN.le, ← Finset.mul_sum]
    dsimp [S]
    field_simp
  rw [hE]
  simpa using mul_le_mul_of_nonneg_left hS (sq_nonneg σ⁻¹)

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EuclideanInvariantScore
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem gradient_table_representation (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x =
      ∑ z : Code m n, tableCoefficient f B σ η c z * BinaryFourier.sign (z.val x) := by
  have hf0 := measurable_answer f B η
  have hmap : Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ • p.1,p.2)) := by fun_prop
  have hf := hf0.comp hmap
  dsimp only [Function.comp_def] at hf
  have hh := GaussianKernel.coupled_score x
    (fun z : Code m n => σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x)) hf
    (fun u => by simp only [bitSign_abs, le_refl])
    (answer_coupled_shift f B σ hη c · · x ·)
  have hN : Real.sqrt (n^m : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast pow_pos hn m)).ne'
  rw [gradient_convolution f B hσ]
  change _ * (∫ g, ∫ l, g x * _ ∂Measure.pi (fun _ => gaussianReal 0 1)
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
  rw [hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [tableCoefficient, gauss]
  field_simp

end MinUncut.Inner
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

omit [Fintype A] in
lemma measurable_thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) (z : Code m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => thirdFailure f B η p.1 p.2 z) := by
  let D : (Code m n → Bool) → ℝ := fun P =>
    if f.answer (fun a => Function.update P z true (labelCode B a)) =
      f.answer (fun a => Function.update P z false (labelCode B a)) then 0 else 1
  have hq : Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 (η • p.2)) := by
    apply Measurable.of_eval
    intro w
    exact (measurable_query w).comp (show Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (p.1, η • p.2)) by fun_prop)
  exact (measurable_of_finite D).comp hq

lemma tableCoefficient_abs_le (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : 0 < η) (c : Point m n → ℝ) (z : Code m n) :
    |tableCoefficient f B σ η c z| ≤
      η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n) := by
  have hmap : Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ • p.1,p.2)) := by fun_prop
  have hf0 := measurable_answer f B η
  have hf := hf0.comp hmap
  dsimp only [Function.comp_def] at hf
  have hs0 := measurable_thirdFailure f B η z
  have hs := hs0.comp hmap
  dsimp only [Function.comp_def] at hs
  have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      p.2 z * bitSign (f.answer (pullQuery B (c+σ • p.1) (η • p.2))))
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_snd (gauss (Point m n))).mul_bdd (c := 1) hf.aestronglyMeasurable
      (ae_of_all _ fun p => by simp only [Real.norm_eq_abs, bitSign_abs, le_refl])
  have hsi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      thirdFailure f B η (c+σ • p.1) p.2 z)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    (integrable_const (1 : ℝ)).mono' hs.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using thirdFailure_abs_le f B η _ _ z)
  rw [tableCoefficient, abs_mul, abs_of_pos (inv_pos.mpr hη)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
  calc
    _ ≤ ∫ g : Point m n → ℝ, |∫ l : Code m n → ℝ,
        l z * bitSign (f.answer (pullQuery B (c+σ • g) (η • l))) ∂gauss (Code m n)|
        ∂gauss (Point m n) := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono hi.integral_prod_left.abs hsi.integral_prod_left
      (fun g => table_score_le_thirdFailure f B η _ z)

theorem tableMass_le_thirdRejection (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : 0 < η) (c : Point m n → ℝ) :
    tableMass f B σ η c ≤ (Fintype.card (Code m n) : ℝ) / η * thirdRejection f B σ η c := by
  have hc : (Fintype.card (Code m n) : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ∑ z : Code m n, η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n) :=
      Finset.sum_le_sum fun z _ => tableCoefficient_abs_le f B σ hη c z
    _ = _ := by
      rw [thirdRejection, Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
      field_simp
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FaceCorrelation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem gradient_convex_correlation (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (c : Point m n → ℝ) (v : Point m n → ℝ) :
    |𝔼 x : Point m n, v x * gradient f B σ η c x| ≤ tableMass f B σ η c * faceCorrelation v := by
  simp_rw [gradient_table_representation f B hn hσ hη]
  exact representation_correlation v (tableCoefficient f B σ η c)
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

variable {ι : Type*} [Fintype ι]

lemma noise_coefficient (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    (∫ x, psi a x * noise ρ s Q x ∂γpi ι) =
      ρ^(∑ i, a i) * ∫ x, psi a x * Q x ∂γpi ι := by
  let μ := (γpi ι).prod (γpi ι)
  let f : ((ι → ℝ) × (ι → ℝ)) → ℝ := fun z => psi a z.1 * Q (ρ • z.1+s • z.2)
  have hqm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => Q (ρ • z.1+s • z.2)) :=
    hQ.comp (by fun_prop)
  have hfm : Measurable f := ((continuous_psi a).measurable.comp measurable_fst).mul hqm
  have hfi : Integrable f μ := ((psi_integrable a).comp_fst (γpi ι)).mul_bdd
    hqm.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb _)
  have hm := rotation_preserves (ι := ι) ρ s h
  have hfm' : Measurable (f ∘ rotation ρ s) := hfm.comp (by fun_prop)
  have hfi' : Integrable (f ∘ rotation ρ s) μ :=
    (hm.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have htrans (z : (ι → ℝ) × (ι → ℝ)) :
      f (rotation ρ s z) = Q z.1 * psi a (ρ • z.1+s • z.2) := by
    have hx := congrArg Prod.fst (rotation_involutive (ι := ι) ρ s h z)
    change ρ • (ρ • z.1+s • z.2)+s • (s • z.1-ρ • z.2) = z.1 at hx
    dsimp [f, rotation_apply]
    rw [hx, mul_comm]
  calc
    _ = ∫ z, f z ∂μ := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_const_mul _ _).symm
    _ = ∫ z, f (rotation ρ s z) ∂μ := by
      simpa only [hm.map_eq] using
        (integral_map (μ := (γpi ι).prod (γpi ι)) hm.measurable.aemeasurable hfm.aestronglyMeasurable)
    _ = ∫ x, ∫ y, Q x * psi a (ρ • x+s • y) ∂γpi ι ∂γpi ι := by
      change (∫ z, (f ∘ rotation ρ s) z ∂(γpi ι).prod (γpi ι)) = _
      rw [integral_prod _ hfi']
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact htrans (x,y)
    _ = _ := by
      simp only [integral_const_mul, show ∀ x y : ι → ℝ, ρ • x+s • y =
          fun i => ρ*x i+s*y i by intros; rfl, psi_noise ρ s h]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

lemma score_coefficient [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    (∫ x, psi a x * score ρ s Q i x ∂γpi ι) =
      s*Real.sqrt (a i+1:ℝ)*ρ^(∑ j, a j) *
        ∫ x, psi (Function.update a i (a i+1)) x * Q x ∂γpi ι := by
  let μ := (γpi ι).prod (γpi ι)
  let f : ((ι → ℝ) × (ι → ℝ)) → ℝ := fun z =>
    (psi a z.1 * z.2 i) * Q (ρ • z.1+s • z.2)
  have hqm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => Q (ρ • z.1+s • z.2)) :=
    hQ.comp (by fun_prop)
  have hfm : Measurable f := (((continuous_psi a).measurable.comp measurable_fst).mul
    (by fun_prop)).mul hqm
  have hfi : Integrable f μ := ((psi_integrable a).mul_prod (coordinate_integrable i)).mul_bdd
    hqm.aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb _)
  have hm := rotation_preserves (ι := ι) ρ s h
  have hfi' : Integrable (f ∘ rotation ρ s) μ :=
    (hm.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have htrans (z : (ι → ℝ) × (ι → ℝ)) :
      f (rotation ρ s z) = Q z.1 * ((s*z.1 i-ρ*z.2 i)*psi a (ρ • z.1+s • z.2)) := by
    have hx := congrArg Prod.fst (rotation_involutive (ι := ι) ρ s h z)
    change ρ • (ρ • z.1+s • z.2)+s • (s • z.1-ρ • z.2) = z.1 at hx
    dsimp [f, rotation_apply]
    rw [hx]
    ring
  calc
    _ = ∫ z, f z ∂μ := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [score, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [f]
      ring
    _ = ∫ z, f (rotation ρ s z) ∂μ := by
      simpa only [hm.map_eq] using
        (integral_map (μ := (γpi ι).prod (γpi ι)) hm.measurable.aemeasurable hfm.aestronglyMeasurable)
    _ = ∫ x, ∫ y, Q x * ((s*x i-ρ*y i)*psi a (ρ • x+s • y)) ∂γpi ι ∂γpi ι := by
      change (∫ z, (f ∘ rotation ρ s) z ∂(γpi ι).prod (γpi ι)) = _
      rw [integral_prod _ hfi']
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact htrans (x,y)
    _ = _ := by
      simp only [integral_const_mul, psi_rotation_moment ρ s h]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

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

lemma gradient_coefficient [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    coeff (gradient ρ s Q i) a =
      Real.sqrt (a i+1:ℝ)*ρ^(degree a+1)*coeff Q (bump i a) := by
  change coeff (fun x => (ρ/s)*score ρ s Q i x) a = _
  rw [coeff_const_mul]
  unfold coeff
  rw [score_coefficient ρ s h hQ hb]
  dsimp [degree, bump]
  rw [pow_succ]
  field_simp

lemma gradient_coefficient_sq [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    (coeff (gradient ρ s Q i) a)^2 =
      (bump i a i : ℝ)*ρ^(2*degree (bump i a))*(coeff Q (bump i a))^2 := by
  rw [gradient_coefficient ρ s h hs hQ hb, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), ← pow_mul, degree_bump]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

lemma hasSum_gradient_energy_coord [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (i : ι) :
    HasSum (fun a => (a i : ℝ)*ρ^(2*degree a)*(coeff Q a)^2)
      (∫ x, (gradient ρ s Q i x)^2 ∂γpi ι) := by
  apply (bump_injective i).hasSum_iff (fun a ha => ?_) |>.mp
  · simpa only [Function.comp_def, ← gradient_coefficient_sq ρ s h hs hQ hb] using
      hasSum_coeff_sq (memLp_gradient ρ s hQ hb i)
  · have hz : a i = 0 := by
      rw [mem_range_bump] at ha
      omega
    simp [hz]

lemma hasSum_gradient_energy [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) :
    HasSum (fun a => (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2)
      (∑ i, ∫ x, (gradient ρ s Q i x)^2 ∂γpi ι) := by
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_gradient_energy_coord ρ s h hs hQ hb i)
  simpa only [← Finset.sum_mul, ← Nat.cast_sum, degree] using hh

lemma coeff_noise (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    coeff (noise ρ s Q) a = ρ^(degree a)*coeff Q a := noise_coefficient ρ s h hQ hb a

lemma coeff_noise_sq (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    (coeff (noise ρ s Q) a)^2 = ρ^(2*degree a)*(coeff Q a)^2 := by
  rw [coeff_noise ρ s h hQ hb, mul_pow, ← pow_mul, mul_comm (degree a) 2]

lemma poincare [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (hmean : (∫ x, noise ρ s Q x ∂γpi ι) = 0) :
    (∫ x, (noise ρ s Q x)^2 ∂γpi ι) ≤
      ∑ i, ∫ x, (gradient ρ s Q i x)^2 ∂γpi ι := by
  apply hasSum_le (fun a => ?_) (hasSum_coeff_sq (memLp_noise ρ s hQ hb))
    (hasSum_gradient_energy ρ s h hs hQ hb)
  by_cases ha : degree a = 0
  · have haz := (degree_eq_zero_iff a).mp ha
    subst a
    simp only [coeff_zero, hmean, zero_pow (by omega : 2 ≠ 0), degree]
    simp
  · rw [coeff_noise_sq ρ s h hQ hb]
    have hd : (1:ℝ) ≤ degree a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
    calc
      _ = 1*(ρ^(2*degree a)*(coeff Q a)^2) := by ring
      _ ≤ (degree a : ℝ)*(ρ^(2*degree a)*(coeff Q a)^2) := by
        apply mul_le_mul_of_nonneg_right hd
        rw [pow_mul]
        exact mul_nonneg (pow_nonneg (sq_nonneg ρ) _) (sq_nonneg _)
      _ = _ := by ring

lemma hasSum_gradient_tail_coord [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) (i : ι) :
    HasSum (fun a => if d+2 ≤ degree a then
      (a i : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
      (∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) := by
  apply (bump_injective i).hasSum_iff (fun a ha => ?_) |>.mp
  · convert hasSum_coeff_sq ((memLp_gradient ρ s hQ hb i).sub
      (memLp_project d (gradient ρ s Q i))) using 1
    · funext a
      change (if d+2 ≤ degree (bump i a) then
        (bump i a i : ℝ)*ρ^(2*degree (bump i a))*(coeff Q (bump i a))^2 else 0) =
        (coeff (fun x => gradient ρ s Q i x-project d (gradient ρ s Q i) x) a)^2
      rw [coeff_residual (memLp_gradient ρ s hQ hb i)]
      split_ifs with hd he he
      · exact (gradient_coefficient_sq ρ s h hs hQ hb a i).symm
      · rw [degree_bump] at hd; omega
      · rw [degree_bump] at hd; omega
      · simp
    · rfl
  · have hz : a i = 0 := by rw [mem_range_bump] at ha; omega
    simp [hz]

lemma hasSum_gradient_tail [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) :
    HasSum (fun a => if d+2 ≤ degree a then
      (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
      (∑ i, ∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) := by
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_gradient_tail_coord ρ s h hs hQ hb d i)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  split_ifs <;> simp [← Finset.sum_mul, degree, Nat.cast_sum]

lemma gradient_tail_le [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hd : ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε) :
    (∑ i, ∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) ≤ ε := by
  have hq : MemLp Q 2 (γpi ι) := MemLp.of_bound hQ.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := hasSum_le (f := fun a => if d+2 ≤ degree a then
      (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
    (g := fun a => ε*(coeff Q a)^2) (fun a => ?_)
    (hasSum_gradient_tail ρ s h hs hQ hb d) ((hasSum_coeff_sq hq).mul_left ε)
  · have hi : (∫ x, Q x^2 ∂γpi ι) ≤ 1 := by
      calc
        _ ≤ ∫ _ : ι → ℝ, (1:ℝ) ∂γpi ι := integral_mono
          (hq.integrable_sq) (integrable_const 1) (fun x => by
            have ha := hb x; nlinarith [sq_abs (Q x), abs_nonneg (Q x)])
        _ = 1 := by simp
    exact he.trans (by nlinarith)
  · split_ifs with ha
    · exact mul_le_mul_of_nonneg_right (hd _ ha) (sq_nonneg _)
    · positivity

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

lemma convolution_poincare {ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (h : ρ^2+(σ*ρ)^2=1) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (hmean : (∫ x, convolution σ Q x ∂γpi ι) = 0) :
    (∫ x, (convolution σ Q x)^2 ∂γpi ι) ≤
      ∑ i, ∫ x, (convolutionGradient σ Q i x)^2 ∂γpi ι := by
  simp_rw [convolution_as_noise hρ, convolutionGradient_as_noise hρ hσ] at *
  exact poincare ρ (σ*ρ) h (mul_ne_zero hσ hρ) (hQ.comp (by fun_prop))
    (fun x => hb _) hmean

lemma convolution_gradient_tail {ρ σ ε : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (h : ρ^2+(σ*ρ)^2=1) (hε : 0 ≤ ε) (d : ℕ)
    (hd : ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) :
    (∑ i, ∫ x, (convolutionGradient σ Q i x -
      project d (convolutionGradient σ Q i) x)^2 ∂γpi ι) ≤ ε := by
  simp_rw [convolutionGradient_as_noise hρ hσ]
  exact gradient_tail_le ρ (σ*ρ) h (mul_ne_zero hσ hρ) (hQ.comp (by fun_prop))
    (fun x => hb _) d hε hd

end MinUncut.GaussianHermite

namespace MinUncut.RowNoise
open BinaryFourier
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

omit [Module F₂ W] in
lemma density_mean (a : ℝ) (B : R → W) : (𝔼 C, density a B C) = 1 := by
  simp only [density, expect_prod, rowDensity_mean, Finset.prod_const_one]

omit [DecidableEq R] [AddCommGroup W] [Module F₂ W] in
lemma density_symmetric (a : ℝ) (B C : R → W) : density a B C = density a C B := by
  simp only [density, rowDensity_symmetric a]

omit [DecidableEq R] [Module F₂ W] in
lemma density_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (B C : R → W) :
    0 ≤ density a B C := Finset.prod_nonneg (fun _ _ => rowDensity_nonneg ha ha1 _ _)

def noise (a : ℝ) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  𝔼 C, density a B C * f C

lemma noise_character (a : ℝ) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    noise a (character α) B = (1-a)^degree α*character α B := by
  simp only [noise, density, character_product]
  simp_rw [← Finset.prod_mul_distrib]
  rw [expect_prod (fun r c => rowDensity a (B r) c * character (frequency α r) c)]
  simp only [row_character_eigen, Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rfl

attribute [local instance] OAI.MinUncut.RowNoise.convolutionDualFintype
lemma noise_expansion (a : ℝ) (f : (R → W) → ℝ) (B : R → W) :
    noise a f B = ∑ α, coefficient f α * (1-a)^degree α * character α B := by
  unfold noise
  simp_rw [← inversion f, Finset.mul_sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  have he : (𝔼 C, density a B C * (coefficient f α * character α C)) =
      coefficient f α * noise a (character α) B := by
    unfold noise
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro C _
    ring
  rw [he, noise_character]
  ring

lemma correlation (a : ℝ) (f : (R → W) → ℝ) :
    (𝔼 B, f B * noise a f B) = ∑ α, (1-a)^degree α*(coefficient f α)^2 := by
  simp_rw [noise_expansion, Finset.mul_sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  calc
    _ = ((1-a)^degree α*coefficient f α) * (𝔼 B, f B * character α B) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro B _
      ring
    _ = _ := by rw [← coefficient]; ring

omit [Module F₂ W] in
lemma stationary (a : ℝ) (f : (R → W) → ℝ) : (𝔼 B, noise a f B) = 𝔼 B, f B := by
  unfold noise
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro C _
  simp_rw [density_symmetric a _ C, ← Finset.expect_mul, density_mean, one_mul]

lemma dirichlet (a : ℝ) (f : (R → W) → ℝ) :
    (𝔼 B, 𝔼 C, density a B C * (f B - f C)^2) =
      2 * ∑ α, (1-(1-a)^degree α)*(coefficient f α)^2 := by
  have he (B C : R → W) : density a B C*(f B-f C)^2 =
      (f B)^2*density a B C + density a B C*(f C)^2 - 2*f B*(density a B C*f C) := by ring
  simp_rw [he, Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, density_mean, mul_one]
  have ht : (𝔼 B, 2*f B*(𝔼 C, density a B C*f C)) =
      2*(𝔼 B, f B*noise a f B) := by
    simp only [noise, Finset.mul_expect, mul_assoc]
  rw [ht]
  change (𝔼 B, f B^2)+(𝔼 B, noise a (fun C => (f C)^2) B) -
    2*(𝔼 B, f B*noise a f B) = _
  rw [stationary, correlation, ← parseval]
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

lemma row_tail_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1 ≤ (k:ℝ)*a) (f : (R → W) → ℝ) :
    (𝔼 B, (f B-project D f B)^2) ≤
      𝔼 B, 𝔼 C, density a B C*(f B-f C)^2 := by
  rw [residual_energy, dirichlet, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  by_cases hd : D < degree α
  · rw [ite_eq_left hd, ← mul_assoc]
    simpa using mul_le_mul_of_nonneg_right
      (spectral_weight_ge_one ha ha1 (degree α) (hD _ hd))
      (sq_nonneg (coefficient f α))
  · rw [ite_eq_right hd]
    have hp : (1-a)^degree α ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    positivity

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FiniteGaussianLaw
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

attribute [local instance] OAI.MinUncut.FiniteGaussian.coordsDecEq
lemma tableGrid_check (m n : ℕ) (ε : ℚ) (hε : 0<ε) :
    (tableGrid m n ε hε).Check (Fintype.card (TestCoordinates m n)) (Fintype.card (ScoreIndex m n))
      (2*(n^m:ℕ)+1) ε := GridData.select_check _ _ _ _ _ _

attribute [local irreducible] tableGrid scoreFamily

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CoupledAnswer
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma coupledAnswer_measurable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : Measurable (coupledAnswer f B σ η c) := by
  have hg : Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ•p.1,p.2)) := by fun_prop
  exact (measurable_answer f B η).comp hg

lemma coupledAnswer_memLp (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    MemLp (coupledAnswer f B σ η c) 2 ((gauss (Point m n)).prod (gauss (Code m n))) :=
  MemLp.of_bound (coupledAnswer_measurable f B σ η c).aestronglyMeasurable 1
    (ae_of_all _ (fun p => by simp only [Real.norm_eq_abs,coupledAnswer,bitSign_abs,le_refl]))

omit [Fintype A] in
lemma secondFailure_eq (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    (coupledAnswer f B σ η c p-coupledAnswer f C σ η c p)^2 = 4*secondFailure f B C σ η c p := by
  unfold coupledAnswer secondFailure
  cases f.answer (pullQuery B (c+σ•p.1) (η•p.2)) <;>
    cases f.answer (pullQuery C (c+σ•p.1) (η•p.2)) <;> norm_num [bitSign]

lemma coupled_score_integrable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) :
    Integrable (fun p => p.1 x*coupledAnswer f B σ η c p)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
  ((GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))).integrable_mul
    (coupledAnswer_memLp f B σ η c)

lemma gradient_coupled_score (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x=Real.sqrt (n^m:ℕ)/σ*
      ∫ p, p.1 x*coupledAnswer f B σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n)) := by
  rw [integral_prod _ (coupled_score_integrable f B σ η c x)]
  exact gradient_convolution f B hσ η c x

theorem gradient_second_comparison (f : FoldedProof A) (B C : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (fun x => gradient f B σ η c x-gradient f C σ η c x) ≤
      4*σ⁻¹^2*secondRejection f B C σ η c := by
  let μ := (gauss (Point m n)).prod (gauss (Code m n))
  let D := fun p => coupledAnswer f B σ η c p-coupledAnswer f C σ η c p
  have hD : MemLp D 2 μ := (coupledAnswer_memLp f B σ η c).sub (coupledAnswer_memLp f C σ η c)
  have hX (x : Point m n) : MemLp (fun p => p.1 x) 2 μ :=
    (GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))
  have hXX (x y : Point m n) : (∫ p, p.1 x*p.1 y ∂μ)=if x=y then 1 else 0 := by
    have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => p.1 x*p.1 y) μ :=
      (hX x).integrable_mul (hX y)
    change (∫ p, p.1 x*p.1 y ∂(gauss (Point m n)).prod (gauss (Code m n)))=_
    rw [integral_prod _ hi]
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul,gauss,GaussianSmoothing.gamma] using GaussianSmoothing.coordinate_second_moment x y
  have hS := GaussianSmoothing.integral_bessel hX hXX hD
  have hN : (0 : ℝ)<(n^m:ℕ) := by exact_mod_cast pow_pos hn m
  have hd (x : Point m n) :
      gradient f B σ η c x-gradient f C σ η c x =
      Real.sqrt (n^m:ℕ)/σ*(∫ p, p.1 x*D p ∂μ) := by
    rw [gradient_coupled_score f B hσ,gradient_coupled_score f C hσ]
    simp only [D,mul_sub]
    rw [integral_sub (coupled_score_integrable f B σ η c x) (coupled_score_integrable f C σ η c x)]
    ring
  have he : spatialEnergy (fun x => gradient f B σ η c x-gradient f C σ η c x) =
      σ⁻¹^2*∑ x, (∫ p, p.1 x*D p ∂μ)^2 := by
    simp only [spatialEnergy,hd,mul_pow,div_pow,Real.sq_sqrt hN.le,← Finset.mul_sum]
    field_simp
  rw [he]
  calc
    _ ≤ σ⁻¹^2*(∫ p, (D p)^2 ∂μ) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by
      simp_rw [D,secondFailure_eq]
      rw [integral_const_mul]
      change σ⁻¹^2*(4*secondRejection f B C σ η c)=_
      ring
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_RowProjectedGradient
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem gradient_row_tail (f : FoldedProof A) (hn : 0 < n)
    {σ a : ℝ} (hσ : σ≠0) (ha : 0≤a) (ha1 : a≤1) (η : ℝ) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1≤(k:ℝ)*a) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x)) ≤
      4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*secondRejection f B C σ η c) := by
  have htail (x : Point m n) := RowNoise.row_tail_le ha ha1 D hD
    (fun B : FaceArray A m n => gradient f B σ η c x)
  calc
    _ = ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        𝔼 B : FaceArray A m n, (gradient f B σ η c x-rowProjectedGradient D f σ η B c x)^2 := by
      simp only [spatialEnergy,← Finset.mul_expect,Finset.expect_sum_comm]
    _ ≤ ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
          RowNoise.density a B C*(gradient f B σ η c x-gradient f C σ η c x)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => htail x)) (by positivity)
    _ = 𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*spatialEnergy
          (fun x => gradient f B σ η c x-gradient f C σ η c x) := by
      simp only [spatialEnergy,Finset.mul_sum,Finset.expect_sum_comm,
        ← Finset.mul_expect,mul_left_comm]
    _ ≤ 𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*(4*σ⁻¹^2*secondRejection f B C σ η c) :=
      Finset.expect_le_expect (fun B _ => Finset.expect_le_expect (fun C _ =>
        mul_le_mul_of_nonneg_left (gradient_second_comparison f B C hn hσ η c)
          (RowNoise.density_nonneg ha ha1 B C)))
    _ = _ := by
      have he (B C : FaceArray A m n) :
          RowNoise.density a B C*(4*σ⁻¹^2*secondRejection f B C σ η c) =
          (4*σ⁻¹^2)*(RowNoise.density a B C*secondRejection f B C σ η c) := by ring
      simp_rw [he,← Finset.mul_expect]
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussNegPreserving
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

lemma tableSmooth_odd (f : FoldedProof A) (B : FaceArray A m n)
    {η : ℝ} (hη : η ≠ 0) (u : Point m n → ℝ) :
    tableSmooth f B η (-u) = -tableSmooth f B η u := by
  unfold tableSmooth
  rw [← gauss_integral_neg (Code m n) (fun l => bitSign (f.answer (pullQuery B (-u) (η • l))))]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [query_no_ties u hη] with l hl
  have hP : pullQuery B (-u) (η • (-l)) = fun a => !(pullQuery B u (η • l) a) := by
    funext a
    simp only [pullQuery, smul_neg]
    exact query_neg u (η • l) (labelCode B a) (hl _)
  rw [hP, f.folded, bitSign_not]

lemma smooth_odd (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) (c : Point m n → ℝ) :
    smooth f B σ η (-c) = -smooth f B σ η c := by
  change (∫ g, tableSmooth f B η (-c + σ • g) ∂gauss (Point m n)) =
    -(∫ g, tableSmooth f B η (c + σ • g) ∂gauss (Point m n))
  rw [← gauss_integral_neg (Point m n) (fun g => tableSmooth f B η (-c + σ • g))]
  simp only [smul_neg, ← neg_add, tableSmooth_odd f B hη, integral_neg]

lemma smooth_mean_zero (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) :
    (∫ c : Point m n → ℝ, smooth f B σ η c ∂gauss (Point m n)) = 0 := by
  have h := gauss_integral_neg (Point m n) (smooth f B σ η)
  simp_rw [smooth_odd f B σ hη, integral_neg] at h
  linarith

end MinUncut.Inner

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SmoothingRho
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

namespace MinUncut.Inner
open GaussianHermite
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [Fintype A] {m n : ℕ}

lemma spatialEnergy_sqrt_scale (hn : 0 < n) (v : Point m n → ℝ) :
    spatialEnergy (fun x => Real.sqrt (n^m : ℕ)*v x) = ∑ x, (v x)^2 := by
  have hN : (0 : ℝ) < (n^m : ℕ) := by exact_mod_cast pow_pos hn m
  simp only [spatialEnergy, mul_pow, Real.sq_sqrt hN.le, ← Finset.mul_sum]
  exact inv_mul_cancel_left₀ (ne_of_gt hN) _

lemma gradient_integral_energy (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) :
    (∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n)) =
      ∑ x, ∫ c, (convolutionGradient σ (tableSmooth f B η) x c)^2
        ∂gauss (Point m n) := by
  simp_rw [show ∀ c, gradient f B σ η c = fun x => Real.sqrt (n^m : ℕ)*
    convolutionGradient σ (tableSmooth f B η) x c by
      intro c; funext x; exact gradient_as_convolutionGradient f B hσ η c x,
    spatialEnergy_sqrt_scale hn]
  exact integral_finsetSum _ (fun x _ =>
    (convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η) x).integrable_sq)

lemma smooth_energy_le_gradient (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) :
    (∫ c, (smooth f B σ η c)^2 ∂gauss (Point m n)) ≤
      ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  rw [gradient_integral_energy f B hn hσ]
  exact convolution_poincare (ne_of_gt (smoothingRho_pos σ)) hσ
    (smoothingRho_rotation σ) (measurable_tableSmooth f B η)
    (tableSmooth_abs_le f B η) (smooth_mean_zero f B σ hη)

lemma gaussian_residual_energy (d : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) :
    (∫ c, spatialEnergy (fun x => gradient f B σ η c x -
      gaussianProject d f B σ η c x) ∂gauss (Point m n)) =
    ∑ x, ∫ c, (convolutionGradient σ (tableSmooth f B η) x c -
       GaussianHermite.project d (convolutionGradient σ (tableSmooth f B η) x) c)^2
         ∂gauss (Point m n) := by
  simp only [gaussianProject]
  simp_rw [gradient_as_convolutionGradient f B hσ, project_const_mul, ← mul_sub,
    spatialEnergy_sqrt_scale hn]
  exact integral_finsetSum _ (fun x _ =>
    ((convolutionGradient_memLp hσ (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η) x).sub (memLp_project d _)).integrable_sq)

end MinUncut.Inner

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace

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

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointEnergy_nonneg (u : (R → W) → (ι → ℝ) → ℝ) : 0 ≤ jointEnergy u :=
  Finset.expect_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_self (u : (R → W) → (ι → ℝ) → ℝ) : jointInner u u = jointEnergy u := by
  simp only [jointInner, jointEnergy, pow_two]

lemma jointInner_source_component (S : Finset R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointInner u (maskHermite S I u) = jointEnergy (maskHermite S I u) := by
  rw [← jointInner_self, jointInner_maskHermite]
  simp only [↓reduceIte]
  unfold jointInner
  apply Finset.expect_congr rfl
  intro B _
  simp only [maskHermite_eq, ← mul_assoc, integral_mul_const]
  congr 1
  unfold GaussianHermite.coeff
  simp only [mul_comm]

lemma selectedProject_source_inner (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointInner u (selectedProject J u) = ∑ j ∈ J, jointEnergy (maskHermite j.1 j.2 u) := by
  change jointInner u (fun B c => ∑ j ∈ J, maskHermite j.1 j.2 u B c) = _
  rw [jointInner_sum_right J u _ hu (fun j _ B => memLp_maskHermite _ _ _ B)]
  exact Finset.sum_congr rfl (fun j _ => jointInner_source_component j.1 j.2 u)

lemma selectedProject_energy (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (selectedProject J u) = ∑ j ∈ J, jointEnergy (maskHermite j.1 j.2 u) := by
  classical
  rw [← jointInner_self]
  change jointInner (fun B c => ∑ j ∈ J, maskHermite j.1 j.2 u B c) (selectedProject J u) = _
  rw [jointInner_sum_left J _ _ (fun j _ B => memLp_maskHermite _ _ _ B) (memLp_selectedProject J u)]
  apply Finset.sum_congr rfl
  intro j hj
  change jointInner (maskHermite j.1 j.2 u) (fun B c => ∑ k ∈ J, maskHermite k.1 k.2 u B c) = _
  rw [jointInner_sum_right J _ _ (memLp_maskHermite _ _ _) (fun k _ B => memLp_maskHermite _ _ _ B)]
  rw [Finset.sum_eq_single j]
  · exact jointInner_self _
  · intro k hk hkj
    exact components_orthogonal j k hkj.symm u
  · exact fun hjn => (hjn hj).elim

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointEnergy_sub (u v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c-v B c) = jointEnergy u - 2*jointInner u v + jointEnergy v := by
  have h (B) : (∫ c, (u B c-v B c)^2 ∂γpi ι) =
      (∫ c, (u B c)^2 ∂γpi ι) - 2*(∫ c, u B c*v B c ∂γpi ι) + ∫ c, (v B c)^2 ∂γpi ι := by
    simp only [sub_sq, mul_assoc]
    have huv : Integrable (fun c => 2*(u B c*v B c)) (γpi ι) := ((hu B).integrable_mul (hv B)).const_mul 2
    have hsub : Integrable (fun c => (u B c)^2-2*(u B c*v B c)) (γpi ι) := (hu B).integrable_sq.sub huv
    rw [integral_add hsub (hv B).integrable_sq, integral_sub (hu B).integrable_sq huv, integral_const_mul]
  simp only [jointEnergy, jointInner, h, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect]

theorem selectedProject_energy_le (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (selectedProject J u) ≤ jointEnergy u := by
  have h := jointEnergy_nonneg (fun B c => u B c-selectedProject J u B c)
  rw [jointEnergy_sub u _ hu (memLp_selectedProject J u), selectedProject_source_inner J u hu,
    ← selectedProject_energy] at h
  linarith

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SecondFailureIndicator
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
attribute [local irreducible] query pullQuery
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

omit [Fintype A] in
lemma secondFailure_indicator (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    secondFailure f B C σ η c p =
      (coupledAnswer f B σ η c p-coupledAnswer f C σ η c p)^2/4 := by
  have h := secondFailure_eq f B C σ η c p
  linarith

lemma secondRejection_measurable (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    Measurable (secondRejection f B C σ η) := by
  have hh (B : FaceArray A m n) : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer f B σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer f B η).comp hm
  have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      secondFailure f B C σ η u.1 u.2) := by
    simp_rw [secondFailure_indicator]
    exact ((hh B).sub (hh C)).pow_const 2 |>.div_const 4
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma secondRejection_range (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : 0≤ secondRejection f B C σ η c ∧ secondRejection f B C σ η c≤1 := by
  have hm : Measurable (secondFailure f B C σ η c) := by
    change Measurable (fun p => secondFailure f B C σ η c p)
    simp_rw [secondFailure_indicator]
    exact ((coupledAnswer_measurable f B σ η c).sub
      (coupledAnswer_measurable f C σ η c)).pow_const 2 |>.div_const 4
  have hb (p : (Point m n → ℝ) × (Code m n → ℝ)) :
      0≤ secondFailure f B C σ η c p ∧ secondFailure f B C σ η c p≤1 := by
    unfold secondFailure; split_ifs <;> norm_num
  have hi : Integrable (secondFailure f B C σ η c)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb p).1]; exact (hb p).2))
  constructor
  · exact integral_nonneg (fun p => (hb p).1)
  · unfold secondRejection
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using
      integral_mono hi (integrable_const 1) (fun p => (hb p).2)

lemma secondRejection_integrable (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    Integrable (secondRejection f B C σ η) (gauss (Point m n)) :=
  Integrable.of_bound (secondRejection_measurable f B C σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (secondRejection_range f B C σ η c).1]
      exact (secondRejection_range f B C σ η c).2))

lemma rowProjectedGradient_memLp (D : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) :
    MemLp (fun c => rowProjectedGradient D f σ η B c x) 2 (gauss (Point m n)) := by
  unfold rowProjectedGradient RowNoise.project
  apply memLp_finsetSum
  intro α _
  apply MemLp.mul_const
  unfold BinaryFourier.coefficient
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact (memLp_finsetSum _ (fun C _ => (gradient_memLp f C hσ η x).mul_const _)).mul_const _

lemma rowResidualEnergy_integrable (D : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    Integrable (fun c => spatialEnergy (fun x => gradient f B σ η c x-
      rowProjectedGradient D f σ η B c x)) (gauss (Point m n)) := by
  unfold spatialEnergy
  exact (integrable_finsetSum _ (fun x _ =>
    ((gradient_memLp f B hσ η x).sub (rowProjectedGradient_memLp D f B hσ η x)).integrable_sq)).const_mul _

theorem gradient_row_tail_average (f : FoldedProof A) (hn : 0 < n)
    {σ a : ℝ} (hσ : σ≠0) (ha : 0≤a) (ha1 : a≤1) (η : ℝ) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1≤(k:ℝ)*a) :
    (𝔼 B : FaceArray A m n, ∫ c, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x) ∂gauss (Point m n)) ≤
    4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
      RowNoise.density a B C*(∫ c, secondRejection f B C σ η c ∂gauss (Point m n))) := by
  have hl : Integrable (fun c => 𝔼 B : FaceArray A m n, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x)) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => rowResidualEnergy_integrable D f B hσ η)).div_const _
  have hr : Integrable (fun c => 4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
      RowNoise.density a B C*secondRejection f B C σ η c)) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    apply Integrable.const_mul
    apply Integrable.div_const
    apply integrable_finsetSum
    intro B _
    exact (integrable_finsetSum _ (fun C _ =>
      (secondRejection_integrable f B C σ η).const_mul _)).div_const _
  have h := integral_mono hl hr (fun c => gradient_row_tail f hn hσ ha ha1 η D hD c)
  simpa only [Fintype.expect_eq_sum_div_card,integral_div,integral_const_mul,
    integral_finsetSum _ (fun B _ => rowResidualEnergy_integrable D f B hσ η),
    integral_finsetSum _ (fun B _ =>
      (integrable_finsetSum _ (fun C _ => (secondRejection_integrable f B C σ η).const_mul _)).div_const _),
    integral_finsetSum _ (fun C _ => (secondRejection_integrable f _ C σ η).const_mul _)] using h
end MinUncut.Inner
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma jointEnergy_project_le (D : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (fun B c => project D (fun C => u C c) B) ≤ jointEnergy u := by
  unfold jointEnergy
  rw [← integral_expect _ (fun B => (project_memLp D u hu B).integrable_sq),
    ← integral_expect _ (fun B => (hu B).integrable_sq)]
  apply integral_mono
  · simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => (project_memLp D u hu B).integrable_sq)).div_const _
  · simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => (hu B).integrable_sq)).div_const _
  · intro c; exact project_energy_le D (fun B => u B c)

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] [DecidableEq ι] in
lemma jointEnergy_add_le (u v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c+v B c) ≤ 2*jointEnergy u+2*jointEnergy v := by
  have hB (B : R → W) : (∫ c, (u B c+v B c)^2 ∂γpi ι) ≤
      2*(∫ c, (u B c)^2 ∂γpi ι)+2*(∫ c, (v B c)^2 ∂γpi ι) := by
    calc
      _ ≤ ∫ c, 2*(u B c)^2+2*(v B c)^2 ∂γpi ι :=
        integral_mono ((hu B).add (hv B)).integrable_sq
          (((hu B).integrable_sq.const_mul 2).add ((hv B).integrable_sq.const_mul 2))
          (fun c => by
            change (u B c+v B c)^2 ≤ 2*(u B c)^2+2*(v B c)^2
            nlinarith [sq_nonneg (u B c-v B c)])
      _ = _ := by rw [integral_add ((hu B).integrable_sq.const_mul 2) ((hv B).integrable_sq.const_mul 2),integral_const_mul,integral_const_mul]
  simpa only [jointEnergy,Finset.expect_add_distrib,← Finset.mul_expect] using
    Finset.expect_le_expect (s := Finset.univ) (fun B _ => hB B)

theorem rectangle_residual_le (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c-selectedProject (rectangle D s) u B c) ≤
      2*jointEnergy (fun B c => u B c-project D (fun C => u C c) B)+
      2*jointEnergy (fun B c => u B c-GaussianHermite.project s (u B) c) := by
  let v := fun B c => u B c-project D (fun C => u C c) B
  let w := fun B c => u B c-GaussianHermite.project s (u B) c
  have hv (B) : MemLp (v B) 2 (γpi ι) := (hu B).sub (project_memLp D u hu B)
  have hw (B) : MemLp (w B) 2 (γpi ι) := (hu B).sub (GaussianHermite.memLp_project s (u B))
  have he (B c) : u B c-selectedProject (rectangle D s) u B c =
      v B c+project D (fun C => w C c) B := by
    rw [rectangle_eq_composition]
    simp only [v,w,project_sub]
    ring
  simp_rw [he]
  exact (jointEnergy_add_le v (fun B c => project D (fun C => w C c) B) hv
    (project_memLp D w hw)).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (jointEnergy_project_le D w hw) (show (0 : ℝ) ≤ 2 by norm_num)) _)

lemma rectangle_energy_identity (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (selectedProject (rectangle D s) u) = jointEnergy u-
      jointEnergy (fun B c => u B c-selectedProject (rectangle D s) u B c) := by
  rw [jointEnergy_sub u _ hu (memLp_selectedProject _ _),
    selectedProject_source_inner _ u hu,← selectedProject_energy]
  ring
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LowGradient
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma lowGradient_energy_identity (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (lowGradient D s f σ η) =
      averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c)-
      averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) := by
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η),
    averagedEnergy_eq_jointEnergy _ (fun B x => gradient_memLp f B hσ η x),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (lowGradient_memLp D s f σ η B x))]
  simp only [lowGradient,rectangle_energy_identity _ _ _ (fun B => gradient_memLp f B hσ η _),
    Finset.sum_sub_distrib,mul_sub]

lemma lowGradient_residual_le (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) ≤
      2*averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-rowProjectedGradient D f σ η B c x)+
      2*averagedEnergy (m := m) (n := n) (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) := by
  have hg (B : FaceArray A m n) (x : Point m n) :
      MemLp (fun c => gaussianProject s f B σ η c x) 2 (gauss (Point m n)) :=
    GaussianHermite.memLp_project _ _
  rw [averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-lowGradient D s f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (lowGradient_memLp D s f σ η B x)),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-rowProjectedGradient D f σ η B c x) (fun B x => (gradient_memLp f B hσ η x).sub
      (rowProjectedGradient_memLp D f B hσ η x)),
    averagedEnergy_eq_jointEnergy (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) (fun B x => (gradient_memLp f B hσ η x).sub (hg B x))]
  calc
    _ ≤ ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        (2*jointEnergy (fun B c => gradient f B σ η c x-rowProjectedGradient D f σ η B c x)+
         2*jointEnergy (fun B c => gradient f B σ η c x-gaussianProject s f B σ η c x)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ =>
        rectangle_residual_le D s _ (fun B => gradient_memLp f B hσ η x))) (by positivity)
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]; ring

lemma averagedEnergy_gradient_le (f : FoldedProof A) (hn : 0 < n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c) ≤ σ⁻¹^2 := by
  have he (B : FaceArray A m n) :
      (∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n)) ≤ σ⁻¹^2 := by
    have hi : Integrable (fun c => spatialEnergy (gradient f B σ η c)) (gauss (Point m n)) :=
      (integrable_finsetSum _ (fun x _ => (gradient_memLp f B hσ η x).integrable_sq)).const_mul _
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const (σ⁻¹^2)) (gradient_spatialEnergy_le f B hn hσ η)
  simpa [averagedEnergy] using Finset.expect_le_expect (s := Finset.univ) (fun B _ => he B)

lemma averagedEnergy_lowGradient_le (D s : ℕ) (f : FoldedProof A) (hn : 0 < n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (lowGradient D s f σ η) ≤ σ⁻¹^2 := by
  apply le_trans _ (averagedEnergy_gradient_le (m := m) f hn hσ η)
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η),
    averagedEnergy_eq_jointEnergy _ (fun B x => gradient_memLp f B hσ η x)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ =>
    selectedProject_energy_le _ _ (fun B => gradient_memLp f B hσ η x))) (by positivity)
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ArraySum
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable [Fintype A]

theorem gradient_addConstantArray (f : FoldedProof A) (B : FaceArray A m n)
    (k : Row m n → F₂) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f (addConstantArray B k) σ η c x =
      BinaryFourier.sign ((rowCode k).val x) * gradient f B σ η (diagonal (rowCode k).val c) x := by
  rw [gradient_convolution f _ hσ, gradient_convolution f _ hσ]
  simp_rw [pullQuery_addConstantArray, diagonal_add, diagonal_smul]
  have hl (g : Point m n → ℝ) := integral_code_translate (rowCode k)
    (fun l => g x*bitSign (f.answer (pullQuery B
      (diagonal (rowCode k).val c+σ • diagonal (rowCode k).val g) (η • l))))
  simp_rw [show ∀ (l : Code m n → ℝ), (fun z => (η • l) (z+rowCode k)) =
      η • (fun z => l (z+rowCode k)) from fun l => rfl, hl]
  have hg := integral_diagonal (rowCode k).val (fun g =>
    ∫ l : Code m n → ℝ, g x * bitSign (f.answer (pullQuery B
      (diagonal (rowCode k).val c+σ • g) (η • l))) ∂gauss (Code m n))
  dsimp only [diagonal] at hg
  simp_rw [mul_assoc, integral_const_mul] at hg
  simp_rw [integral_const_mul]
  rw [← hg]
  have hs := BinaryFourier.sign_sq ((rowCode k).val x)
  ring_nf at hs ⊢
  simp only [hs, one_mul]
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
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma H_mean {d : ℕ} (hd : 0<d) : (∫ t, H d t ∂γ)=0 := by
  simpa only [H_zero,mul_one,ite_eq_right (Nat.ne_zero_of_lt hd)] using H_product d 0

end MinUncut.GaussianHermite

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
namespace MinUncut.Slice
open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq W] in
lemma processed_energy_le {H γ A : ℝ} (hA : 0 ≤ A) (one : W) (f : W → ℝ) :
    (𝔼 w, (processed H γ A one f w)^2) ≤ H^2 := by
  by_cases h : H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f
  · simp only [processed, h, ↓reduceIte, zero_pow (by omega : 2 ≠ 0), Fintype.expect_const]
    exact sq_nonneg H
  · have hs : Real.sqrt (𝔼 b, (f b)^2) ≤ H := le_of_not_gt (fun ht => h (Or.inl ht))
    have he : 0 ≤ 𝔼 b, (f b)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
    calc
      _ ≤ 𝔼 w, (f w)^2 := Finset.expect_le_expect (fun w _ => processed_sq_le hA one f w)
      _ ≤ H^2 := by nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (𝔼 b, (f b)^2)]

open BinaryFourier
end MinUncut.Slice

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
namespace MinUncut.RowNoise
open BinaryFourier GaussianHermite MeasureTheory
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [AddCommGroup W] [Module F₂ W] [DecidableEq ι] in
lemma selectedProject_continuous (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) :
    Continuous (selectedProject J u B) := by
  unfold selectedProject
  apply continuous_finsetSum
  intro j _
  change Continuous (fun c => maskHermite j.1 j.2 u B c)
  simp only [maskHermite_eq]
  exact (continuous_psi j.2).mul_const _
end MinUncut.RowNoise

namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_c_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    Measurable (fun c => pairSlice f σ η x Y p J B c b) := by
  unfold pairSlice localSlice
  exact (selectedProject_continuous _ _ _).measurable

lemma pairProcessedOnBox_c_measurable (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (u : Point m (k+1)) :
    Measurable (fun c => pairProcessedOnBox f σ η Y p J H γ A₀ B c u) := by
  unfold pairProcessedOnBox
  exact Slice.processed_measurable _ _ (pairSlice_c_measurable f σ η _ _ p J B) H γ A₀ _

lemma pairProcessedOnBox_abs_le (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ : ℝ) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) :
    |pairProcessedOnBox f σ η Y p J H γ A₀ B c u|≤A₀ := by
  unfold pairProcessedOnBox
  exact Slice.processed_abs_le hA _ _ _
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FreshCorrelation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma spatialEnergy_eq_expect (v : Point m n → ℝ) :
    spatialEnergy v = 𝔼 x : Point m n, (v x)^2 := by
  simp [spatialEnergy,Fintype.expect_eq_sum_div_card,Point,div_eq_mul_inv,mul_comm]

lemma spatial_young (v w : Point m n → ℝ) {a : ℝ} (ha : 0<a) :
    (𝔼 x : Point m n, v x*w x) ≤ a*spatialEnergy v+(4*a)⁻¹*spatialEnergy w := by
  rw [spatialEnergy_eq_expect,spatialEnergy_eq_expect]
  simp only [Finset.mul_expect,← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro x _
  have he : (4*a)*((4*a)⁻¹) = 1 := mul_inv_cancel₀ (by positivity)
  nlinarith [sq_nonneg (2*a*v x-w x)]

lemma gradient_correlation_truncate (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a)
    (c : Point m n → ℝ) (v : Point m n → ℝ) :
    (𝔼 x : Point m n, v x*gradient f B σ η c x) ≤
      T*faceCorrelation v+a*spatialEnergy v+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c := by
  have hE : 0 ≤ spatialEnergy v := by rw [spatialEnergy_eq_expect]; positivity
  have hW := tableMass_le_thirdRejection f B σ hη c
  have hcoeff : 0 ≤ σ⁻¹^2/(4*a*T) := by positivity
  have hsmall : 0 ≤ (σ⁻¹^2/(4*a*T))*tableMass f B σ η c :=
    mul_nonneg hcoeff (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hmid : (𝔼 x : Point m n, v x*gradient f B σ η c x) ≤
      T*faceCorrelation v+a*spatialEnergy v+(σ⁻¹^2/(4*a*T))*tableMass f B σ η c := by
    by_cases h : tableMass f B σ η c ≤ T
    · have hz := (le_abs_self _).trans (gradient_convex_correlation f B hn hσ hη.ne' c v)
      have hm := mul_le_mul_of_nonneg_right h (faceCorrelation_nonneg v)
      nlinarith [mul_nonneg ha.le hE]
    · have hy := spatial_young v (gradient f B σ η c) ha
      have hg := mul_le_mul_of_nonneg_left (gradient_spatialEnergy_le f B hn hσ η c)
        (show 0≤(4*a)⁻¹ by positivity)
      have hw := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hcoeff
      have he : (σ⁻¹^2/(4*a*T))*T = (4*a)⁻¹*σ⁻¹^2 := by field_simp
      rw [he] at hw
      nlinarith [mul_nonneg hT.le (faceCorrelation_nonneg v)]
  exact hmid.trans (by nlinarith [mul_le_mul_of_nonneg_left hW hcoeff])

omit [Fintype A] in
lemma thirdRejection_measurable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (thirdRejection f B σ η) := by
  have hh (z : Code m n) : Measurable
      (fun p : ((Point m n → ℝ) × (Point m n → ℝ)) × (Code m n → ℝ) =>
        thirdFailure f B η (p.1.1+σ•p.1.2) p.2 z) :=
    (measurable_thirdFailure f B η z).comp (show Measurable
      (fun p : ((Point m n → ℝ) × (Point m n → ℝ)) × (Code m n → ℝ) =>
        (p.1.1+σ•p.1.2,p.2)) by fun_prop)
  have hi (z : Code m n) : Measurable (fun c : Point m n → ℝ =>
      ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n) ∂gauss (Point m n)) :=
    (hh z).stronglyMeasurable.integral_prod_right.measurable.stronglyMeasurable.integral_prod_right.measurable
  unfold thirdRejection
  simp only [Fintype.expect_eq_sum_div_card]
  exact (Finset.measurable_sum _ (fun z _ => hi z)).div_const _

omit [Fintype A] in
lemma thirdRejection_abs_le (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : |thirdRejection f B σ η c| ≤ 1 := by
  have he (z : Code m n) (g : Point m n → ℝ) :
      |∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n)| ≤ 1 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := gauss (Code m n))
        (f := fun l => thirdFailure f B η (c+σ•g) l z) (C := 1)
        (ae_of_all _ (fun l => by simpa only [Real.norm_eq_abs] using thirdFailure_abs_le f B η _ l z))
  have hb (z : Code m n) :
      |∫ g, ∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n) ∂gauss (Point m n)| ≤ 1 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := gauss (Point m n))
        (f := fun g => ∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n)) (C := 1)
        (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using he z g))
  exact (Finset.abs_expect_le _ _).trans (by
    simpa using Finset.expect_le_expect (s := Finset.univ) (fun z _ => hb z))

omit [Fintype A] in
lemma thirdRejection_integrable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Integrable (thirdRejection f B σ η) (gauss (Point m n)) :=
  Integrable.of_bound (thirdRejection_measurable f B σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using thirdRejection_abs_le f B σ η c))

lemma lowGradient_continuous (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (x : Point m n) :
    Continuous (fun c => lowGradient D s f σ η B c x) :=
  selectedProject_continuous _ _ _

lemma lowGradient_correlation_continuous (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) :
    Continuous (fun c => faceCorrelation (lowGradient D s f σ η B c)) := by
  apply Continuous.finset_sup'_apply
  intro z _
  simp only [Fintype.expect_eq_sum_div_card]
  exact ((continuous_finsetSum _ (fun x _ =>
    (lowGradient_continuous D s f σ η B x).mul continuous_const)).div_const _).abs

lemma lowGradient_correlation_integrable (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) :
    Integrable (fun c => faceCorrelation (lowGradient D s f σ η B c)) (gauss (Point m n)) := by
  have hi : Integrable (fun c => 𝔼 x : Point m n, |lowGradient D s f σ η B c x|)
      (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ =>
      ((lowGradient_memLp D s f σ η B x).integrable (by norm_num)).abs)).div_const _
  exact hi.mono' (lowGradient_correlation_continuous D s f σ η B).aestronglyMeasurable
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (faceCorrelation_nonneg _)]
      exact faceCorrelation_le_l1 _))

lemma lowGradient_inner_identity (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 B : FaceArray A m n, ∫ c, (𝔼 x : Point m n,
      lowGradient D s f σ η B c x*gradient f B σ η c x) ∂gauss (Point m n)) =
      averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) := by
  have hi (B : FaceArray A m n) :
      (∫ c, (𝔼 x : Point m n, lowGradient D s f σ η B c x*gradient f B σ η c x)
        ∂gauss (Point m n)) =
      (𝔼 x : Point m n, ∫ c, lowGradient D s f σ η B c x*gradient f B σ η c x
        ∂gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card,integral_div]
    rw [integral_finsetSum (f := fun x c => lowGradient D s f σ η B c x*gradient f B σ η c x) _ (fun x _ =>
      (lowGradient_memLp D s f σ η B x).integrable_mul (gradient_memLp f B hσ η x))]
  simp_rw [hi]
  rw [Finset.expect_comm]
  have he (x : Point m n) :
      (𝔼 B : FaceArray A m n, ∫ c,
        lowGradient D s f σ η B c x*gradient f B σ η c x ∂gauss (Point m n)) =
      jointEnergy (fun B c => lowGradient D s f σ η B c x) := by
    change jointInner (selectedProject (rectangle D s) (fun B c => gradient f B σ η c x))
      (fun B c => gradient f B σ η c x) = _
    rw [jointInner_symm,selectedProject_source_inner _ _ (fun B => gradient_memLp f B hσ η x),
      ← selectedProject_energy]
    rfl
  simp_rw [he]
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η)]
  simp [Point,Fintype.expect_eq_sum_div_card,div_eq_mul_inv,mul_comm]

lemma lowGradient_correlation_truncated (D s : ℕ) (f : FoldedProof A)
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a) :
    averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) ≤
      T*averagedCorrelation (lowGradient (m := m) (n := n) D s f σ η)+
      a*averagedEnergy (lowGradient (m := m) (n := n) D s f σ η)+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdError (m := m) (n := n) f σ η := by
  have hi (B : FaceArray A m n) :
      Integrable (fun c => 𝔼 x : Point m n,
        lowGradient D s f σ η B c x*gradient f B σ η c x) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ =>
      (lowGradient_memLp D s f σ η B x).integrable_mul (gradient_memLp f B hσ η x))).div_const _
  have he (B : FaceArray A m n) :
      Integrable (fun c => spatialEnergy (lowGradient D s f σ η B c)) (gauss (Point m n)) := by
    simp only [spatialEnergy]
    exact (integrable_finsetSum _ (fun x _ => (lowGradient_memLp D s f σ η B x).integrable_sq)).const_mul _
  have hp (B : FaceArray A m n) := integral_mono (hi B)
    (((lowGradient_correlation_integrable D s f σ η B).const_mul T).add ((he B).const_mul a) |>.add
      ((thirdRejection_integrable f B σ η).const_mul ((σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η))))
    (fun c => gradient_correlation_truncate f B hn hσ hη hT ha c (lowGradient D s f σ η B c))
  have hp' (B : FaceArray A m n) :
      (∫ c, (𝔼 x : Point m n, lowGradient D s f σ η B c x*gradient f B σ η c x)
        ∂gauss (Point m n)) ≤
      T*(∫ c, faceCorrelation (lowGradient D s f σ η B c) ∂gauss (Point m n))+
      a*(∫ c, spatialEnergy (lowGradient D s f σ η B c) ∂gauss (Point m n))+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*
        (∫ c, thirdRejection f B σ η c ∂gauss (Point m n)) := by
    have hh := hp B
    change _ ≤ ∫ c, (T*faceCorrelation (lowGradient D s f σ η B c)+
      a*spatialEnergy (lowGradient D s f σ η B c)+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c)
        ∂gauss (Point m n) at hh
    rw [integral_add (f := fun c => T*faceCorrelation (lowGradient D s f σ η B c)+a*spatialEnergy (lowGradient D s f σ η B c))
      (g := fun c => (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c)
      ((lowGradient_correlation_integrable D s f σ η B).const_mul T |>.add ((he B).const_mul a))
      ((thirdRejection_integrable f B σ η).const_mul _),
      integral_add ((lowGradient_correlation_integrable D s f σ η B).const_mul T) ((he B).const_mul a)] at hh
    simpa only [integral_const_mul] using hh
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun B _ => hp' B)
  rw [lowGradient_inner_identity D s f hσ η] at hh
  simpa only [Finset.expect_add_distrib,← Finset.mul_expect,averagedCorrelation,averagedEnergy,thirdError]
    using hh
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma lowGradient_correlation_truncated_weighted (D s : ℕ)
    (w : Ξ → ℝ) (hw : ∀ ξ,0≤w ξ) (f : ∀ ξ, FoldedProof (A ξ))
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a) :
    (∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η)) ≤
      T*(∑ ξ, w ξ*averagedCorrelation (lowGradient (m := m) (n := n) D s (f ξ) σ η))+
      a*(∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η))+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*
        (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) σ η) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ξ _ => mul_le_mul_of_nonneg_left
    (lowGradient_correlation_truncated (m := m) D s (f ξ) hn hσ hη hT ha) (hw ξ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_add,Finset.sum_add_distrib]
  congr 2 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro ξ _ <;> ring
end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ActualBoxBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

omit [Fintype A] in
lemma firstFailure_eq (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    firstFailure f B σ η c g l =
      (1-bitSign (f.answer (pullQuery B c 0))*bitSign (f.answer (pullQuery B (c+σ•g) (η•l))))/2 := by
  unfold firstFailure
  cases f.answer (pullQuery B c 0) <;> cases f.answer (pullQuery B (c+σ•g) (η•l)) <;> norm_num [bitSign]

lemma measurable_smooth (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (smooth f B σ η) := by
  have hh : Measurable (fun p : (Point m n → ℝ) × (Point m n → ℝ) =>
      tableSmooth f B η (p.1+σ•p.2)) := (measurable_tableSmooth f B η).comp (by fun_prop)
  exact hh.stronglyMeasurable.integral_prod_right.measurable

omit [Fintype A] in
lemma smooth_abs_le (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : |smooth f B σ η c|≤1 := by
  change |∫ g, tableSmooth f B η (c+σ•g) ∂gauss (Point m n)|≤1
  simpa only [Real.norm_eq_abs,MeasureTheory.probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := gauss (Point m n)) (f := fun g => tableSmooth f B η (c+σ•g)) (C := 1)
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using tableSmooth_abs_le f B η (c+σ•g)))

lemma firstRejection_eq (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    firstRejection f B σ η c = (1-bitSign (f.answer (pullQuery B c 0))*smooth f B σ η c)/2 := by
  have hi (g : Point m n → ℝ) : Integrable
      (fun l => bitSign (f.answer (pullQuery B (c+σ•g) (η•l)))) (gauss (Code m n)) :=
    Box.bounded_integrable ((measurable_answer f B η).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (fun l => (bitSign_abs _).le)
  have ht : Integrable (fun g => tableSmooth f B η (c+σ•g)) (gauss (Point m n)) :=
    Box.bounded_integrable ((measurable_tableSmooth f B η).comp (by fun_prop)).aestronglyMeasurable
      (fun g => tableSmooth_abs_le f B η _)
  unfold firstRejection
  simp_rw [firstFailure_eq, integral_div]
  simp_rw [integral_sub (integrable_const 1) ((hi _).const_mul _), integral_const_mul]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  change (∫ g, (1-bitSign (f.answer (pullQuery B c 0))*tableSmooth f B η (c+σ•g)) ∂gauss (Point m n))/2=_
  rw [integral_sub (integrable_const 1) (ht.const_mul _),integral_const_mul]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  rfl

lemma measurable_firstRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (firstRejection f B σ η) := by
  simp_rw [show firstRejection f B σ η = fun c =>
    (1-bitSign (f.answer (pullQuery B c 0))*smooth f B σ η c)/2 by
    funext c; exact firstRejection_eq f B σ η c]
  have h0 : Measurable (fun c : Point m n → ℝ => bitSign (f.answer (pullQuery B c 0))) :=
    (measurable_of_finite bitSign).comp ((measurable_of_finite f.answer).comp
      ((measurable_pullQuery B).comp (measurable_id.prodMk measurable_const)))
  exact (measurable_const.sub (h0.mul (measurable_smooth f B σ η))).div_const _

lemma firstRejection_range (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : 0≤firstRejection f B σ η c ∧ firstRejection f B σ η c≤1 := by
  rw [firstRejection_eq]
  have hb := abs_le.mp (smooth_abs_le f B σ η c)
  cases f.answer (pullQuery B c 0) <;> norm_num [bitSign] <;> constructor <;> linarith

lemma smooth_energy_first (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    1-4*firstRejection f B σ η c≤(smooth f B σ η c)^2 := by
  rw [firstRejection_eq]
  cases f.answer (pullQuery B c 0) <;> simp only [bitSign,Bool.false_eq_true,↓reduceIte] <;>
    nlinarith [sq_nonneg (smooth f B σ η c-1),sq_nonneg (smooth f B σ η c+1)]

theorem gradient_energy_first (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ≠0) (hη : η≠0) :
    1-4*(∫ c, firstRejection f B σ η c ∂gauss (Point m n)) ≤
      ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  have hr : Integrable (firstRejection f B σ η) (gauss (Point m n)) :=
    Box.bounded_integrable (measurable_firstRejection f B σ η).aestronglyMeasurable (fun c => by
      rw [abs_of_nonneg (firstRejection_range f B σ η c).1]
      exact (firstRejection_range f B σ η c).2)
  have hs : MemLp (smooth f B σ η) 2 (gauss (Point m n)) :=
    MemLp.of_bound (measurable_smooth f B σ η).aestronglyMeasurable 1
      (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using smooth_abs_le f B σ η c))
  apply le_trans _ (smooth_energy_le_gradient f B hn hσ hη)
  calc
    _ = ∫ c, 1-4*firstRejection f B σ η c ∂gauss (Point m n) := by
      rw [integral_sub (integrable_const 1) (hr.const_mul 4),integral_const_mul]
      simp
    _ ≤ _ := integral_mono ((integrable_const 1).sub (hr.const_mul 4)) hs.integrable_sq
      (smooth_energy_first f B σ η)
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GradientEnergyFirstTables
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma gradient_energy_first_tables (f : FoldedProof A) (hn : 0 < n)
    {σ η : ℝ} (hσ : σ≠0) (hη : η≠0) :
    1-4*(𝔼 B : FaceArray A m n, ∫ c, firstRejection f B σ η c ∂gauss (Point m n)) ≤
      𝔼 B : FaceArray A m n, ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  calc
    _ = 𝔼 B : FaceArray A m n, (1-4*(∫ c, firstRejection f B σ η c ∂gauss (Point m n))) := by
      rw [Finset.expect_sub_distrib,← Finset.mul_expect,Fintype.expect_const]
    _ ≤ _ := Finset.expect_le_expect (fun B _ => gradient_energy_first f B hn hσ hη)
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FirstError
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma gaussian_tail_of_cutoff (f : FoldedProof A) (hn : 0 < n)
    {σ ε : ℝ} (hσ : σ≠0) (hε : 0≤ε) (η : ℝ) (s : ℕ)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    averagedEnergy (m := m) (n := n)
      (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) ≤ ε := by
  have he (B : FaceArray A m n) :
      (∫ c, spatialEnergy (fun x => gradient f B σ η c x-gaussianProject s f B σ η c x)
        ∂gauss (Point m n)) ≤ ε := by
    rw [gaussian_residual_energy s f B hn hσ]
    exact convolution_gradient_tail (ne_of_gt (smoothingRho_pos σ)) hσ
      (smoothingRho_rotation σ) hε s hs (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η)
  simpa [averagedEnergy] using Finset.expect_le_expect (s := Finset.univ) (fun B _ => he B)

theorem lowGradient_energy_lower (f : FoldedProof A) (hn : 0 < n)
    {σ η a ε : ℝ} (hσ : σ≠0) (hη : η≠0) (ha : 0≤a) (ha1 : a≤1) (hε : 0≤ε)
    (D s : ℕ) (hD : ∀ k : ℕ, D<k → 1≤(k:ℝ)*a)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    1-4*firstError (m := m) (n := n) f σ η-
      8*σ⁻¹^2*secondError (m := m) (n := n) f a σ η-2*ε ≤
      averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) := by
  have h1 := gradient_energy_first_tables (m := m) f hn hσ hη
  have h2 := gradient_row_tail_average (m := m) f hn hσ ha ha1 η D hD
  have hc := gaussian_tail_of_cutoff (m := m) f hn hσ hε η s hs
  have he := lowGradient_residual_le (m := m) (n := n) D s f hσ η
  have hi := lowGradient_energy_identity (m := m) (n := n) D s f hσ η
  change 1-4*firstError (m := m) (n := n) f σ η ≤
    averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c) at h1
  change averagedEnergy (m := m) (n := n) (fun B c x =>
    gradient f B σ η c x-rowProjectedGradient D f σ η B c x) ≤
    4*σ⁻¹^2*secondError (m := m) (n := n) f a σ η at h2
  linarith
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LowGradientEnergyLowerWeighted
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

theorem lowGradient_energy_lower_weighted (w : Ξ → ℝ) (hw : ∀ ξ, 0≤w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) (hn : 0 < n)
    {σ η a ε : ℝ} (hσ : σ≠0) (hη : η≠0) (ha : 0≤a) (ha1 : a≤1) (hε : 0≤ε)
    (D s : ℕ) (hD : ∀ k : ℕ, D<k → 1≤(k:ℝ)*a)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    1-4*(∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) σ η)-
      8*σ⁻¹^2*(∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ) a σ η)-2*ε ≤
      ∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η) := by
  calc
    _ = ∑ ξ, w ξ*(1-4*firstError (m := m) (n := n) (f ξ) σ η-
        8*σ⁻¹^2*secondError (m := m) (n := n) (f ξ) a σ η-2*ε) := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
      simp_rw [show ∀ ξ, w ξ*(4*firstError (m := m) (n := n) (f ξ) σ η) =
        4*(w ξ*firstError (m := m) (n := n) (f ξ) σ η) by intro ξ; ring,
        show ∀ ξ, w ξ*(8*σ⁻¹^2*secondError (m := m) (n := n) (f ξ) a σ η) =
        (8*σ⁻¹^2)*(w ξ*secondError (m := m) (n := n) (f ξ) a σ η) by intro ξ; ring,
        show ∀ ξ, w ξ*(2*ε) = (2*ε)*w ξ by intro ξ; ring]
      rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hw1,mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left
      (lowGradient_energy_lower (m := m) (f ξ) hn hσ hη ha ha1 hε D s hD hs) (hw ξ))

open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable

end MinUncut.Inner

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

lemma rationalDensity_cast (a : ℚ) (B C : R → W) :
    (rationalDensity a B C:ℝ)=density a B C := by
  simp only [rationalDensity,density,Rat.cast_prod,rationalRowDensity_cast]

end MinUncut.RowNoise

end
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

lemma classField_measurable (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (x : Point m n) :
    Measurable (fun c => classField f σ η J a B c x) :=
  (selectedProject_continuous _ _ _).measurable

lemma classField_correlation_integrable (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) :
    Integrable (fun c => faceCorrelation (classField f σ η J a B c)) (γpi (Point m n)) :=
  faceCorrelation_integrable _ (classField_measurable f σ η J a B)
    (fun x => (classField_memLp f σ η J a B x).integrable (by norm_num))

lemma lowGradient_classes_correlation (D s : ℕ) (f : FoldedProof A) (σ η : ℝ) :
    averagedCorrelation (lowGradient (m := m) (n := n) D s f σ η) ≤
      ∑ a : Option (PairClass m), averagedCorrelation (classField (n := n) f σ η (rectangle D s) a) := by
  have hp (B : FaceArray A m n) (c : Point m n → ℝ) :
      faceCorrelation (lowGradient D s f σ η B c) ≤
        ∑ a : Option (PairClass m), faceCorrelation (classField f σ η (rectangle D s) a B c) := by
    conv_lhs => arg 1; ext x; rw [lowGradient_class_partition]
    exact faceCorrelation_sum_le _ _
  unfold averagedCorrelation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro B _
  calc
    _ ≤ ∫ c, (∑ a : Option (PairClass m), faceCorrelation (classField f σ η (rectangle D s) a B c)) ∂γpi (Point m n) :=
      integral_mono (lowGradient_correlation_integrable D s f σ η B)
        (integrable_finsetSum _ (fun a _ => classField_correlation_integrable f σ η (rectangle D s) a B)) (hp B)
    _ = _ := integral_finsetSum _ (fun a _ => classField_correlation_integrable f σ η (rectangle D s) a B)
end MinUncut.Inner

open scoped BigOperators

open scoped BigOperators

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

lemma weighted_lowGradient_classes (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (D s : ℕ) (f : ∀ ξ, FoldedProof (A ξ)) (σ η : ℝ) :
    (∑ ξ, w ξ*averagedCorrelation (lowGradient (m := m) (n := n) D s (f ξ) σ η)) ≤
      ∑ a : Option (PairClass m), ∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η (rectangle D s) a) := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (lowGradient_classes_correlation (m := m) (n := n) D s (f ξ) σ η) (hw ξ))
  simp only [Finset.mul_sum] at hh
  rwa [Finset.sum_comm] at hh

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

lemma classTarget_pos {T : ℝ} (hT : 0 < T) (m : ℕ) : 0 < classTarget T m := by
  unfold classTarget
  positivity

lemma classes_times_target {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (Fintype.card (Option (PairClass m)):ℝ)*classTarget T m = 1/(4*T) := by
  have hc : (Fintype.card (Option (PairClass m)):ℝ) ≠ 0 := by positivity
  unfold classTarget
  field_simp

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TableTestFunctions
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
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def firstTable (f : FoldedProof A) (B : FaceArray A m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (false,labelCode B a)))
    (f.answer (fun a => t (true,labelCode B a)))

def secondTable (f : FoldedProof A) (B C : FaceArray A m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (true,labelCode B a)))
    (f.answer (fun a => t (true,labelCode C a)))

def thirdTable (f : FoldedProof A) (B : FaceArray A m n) (z : Code m n)
    (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => Function.update (fun z => t (true,z)) z true (labelCode B a)))
    (f.answer (fun a => Function.update (fun z => t (true,z)) z false (labelCode B a)))

def fourthTable (f : FoldedProof A) (g : FoldedProof A') (B : FaceArray A m n)
    (C : FaceArray A' m n) (t : ScoreIndex m n → Bool) : ℝ :=
  disagreement (f.answer (fun a => t (true,labelCode B a)))
    (g.answer (fun a => t (true,labelCode C a)))

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]

def totalFailure (e : D → Demand V) (s : V → Bool) : ℕ := ∑ d, failure (e d) s

end MinUncut.PathRealization

end
namespace MinUncut.FiniteProof

variable {Q : Type*} {A : Q → Type*} (base : ∀ q, A q)

lemma QueryDemand.failure_signed (d : QueryDemand (A := A)) (y : Variable base → Bool) :
    PathRealization.failure (d.signed base) y=d.failure (answer base y) := by
  unfold PathRealization.failure QueryDemand.signed QueryDemand.failure answer
  cases d.equal <;> cases d.left.2 (base d.left.1) <;> cases d.right.2 (base d.right.1) <;>
    cases y (vertex base d.left) <;> cases y (vertex base d.right) <;> rfl

end MinUncut.FiniteProof

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteAverageBounds
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
attribute [local instance] coordsDecEq
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def tableAverage (g : GridData) (σ η : ℚ) (F : (ScoreIndex m n → Bool) → ℝ) : ℝ :=
  ∑ j : TestCoordinates m n → Fin g.L,
    (gridWeight g j:ℝ)*F (rationalScoreTable σ η (fun i => midpoint g.T g.L (j i)))

def finiteFirst (g : GridData) (f : FoldedProof A) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, tableAverage g σ η (firstTable f B)

def finiteSecond (g : GridData) (f : FoldedProof A) (a : ℝ) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
    RowNoise.density a B C*tableAverage g σ η (secondTable f B C)

def finiteThird (g : GridData) (f : FoldedProof A) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 z : Code m n, tableAverage g σ η (thirdTable f B z)

def finiteFourth (g : GridData) (π : A →ᵃ[F₂] A') (f : FoldedProof A) (f' : FoldedProof A')
    (σ η : ℚ) : ℝ :=
  𝔼 C : FaceArray A' m n, tableAverage g σ η (fourthTable f f' (pullbackFaces π C) C)

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerCost
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S]

lemma rationalRate_cast (J : ℕ) (d : InnerData) :
    (rationalRate J d:ℝ)=(sourceEta J)^2/d.m := by
  simp only [rationalRate,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,rationalEta_cast]

lemma rationalRate_bounds {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J) :
    0 ≤ rationalRate J d ∧ rationalRate J d≤1 := by
  have ha := source_row_rate (by exact_mod_cast hJ : (1:ℝ)≤J)
    (by have := (d.realize hJ hd).hm; change 2≤d.m at this; omega : 0<d.m)
  rw [← rationalRate_cast] at ha
  exact ⟨by exact_mod_cast ha.1,by exact_mod_cast ha.2.1⟩

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

namespace Parameters

lemma t_pos {J : ℕ} (P : Parameters J) : 0<P.o.t := P.ho.2.2.2.1

end Parameters
end MinUncut.Outer

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

lemma expanded_failure (D : ℕ) (w : E → ℚ) (d : E → Demand V) (y : V → Bool) :
    totalFailure (expanded D w d) y = ∑ e, multiplicity D (w e)*failure (d e) y := by
  simp [totalFailure,expanded,Fintype.sum_sigma]

lemma expanded_weight (D : ℕ) (w : E → ℚ) (hw : ∀ e, 0≤w e) (hD : ∀ e, (w e).den ∣ D)
    (d : E → Demand V) (y : V → Bool) :
    (totalFailure (expanded D w d) y:ℝ)=(D:ℝ)*∑ e, (w e:ℝ)*(failure (d e) y:ℝ) := by
  rw [expanded_failure]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have h : (multiplicity D (w e):ℝ)=(D:ℝ)*(w e:ℝ) := by
    exact_mod_cast multiplicity_cast (hw e) (hD e)
  rw [h,mul_assoc]


open scoped BigOperators
open PathRealization
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteProof

end

end OAI
end


