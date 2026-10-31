-- Prove2me | Definitions.Def_OAIQ024S000
-- name    : OAIQ024S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:18:09.197117+00:00
-- url     : https://prove2.me/theorems/e7d362da-4713-4cb5-9562-8db9196cedc0
-- title:
--   Definitions bundle OAIQ024S000 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 306 declarations of OpenAI's Lean: 188 definitions, 5 inductive types or structures, 6 instances and 107 theorems. The definitions and types are `OAI.SKRatio.Bins.Coordinates`, `OAI.SKRatio.Bins.DirectionSet`, `OAI.SKRatio.Bins.Directions`, `OAI.SKRatio.Bins.ParameterSet`, `OAI.SKRatio.Bins.ParameterSpace`, `OAI.SKRatio.Bins.Parameters`, `OAI.SKRatio.Bins.WeightBox`, `OAI.SKRatio.Bins.ZeroSum`, `OAI.SKRatio.Bins.average`, `OAI.SKRatio.Bins.binBox`, `OAI.SKRatio.Bins.binCentered`, `OAI.SKRatio.Bins.binFormBad`, `OAI.SKRatio.Bins.binMass`, `OAI.SKRatio.Bins.binMean`, `OAI.SKRatio.Bins.binT`, `OAI.SKRatio.Bins.binVariance`, `OAI.SKRatio.Bins.blockNorm`, `OAI.SKRatio.Bins.centered`, `OAI.SKRatio.Bins.comparisonCoeff`, `OAI.SKRatio.Bins.correctedForm`, `OAI.SKRatio.Bins.count`, `OAI.SKRatio.Bins.crossCoeff`, `OAI.SKRatio.Bins.fieldDiagonal`, `OAI.SKRatio.Bins.fieldForm`, `OAI.SKRatio.Bins.fieldRadicand`, `OAI.SKRatio.Bins.finiteA`, `OAI.SKRatio.Bins.finiteGaussian`, `OAI.SKRatio.Bins.finiteRadicalSq`, `OAI.SKRatio.Bins.finiteV`, `OAI.SKRatio.Bins.fullCoeff`, `OAI.SKRatio.Bins.gridCut`, `OAI.SKRatio.Bins.gridQuant`, `OAI.SKRatio.Bins.gridRep`, `OAI.SKRatio.Bins.intervalBin`, `OAI.SKRatio.Bins.linearMatrix`, `OAI.SKRatio.Bins.massRoot`, `OAI.SKRatio.Bins.matrixInner`, `OAI.SKRatio.Bins.moment`, `OAI.SKRatio.Bins.overlap`, `OAI.SKRatio.Bins.paramB` and 153 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKRatio_Calculus_Energy`, `SKRatio_Calculus_FieldTails`, `SKRatio_Calculus_GibbsMeanCLM`, `SKRatio_Calculus_Interaction`, `SKRatio_Calculus_PlusSpin`, `SKRatio_Calculus_RowControl`, `SKRatio_Calculus_SignedVector`, `SKRatio_Calculus_SpectralLower`, `SKRatio_Certificates_CertifiedFunctions`, `SKRatio_Certificates_CertifiedInterpolation`, `SKRatio_Certificates_CertifiedInterval`, `SKRatio_Certificates_CertifiedJet`, `SKRatio_Certificates_CertifiedQuadrature`, `SKRatio_Certificates_FixedExp`, `SKRatio_Certificates_ScalarDataJ0K0`, `SKRatio_Certificates_ScalarDataJ0K1`, `SKRatio_Certificates_ScalarDataJ0K2`, `SKRatio_Certificates_ScalarDataJ0K3`, `SKRatio_Certificates_ScalarDataJ0K4`, `SKRatio_Certificates_ScalarDataJ0K5`, `SKRatio_Certificates_ScalarDataJ0K6`, `SKRatio_Certificates_ScalarDataJ0K7`, `SKRatio_Certificates_ScalarDataJ1K0`, `SKRatio_Certificates_ScalarDataJ1K1`, `SKRatio_Certificates_ScalarDataJ1K2`, `SKRatio_Certificates_ScalarDataJ1K3`, `SKRatio_Certificates_ScalarDataJ1K4`, `SKRatio_Certificates_ScalarDataJ1K6`, `SKRatio_Dynamics_ClockBridge`, `SKRatio_Dynamics_Concentration`, `SKRatio_Dynamics_Median`, `SKRatio_Dynamics_PositiveLag`, `SKRatio_Entropy_Entropy`, `SKRatio_FiniteChain_DiscreteDistanceNonneg`, `SKRatio_FiniteChain_Mean`, `SKRatio_FiniteChain_Spin`, `SKRatio_Gaussian_HammingGeometry`, `SKRatio_Matrices_GOERegression`, `SKRatio_Matrices_PlantedGOE`, `SKRatio_Quantization_BinCoefficients`, `SKRatio_Quantization_BinDirections`, `SKRatio_Quantization_BinForm`, `SKRatio_Quantization_BinFunctional`, `SKRatio_Quantization_BinGaussian`, `SKRatio_Quantization_BinGeometry`, `SKRatio_Quantization_BinNet`, `SKRatio_Quantization_BinParameters`, `SKRatio_Quantization_BinPartition`, `SKRatio_Quantization_BinProcess`, `SKRatio_Quantization_BinProjected`, `SKRatio_Quantization_BinStability`, `SKRatio_Quantization_BinTail`, `SKRatio_Quantization_BinWeightContinuity`, `SKRatio_Quantization_ConditionalBins`, `SKRatio_Quantization_IntervalBins`, `SKRatio_Quantization_Quantizer`, `SKRatio_Variational_CompactField`, `SKRatio_Variational_FieldFunctional`, `SKRatio_Variational_FieldRadical`, `SKRatio_Variational_FormAlgebra`, `SKRatio_Variational_ScalarKernel`, `SKRatio_Variational_ScalarMoments`.
--
--   **Imports.** It imports the published bundle `Def_SKRatio`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ024S002`, `OAIQ024S003`, `OAIQ024S004`, `OAIQ024S005`, `OAIQ024S006`, `OAIQ024S007`, `OAIQ024S008`, `OAIQ024S009`, `OAIQ024S010`, `OAIQ024S011`, `OAIQ024S012`, `OAIQ024S013`, `OAIQ024S014` and `OAIQ024S015`; the statements `OAI.SKRatio.Certificate.Data.J0K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K2.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J2K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J2K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K7.integral_bound` and `OAI.SKRatio.Planted.residual_norm_rare`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Spin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

section ElementaryGibbs
variable {n : ℕ}

@[simp] theorem coupling_diag (g : Disorder n) (i : Fin n) : coupling g i i = 0 := by
  simp [coupling]

theorem coupling_symm (g : Disorder n) (i j : Fin n) : coupling g i j = coupling g j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [coupling, hij, not_lt_of_gt hij]
  · rfl
  · simp [coupling, hji, not_lt_of_gt hji]

@[simp] theorem flip_same (i : Fin n) (x : Spin n) : flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_other (i j : Fin n) (x : Spin n) (h : j ≠ i) : flip i x j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip (i : Fin n) (x : Spin n) : flip i (flip i x) = x := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [flip_other, h]

@[simp] theorem flip_ne (i : Fin n) (x : Spin n) : flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp at hi

theorem weight_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < weight g h x := Real.exp_pos _

theorem partition_pos (g : Disorder n) (h : Fin n → ℝ) : 0 < partition g h := by
  exact Finset.sum_pos (fun x _ => weight_pos g h x) Finset.univ_nonempty

theorem mass_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < mass g h x := div_pos (weight_pos g h x) (partition_pos g h)

theorem mass_nonneg (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 ≤ mass g h x := (mass_pos g h x).le

@[simp] theorem sum_mass (g : Disorder n) (h : Fin n → ℝ) : ∑ x, mass g h x = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos g h))

end ElementaryGibbs

section HeatBath
variable {n : ℕ}

@[simp] theorem sum_siteKernel (g : Disorder n) (i : Fin n) (x : Spin n) :
    ∑ y, siteKernel g i x y = 1 := by
  have hd : mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    ne_of_gt (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))
  simp only [siteKernel, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, if_true]
  rw [← add_div, div_self hd]

theorem siteKernel_balance (g : Disorder n) (i : Fin n) (x y : Spin n) :
    mass g 0 x * siteKernel g i x y = mass g 0 y * siteKernel g i y x := by
  by_cases hxy : y = x
  · subst y; rfl
  by_cases hflip : y = flip i x
  · subst y
    simp only [siteKernel, flip_ne, Ne.symm (flip_ne i x), ↓reduceIte, flip_flip,
      zero_add]
    rw [add_comm (mass g 0 (flip i x)) (mass g 0 x)]
    ring
  · have hyx : x ≠ y := Ne.symm hxy
    have hflip' : x ≠ flip i y := by
      intro h
      apply hflip
      rw [h, flip_flip]
    simp [siteKernel, hxy, hflip, hyx, hflip']

def updatePath (x y : Spin n) (k : ℕ) : Spin n :=
  fun i => if (i : ℕ) < k then y i else x i

@[simp] theorem updatePath_zero (x y : Spin n) : updatePath x y 0 = x := by
  ext i; simp [updatePath]

@[simp] theorem updatePath_end (x y : Spin n) : updatePath x y n = y := by
  ext i; simp [updatePath]

end HeatBath

end SKRatio
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Interaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
abbrev Interaction (n : ℕ) := Fin n → Fin n → ℝ

def spin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ := if x i then 1 else -1

def replace {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) : Spin n :=
  Function.update x i b

noncomputable def halfDiff {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : ℝ := (f (replace x i true) - f (replace x i false)) / 2

noncomputable def field {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  ∑ j, J i j * spin x j

noncomputable def mean {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  Real.tanh (field J x i)

noncomputable def generator {n : ℕ} (J : Interaction n) (f : Spin n → ℝ)
    (x : Spin n) : ℝ := ∑ j, (mean J x j - spin x j) * halfDiff j f x

noncomputable def gradientGenerator {n : ℕ} (J : Interaction n)
    (p : Spin n → Fin n → ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  generator J (fun y => p y i) x - p x i -
    2 * spin x i * ∑ j, halfDiff i (fun y => mean J y j) x *
      halfDiff j (fun y => p y i) x +
    ∑ j, halfDiff i (fun y => mean J y j) x * p x j

@[simp] theorem replace_same {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) :
    replace x i b i = b := by
  simp [replace]

@[simp] theorem replace_replace {n : ℕ} (x : Spin n) (i : Fin n) (a b : Bool) :
    replace (replace x i a) i b = replace x i b := by
  simp [replace, Function.update_idem]

@[simp] theorem replace_self {n : ℕ} (x : Spin n) (i : Fin n) :
    replace x i (x i) = x := by
  simp [replace]

@[simp] theorem halfDiff_replace {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) (b : Bool) : halfDiff i f (replace x i b) = halfDiff i f x := by
  simp [halfDiff]

@[simp] theorem halfDiff_self {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : halfDiff i (halfDiff i f) x = 0 := by
  simp [halfDiff]

@[simp] theorem halfDiff_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Spin n) :
    halfDiff i (fun _ => c) x = 0 := by
  simp [halfDiff]

@[simp] theorem halfDiff_spin {n : ℕ} (i j : Fin n) (x : Spin n) :
    halfDiff i (fun y => spin y j) x = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    norm_num [halfDiff, spin]
  · simp [halfDiff, spin, replace, Function.update_of_ne (Ne.symm h), h]

abbrev Observables (n : ℕ) := Spin n → ℝ
abbrev VectorFields (n : ℕ) := Spin n → Fin n → ℝ

noncomputable def gradientLM (n : ℕ) : Observables n →ₗ[ℝ] VectorFields n where
  toFun f x i := halfDiff i f x
  map_add' f g := by
    funext x i
    simp only [halfDiff, Pi.add_apply]
    ring
  map_smul' a f := by
    funext x i
    simp only [halfDiff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

noncomputable def generatorLM {n : ℕ} (J : Interaction n) :
    Observables n →ₗ[ℝ] Observables n where
  toFun := generator J
  map_add' f g := by
    funext x
    simp only [generator]
    change (∑ j, (mean J x j - spin x j) *
      (gradientLM n (f + g) x j)) = _
    simp [map_add, gradientLM, generator, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    simp only [generator]
    change (∑ j, (mean J x j - spin x j) *
      (gradientLM n (a • f) x j)) = _
    simp [map_smul, gradientLM, generator, mul_left_comm, Finset.mul_sum]

noncomputable def generatorCLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n := (generatorLM J).toContinuousLinearMap

noncomputable def semigroup {n : ℕ} (J : Interaction n) (t : ℝ) :
    Observables n →L[ℝ] Observables n := NormedSpace.exp (t • generatorCLM J)

@[simp] lemma spin_sq {n : ℕ} (x : Spin n) (i : Fin n) : spin x i ^ 2 = 1 := by
  cases h : x i <;> simp [spin, h]

@[simp] lemma semigroup_zero {n : ℕ} (J : Interaction n) : semigroup J 0 = 1 := by
  simp [semigroup]

noncomputable def jumpEnergy {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) : ℝ :=
  2 * ∑ i, (1 - mean J x i * spin x i) * (halfDiff i f x) ^ 2

lemma spin_flip_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (flip i x) i = -spin x i := by
  cases h : x i <;> simp [SKRatio.flip, spin, h]

lemma spin_flip {n : ℕ} (x : Spin n) (i j : Fin n) :
    spin (flip i x) j = spin x j - if j = i then 2 * spin x i else 0 := by
  by_cases h : j = i
  · subst j; rw [spin_flip_self]; simp; ring
  · simp [flip, spin, h]

lemma hamiltonian_flip {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    hamiltonian g 0 (flip i x) = hamiltonian g 0 x -
      2 * spin x i * field (coupling g) x i := by
  have hr : ∑ j, spin x j * coupling g j i = field (coupling g) x i := by
    simp only [field, coupling_symm, mul_comm]
  have he (y : Spin n) : hamiltonian g 0 y =
      (∑ j, ∑ k, spin y j * coupling g j k * spin y k) / 2 := by
    simp only [hamiltonian, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [spinValue, spin]
    ring
  rw [he, he]
  simp only [spin_flip, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, coupling_diag]
  simp only [← Finset.sum_mul, hr]
  simp only [mul_assoc, ← Finset.mul_sum, field]
  ring

lemma mass_flip {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    mass g 0 (flip i x) = mass g 0 x * Real.exp (-2 * spin x i * field (coupling g) x i) := by
  unfold mass weight
  rw [hamiltonian_flip, Real.exp_sub, neg_mul, neg_mul, Real.exp_neg]
  ring

lemma exp_two_mul_one_sub_tanh (a : ℝ) :
    Real.exp (2 * a) * (1 - Real.tanh a) = 1 + Real.tanh a := by
  rw [Real.tanh_eq, show 2 * a = a + a by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos a
  field_simp
  nlinarith

lemma exp_neg_two_mul_one_add_tanh (a : ℝ) :
    Real.exp (-2 * a) * (1 + Real.tanh a) = 1 - Real.tanh a := by
  simpa only [mul_neg, neg_mul, Real.tanh_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using
    exp_two_mul_one_sub_tanh (-a)

def flipRate {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  (1 - spin x i * mean J x i) / 2

lemma mass_flip_ratio {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) =
      flipRate (coupling g) x i := by
  have hx := mass_pos g 0 x
  rw [mass_flip]
  have he := Real.exp_pos (-2 * spin x i * field (coupling g) x i)
  have hden : mass g 0 x + mass g 0 x * Real.exp (-2 * spin x i * field (coupling g) x i) ≠ 0 := by
    positivity
  apply (div_eq_iff hden).mpr
  cases hi : x i
  · have h := exp_two_mul_one_sub_tanh (field (coupling g) x i)
    simp only [flipRate, mean, spin, hi, Bool.false_eq_true, ↓reduceIte, mul_neg,
      mul_one, sub_neg_eq_add, neg_mul, neg_neg]
    linear_combination (mass g 0 x / 2) * h
  · have h := exp_neg_two_mul_one_add_tanh (field (coupling g) x i)
    simp only [flipRate, mean, spin, hi, ↓reduceIte, mul_one, one_mul]
    linear_combination (mass g 0 x / 2) * h

lemma siteKernel_apply {n : ℕ} (g : Disorder n) (i : Fin n) (f : Observables n) (x : Spin n) :
    ∑ y, siteKernel g i x y * f y =
      f x + flipRate (coupling g) x i * (f (flip i x) - f x) := by
  have hd : mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x))).ne'
  have hs : mass g 0 x / (mass g 0 x + mass g 0 (flip i x)) +
      mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) = 1 := by
    rw [← add_div, div_self hd]
  simp only [siteKernel, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [← mass_flip_ratio]
  linear_combination f x * hs

lemma generator_flip {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J f x = ∑ i, flipRate J x i * (f (flip i x) - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flipRate, flip, Bool.not_false,
      halfDiff]
    rw [hx]
    simp only [replace]
    ring
  · simp only [spin, hi, ↓reduceIte, flipRate, flip, Bool.not_true, halfDiff]
    rw [hx]
    simp only [replace]
    ring

theorem generator_eq_transition {n : ℕ} (g : Disorder n) (f : Observables n) (x : Spin n) :
    generator (coupling g) f x = (n : ℝ) * ((∑ y, transition g x y * f y) - f x) := by
  by_cases hn : n = 0
  · subst n; simp [generator]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hP : transition g = fun x y => (∑ i, siteKernel g i x y) / (n : ℝ) := by
    simp only [transition, hn, ↓reduceIte]
    rfl
  rw [hP]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_sub, mul_div_cancel₀ _ hn']
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [siteKernel_apply]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [generator_flip]
  ring

def unweightedGradient {n : ℕ} (f : Observables n) (x : Spin n) : ℝ :=
  ∑ i, (halfDiff i f x) ^ 2

def gradientWeight {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  1 - spin x i * mean J x i

def weightedGradient {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) : ℝ :=
  ∑ i, gradientWeight J x i * (halfDiff i f x)^2

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

def plusSpin (n : ℕ) : Spin n := fun _ => true

open Real Set

def scalarVariance (h : ℝ) : ℝ := 1 - Real.tanh h ^ 2

def q (z m : ℝ) : ℝ := Real.tanh (2*z) / (2*(1-m*Real.tanh (2*z)))

def conditionalVariance {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  1 - mean J x i ^ 2

@[simp] lemma mean_weight_plus {n : ℕ} (J : Interaction n) (i : Fin n) :
    gradientWeight J (plusSpin n) i = 1 - mean J (plusSpin n) i := by
  simp [gradientWeight, spin, plusSpin]

def pairSum {n : ℕ} (F : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_RowControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

def rowControl {n : ℕ} (J : Interaction n) (k : ℕ) : ℝ :=
  (Finset.univ.sup (fun i => ∑ j, ‖J i j‖₊ ^ k) : NNReal)

abbrev R2 {n : ℕ} (J : Interaction n) : ℝ := rowControl J 2
abbrev R3 {n : ℕ} (J : Interaction n) : ℝ := rowControl J 3

def gradientForm {n : ℕ} (J : Interaction n) (p : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
    J i j * p i * conditionalVariance J (plusSpin n) j * p j) +
  2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
    J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
  pairSum (fun i j =>
    J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
      conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j))

def signProduct {n : ℕ} (x y : Spin n) : Spin n :=
  fun i => if x i then y i else !(y i)

@[simp] lemma signProduct_plus {n : ℕ} (x : Spin n) : signProduct x (plusSpin n) = x := by
  funext i
  cases hi : x i <;> simp [signProduct, plusSpin, hi]

@[simp] lemma plus_signProduct {n : ℕ} (x : Spin n) : signProduct (plusSpin n) x = x := by
  funext i
  simp [signProduct, plusSpin]

@[simp] lemma abs_spin {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hx : x i <;> simp [spin, hx]

def signConjugate {n : ℕ} (x : Spin n) (J : Interaction n) : Interaction n :=
  fun i j => spin x i * J i j * spin x j

def signPullback {n : ℕ} (x : Spin n) (f : Observables n) : Observables n :=
  fun y => f (signProduct x y)

@[simp] lemma abs_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    |signConjugate x J i j| = |J i j| := by
  simp [signConjugate, abs_mul]

def euclideanOpNorm {n : ℕ} (J : Interaction n) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J‖

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Mean
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.spin_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

def mean (p : α → ℝ) (f : α → ℝ) : ℝ := ∑ x, p x * f x

end FiniteLaw
namespace Independent
variable {n : ℕ}

@[simp] theorem spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] theorem spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

@[simp] theorem coupling_zero (i j : Fin n) : coupling (0 : Disorder n) i j = 0 := by
  simp [coupling]

@[simp] theorem mass_zero (x : Spin n) : mass (0 : Disorder n) 0 x = 1 / (2 : ℝ) ^ n := by
  simp [mass, weight, hamiltonian, partition, Spin]

@[simp] theorem siteKernel_zero (i : Fin n) (x y : Spin n) :
    siteKernel (0 : Disorder n) i x y =
      (if y = x then 1 / 2 else 0) + (if y = flip i x then 1 / 2 else 0) := by
  have h : (1 / (2 : ℝ) ^ n) / (1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ n) = 1 / 2 := by
    field_simp
    norm_num
  simp only [siteKernel, mass_zero, h]

end Independent
end SKRatio
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SignedVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

def signedVector {n : ℕ} (x : Spin n) (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => spin x i * p.ofLp i)

@[simp] lemma norm_signedVector {n : ℕ} (x : Spin n) (p : EuclideanSpace ℝ (Fin n)) :
    ‖signedVector x p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, signedVector, mul_pow, spin_sq, one_mul]

@[simp] lemma signConjugate_twice {n : ℕ} (J : Interaction n) (x : Spin n) :
    signConjugate x (signConjugate x J) = J := by
  funext i j
  simp only [signConjugate]
  calc
    _ = (spin x i)^2 * (spin x j)^2 * J i j := by ring
    _ = J i j := by simp only [spin_sq, one_mul]

noncomputable def attemptLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n :=
  1 + (n : ℝ)⁻¹ • generatorCLM J

noncomputable def continuousKernel {n : ℕ} (J : Interaction n) (t : ℝ) :
    Matrix (Spin n) (Spin n) ℝ := fun x y =>
      semigroup J t (fun z => if z = y then 1 else 0) x

noncomputable def siteRefresh {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (x : Spin n) : ℝ :=
  ((1 + mean J x i) / 2) * f (replace x i true) +
  ((1 - mean J x i) / 2) * f (replace x i false)

@[simp] theorem generator_const {n : ℕ} (J : Interaction n) (a : ℝ) (x : Spin n) :
    generator J (fun _ => a) x = 0 := by
  simp [generator]

@[simp] theorem siteRefresh_const {n : ℕ} (J : Interaction n) (i : Fin n)
    (a : ℝ) (x : Spin n) : siteRefresh J i (fun _ => a) x = a := by
  unfold siteRefresh
  ring

@[simp] theorem attempt_const {n : ℕ} (J : Interaction n) (a : ℝ) :
    attemptLM J (fun _ => a) = fun _ => a := by
  funext x
  change a + (n : ℝ)⁻¹ * generator J (fun _ => a) x = a
  simp

@[simp] theorem attempt_pow_const {n : ℕ} (J : Interaction n) (k : ℕ) (a : ℝ) :
    (attemptLM J ^ k) (fun _ => a) = fun _ => a := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ', mul_apply_eq_comp, ih, attempt_const]

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_GibbsMeanCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

def gibbsMeanCLM {n : ℕ} (g : Disorder n) : Observables n →L[ℝ] ℝ :=
  (∑ x : Spin n, mass g 0 x • ContinuousLinearMap.proj x)

@[simp] lemma gibbsMeanCLM_apply {n : ℕ} (g : Disorder n) (f : Observables n) :
    gibbsMeanCLM g f = FiniteLaw.mean (mass g 0) f := by
  simp [gibbsMeanCLM, FiniteLaw.mean]

def continuousDistance {n : ℕ} (g : Disorder n) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : Spin n => totalVariation (continuousKernel (coupling g) t x) (mass g 0))

def backwardEnergy {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) : ℝ :=
  semigroup J u (weightedGradient J (semigroup J (T-u) f)) x

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

def stationaryEnergy {n : ℕ} (g : Disorder n) (f : Observables n) : ℝ :=
  FiniteLaw.mean (mass g 0) (weightedGradient (coupling g) f)

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

noncomputable def expDrift {n : ℕ} (J : Interaction n) (θ : ℝ)
    (f : Observables n) (x : Spin n) : ℝ :=
  generator J (fun y => Real.exp (θ * f y)) x -
    θ * Real.exp (θ * f x) * generator J f x

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_PositiveLag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def dimensionDecay (a : ℝ) (n : ℕ) : ℝ := Real.exp (-a * Real.log n)

def logarithmicVarianceBound (κ A d₀ D α : ℝ) (n : ℕ) : ℝ :=
  (4*D*Real.exp (A*d₀)/α) * dimensionDecay (κ*α/4) n +
    (4*A*D^2*Real.exp (A*d₀)) * ((Real.log n)^2 * dimensionDecay 3 n) +
    (4*D*Real.exp (A*d₀)) * (Real.log n * dimensionDecay 3 n)

def logarithmicSmoothingBound (κ A d₀ D α γ ε : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (logarithmicVarianceBound κ A d₀ D α n) +
    dimensionDecay (γ*α) n) / (2*Real.sqrt ε)

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_FieldTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def reversal {n : ℕ} (x : Spin n) : Spin n := fun i => !(x i)

@[simp] lemma reversal_reversal {n : ℕ} (x : Spin n) : reversal (reversal x) = x := by
  funext i
  simp [reversal]

@[simp] lemma spin_reversal {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (reversal x) i = -spin x i := by
  cases h : x i <;> simp [spin, reversal, h]

@[simp] lemma mass_reversal {n : ℕ} (g : Disorder n) (x : Spin n) :
    mass g 0 (reversal x) = mass g 0 x := by
  have hv (i : Fin n) : spinValue (reversal x i) = -spinValue (x i) :=
    spin_reversal x i
  simp [mass, weight, hamiltonian, hv]

@[simp] lemma field_reversal {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    field J (reversal x) i = -field J x i := by
  simp [field, spin_reversal, Finset.sum_neg_distrib]

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_DiscreteDistanceNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio

section Measurability
variable {n : ℕ}

@[fun_prop] theorem continuous_coupling (i j : Fin n) :
    Continuous (fun g : Disorder n => coupling g i j) := by
  unfold coupling
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_hamiltonian (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => hamiltonian g h x) := by
  unfold hamiltonian
  fun_prop

@[fun_prop] theorem continuous_weight (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => weight g h x) := by
  unfold weight
  fun_prop

@[fun_prop] theorem continuous_partition (h : Fin n → ℝ) :
    Continuous (fun g : Disorder n => partition g h) := by
  unfold partition
  fun_prop

@[fun_prop] theorem continuous_mass (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => mass g h x) := by
  exact (continuous_weight h x).div (continuous_partition h)
    (fun g => (partition_pos g h).ne')

@[fun_prop] theorem continuous_siteKernel (i : Fin n) (x y : Spin n) :
    Continuous (fun g : Disorder n => siteKernel g i x y) := by
  have hd : ∀ g : Disorder n, mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    fun g => (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x))).ne'
  have hx := (continuous_mass 0 x).div
    ((continuous_mass 0 x).add (continuous_mass 0 (flip i x))) hd
  have hf := (continuous_mass 0 (flip i x)).div
    ((continuous_mass 0 x).add (continuous_mass 0 (flip i x))) hd
  unfold siteKernel
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_transition (x y : Spin n) :
    Continuous (fun g : Disorder n => transition g x y) := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte]
    fun_prop
  · simp only [transition, hn, ↓reduceIte]
    fun_prop

@[fun_prop] theorem continuous_transition_pow (k : ℕ) (x y : Spin n) :
    Continuous (fun g : Disorder n => (transition g ^ k) x y) := by
  induction k generalizing x y with
  | zero => simp only [pow_zero]; fun_prop
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    fun_prop

@[fun_prop] theorem continuous_discreteDistance (k : ℕ) :
    Continuous (fun g : Disorder n => discreteDistance g k) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun (x : Spin n) (g : Disorder n) =>
        totalVariation ((transition g ^ k) x) (mass g 0))) := by
    apply Continuous.finset_sup'
    intro x _
    unfold totalVariation
    fun_prop
  exact h.congr (fun g => Finset.sup'_apply _ _ g)

end Measurability

end SKRatio

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Median
attribute [-simp] _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

@[simp] lemma continuousKernel_zero {n : ℕ} (J : Interaction n) :
    continuousKernel J 0 = (1 : Matrix (Spin n) (Spin n) ℝ) := by
  funext x y
  simp [continuousKernel, Matrix.one_apply]

@[simp] lemma continuousDistance_zero {n : ℕ} (g : Disorder n) :
    continuousDistance g 0 = discreteDistance g 0 := by
  simp [continuousDistance, discreteDistance]

def medianTime {n : ℕ} (g : Disorder n) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ continuousDistance g t ≤ 1/2}

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SpectralLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter

namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma transition_balance {n : ℕ} (g : Disorder n) (x y : Spin n) :
    mass g 0 x * transition g x y = mass g 0 y * transition g y x := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte, Matrix.one_apply]
    by_cases h : x = y
    · subst y
      simp
    · simp [h, Ne.symm h]
  · simp only [transition, hn, ↓reduceIte, mul_div, Finset.mul_sum]
    simp_rw [siteKernel_balance g _ x y]

def stationaryInner {n : ℕ} (g : Disorder n) (f h : Observables n) : ℝ :=
  FiniteLaw.mean (mass g 0) (fun x => f x*h x)

def stationaryPairingCLM {n : ℕ} (g : Disorder n) (f : Observables n) :
    Observables n →L[ℝ] ℝ :=
  (show Observables n →ₗ[ℝ] ℝ from
    { toFun := stationaryInner g f
      map_add' a b := by
        simp [stationaryInner, FiniteLaw.mean, mul_add, Finset.sum_add_distrib]
      map_smul' c a := by
        simp [stationaryInner, FiniteLaw.mean, mul_left_comm, ← Finset.mul_sum]
    }).toContinuousLinearMap

@[simp] lemma stationaryPairingCLM_apply {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryPairingCLM g f h = stationaryInner g f h := rfl

lemma generator_symmetric {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryInner g f (generator (coupling g) h) =
      stationaryInner g (generator (coupling g) f) h := by
  have hpair : (∑ x, ∑ y, mass g 0 x * transition g x y * f x * h y) =
      ∑ y, ∑ x, mass g 0 y * transition g y x * f x * h y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [transition_balance]
  unfold stationaryInner FiniteLaw.mean
  simp only [generator_eq_transition, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  have he (x : Spin n) (y : Spin n) :
      mass g 0 x * (f x * ((n:ℝ)*(transition g x y*h y))) =
        (n:ℝ)*(mass g 0 x*transition g x y*f x*h y) := by ring
  have he' (y : Spin n) (x : Spin n) :
      mass g 0 y * (((n:ℝ)*(transition g y x*f x))*h y) =
        (n:ℝ)*(mass g 0 y*transition g y x*f x*h y) := by ring
  simp_rw [he,he',← Finset.mul_sum,hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

def gibbsEuclideanEquiv {n : ℕ} (g : Disorder n) :
    Observables n ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (mass g 0 x)*f x)
  invFun u x := u x/Real.sqrt (mass g 0 x)
  left_inv f := by
    funext x
    exact mul_div_cancel_left₀ (f x) (ne_of_gt (Real.sqrt_pos.2 (mass_pos g 0 x)))
  right_inv u := by
    ext x
    exact mul_div_cancel₀ (u x) (ne_of_gt (Real.sqrt_pos.2 (mass_pos g 0 x)))
  map_add' f h := by ext x; simp [mul_add]
  map_smul' a f := by ext x; simp [mul_left_comm]

@[simp] lemma gibbsEuclideanEquiv_apply {n : ℕ} (g : Disorder n) (f : Observables n) (x : Spin n) :
    gibbsEuclideanEquiv g f x = Real.sqrt (mass g 0 x)*f x := rfl

lemma gibbsEuclideanEquiv_inner {n : ℕ} (g : Disorder n) (f h : Observables n) :
    inner (𝕜 := ℝ) (gibbsEuclideanEquiv g f) (gibbsEuclideanEquiv g h) = stationaryInner g f h := by
  rw [PiLp.inner_apply]
  unfold stationaryInner FiniteLaw.mean
  apply Finset.sum_congr rfl
  intro x _
  simp only [gibbsEuclideanEquiv_apply,RCLike.inner_apply,conj_trivial]
  nlinarith only [congrArg (fun a : ℝ => a*f x*h x) (Real.sq_sqrt (mass_nonneg g 0 x))]

def negativeGeneratorEuclidean {n : ℕ} (g : Disorder n) :
    EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
  (gibbsEuclideanEquiv g).toLinearMap.comp
    ((-generatorLM (coupling g)).comp (gibbsEuclideanEquiv g).symm.toLinearMap)

lemma negativeGeneratorEuclidean_lift {n : ℕ} (g : Disorder n) (f : Observables n) :
    negativeGeneratorEuclidean g (gibbsEuclideanEquiv g f) =
      gibbsEuclideanEquiv g (-generator (coupling g) f) := by
  simp [negativeGeneratorEuclidean,generatorLM]

lemma negativeGeneratorEuclidean_symmetric {n : ℕ} (g : Disorder n) :
    (negativeGeneratorEuclidean g).IsSymmetric := by
  intro u v
  obtain ⟨f,rfl⟩ := (gibbsEuclideanEquiv g).surjective u
  obtain ⟨h,rfl⟩ := (gibbsEuclideanEquiv g).surjective v
  rw [negativeGeneratorEuclidean_lift,negativeGeneratorEuclidean_lift,
    gibbsEuclideanEquiv_inner,gibbsEuclideanEquiv_inner]
  have he := generator_symmetric g f h
  simp only [stationaryInner,FiniteLaw.mean] at he ⊢
  simpa only [Pi.neg_apply,neg_mul,mul_neg,Finset.sum_neg_distrib] using congrArg Neg.neg he.symm

def spinEigenvalues {n : ℕ} (g : Disorder n) : Fin (Fintype.card (Spin n)) → ℝ :=
  (negativeGeneratorEuclidean_symmetric g).eigenvalues finrank_euclideanSpace

def spinEigenbasis {n : ℕ} (g : Disorder n) :
    OrthonormalBasis (Fin (Fintype.card (Spin n))) ℝ (EuclideanSpace ℝ (Spin n)) :=
  (negativeGeneratorEuclidean_symmetric g).eigenvectorBasis finrank_euclideanSpace

def spectralCoefficient {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) : ℝ :=
  (spinEigenbasis g).repr (gibbsEuclideanEquiv g f) a

def scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) : Observables n :=
  (gibbsEuclideanEquiv g).symm (spinEigenbasis g a)

@[simp] lemma lift_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) :
    gibbsEuclideanEquiv g (scalarEigenfunction g a) = spinEigenbasis g a :=
  (gibbsEuclideanEquiv g).apply_symm_apply _

def linearObservable {n : ℕ} (a : Fin n → ℝ) : Observables n := fun x => ∑ i, a i * spin x i

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def m (h : ℝ) : ℝ := tanh h
def v (h : ℝ) : ℝ := 1 - m h ^ 2
def w (h : ℝ) : ℝ := 1 - m h
def kernel (h t : ℝ) : ℝ := v h * v t / (w h + w t)
def g (h : ℝ) : ℝ := v h / (w h + 3/4)
def rho (h : ℝ) : ℝ := (1+m h)*v h/2 - (3/2)*g h^2

lemma m_bounds (h : ℝ) : -1 < m h ∧ m h < 1 :=
  ⟨neg_one_lt_tanh h, tanh_lt_one h⟩
lemma w_pos (h : ℝ) : 0 < w h := sub_pos.mpr (m_bounds h).2
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def multiplier (h : ℝ) : ℝ := 45/100 + (1/4)*m h^2 - (6/100)*m h

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_FixedExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate.Fixed

def S : ℤ := 1000000000000000000000000
structure I where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def round (a b : ℚ) : I := ⟨⌊a*(S:ℚ)⌋,⌈b*(S:ℚ)⌉⟩
def sq (A : I) : I := ⟨(max 0 A.lo)^2/S,(A.hi^2+S)/S⟩
def iter : ℕ → I → I
  | 0,A => A
  | n+1,A => iter n (sq A)
def expBounds (a b : ℚ) : I :=
  iter 30 (round (1+a/1073741824) (1/(1-b/1073741824)))

end SKRatio.Certificate.Fixed

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

@[reducible] def scale : ℚ := 10000000000000000000000

def down (q : ℚ) : ℚ := (⌊q*scale⌋ : ℚ)/scale
def up (q : ℚ) : ℚ := (⌈q*scale⌉ : ℚ)/scale

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace Box

def Mem (A : Box) (x : ℝ) : Prop := (A.lo:ℝ) ≤ x ∧ x ≤ A.hi
instance instMembershipReal : Membership ℝ Box := ⟨fun A x => A.Mem x⟩

def rat (q : ℚ) : Box := ⟨q,q⟩
def round (a b : ℚ) : Box := ⟨down a,up b⟩
def add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : Box) : Box := ⟨-A.hi,-A.lo⟩
def sub (A B : Box) : Box := add A (neg B)
def mul (A B : Box) : Box := round
  (min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi)))
  (max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi)))
def inv (A : Box) : Option Box := if 0 < A.lo then some (round (1/A.hi) (1/A.lo)) else none

def sq (A : Box) : Box := round
  (if 0 ≤ A.lo then A.lo^2 else if A.hi ≤ 0 then A.hi^2 else 0)
  (max (A.lo^2) (A.hi^2))

def exp (A : Box) : Option Box :=
  if A.hi < 1073741824 then
    let B := Fixed.expBounds A.lo A.hi
    some ⟨(B.lo:ℚ)/(Fixed.S:ℚ),(B.hi:ℚ)/(Fixed.S:ℚ)⟩
  else none

end Box
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

structure Jet where
  val : Box
  der : Box
  sec : Box
  deriving DecidableEq, Repr

namespace Jet
open Box

def neg (A : Jet) : Jet := ⟨Box.neg A.val,Box.neg A.der,Box.neg A.sec⟩
end Jet

inductive Expr where
  | rat : ℚ → Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | sq : Expr → Expr
  | inv : Expr → Expr
  | exp : Expr → Expr
  | tanh : Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

def val (e : Expr) (x : ℝ) : ℝ := match e with
  | rat q => q
  | var => x
  | add a b => a.val x+b.val x
  | neg a => -a.val x
  | mul a b => a.val x*b.val x
  | sq a => (a.val x)^2
  | inv a => (a.val x)⁻¹
  | exp a => Real.exp (a.val x)
  | tanh a => Real.tanh (a.val x)

def Regular (e : Expr) (x : ℝ) : Prop := match e with
  | rat _ | var => True
  | add a b | mul a b => a.Regular x ∧ b.Regular x
  | neg a | sq a | exp a | tanh a => a.Regular x
  | inv a => a.Regular x ∧ a.val x ≠ 0

end Expr
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Expr
instance instAdd : Add Expr := ⟨Expr.add⟩
instance instSub : Sub Expr := ⟨fun a b => Expr.add a (Expr.neg b)⟩
instance instMul : Mul Expr := ⟨Expr.mul⟩
instance instDiv : Div Expr := ⟨fun a b => Expr.mul a (Expr.inv b)⟩
instance instOfNat (n : ℕ) : OfNat Expr n := ⟨Expr.rat n⟩
@[simp] lemma val_add (a b : Expr) (x : ℝ) : (a+b).val x = a.val x+b.val x := rfl
@[simp] lemma val_sub (a b : Expr) (x : ℝ) : (a-b).val x = a.val x-b.val x := rfl
@[simp] lemma val_mul (a b : Expr) (x : ℝ) : (a*b).val x = a.val x*b.val x := rfl
@[simp] lemma val_div (a b : Expr) (x : ℝ) : (a/b).val x = a.val x/b.val x := rfl
@[simp] lemma val_ofNat (n : ℕ) (x : ℝ) : (ofNat(n) : Expr).val x = n := by
  change ((n:ℚ):ℝ) = n
  norm_cast
end Expr

def approxF (β A C h : ℝ) : ℝ := (v h+A)*h+2*β^2*(m h*v h)+
  (1/2-β^2*A/(64/100-(19/100)*A))*v h+(12/100)*m h+3*β^2*C*g h

def scalarFunction (β A C M Q : ℝ) (k : ℕ) (h : ℝ) : ℝ := match k with
  | 0 => v h
  | 1 => g h
  | 2 => m h*v h
  | 3 => rho h
  | 4 => (v h-A)^2
  | 5 => (g h-C)^2
  | 6 => (m h*v h-M)^2
  | 7 => (approxF β A C h-Q)^2
  | 8 => (1+v h)^2/multiplier h/16
  | 9 => v h^2/multiplier h/16
  | 10 => v h^2/(2-m h)/4
  | 11 => v h^2/(2-m h)^2/4
  | _ => v h*(1+m h)/4

def scalarExpr (β A C M Q : ℚ) (k : ℕ) (h : Expr) : Expr :=
  let m := Expr.tanh h
  let v := 1-Expr.sq m
  let g := v/(Expr.rat (7/4)-m)
  let L := Expr.rat (45/100)+Expr.rat (1/4)*Expr.sq m-Expr.rat (6/100)*m
  let F := (v+Expr.rat A)*h+Expr.rat (2*β^2)*(m*v)+
    Expr.rat (1/2-β^2*A/(64/100-(19/100)*A))*v+
      Expr.rat (12/100)*m+Expr.rat (3*β^2*C)*g
  match k with
  | 0 => v
  | 1 => g
  | 2 => m*v
  | 3 => Expr.rat (1/2)*((1+m)*v)-Expr.rat (3/2)*Expr.sq g
  | 4 => Expr.sq (v-Expr.rat A)
  | 5 => Expr.sq (g-Expr.rat C)
  | 6 => Expr.sq (m*v-Expr.rat M)
  | 7 => Expr.sq (F-Expr.rat Q)
  | 8 => Expr.rat (1/16)*(Expr.sq (1+v)/L)
  | 9 => Expr.rat (1/16)*(Expr.sq v/L)
  | 10 => Expr.rat (1/4)*(Expr.sq v/(2-m))
  | 11 => Expr.rat (1/4)*(Expr.sq v/Expr.sq (2-m))
  | _ => Expr.rat (1/4)*(v*(1+m))

def integrandExpr (β A C M Q : ℚ) (k : ℕ) : Expr :=
  (scalarExpr β A C M Q k (Expr.rat (β^2)+Expr.rat β*Expr.var))*
    (Expr.exp (Expr.rat (-1/2)*Expr.sq Expr.var))

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Box

def posInv (A : Box) : Box := round (1/A.hi) (1/A.lo)
def divPos (A B : Box) : Box := mul A (posInv B)
end Box

structure Enclosures where
  av : Box
  gv : Box
  mv : Box
  rv : Box
  vs : Box
  gs : Box
  ms : Box
  fs : Box

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

namespace Box

def absUpper (A : Box) : ℚ := max |A.lo| |A.hi|
def widen (A : Box) (r : ℚ) : Box := ⟨A.lo-r,A.hi+r⟩

def contains (A B : Box) : Bool := decide (A.lo ≤ B.lo ∧ B.hi ≤ A.hi)

end Box

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K0

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 0
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨1/1000000,1/500000⟩
  | 11 => ⟨1/62500,19/1000000⟩
  | 12 => ⟨81/500000,169/1000000⟩
  | 13 => ⟨297/250000,61/50000⟩
  | 14 => ⟨3309/500000,6739/1000000⟩
  | 15 => ⟨13957/500000,7057/250000⟩
  | 16 => ⟨88509/1000000,89029/1000000⟩
  | 17 => ⟨209517/1000000,26239/125000⟩
  | 18 => ⟨367737/1000000,23009/62500⟩
  | 19 => ⟨477123/1000000,478093/1000000⟩
  | 20 => ⟨457861/1000000,57341/125000⟩
  | 21 => ⟨325663/1000000,325973/1000000⟩
  | 22 => ⟨34441/200000,34543/200000⟩
  | 23 => ⟨68157/1000000,17169/250000⟩
  | 24 => ⟨4069/200000,5159/250000⟩
  | 25 => ⟨4611/1000000,4721/1000000⟩
  | 26 => ⟨399/500000,207/250000⟩
  | 27 => ⟨21/200000,113/1000000⟩
  | 28 => ⟨1/100000,3/250000⟩
  | 29 => ⟨0,1/500000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J0K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K1

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 1
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨3/500000,1/125000⟩
  | 12 => ⟨63/1000000,33/500000⟩
  | 13 => ⟨237/500000,61/125000⟩
  | 14 => ⟨2731/1000000,557/200000⟩
  | 15 => ⟨12041/1000000,381/31250⟩
  | 16 => ⟨20197/500000,40677/1000000⟩
  | 17 => ⟨102507/1000000,102801/1000000⟩
  | 18 => ⟨48883/250000,195703/1000000⟩
  | 19 => ⟨69689/250000,279267/1000000⟩
  | 20 => ⟨74083/250000,296971/1000000⟩
  | 21 => ⟨117189/500000,117363/500000⟩
  | 22 => ⟨137699/1000000,34501/250000⟩
  | 23 => ⟨15027/250000,30263/500000⟩
  | 24 => ⟨9789/500000,19853/1000000⟩
  | 25 => ⟨4779/1000000,153/31250⟩
  | 26 => ⟨439/500000,457/500000⟩
  | 27 => ⟨61/500000,13/100000⟩
  | 28 => ⟨3/250000,3/200000⟩
  | 29 => ⟨0,1/500000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J0K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K2

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 2
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/500000,-1/1000000⟩
  | 11 => ⟨-1/62500,-7/500000⟩
  | 12 => ⟨-139/1000000,-133/1000000⟩
  | 13 => ⟨-921/1000000,-449/500000⟩
  | 14 => ⟨-4521/1000000,-4453/1000000⟩
  | 15 => ⟨-999/62500,-7931/500000⟩
  | 16 => ⟨-39167/1000000,-7813/200000⟩
  | 17 => ⟨-61811/1000000,-30749/500000⟩
  | 18 => ⟨-4891/100000,-48441/1000000⟩
  | 19 => ⟨8697/500000,17603/1000000⟩
  | 20 => ⟨2907/31250,93501/1000000⟩
  | 21 => ⟨23371/200000,23473/200000⟩
  | 22 => ⟨4287/50000,85947/1000000⟩
  | 23 => ⟨20971/500000,42191/1000000⟩
  | 24 => ⟨3613/250000,14649/1000000⟩
  | 25 => ⟨3619/1000000,3707/1000000⟩
  | 26 => ⟨671/1000000,349/500000⟩
  | 27 => ⟨93/1000000,1/10000⟩
  | 28 => ⟨9/1000000,11/1000000⟩
  | 29 => ⟨0,1/500000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J0K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K3

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 3

end SKRatio.Certificate.Data.J0K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K4

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 4

end SKRatio.Certificate.Data.J0K4

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K5

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 5

end SKRatio.Certificate.Data.J0K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K6

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 6

end SKRatio.Certificate.Data.J0K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K7

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 7

end SKRatio.Certificate.Data.J0K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K0

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 0

end SKRatio.Certificate.Data.J1K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K1

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 1

end SKRatio.Certificate.Data.J1K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K2

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 2

end SKRatio.Certificate.Data.J1K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K3

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 3

end SKRatio.Certificate.Data.J1K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K4

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 4

end SKRatio.Certificate.Data.J1K4

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K6

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 6

end SKRatio.Certificate.Data.J1K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_ClockBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter ProbabilityTheory
namespace SKRatio.Calculus

def attemptKernel {n : ℕ} (J : Interaction n) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => attemptLM J (fun z => if z = y then 1 else 0) x

noncomputable def residualAttempt {n : ℕ} (J : Interaction n) (q : ℝ) :
    Observables n →L[ℝ] Observables n :=
  q⁻¹ • (attemptLM J-(1-q) • 1)

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter ContinuousLinearMap
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def relativeEntropy (p q : α → ℝ) : ℝ := ∑ x, p x * Real.log (p x / q x)

end SKRatio.FiniteLaw

namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def transitionDensity {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) : Observables n :=
  fun y => continuousKernel (coupling g) t x y/mass g 0 y

def transitionEntropy {n : ℕ} (g : Disorder n) (x : Spin n) (t : ℝ) : ℝ :=
  FiniteLaw.relativeEntropy (continuousKernel (coupling g) t x) (mass g 0)

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_HammingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def spinVector {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spinValue (x i))

def hammingNeighborhood {n : ℕ} (B : Set (Spin n)) (δ : ℝ) : Set (Spin n) :=
  {x | ∃ y ∈ B, (hammingDist x y:ℝ) ≤ δ*n}

def hammingTo {n : ℕ} (B : Set (Spin n)) (x : Spin n) : ℕ :=
  if h : B.Nonempty then B.toFinset.inf' (Set.toFinset_nonempty.mpr h) (hammingDist x) else 0

def distanceObservable {n : ℕ} (B : Set (Spin n)) : Observables n :=
  fun x => (hammingTo B x:ℝ)/Real.sqrt n

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

noncomputable def goe {n : ℕ} (g : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (g (i,j) + g (j,i)) / Real.sqrt (2*n)

noncomputable def goeCLM (n : ℕ) : ((Fin n × Fin n) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (Real.sqrt (2*n))⁻¹ • ((ContinuousLinearMap.proj (i,j) : ((Fin n × Fin n) → ℝ) →L[ℝ] ℝ) + ContinuousLinearMap.proj (j,i))

@[simp] lemma goeCLM_apply (n : ℕ) (g : (Fin n × Fin n) → ℝ) : goeCLM n g = goe g := by
  ext i j
  change (Real.sqrt (2*n))⁻¹ * (g (i,j) + g (j,i)) =
    (g (i,j) + g (j,i)) / Real.sqrt (2*n)
  rw [div_eq_mul_inv, mul_comm]

def residualProjection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - U * Uᵀ

def queryColumn {n : ℕ} (q : Fin n → ℝ) : Matrix (Fin n) (Fin 1) ℝ := fun i _ => q i

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def constantDirection (n : ℕ) : Fin n → ℝ := fun _ => (sqrt n)⁻¹

def fieldProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  residualProjection (queryColumn (constantDirection n))

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def sum (σ : ι → α) (f : ι → ℝ) (a : α) : ℝ :=
  ∑ i with σ i = a, f i

def overlap (σ : ι → α) (u z : ι → ℝ) (a : α) : ℝ :=
  sum σ (fun i => u i*z i) a

def ZeroSum (σ : ι → α) (u : ι → ℝ) : Prop := ∀ a, sum σ u a = 0

lemma sum_fibers (σ : ι → α) (f : ι → ℝ) : ∑ a, sum σ f a = ∑ i, f i := by
  classical
  simpa only [sum,Finset.mem_univ,true_and] using
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := σ)
      (fun _ _ => Finset.mem_univ _) f)

omit [Fintype α] in
lemma overlap_self_nonneg (σ : ι → α) (u : ι → ℝ) (a : α) : 0 ≤ overlap σ u u a := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def matrixInner (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j*B i j

def linearMatrix (σ : ι → α) (C : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => u i*C (σ i) (σ j)

def quadraticMatrix (σ : ι → α) (K : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K (σ i) (σ j)*u i*u j

def binVariance (σ : ι → α) (C : α → α → ℝ) (a : α) : ℝ :=
  ∑ j, C a (σ j)^2

def residualMatrix (σ : ι → α) (C K : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  linearMatrix σ C u+(linearMatrix σ C u)ᵀ+quadraticMatrix σ K u

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def count (σ : ι → α) (a : α) : ℕ := (Finset.univ.filter (fun i => σ i=a)).card

def binMean (σ : ι → α) (p : ι → ℝ) (a : α) : ℝ := sum σ p a/(count σ a:ℝ)

def binCentered (σ : ι → α) (p : ι → ℝ) (i : ι) : ℝ := p i-binMean σ p (σ i)

lemma sum_const_bin (σ : ι → α) (c : α → ℝ) (a : α) :
    sum σ (fun i => c (σ i)) a = (count σ a:ℝ)*c a := by
  unfold sum count
  calc
    _ = ∑ i with σ i=a, c a := Finset.sum_congr rfl (fun i hi => by dsimp only []; rw [(Finset.mem_filter.mp hi).2])
    _ = _ := by simp

lemma sum_add_bin (σ : ι → α) (p q : ι → ℝ) (a : α) :
    sum σ (fun i => p i+q i) a = sum σ p a+sum σ q a := Finset.sum_add_distrib
lemma sum_sub_bin (σ : ι → α) (p q : ι → ℝ) (a : α) :
    sum σ (fun i => p i-q i) a = sum σ p a-sum σ q a := Finset.sum_sub_distrib _ _

lemma count_mul_binMean (σ : ι → α) (p : ι → ℝ) (a : α) :
    (count σ a:ℝ)*binMean σ p a=sum σ p a := by
  by_cases h : count σ a=0
  · have he : Finset.univ.filter (fun i => σ i=a)=∅ := Finset.card_eq_zero.mp h
    simp [binMean,h,sum,he]
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr h)

lemma binCentered_zeroSum (σ : ι → α) (p : ι → ℝ) : ZeroSum σ (binCentered σ p) := by
  intro a
  change sum σ (fun i => p i-binMean σ p (σ i)) a=0
  rw [sum_sub_bin,sum_const_bin,count_mul_binMean,sub_self]

lemma binCentered_decomp (σ : ι → α) (p : ι → ℝ) (i : ι) :
    p i=binMean σ p (σ i)+binCentered σ p i := by unfold binCentered; ring

lemma bin_orthogonal_decomposition {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u)
    (b : α → ℝ) (a : α) :
    sum σ (fun i => (b (σ i)+u i)^2) a =
      (count σ a:ℝ)*b a^2+overlap σ u u a := by
  have he : sum σ (fun i => b (σ i)*u i) a = b a*sum σ u a := by
    unfold sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only []
    rw [(Finset.mem_filter.mp hi).2]
  simp only [add_sq,sum_add_bin]
  have hcross : sum σ (fun i => 2*b (σ i)*u i) a=0 := by
    calc
      _ = 2*sum σ (fun i => b (σ i)*u i) a := by unfold sum; simp [mul_assoc,Finset.mul_sum]
      _ = 0 := by rw [he,hu a,mul_zero,mul_zero]
  rw [sum_const_bin σ (fun a => b a^2),hcross,add_zero]
  simp only [overlap,pow_two]

lemma centered_fiber_sq (σ : ι → α) (p : ι → ℝ) (a : α) :
    sum σ (fun i => p i^2) a =
      (count σ a:ℝ)*binMean σ p a^2+overlap σ (binCentered σ p) (binCentered σ p) a := by
  have he : (fun i => p i^2) = (fun i => (binMean σ p (σ i)+binCentered σ p i)^2) := by
    ext i
    rw [←binCentered_decomp]
  rw [he,bin_orthogonal_decomposition (binCentered_zeroSum σ p)]

lemma normalized_fiber_sq (σ : ι → α) (p : ι → ℝ) (a : α) :
    (sqrt (count σ a:ℝ)*binMean σ p a)^2+
      (sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))^2 =
      sum σ (fun i => p i^2) a := by
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg _),sq_sqrt (overlap_self_nonneg ..),centered_fiber_sq]

variable [Fintype α]

abbrev ParameterSpace (α : Type*) [Fintype α] := EuclideanSpace ℝ (α ⊕ α)

def ParameterSet (α : Type*) [Fintype α] : Set (ParameterSpace α) :=
  {z | ‖z‖=1 ∧ ∀ a, 0≤z (.inr a)}

abbrev Parameters (α : Type*) [Fintype α] := ↥(ParameterSet α)

def paramB (z : Parameters α) (a : α) : ℝ := z.val (.inl a)
def paramR (z : Parameters α) (a : α) : ℝ := z.val (.inr a)

def parametersOf (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) : Parameters α :=
  ⟨WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
    (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))),by
    constructor
    · have hs : ‖WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
          (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a)))‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          ←Finset.sum_add_distrib,normalized_fiber_sq,sum_fibers,hp]
      nlinarith only [hs,norm_nonneg (WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
        (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))))]
    · intro a
      exact sqrt_nonneg _⟩

@[simp] lemma parametersOf_B (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) (a : α) :
    paramB (parametersOf σ p hp) a = sqrt (count σ a:ℝ)*binMean σ p a := rfl
@[simp] lemma parametersOf_R (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) (a : α) :
    paramR (parametersOf σ p hp) a = sqrt (overlap σ (binCentered σ p) (binCentered σ p) a) := rfl

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def DirectionSet (σ : ι → α) : Set (EuclideanSpace ℝ ι) :=
  {u | ∀ a, sum σ u a=0 ∧ overlap σ u u a=1}

abbrev Directions (σ : ι → α) := ↥(DirectionSet σ)

variable [Fintype α]

def vectorOf {σ : ι → α} (z : Parameters α) (u : Directions σ) (i : ι) : ℝ :=
  paramB z (σ i)/sqrt (count σ (σ i):ℝ)+paramR z (σ i)*u.val i

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

abbrev Coordinates (ι : Type*) := (ι × ι) ⊕ ι

def radicalSq (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (a : α) : ℝ :=
  binVariance σ C a+∑ d, K a d^2*s d

def residualCoeff (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ) (u : ι → ℝ) : Coordinates ι → ℝ
  | Sum.inl (i,j) => δ/sqrt 2*residualMatrix σ C K u i j
  | Sum.inr _ => 0

def comparisonCoeff (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ)
    (u : ι → ℝ) : Coordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => δ*sqrt (radicalSq σ C K s (σ i))*u i

def blockNorm (σ : ι → α) (a : α) (g : Coordinates ι → ℝ) : ℝ :=
  sqrt (sum σ (fun i => g (Sum.inr i)^2) a)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def average (p : ι → ℝ) : ℝ := (∑ i, p i)/(Fintype.card ι:ℝ)
def centered (p : ι → ℝ) : ι → ℝ := fun i => p i-average p

def fullCoeff (v p : ι → ℝ) (δ : ℝ) : Coordinates ι → ℝ
  | .inl (i,j) => δ/sqrt 2*(centered p i*centered (fun k => v k*p k) j+
      centered p j*centered (fun k => v k*p k) i)
  | .inr _ => 0

def crossCoeff (σ : ι → α) (v b : α → ℝ) (a d : α) : ℝ :=
  (v a+v d)*b d-average (fun i => (v a+v (σ i))*b (σ i))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_CompactField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

abbrev FieldWeight := Set.Icc (0:ℝ) 2

def compactWeight (h : ℝ) : FieldWeight :=
  ⟨w h, (w_pos h).le, by unfold w; linarith [(m_bounds h).1]⟩

@[simp] lemma compactWeight_coe (h : ℝ) : (compactWeight h : ℝ) = w h := rfl

def compactV (a : FieldWeight) : ℝ := (a:ℝ)*(2-a)

def compactF (p : FieldWeight × FieldWeight) : ℝ :=
  (p.2:ℝ)^2*(2-p.2)^2/((p.1:ℝ)+p.2)
def compactK (p : FieldWeight × FieldWeight) : ℝ :=
  compactV p.1*compactV p.2/((p.1:ℝ)+p.2)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def quadratic (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*p i*p j

def weightedForm (A : Matrix (Fin n) (Fin n) ℝ) (G : FieldWeight × FieldWeight → ℝ)
    (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  quadratic (fun i j => A i j*G (x i,x j)) p

def diagonalForm (A : Matrix (Fin n) (Fin n) ℝ) (G : FieldWeight × FieldWeight → ℝ)
    (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j, A i j*G (x i,x j))*p i^2

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real

namespace SKRatio.Bins
open SKRatioClock.Regression Planted
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

def projectedSup (β : ℝ) (v : Fin n → ℝ) (p : I → Fin n → ℝ)
    (g : (Fin n × Fin n) → ℝ) : ℝ :=
  sSup (Set.range (fun t => p t ⬝ᵥ
    ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ (fun i => v i*p t i))))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def binT (σ : ι → α) (a : α) : ℝ := sqrt (count σ a:ℝ)/sqrt (Fintype.card ι:ℝ)

omit [DecidableEq ι] in
lemma sum_count (σ : ι → α) : (∑ a, (count σ a:ℝ))=(Fintype.card ι:ℝ) := by
  have hh := sum_fibers σ (fun _ => (1:ℝ))
  simpa only [sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,count] using hh

omit [DecidableEq ι] [Fintype α] in
lemma binT_nonneg (σ : ι → α) (a : α) : 0≤binT σ a := by unfold binT; positivity

omit [DecidableEq ι] [Fintype α] in
lemma binT_sq (σ : ι → α) (a : α) : binT σ a^2=(count σ a:ℝ)/(Fintype.card ι:ℝ) := by
  simp only [binT,div_pow,sq_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq ι] in
lemma binT_unit [Nonempty ι] (σ : ι → α) : (∑ a, binT σ a^2)=1 := by
  simp only [binT_sq,←Finset.sum_div,sum_count]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

def moment (t B f : α → ℝ) : ℝ := ∑ a, t a*B a*f a

def finiteRadicalSq (t v : α → ℝ) (z : Parameters α) (a : α) : ℝ :=
  (∑ d, (v a+v d)^2*((paramB z d)^2+(paramR z d)^2))-
    (moment t (paramB z) (fun d => v a+v d))^2

def finiteGaussian (β : ℝ) (t v : α → ℝ) (z : Parameters α) : ℝ :=
  β*∑ a, t a*paramR z a*sqrt (finiteRadicalSq t v z a)

def finiteA (β : ℝ) (t h : α → ℝ) (z : Parameters α) : ℝ :=
  moment t (paramB z) h*moment t (paramB z) (fun a => v (h a))+
  moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => h a*v (h a))-
  β^2*moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => v (h a))+
  2*β^2*moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => m (h a)*v (h a))+
  β^2*(∑ a, ∑ d, t d^2*(v (h d)^2/(w (h a)+w (h d)))*
      ((paramB z a)^2+(paramR z a)^2))+
  β^2*(∑ a, ∑ d, t a*paramB z a*kernel (h a) (h d)*(t d*paramB z d))

def finiteV (β : ℝ) (t h : α → ℝ) (z : Parameters α) : ℝ :=
  finiteA β t h z+finiteGaussian β t (fun a => v (h a)) z

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

def siteMoment (p f : Fin n → ℝ) : ℝ := (∑ i, p i*f i)/sqrt (n:ℝ)

def correctedForm (β : ℝ) (H p : Fin n → ℝ) : ℝ :=
  siteMoment p H*siteMoment p (fun i => v (H i))+
  siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
  β^2*siteMoment p (fun _ => 1)*siteMoment p (fun i => v (H i))+
  2*β^2*siteMoment p (fun _ => 1)*siteMoment p (fun i => m (H i)*v (H i))+
  diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p+
  weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression Calculus
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

abbrev WeightBox (α : Type*) := α → Set.Icc (0:ℝ) 1

lemma binT_le_one [Nonempty (Fin n)] (σ : Fin n → α) (a : α) : binT σ a≤1 := by
  have hs : binT σ a^2≤1 := by
    rw [←binT_unit σ]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (binT σ i)) (Finset.mem_univ a)
  nlinarith only [hs]

def binBox [Nonempty (Fin n)] (σ : Fin n → α) : WeightBox α :=
  fun a => ⟨binT σ a,binT_nonneg σ a,binT_le_one σ a⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar
variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

def binMass (μ : Measure Ω) (σ : Ω → α) (a : α) : ℝ := μ.real {x | σ x=a}

def massRoot (μ : Measure Ω) (σ : Ω → α) (a : α) : ℝ := sqrt (binMass μ σ a)

def pullback (μ : Measure Ω) (σ : Ω → α) (B : α → ℝ) (x : Ω) : ℝ :=
  B (σ x)/massRoot μ σ (σ x)

lemma integral_finite_partition {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    (∫ x, f (σ x) ∂μ)=∑ a, binMass μ σ a*f a := by
  rw [←integral_map hσ.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    integral_fintype (by exact Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_mul,map_measureReal_apply hσ (measurableSet_singleton a)]
  rfl

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma binMass_nonneg (σ : Ω → α) (a : α) : 0 ≤ binMass μ σ a := measureReal_nonneg

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma massRoot_sq (σ : Ω → α) (a : α) : massRoot μ σ a^2=binMass μ σ a :=
  sq_sqrt (binMass_nonneg σ a)

lemma sum_binMass {σ : Ω → α} (hσ : Measurable σ) : (∑ a, binMass μ σ a)=1 := by
  have hh := integral_finite_partition (μ := μ) hσ (fun _ => (1:ℝ))
  simpa only [mul_one,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh.symm

lemma massRoot_unit {σ : Ω → α} (hσ : Measurable σ) : (∑ a, massRoot μ σ a^2)=1 := by
  simp_rw [massRoot_sq]
  exact sum_binMass hσ

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression Calculus
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

def siteNorm (f : Fin n → ℝ) : ℝ := ‖WithLp.toLp 2 f‖/sqrt (n:ℝ)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression Calculus
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def binFormBad {n : ℕ} (β : ℝ) (h : α → ℝ) (σ : Fin n → α)
    (K C : ℝ) : Set ((Fin n × Fin n) → ℝ) :=
  {g | euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n)≤K ∧
    ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
      p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
        (fun i => v (h (σ i))*p i))+ correctedForm β (fun i => h (σ i)) p}

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinWeightContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar
variable {α : Type*} [Fintype α] [DecidableEq α]

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq α] in
lemma massRoot_le_one {σ : Ω → α} (hσ : Measurable σ) (a : α) : massRoot μ σ a≤1 := by
  have hs : massRoot μ σ a^2≤1 := by
    rw [←massRoot_unit (μ := μ) hσ]
    exact Finset.single_le_sum (fun d _ => sq_nonneg (massRoot μ σ d)) (Finset.mem_univ a)
  nlinarith only [hs]

def populationBox {σ : Ω → α} (hσ : Measurable σ) : WeightBox α :=
  fun a => ⟨massRoot μ σ a,sqrt_nonneg _,massRoot_le_one hσ a⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_ConditionalBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ENNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression Calculus
attribute [local instance] Classical.propDecidable

def residualFormBad {α : Type*} {n : ℕ} (β : ℝ) (h : α → ℝ)
    (σ : Fin n → α) (K C : ℝ) : Set ((Fin n × Fin n) → ℝ) :=
  {M | euclideanOpNorm (fun i j => M (i,j)) ≤ K ∧
    ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
      p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
        correctedForm β (fun i => h (σ i)) p}

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_IntervalBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def intervalBin {N : ℕ} (e : Fin N → ℝ) (x : ℝ) : Fin (N+1) :=
  ⟨(Finset.univ.filter (fun i => e i<x)).card,by
    have h := Finset.card_le_card (Finset.filter_subset (s:=Finset.univ) (p:=fun i => e i<x))
    simpa only [Finset.card_univ,Fintype.card_fin] using Nat.lt_succ_of_le h⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_Quantizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def gridCut (R : ℝ) (N : ℕ) (j : Fin (N+1)) : ℝ := -R+(2*R/N)*(j.val:ℝ)

def gridRep (R : ℝ) (N : ℕ) (j : Fin (N+2)) : ℝ := -R+(2*R/N)*((min j.val N:ℕ):ℝ)

def gridQuant (R : ℝ) (N : ℕ) (x : ℝ) : ℝ := gridRep R N (intervalBin (gridCut R N) x)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FieldRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def fieldRadicand (μ : Measure ℝ) (H b r : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y, ((v (H x)+v (H y))*r y)^2 ∂μ)+
    (∫ y, ((v (H x)+v (H y))*b y-(∫ t, (v (H x)+v (H t))*b t ∂μ))^2 ∂μ)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FieldFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def fieldDiagonal (μ : Measure ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, v (H y)^2/(w (H x)+w (H y)) ∂μ

def fieldForm (μ : Measure ℝ) (β : ℝ) (H b r : ℝ → ℝ) : ℝ :=
  (∫ x, (β^2*fieldDiagonal μ H x)*(b x^2+r x^2) ∂μ)+
  (∫ x, b x*H x ∂μ)*(∫ x, b x*v (H x) ∂μ)+
  (∫ x, b x ∂μ)*(∫ x, b x*(H x*v (H x)) ∂μ)-
  β^2*(∫ x, b x ∂μ)*(∫ x, b x*v (H x) ∂μ)+
  2*β^2*(∫ x, b x ∂μ)*(∫ x, b x*(m (H x)*v (H x)) ∂μ)+
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)+
  β*(∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)

end SKRatio.Bins

end

end OAI
end


