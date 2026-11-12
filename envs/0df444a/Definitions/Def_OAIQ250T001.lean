-- Prove2me | Definitions.Def_OAIQ250T001
-- name    : OAIQ250T001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:05:52.165879+00:00
-- url     : https://prove2.me/theorems/3d295512-0def-4fca-a947-c20f1084fb03
-- title:
--   Definitions bundle OAIQ250T001 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 244 declarations of OpenAI's Lean: 88 definitions and 156 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Bkernel`, `OAI.AtomicTriangular.Construction.Ckernel`, `OAI.AtomicTriangular.Construction.DeltaStar`, `OAI.AtomicTriangular.Construction.Dkernel`, `OAI.AtomicTriangular.Construction.FiniteCoefficients`, `OAI.AtomicTriangular.Construction.JetVector`, `OAI.AtomicTriangular.Construction.ParameterPolytope`, `OAI.AtomicTriangular.Construction.Pstar`, `OAI.AtomicTriangular.Construction.Spectrum`, `OAI.AtomicTriangular.Construction.Ustar`, `OAI.AtomicTriangular.Construction.Wstar`, `OAI.AtomicTriangular.Construction.atomFunction`, `OAI.AtomicTriangular.Construction.beta`, `OAI.AtomicTriangular.Construction.cVariation`, `OAI.AtomicTriangular.Construction.cellHi`, `OAI.AtomicTriangular.Construction.cellLo`, `OAI.AtomicTriangular.Construction.cellMagnitude`, `OAI.AtomicTriangular.Construction.coeffAbs`, `OAI.AtomicTriangular.Construction.curvaturePoint`, `OAI.AtomicTriangular.Construction.dVariation`, `OAI.AtomicTriangular.Construction.deletedSecond`, `OAI.AtomicTriangular.Construction.delta`, `OAI.AtomicTriangular.Construction.extend`, `OAI.AtomicTriangular.Construction.farK`, `OAI.AtomicTriangular.Construction.finiteCurvatureCap`, `OAI.AtomicTriangular.Construction.finiteCurvatureEnvelope`, `OAI.AtomicTriangular.Construction.finiteErrorBound`, `OAI.AtomicTriangular.Construction.finiteRatio`, `OAI.AtomicTriangular.Construction.finiteResidualBound`, `OAI.AtomicTriangular.Construction.finiteSpectrum`, `OAI.AtomicTriangular.Construction.finiteTargetEnvelope`, `OAI.AtomicTriangular.Construction.frequencyDistance`, `OAI.AtomicTriangular.Construction.frequencyFunction`, `OAI.AtomicTriangular.Construction.fullTailW`, `OAI.AtomicTriangular.Construction.gaussian`, `OAI.AtomicTriangular.Construction.gaussianG`, `OAI.AtomicTriangular.Construction.gaussianTarget`, `OAI.AtomicTriangular.Construction.integralCBasis`, `OAI.AtomicTriangular.Construction.integralDBasis`, `OAI.AtomicTriangular.Construction.integralLinear` and 48 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_IntegralBounds`, `Triangular_Auxiliary_MatrixNorm`, `Triangular_Certificate_Inverse`, `Triangular_Certificate_MatrixInterval`, `Triangular_Certificate_Param`, `Triangular_Certificate_ParamActual`, `Triangular_Certificate_ParamNorm`, `Triangular_Certificate_Polytope`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_AtomicCurvature`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_CoefficientAddition`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_DirectCoordinates`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteAssembly`, `Triangular_Construction_FiniteJets`, `Triangular_Construction_FinitePairBridge`, `Triangular_Construction_FiniteProjection`, `Triangular_Construction_FiniteTargetBridge`, `Triangular_Construction_Normalization`, `Triangular_Construction_NormalizedJets`, `Triangular_Construction_RepetitionOperators`, `Triangular_Construction_Schur`, `Triangular_Construction_SpectralJetBridge`, `Triangular_Construction_SpectralProduct`, `Triangular_Construction_TailJetVector`, `Triangular_Envelope_Analytic`, `Triangular_Envelope_Basic`, `Triangular_Envelope_EnvelopeBoxes`, `Triangular_Envelope_KernelBounds`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Schwartz_FourierCLM`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_InputCLM`, `Triangular_Schwartz_Realness`, `Triangular_Schwartz_Regularity`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_SpectralEnvelope`, `Triangular_Schwartz_TailSpectral`, `Triangular_Signs_DeletedQuotient`, `Triangular_Signs_FarSigns`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_Taylor`, `Triangular_Taylor_TaylorPhase`, `Triangular_Taylor_TaylorRowsBase`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007`, `OAIQ250T008`, `OAIQ250T009`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T017`, `OAIQ250T040`, `OAIQ250T045` and `OAIQ250T046`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_IntegralBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace AtomicTriangular.IntegralVectors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma weighted_interval_bound {a b t M : ℝ} (hab : a≤b) (hbt : b≤t)
    (f : ℝ → E) (hf : ∀ x ∈ Icc a b, ‖f x‖≤M) :
    ‖∫ x in a..b, (t-x) • f x‖ ≤ ((t-a)^2-(t-b)^2)/2*M := by
  calc
    _ ≤ ∫ x in a..b, (t-x)*M := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
      · exact ae_of_all _ fun x hx => by
          rw [norm_smul,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hx.2.trans hbt))]
          exact mul_le_mul_of_nonneg_left (hf x ⟨hx.1.le,hx.2⟩) (sub_nonneg.mpr (hx.2.trans hbt))
      · exact (show Continuous (fun x : ℝ => (t-x)*M) by fun_prop).intervalIntegrable a b
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub (f:=fun _ : ℝ => t)
        (g:=fun x : ℝ => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),integral_id]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring

lemma norm_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=f) (fun i _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => hM i (Finset.mem_range.mp hi) x (by
          rw [Set.uIoc_of_le (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)] at hx
          exact ⟨hx.1.le,hx.2⟩))
        (a := (i:ℝ)*δ) (b := (i+1:ℕ)*δ)
      have hd : |((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ|=δ := by
        rw [show ((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ=δ by push_cast; ring,abs_of_nonneg hδ]
      rw [hd] at hh
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma weighted_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, ((n:ℝ)*δ-x) • f x‖ ≤
      δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  have hc : Continuous (fun x : ℝ => ((n:ℝ)*δ-x) • f x) := by fun_prop
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=fun x : ℝ => ((n:ℝ)*δ-x) • f x) (fun i _ => hc.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, ((n:ℝ)*δ-x) • f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ^2*((n:ℝ)-i-1/2)*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i+1≤n := Finset.mem_range.mp hi
      have hiR : ((i+1:ℕ):ℝ)≤n := by exact_mod_cast hin
      have hh := weighted_interval_bound (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)
        (mul_le_mul_of_nonneg_right hiR hδ) f (hM i (Finset.mem_range.mp hi))
      calc
        _ ≤ (((n:ℝ)*δ-(i:ℝ)*δ)^2-((n:ℝ)*δ-((i+1:ℕ):ℝ)*δ)^2)/2*M i := by
          exact hh
        _ = _ := by push_cast <;> ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
lemma norm_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, f x‖ = ‖∫ x in (0:ℝ)..t, f (-x)‖ := by
  rw [intervalIntegral.integral_comp_neg,neg_zero,intervalIntegral.integral_symm,norm_neg]
lemma norm_weighted_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, (-t-x) • f x‖ = ‖∫ x in (0:ℝ)..t, (t-x) • f (-x)‖ := by
  rw [norm_integral_neg]
  simp only [show ∀ x : ℝ, -t- -x=-(t-x) by intro x; ring,neg_smul,
    intervalIntegral.integral_neg,norm_neg]
lemma norm_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact norm_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_integral_neg]
    exact norm_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
lemma weighted_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, (t-x) • f x‖ ≤ δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact weighted_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_weighted_integral_neg]
    exact weighted_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
end AtomicTriangular.IntegralVectors
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_MatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.MatrixBounds
def colNorm {m n : Type*} [Fintype m] (A : Matrix m n ℝ) (j : n) : ℝ := ∑ i, |A i j|
def matNorm {m n : Type*} [Fintype m] [Fintype n] [Nonempty n] (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' (by classical exact Finset.univ_nonempty) (colNorm A)

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

omit [Fintype n] in
lemma colNorm_nonneg (A : Matrix m n ℝ) (j : n) : 0 ≤ colNorm A j :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
lemma colNorm_le_matNorm [Nonempty n] (A : Matrix m n ℝ) (j : n) :
    colNorm A j ≤ matNorm A := by
  classical
  exact Finset.le_sup' (f := colNorm A) (Finset.mem_univ j)
lemma matNorm_nonneg [Nonempty n] (A : Matrix m n ℝ) : 0 ≤ matNorm A := by
  obtain ⟨j⟩ := ‹Nonempty n›
  exact (colNorm_nonneg A j).trans (colNorm_le_matNorm A j)
lemma matNorm_le [Nonempty n] {A : Matrix m n ℝ} {c : ℝ}
    (h : ∀ j, colNorm A j ≤ c) : matNorm A ≤ c := by
  classical
  exact (Finset.sup'_le_iff _ _).mpr (fun j _ => h j)
omit [Fintype n] in
lemma colNorm_add (A B : Matrix m n ℝ) (j : n) :
    colNorm (A+B) j ≤ colNorm A j + colNorm B j := by
  unfold colNorm
  simp only [Matrix.add_apply,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)
lemma matNorm_add [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A+B) ≤ matNorm A + matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_add A B j).trans (add_le_add (colNorm_le_matNorm A j) (colNorm_le_matNorm B j))
omit [Fintype n] in
lemma colNorm_neg (A : Matrix m n ℝ) (j : n) : colNorm (-A) j = colNorm A j := by
  simp only [colNorm,Matrix.neg_apply,abs_neg]
lemma matNorm_neg [Nonempty n] (A : Matrix m n ℝ) : matNorm (-A) = matNorm A := by
  simp only [matNorm,colNorm_neg]
lemma matNorm_sub [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A-B) ≤ matNorm A + matNorm B := by
  simpa only [sub_eq_add_neg,matNorm_neg] using matNorm_add A (-B)
omit [Fintype p] in
lemma colNorm_mul [Nonempty n] (A : Matrix m n ℝ) (B : Matrix n p ℝ) (j : p) :
    colNorm (A*B) j ≤ matNorm A * colNorm B j := by
  classical
  calc
    colNorm (A*B) j ≤ ∑ i, ∑ k, |A i k * B k j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k, colNorm A k * |B k j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ k, matNorm A * |B k j| := Finset.sum_le_sum
      (fun k _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A k) (abs_nonneg _))
    _ = matNorm A * colNorm B j := by simp only [colNorm,Finset.mul_sum]
lemma matNorm_mul [Nonempty n] [Nonempty p] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    matNorm (A*B) ≤ matNorm A * matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_mul A B j).trans (mul_le_mul_of_nonneg_left
    (colNorm_le_matNorm B j) (matNorm_nonneg A))

end AtomicTriangular.MatrixBounds

namespace AtomicTriangular.MatrixBounds
open Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
def vecNorm (v : n → ℝ) : ℝ := ∑ i, |v i|
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_nonneg (v : n → ℝ) : 0 ≤ vecNorm v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_zero_iff (v : n → ℝ) : vecNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi : |v i| ≤ vecNorm v := (Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    rw [h] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl; simp [vecNorm]
omit [DecidableEq n] in
lemma matrix_vecNorm (A : Matrix n n ℝ) (v : n → ℝ) :
    vecNorm (A.mulVec v) ≤ matNorm A * vecNorm v := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * v j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, colNorm A j * |v j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ j, matNorm A * |v j| := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A j) (abs_nonneg _))
    _ = _ := by simp only [vecNorm,Finset.mul_sum]
lemma isUnit_of_residual (A C : Matrix n n ℝ) (he : matNorm (C*A-1) < 1) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hh
  have hzero : A.mulVec (v-w) = 0 := by rw [mulVec_sub,hh,sub_self]
  have hres : (C*A-1).mulVec (v-w) = -(v-w) := by
    rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec, hzero,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
  have hb := matrix_vecNorm (C*A-1) (v-w)
  rw [hres] at hb
  have hneg : vecNorm (-(v-w)) = vecNorm (v-w) := by simp only [vecNorm, Pi.neg_apply, abs_neg]
  rw [hneg] at hb
  have hz := vecNorm_nonneg (v-w)
  have hv : vecNorm (v-w) = 0 := by nlinarith
  exact sub_eq_zero.mp ((vecNorm_zero_iff _).mp hv)
lemma inverse_bound_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (_hb : 0 ≤ b) (he1 : e < 1) :
    matNorm A⁻¹ ≤ b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹ = C-(C*A-1)*A⁻¹ := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  have hx : matNorm A⁻¹ ≤ b+e*matNorm A⁻¹ := by
    calc
      _ ≤ matNorm C + matNorm ((C*A-1)*A⁻¹) := by
        conv_lhs => rw [hid]
        exact matNorm_sub _ _
      _ ≤ b+e*matNorm A⁻¹ := add_le_add hc ((matNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right he (matNorm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr he1)).mpr
  nlinarith
lemma inverse_error_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (hb : 0 ≤ b) (he0 : 0 ≤ e) (he1 : e < 1) :
    matNorm (A⁻¹-C) ≤ e*b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹-C = -((C*A-1)*A⁻¹) := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  rw [hid,matNorm_neg]
  exact (matNorm_mul _ _).trans ((mul_le_mul he
    (inverse_bound_of_residual A C b e hc he hb he1) (matNorm_nonneg _) he0).trans_eq (by ring))
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction

def rootProduct (s : ℂ) : ℂ := ∏ a : Fin 15, sineFactor a s

theorem P_eq_square (s : ℂ) : P s = rootProduct s ^ 2 := by
  simp only [P, rootProduct, Finset.prod_pow]

theorem differentiable_rootProduct : Differentiable ℂ rootProduct := by
  unfold rootProduct sineFactor
  fun_prop

theorem differentiable_P : Differentiable ℂ P := by
  unfold P sineFactor
  fun_prop

theorem differentiable_dBasis (n : Node) : Differentiable ℂ (dBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    differentiable_P.differentiableOn

theorem differentiable_cBasis (n : Node) : Differentiable ℂ (cBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    (differentiable_dBasis n).differentiableOn

theorem differentiable_finiteC (a : Fin 15) : Differentiable ℂ (finiteC a) := by
  unfold finiteC sineFactor
  fun_prop

theorem differentiable_finiteD (a : Fin 15) : Differentiable ℂ (finiteD a) := by
  unfold finiteD sineFactor
  fun_prop

theorem P_factor (a : Fin 15) (s : ℂ) :
    P s = (sineFactor a s)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

open Polynomial

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2 = 3/4 := by
  unfold b
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith

lemma complex_gaussian_transform (a : ℂ) (ha : 0 < a.re) (w : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) w =
      a⁻¹ * Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2 / a) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 : a ≠ 0 := by intro h; subst a; simp at ha
  have hh : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  have hg := fourier_gaussian_innerProductSpace hh w
  have hf : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hf] at hg
  norm_num at hg
  have hfun : (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) =
      (fun x : Plane => Complex.exp (-((Real.pi : ℂ) * a * ‖x‖ ^ 2))) := by
    funext x
    congr 1
    ring
  rw [hfun, hg]
  have hquot : (Real.pi : ℂ) / ((Real.pi : ℂ) * a) = a⁻¹ := by field_simp
  rw [hquot]
  congr 2
  field_simp

def spectralParameter (k t : ℝ) : ℂ := (b:ℂ)*((k:ℂ)-I*t)
lemma spectralParameter_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < (spectralParameter k t).re := by
  simpa [spectralParameter] using mul_pos b_pos hk

end AtomicTriangular.Construction

end
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma matrixEntry_le_norm [Nonempty n] (A : Matrix m n ℝ) (i : m) (j : n) :
    |A i j| ≤ matNorm A := by
  have hh : |A i j| ≤ colNorm A j :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A k j)) (Finset.mem_univ i)
  exact hh.trans (colNorm_le_matNorm A j)
end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
def minusApproxNum : Fin 20 → Fin 20 → ℤ :=
  ![![1349044106410383572030815946882954857821400000000000000000000,-964512039954917735360838164642275637018600000000000000000000,115895178912356922568797372485804018418000000000000000000000,-47071428170313443525526465711671049600300000000000000000000,-9045356458601113843094233341852674998400000000000000000000,-17107865807968104741774225012600476049000000000000000000000,4202977997010455990277813526799255370600000000000000000000,-2552224230012956379472009996353683054300000000000000000000,84095504524230128862556204524275726900000000000000000000,-167915213342581004955403635721395856800000000000000000000,26457146529500886083805076626310976500000000000000000000,-41868227024650773709103792543642764300000000000000000000,27491964471530530253007956157954083200000000000000000000,-15111666526948377661718017371450282600000000000000000000,31686505683749714625236812653279992800000000000000000000,73943296257424961004727444247848837900000000000000000000,37671237019674924014371125608523085500000000000000000000,177039107093322076166594560151820314400000000000000000000,44633148124913363156982233429713714400000000000000000000,258789996097089584546855612306683332200000000000000000000],
  ![-5114019374887022731805515753589795754780000000000000000000000,9830246832180972431144801151021516330240400000000000000000000,-667008128440522060642952861127014311666400000000000000000000,-54497816313556849206483802685194246141600000000000000000000,275509393639308075725210911332262532476600000000000000000000,-27399797604458825508203228668176800939900000000000000000000,-29640079210973289538332030800932486299600000000000000000000,-4463344716537187711107151792262871095400000000000000000000,1565998051035841570499015700686595848000000000000000000000,-16958068015417350259769015483997547362900000000000000000000,2501503833304588593236460330380442674100000000000000000000,-10880527001922129782333330594609182038000000000000000000000,2595218058220931060594998732772435340700000000000000000000,-8323414013454913970568720564795293975500000000000000000000,2684109071986407241676473597784268870900000000000000000000,-399315607575629854699579219769381502400000000000000000000,2915636880388644139513345062165958280300000000000000000000,7933765472633900429048437521719181812600000000000000000000,3263190048769786254289317310984949209700000000000000000000,14078965900171800100213144346725410249600000000000000000000],
  ![1264635142061599413343783873288672282795600000000000000000000,-2375163146479684004142167564167185241668700000000000000000000,1218950576192061373883024120569269390670100000000000000000000,-125409201753491168304528194770653799264100000000000000000000,-20066278847496082747652929602330462502200000000000000000000,-79139798168555224622622940532183776974600000000000000000000,16056075434370132771123980227253784634000000000000000000000,-8380864818373668481255635366220107773300000000000000000000,810417165098056336797569416022490297400000000000000000000,2986009486793077215374530910304416294900000000000000000000,-1471773076128778160982489890731277297700000000000000000000,1008230548912257586665785368766014808000000000000000000000,-1697707627367341353552925846302492670400000000000000000000,-584354031290178006353150643129230067500000000000000000000,-2127911013332883109316366355160889607100000000000000000000,-6359016748010057665473319953142037569100000000000000000000,-2610729770946826068708241532494892090300000000000000000000,-13412262853145116902760966399512140867600000000000000000000,-3123466853925599488210990854836533622600000000000000000000,-19109178401344461287567552305727978644300000000000000000000],
  ![-174038276417592721983781599032459475262000000000000000000000,61922740536719803841746140993674001502500000000000000000000,-107290624176854267287874859019099364094200000000000000000000,715785286710000927838723768133404710694500000000000000000000,-37986578182872666658989715283479534364300000000000000000000,-354705614910362127604380002723991176713300000000000000000000,41190088479829612225875299187066391042200000000000000000000,-309791132061582608468445745771083917963600000000000000000000,36537277602829648134704796613708518156100000000000000000000,-229430278863663499030438884640362177749300000000000000000000,24166769729133250711108577511828415715700000000000000000000,-140087921378603428523006376815964247799100000000000000000000,21615125194032269340586816734230554125600000000000000000000,-117253654986428431072696645160783262487400000000000000000000,17088097687657254952598976982673718013100000000000000000000,-60155154554270810756797052699661379526600000000000000000000,15489991213738344495912579755351072168000000000000000000000,-11854305328290714752258226969245591278400000000000000000000,15577575467912751413287229133142002282300000000000000000000,19068231024451229667368296144997031657300000000000000000000],
  ![-375947228131675420315314105673045406308600000000000000000000,709607458073591498853761351862773597246200000000000000000000,-59890272766799961726954310551061904793400000000000000000000,46844002017348807991504674437762494302900000000000000000000,1009676009098295094974490271814160025684300000000000000000000,37746031043661225958896812045142846376600000000000000000000,-6958256466654343499476847427822178326700000000000000000000,17290242905928387883030718127260487812500000000000000000000,-2360592554452272398574660967335826413600000000000000000000,9258058560146661683133514209668183198300000000000000000000,-336076012248412061086729216481328364000000000000000000000,5611627247929911084161077951530661476400000000000000000000,23415238981633547052796020928651324600000000000000000000,5464914671500946530266099531427650863700000000000000000000,655577477854614434990273484147225404700000000000000000000,6595973981779471970582078691307983745200000000000000000000,1069242756151025631171004568235925564100000000000000000000,9192344464073989734677997195227634090200000000000000000000,1376786322644510555872507004833777284500000000000000000000,11626445815307516095622002013210340983100000000000000000000],
  ![1169914278690377987589937250186298781988000000000000000000000,-2147280923061807662132398012206767446154000000000000000000000,222153121980078835294367110900266279367500000000000000000000,-58434193644257002744709928327495723225400000000000000000000,1164359099074312737352770526671477100600000000000000000000,1005156715697653123033347856687327442365500000000000000000000,15633428102009501638216022436769307216800000000000000000000,100913126094960719085631231875766100004400000000000000000000,-7153253542945607039370978408493829719700000000000000000000,103276307642249879413986037801207483515800000000000000000000,-11944876848178242400020120979959542182500000000000000000000,71550685859231102545504964595111903580000000000000000000000,-11835660449169676730612947282802887846600000000000000000000,59637075869818254716664849064980019652400000000000000000000,-11054809910954081973527558930268734674700000000000000000000,25350735287282196857045375588100718103900000000000000000000,-10970554575580166680657254916253982419400000000000000000000,-7438250741969066578019612188859664003300000000000000000000,-11537567006683501182602039575746076084200000000000000000000,-29851265794353862963468897327520594665700000000000000000000],
  ![5740557895570603969383877651573054000100000000000000000000,-10952289095609807273424676912099355049600000000000000000000,692722999824231292021840684161868485200000000000000000000,-1041800496265917389417322492618294276700000000000000000000,-402778780511296739862812732213210041400000000000000000000,-1147727893436975652267806993893288580600000000000000000000,999994624362170367157042714500315326797100000000000000000000,-1431254659780426294582206680500071402600000000000000000000,37956619751310564274559570739636178200000000000000000000,-1410565639922250518835059721026748255300000000000000000000,78025658063395851425641178736811590400000000000000000000,-1215666607890796460717972057072346022900000000000000000000,77241533587945178601139268371333320000000000000000000000,-1137679442574024396437690387980199906100000000000000000000,59909372379995418952797441699988214500000000000000000000,-928655061568503514851256011158398527100000000000000000000,37569313686392878803333298658998931700000000000000000000,-782487124335821096367926027151000671800000000000000000000,22997793036656578142649066679727405800000000000000000000,-721933247504422714769031600672700508500000000000000000000],
  ![-19611909525777893352511605223621786968100000000000000000000,36731887336751200179623890745710183612900000000000000000000,-3037912338913790818566466664106256481600000000000000000000,2338780491788140552189260835964501334100000000000000000000,600715759037801344791588041679581582700000000000000000000,1955213179156775573672044453009145723700000000000000000000,-423598362301517530317426625081605192900000000000000000000,1000994285888838638562147170347021924560700000000000000000000,-248395322748356345711237374105320533500000000000000000000,368826314351219258559908836195737583500000000000000000000,-61887725710337393369632327013894000300000000000000000000,-107955180525951608145260519186413279500000000000000000000,-1744461962454710438200748074324733000000000000000000000,-139170007067277154642870165211802448600000000000000000000,129273750332798311385828555583796251400000000000000000000,70783018088166222080259434469874653300000000000000000000,201578845470718461260222008242397647700000000000000000000,577110517502389643568274476179176899700000000000000000000,234865159442038536064588222714617460400000000000000000000,1014532878879646630448348499040367378700000000000000000000],
  ![424065601264256747583244254098671576200000000000000000000,-819027627779734727564293271789321961200000000000000000000,36940652755679816918025376748207318600000000000000000000,-98968278212667452064322420801318265400000000000000000000,-47859549029904718579967979102058517700000000000000000000,-123300672968697914007270870400216685600000000000000000000,-17809875260571269524930178940252660300000000000000000000,-200494599157332312259760532867469517700000000000000000000,999990943154827375073145305023270341436900000000000000000000,-228638297561959661734507733391449325100000000000000000000,3859918305715003882265964521266618100000000000000000000,-234740590781662290933659545328431732900000000000000000000,6710799465075413328759716765428664300000000000000000000,-229398461805387713359597539451696564000000000000000000000,11615652257348566244021129744409071000000000000000000000,-200671320880440186913725880234828339000000000000000000000,12595560371052699270591741191486978600000000000000000000,-163621243830545810436444318930956366100000000000000000000,11944195689254041184219450442818148800000000000000000000,-138949041716961853356297323003653173000000000000000000000],
  ![-5847474957802331632756105688081902700100000000000000000000,11056242264759272347595410030923988432900000000000000000000,-767246362939414822917825260786572082900000000000000000000,919334062837452643789900639279852290800000000000000000000,348425071119788175987854603374104651500000000000000000000,962661892326778471416051288319906808700000000000000000000,925451596322744967757825103605303000000000000000000000,1150868794635147912950792210238770631800000000000000000000,-15188932028992255933445945035851064000000000000000000000,1001151591977179704298167772811023720269200000000000000000000,-44100689041353300268255096326493074700000000000000000000,1048379566158584808229745002800791277000000000000000000000,-43736838372828632078777403303959025800000000000000000000,1004184657206954623110246444543507611800000000000000000000,-29459339401903519692686223365125658600000000000000000000,891014198961810449009716950326038925200000000000000000000,-8492681797833342766219483919319396800000000000000000000,833675048581485631465739809658478320700000000000000000000,5630531282109640872481350266025091500000000000000000000,830859085726035290638427899126732629700000000000000000000],
  ![376250556609470068345860772540495649500000000000000000000,-708272503609826921574335117396425368600000000000000000000,51390392755277404482884429165358150900000000000000000000,-54651881498642307943341550361097319700000000000000000000,-20291902892636591778994404125528542700000000000000000000,-55277014441743378685805205133095732900000000000000000000,432642865707251737588357201491625500000000000000000000,-63333904061936630076669660934692102200000000000000000000,464418026228152298798119283599791900000000000000000000,-63463618776321337244492203694407732700000000000000000000,1000001628206867998970313556841665522997800000000000000000000,-59631845359536436951181826101612254000000000000000000000,1533657759052520614650968408182621400000000000000000000,-58037460123768120958375291250123809300000000000000000000,576935124442761262881245573266145200000000000000000000,-54689525071690251173663115234956750000000000000000000000,-763149317984146734354449625885666100000000000000000000,-54944045796758031353757257883185301100000000000000000000,-1639653644451750253854380807254954600000000000000000000,-57357956547159547615957686937585166600000000000000000000],
  ![1680595948887393849565700515132282570500000000000000000000,-3174813683288067751347032445357464174100000000000000000000,214468999024631274482227076352482724400000000000000000000,-267943556644926352422399902154232165400000000000000000000,-109749188561178857096582434838769729300000000000000000000,-288188391936581679117314172698551422500000000000000000000,-17687868448439207128925209814188420500000000000000000000,-384686734986616088465640302872915192800000000000000000000,-13735542285940960675678916798944765600000000000000000000,-421053309177290653754698995274510323200000000000000000000,-201644125222941049307476691656749300000000000000000000,999560635135568564602133490964922617050900000000000000000000,2437560284914344056615091001167391600000000000000000000,-438188741612430738051495010512326685400000000000000000000,6803128815771158658990728669109062000000000000000000000,-423140313087656966746092678636182405600000000000000000000,7156244809127925038493991419344867200000000000000000000,-401367530362630676248625657066359824900000000000000000000,5791022401418414670005910903840965500000000000000000000,-388242634279627924690761695955460327300000000000000000000],
  ![-213066531531668279714620593685520536100000000000000000000,401506397100806371100030252294484224000000000000000000000,-28359000403919896723363138910154180600000000000000000000,32019482318513848095337019667203683000000000000000000000,12465595598733434804471060744189796600000000000000000000,33246665918590265911075309368679626800000000000000000000,892791159925957962340578728698279300000000000000000000,41107142505521965849482962876712188300000000000000000000,742357159866427285151095052016930900000000000000000000,43348287523154484714116541158848489100000000000000000000,-329175491012690383388002790003096700000000000000000000,43625148172088363651505615108120767600000000000000000000,999999553486760757110409197891955607821900000000000000000000,43230411339116194301426841436997630100000000000000000000,-420452382132628697329211578195737400000000000000000000,41815609352938969762673720444823091300000000000000000000,-69810375470958573026257298466261800000000000000000000,41027359883204638815916658766405519500000000000000000000,247385699346820042327762759117045700000000000000000000,41198355404412284764178137078313115200000000000000000000],
  ![180605145766286657958915857107666876700000000000000000000,-337999705198966329488472174176542844100000000000000000000,27629116360099483501027072289856789100000000000000000000,-21722157748713526655802917440951241200000000000000000000,-5928947691565970655899736953483083300000000000000000000,-18571262479985389365697406426003903900000000000000000000,4419159057075277460683996458684694700000000000000000000,-9939968827553430188046991905776904500000000000000000000,3877765402855642701601192252405188700000000000000000000,-2058742326278584711449971180280432300000000000000000000,2936416202049901445568029403035441400000000000000000000,8654042002521866706922579165047680600000000000000000000,2276455086712735943435548977394270800000000000000000000,1000011269946235781793842586502211632812200000000000000000000,-93103615397776650052190852344371300000000000000000000,14617629172131552815080145097720928000000000000000000000,-2352170930943182070891610432187363700000000000000000000,10837465901435236255204000423773508100000000000000000000,-3523440894067374762365227834886104700000000000000000000,4906961221014249523367768851154934100000000000000000000],
  ![2618732624731002541758697697405233200000000000000000000,-4933284465024180710814471022601921100000000000000000000,343297132729526970211656811915419500000000000000000000,-397633926548409623528661556232539000000000000000000000,-161172022748125586207531856401191000000000000000000000,-419319395824741955987918683533933200000000000000000000,-24978031390655714081132657192823900000000000000000000,-549954297148548379960061309152183800000000000000000000,-24743514934834704734236870936369300000000000000000000,-607459967224756158661894395789011400000000000000000000,-10047661348303857451250937061700100000000000000000000,-656618606907967562523082284547263800000000000000000000,-7106860850267830378037918201228400000000000000000000,-665147192521091187177945636773956900000000000000000000,999999999057470549191237867745413244384800000000000000000000,-676389320381968837011311969620305200000000000000000000,2267665036209604884745954519717100000000000000000000,-673710901590669973391601504707691700000000000000000000,2886191083464137084903837175919300000000000000000000,-668355888675541726505783205477216100000000000000000000],
  ![-10222760669380545870630783669969282200000000000000000000,19252438807601229451051037181919644100000000000000000000,-1359588905537868592552698580448275600000000000000000000,1528301907573839957187320076661023700000000000000000000,602417317310841139233992459301710300000000000000000000,1589602006979654418767917025781424200000000000000000000,60182658497447985340425530475910800000000000000000000,2000205390912170375343691101524041000000000000000000000,58530292932903984155663632784199200000000000000000000,2148578260586811952345299937965080600000000000000000000,7976243654304292824297569759223300000000000000000000,2234193448687800205444194008006527200000000000000000000,721192201110487229745943583184900000000000000000000,2238280115721655939731200850823841700000000000000000000,-6664839855451388922996051431668600000000000000000000,1000002224959376281798618604328173299537800000000000000000000,-576405251520709822131579307361600000000000000000000,2211580926332692550674979329620860500000000000000000000,8011666335580386131963000170372400000000000000000000,2218561420443912119218560197860462500000000000000000000],
  ![136801284016940797826318301114302100000000000000000000,-257532187600920433809837882735797100000000000000000000,18362758724266264285427996133194800000000000000000000,-20200641590360084303099711351751100000000000000000000,-7843326682345150928625093122134400000000000000000000,-20823986631128075695150735653948100000000000000000000,-555712495637799491463285525736800000000000000000000,-25591830253243487463750998222278800000000000000000000,-555313418880622491018170328868800000000000000000000,-27095963578905399928577106294295700000000000000000000,53887606146187164428082540939300000000000000000000,-27649537730639015014531181781896500000000000000000000,120837950726543081690034598684600000000000000000000,-27558389498847966047469477403409200000000000000000000,114217179186313490004321167561000000000000000000000,-27142663360445340390892023722359800000000000000000000,999999999922338342345617829274897577800700000000000000000000,-27055966827433518635174404445572400000000000000000000,-256726791980299574216533984118100000000000000000000,-27386354717729652554113102825160200000000000000000000],
  ![1513915751250151382769067935765026800000000000000000000,-2849153429530718325337594625622703900000000000000000000,201159822461058122986556682561897400000000000000000000,-224974882001627171063754755764573000000000000000000000,-89933185493749285147814556260402300000000000000000000,-234459864246038653499415446894570300000000000000000000,-11813484671484335399692140168268200000000000000000000,-300824808249943067792336741786664500000000000000000000,-12631603847734621711339711627087400000000000000000000,-329737042773278093562462366022691500000000000000000000,-5694621182726853556278471552576800000000000000000000,-355478288528970475649803471747448500000000000000000000,-4494056012925396562946056906638200000000000000000000,-360546444448275217930051884335990600000000000000000000,-2200780238990193542569466638343500000000000000000000,-370215689511087893644796997410478300000000000000000000,-1069303997544846985329065559071300000000000000000000,999999625120352423990815554967274483401200000000000000000000,-834341795346961383863842561030300000000000000000000,-376715091391256638011199539056432800000000000000000000],
  ![85202366067208559476588521715940300000000000000000000,-160318988895245316743068990209991000000000000000000000,11373730867714082421890959813514400000000000000000000,-12585462820326483879808198455595300000000000000000000,-4992483887958045988337494042395500000000000000000000,-13057522478949566693312191199426600000000000000000000,-582026140115159050895858873753600000000000000000000,-16557007202342944383391184844903800000000000000000000,-632961129912048945391073835308100000000000000000000,-18021995687051578261025356314915600000000000000000000,-263861916293282610658396726359200000000000000000000,-19264930035314903579743805028445500000000000000000000,-206654176386787963616654605911100000000000000000000,-19498597389441607915666344379010900000000000000000000,-114782454073852429390275414968100000000000000000000,-19958139437460523386669091232226000000000000000000000,-89498480393166570180534902453300000000000000000000,-20251999607266858275099228771595500000000000000000000,999999999902407353484363370880210361960900000000000000000000,-20436111109213172158001436942484200000000000000000000],
  ![49036966131251416424729655418757200000000000000000000,-92152236979070863917287194853741800000000000000000000,6520991436361714754055269726854000000000000000000000,-7178395008908573937072976835713800000000000000000000,-2934969605427308562042909752720700000000000000000000,-7490841664273710607039351986282600000000000000000000,-531977182772724158056692371771500000000000000000000,-9902946030847419680033192380746400000000000000000000,-624837414874030074805230747103200000000000000000000,-11208247377537147793947722081997100000000000000000000,-444987553364041562748324900284000000000000000000000,-12774786930294279228504241363532300000000000000000000,-404343459872178006247242660582100000000000000000000,-13199305829616712643344306385655900000000000000000000,-276902847655701336769309548578600000000000000000000,-14226101133494784620519557027415000000000000000000000,-130876356692957550610087705552300000000000000000000,-14840551023269826292179806727544400000000000000000000,-34334807358219756749841430002400000000000000000000,999999984995503594037126518864546968609100000000000000000000]]
def plusApproxNum : Fin 20 → Fin 20 → ℤ :=
  ![![1393025059208167059064840538935162448086400000000000000000000,127701192221473847671136921704418870111800000000000000000000,-54928708377421126634675321704601669571600000000000000000000,258880792351218567896446159623184466551500000000000000000000,-36746830235669428904068552185246316307700000000000000000000,212421809528689233823816125285645940093100000000000000000000,-26547943466861388670647598141370742952500000000000000000000,123097048039438823152949172289121990567500000000000000000000,-16446924405371259967469473980296680955200000000000000000000,80233177751462614014924558372032413597700000000000000000000,-8284047067174460803969536678744131129900000000000000000000,45335963880886241364483304692181632595800000000000000000000,-7048492375740389650807381326932922716300000000000000000000,37706868090735204231956897306998816966100000000000000000000,-5102844746338690483629282153297495160800000000000000000000,19952570200257495121969799878465981078500000000000000000000,-4425861777606716405513363626850950939800000000000000000000,5869801740621695603777116852395073831400000000000000000000,-4376298207370634421772032811102682071300000000000000000000,-2885133509361673023886884608901504871100000000000000000000],
  ![520654817579173108190723838874917540884700000000000000000000,621599376641549516183592757571564023711200000000000000000000,3848531073949391312588070047639015023100000000000000000000,199704381989180242481902291711788448715800000000000000000000,-42001572317397555068875018494584151906400000000000000000000,167684534129570512815113221128294867852600000000000000000000,-19490408138098771292873582121838859563200000000000000000000,94785606756228769074374312777882516931500000000000000000000,-12816322420610718393940768983127078275300000000000000000000,61810582143622760633664411418062292647000000000000000000000,-6279109651419072247199503856206684056200000000000000000000,34977148240790691548526030468736035176800000000000000000000,-5300071734984512416663907636810686935800000000000000000000,29216922119629121016737654980991853797500000000000000000000,-3750712062719658403501570011331407602300000000000000000000,16011307251907235896619315318897915468500000000000000000000,-3181795323580107583644199881993501972700000000000000000000,5770816814504415117606995157199773395200000000000000000000,-3097096353204073797087937801708000739500000000000000000000,-474776614410712176483340231206441599900000000000000000000],
  ![311031760448952017335006833964320006345800000000000000000000,266451798197550400456479264825211678884100000000000000000000,969895307787651995210915632925341155808300000000000000000000,555526182726964728649455871288836149298800000000000000000000,-80183350388056793434955520226378119392300000000000000000000,493261118660291352232190536816885958417800000000000000000000,-63992417429385262561196245639723509382600000000000000000000,258246795827275620042215218366266416807300000000000000000000,-35425715741208324491297725818539289400400000000000000000000,160163934287896338190717195573724601340400000000000000000000,-15030939650971153283943636949223141678100000000000000000000,90460313506767415523636579038692171048700000000000000000000,-12115735552582271418609806059610757044200000000000000000000,76977179674688217215132364170537511835400000000000000000000,-7475164849707692429200962128740227589700000000000000000000,48645602535766847410994456167082152621100000000000000000000,-5436322429503777523094960565707718355300000000000000000000,29642780919418456786423730083233397845300000000000000000000,-4655840089164240883529838684197408225400000000000000000000,19598708206067241174908705003261090344100000000000000000000],
  ![876918815226574970484028044275687773135300000000000000000000,430053304153413149176709650884394681885700000000000000000000,105165864078435633703499085637458877727700000000000000000000,2404246053904486532522553938535501737948800000000000000000000,-75613039325467308213201646224016839586800000000000000000000,1407362267586794789191765261470156649285400000000000000000000,-186414038804488821851509877580257198683900000000000000000000,904996593841562407865848198729136021172600000000000000000000,-120552408669588527022651904820711725978800000000000000000000,596403426996190654663399959541909577550000000000000000000000,-60163377969233355162479535198740634904400000000000000000000,340922906888823457672075367508903023777200000000000000000000,-50843748690125608149111148835974222753800000000000000000000,285696213939592892299734139808354917620300000000000000000000,-35959391135644609101419921617157004890800000000000000000000,158985436241923856196746059129400298736200000000000000000000,-30318747611241713160131748087841895185900000000000000000000,61054587747677689841634580970401232423400000000000000000000,-29294276903465375459759876600969321591700000000000000000000,1744568839554417306379467158243589446200000000000000000000],
  ![-118207403353290808625097010331402722363700000000000000000000,-94590717605793701059865796311845936659300000000000000000000,3447061311394328363183358721234967012000000000000000000000,-213253342874903921063778349394179713670100000000000000000000,1024425807894256520515251926469085529469300000000000000000000,-196915009791679320701665381408733409846100000000000000000000,26203953709940982515530850130481063392400000000000000000000,-111477015710772180505427055060794883451100000000000000000000,15492647422068794718353183585505345052500000000000000000000,-69867668878431069778372084764664363712600000000000000000000,6421166455227497862986924905044980050500000000000000000000,-39370817417344807756689376257389657449800000000000000000000,5031942205200293659614977737168282916900000000000000000000,-33685979570695393119318727871510230985500000000000000000000,2798545077681887176275287679054790642100000000000000000000,-22441901336970633235409202523918804917000000000000000000000,1784875532516796939419038706090213710600000000000000000000,-15730759781867133918841775235604960521600000000000000000000,1357288818902597401483353893217144240200000000000000000000,-12607003347276376571853221290949515589500000000000000000000],
  ![111326902791913367651299141919207650638000000000000000000000,155111868296740189874710193067850354410800000000000000000000,-50930773630245272778039794799187772827400000000000000000000,228471946009569587020802196240112304905000000000000000000000,-68392562732296335439784020327780494071100000000000000000000,1164556212103869820641187004974638969492500000000000000000000,-30649344126957822964131411802856399338000000000000000000000,10822078165512161067958371927005411943600000000000000000000,-7926677819340041825589139048292664876000000000000000000000,-25622030333630570234037788709747194239900000000000000000000,3859458203718613219516773241251644181000000000000000000000,-26876908642028442248571498262062106631000000000000000000000,4875939919697087368675405127919826131800000000000000000000,-22454437332345807537580200157616680685600000000000000000000,5917884846271040155449833853512567141600000000000000000000,-5882550678432037528003792080450179297500000000000000000000,6468469677183049270652071974729440503300000000000000000000,12652196244425333323507687072787855790700000000000000000000,7061519214636118267368226364726715062600000000000000000000,26134759241382040614803786043302402010600000000000000000000],
  ![2687215258361298543491176346070293762900000000000000000000,1986760086237358808317775761006848652000000000000000000000,169055086366293962023091164914721564200000000000000000000,4913533832784327904535030646646346854400000000000000000000,-275263213606814812682010321696213884000000000000000000000,4813104734973744192499265467496258844500000000000000000000,999539061021880524183117301749563916293000000000000000000000,3534724718359839864722489918283652139900000000000000000000,-334492030499983668435096251703693515800000000000000000000,2734676528252110756193041178394812622400000000000000000000,-209555324847541700369016041644851357900000000000000000000,1945182161503209716487428855313236493300000000000000000000,-185285005095665373905890098152650444000000000000000000000,1748161834597386901488274797573038194800000000000000000000,-131890430841183887729299636743126831200000000000000000000,1277961399444341369754955736042049575000000000000000000000,-95857591192832675840253251193400770200000000000000000000,939741638904142582182241777297152405900000000000000000000,-78081635388372652000786294195858679200000000000000000000,766435170585105552465158086695248129100000000000000000000],
  ![-5711149797287258087958324408005092781100000000000000000000,-4797039777314492824315810747299676733800000000000000000000,120861077037702718765675366592927639600000000000000000000,-10656816978875543642556431101649303730400000000000000000000,1145386958858152006586000848325889763200000000000000000000,-9907508290329697279151680985464402975200000000000000000000,1382174650009430776691027767695811599500000000000000000000,994315186329885536736732379301179293398500000000000000000000,903542729287529875062641564346071366200000000000000000000,-3383942363549816727342178197703436780000000000000000000000,364489933540047497918436314568768889800000000000000000000,-1569695259253257897267723637739852652200000000000000000000,252958019728300262886103760381856349100000000000000000000,-1263177709763688051573920936504989912300000000000000000000,42115254020460206046206366981036397700000000000000000000,-858646730455489788251840454001896678400000000000000000000,-60102846453405827993105103160810386200000000000000000000,-903381816428230134676674796721612126700000000000000000000,-99415637621551056874015097877898332800000000000000000000,-1065384205215076466257085195941569372800000000000000000000],
  ![259281360804320414996321709373744194200000000000000000000,183107447247409062350854873265206979000000000000000000000,26784356574972867363503366265737210500000000000000000000,473945361628504486870866110680602847000000000000000000000,-12807615672866341957977897892581123500000000000000000000,476588753906538897238233892280051525300000000000000000000,-28152737029951733882682372206463118300000000000000000000,400344579422381567121447736699849480400000000000000000000,999980738357297772926063786874679958632000000000000000000000,353105021364772772268998080830837088800000000000000000000,-16157644183508915644030043976941351800000000000000000000,302952604935697054251186276059788973500000000000000000000,-16757064663931037440955182046370032600000000000000000000,286511726139218874342951178569666129600000000000000000000,-18227658421243077250059199942364882600000000000000000000,233646350170038904182907089747816921900000000000000000000,-17897353882922448835936488939791491500000000000000000000,179038937412462583453679762662273982300000000000000000000,-16920085813707584580529049756505563500000000000000000000,144145281902401965551081128914519372900000000000000000000],
  ![-2319159918380433663366027902023568571300000000000000000000,-1795984861454023703073424601642753548200000000000000000000,-104256750581884016681831679636576342000000000000000000000,-4296842959362257573973416330586379084300000000000000000000,278119472193316766691003094877274550900000000000000000000,-4167015401870223408910411384068006656200000000000000000000,401015756835197030175373459733127329800000000000000000000,-3000092290561823910102120764210717365300000000000000000000,275439310025919933563533441230821985400000000000000000000,997678642003466437367091577166847914683800000000000000000000,160588618374741865385156259099902317900000000000000000000,-1694259871672378227293169838678554137000000000000000000000,139669864153922941491225938780469888100000000000000000000,-1544510437248390806815196654161616768000000000000000000000,93764935852624350694300443916000849100000000000000000000,-1198742394016196275791783623401339747800000000000000000000,60838599643379769317050598441742302000000000000000000000,-969393301057882249617659647950639140500000000000000000000,44014580386420341246711459481425051600000000000000000000,-865142518277830688179585736188022436800000000000000000000],
  ![135986956131567343012411246409793740800000000000000000000,108315044390110002629218119306243216400000000000000000000,4499643369962986300562109480543594100000000000000000000,253990008650288201331622209334420767200000000000000000000,-17975589416036684072682261876111109200000000000000000000,244662251266642385825909818633472455000000000000000000000,-23974813889126126247315902308548886900000000000000000000,173031559470726276725302748886343857500000000000000000000,-15885093538041295430992590645703394700000000000000000000,133072487050841722961380778638932373800000000000000000000,999991429094358610800775354919565150164500000000000000000000,98119888635277805420155516814950582500000000000000000000,-7260498181866747137167983180694144900000000000000000000,90229399057550646927297554710335488900000000000000000000,-4430284091284409782182923330698317900000000000000000000,72970406177981751724703105153453362900000000000000000000,-2383511386443393492552814007383354000000000000000000000,62901717596375901258145575232037872300000000000000000000,-1351087957753646339641222017352756500000000000000000000,59211658852597259464792136086544454100000000000000000000],
  ![673462543520266477052329073061050303100000000000000000000,523060617264300008837090263770774988200000000000000000000,35307186410906425881937732818544222700000000000000000000,1254506481513786706225401061086244866300000000000000000000,-72583976550856792673674320702557803500000000000000000000,1223368589356249597303423991790462067200000000000000000000,-99913284554534594099480988766310014600000000000000000000,922850556766217386792535739201800806700000000000000000000,-62085563777864519602305864709575233600000000000000000000,760889614834734560832634811400131578000000000000000000000,-33610238195429057897155026527719182800000000000000000000,1000626832655973710398662456464909058348900000000000000000000,-30259739762035655799921851745190343200000000000000000000,595031218680383621612384723012410627400000000000000000000,-25423077963383098947177279633693032100000000000000000000,512581384248404273489258258433012775600000000000000000000,-22296330013594268177324484412595299600000000000000000000,441029564364939311578157614191911651600000000000000000000,-20138500111835537970154053070955601000000000000000000000,398577826142024200008688409741021042300000000000000000000],
  ![-79913917893629737545886945578329369900000000000000000000,-63114342246284625265859406564723652000000000000000000000,-3284170654618591595713411033377097500000000000000000000,-149238622765481304813336242677681941100000000000000000000,9725607385464137547398244436183369500000000000000000000,-144509054926387640183384303557967522500000000000000000000,13000509539564105956056956460183841800000000000000000000,-105377818505011538271228929943809487300000000000000000000,8301043046200904307119359199169559500000000000000000000,-84050892826651343734593121436331680700000000000000000000,4384757536877946036759905438006412300000000000000000000,-66109051012474784748480188491582841600000000000000000000,1000003788549100724810338373567638277553500000000000000000000,-62038259051565745171906161983990824900000000000000000000,2664395371424897128550567872098493900000000000000000000,-52513978791643159282534218204732379600000000000000000000,1899174690642555773040786936348966600000000000000000000,-45719041928023060316525575169234386800000000000000000000,1489337101932288776674966789146208700000000000000000000,-42343378402832550677151313023424577600000000000000000000],
  ![52873820228897540241214094650966797600000000000000000000,44541371113120493302636271500265091300000000000000000000,-805457184543791562786604963292913500000000000000000000,99176971922022345402736999882334037200000000000000000000,-10267572923126219402253645335164670000000000000000000000,92574939825310433475269196124383729400000000000000000000,-13359948571414235267462845523057665700000000000000000000,53500539897293088322129050380621816200000000000000000000,-9967707388247414304570480820229188400000000000000000000,30023544625446135167065668594669713700000000000000000000,-5741868384109743140449842472307107000000000000000000000,6893109661611325880899230395320413700000000000000000000,-4603897132942072799816367167060657300000000000000000000,1000001725713215267462685839264576947248500000000000000000000,-1492337301328845010095305105521864600000000000000000000,-7310670252905954809796014194683328500000000000000000000,1044997551597328662337352549688307300000000000000000000,-7797963183644802230794332344172878300000000000000000000,2272873184492421758424172251766002000000000000000000000,-4411279650385145620731448690519739300000000000000000000],
  ![990980976177682442683559524243602700000000000000000000,782987444765410944650885372844484700000000000000000000,45126424726208638227142478851533100000000000000000000,1855448245781384772078597753079800500000000000000000000,-113866817185369817037836045988171100000000000000000000,1802355875394090065999062735475263600000000000000000000,-148016334319806393838461511301257300000000000000000000,1347570311695434719083186192497815600000000000000000000,-87555209712749404662270554370300800000000000000000000,1112071404023864488751436703063420900000000000000000000,-40204452680114408812985818630802800000000000000000000,935218924447673777549864740849243200000000000000000000,-34282996844058285073613965866620000000000000000000000,898209608917943155983478022557554000000000000000000000,999999973179423415918685338980948876666500000000000000000000,809069614494710526298665331451551200000000000000000000,-24885371080850245534167068754640200000000000000000000,732099401797583272022387878640819600000000000000000000,-24347697106639031153492955882641600000000000000000000,682905257332751078719001848870264100000000000000000000],
  ![-3806315123000671820754055444006069900000000000000000000,-3016270197450624965980536077516405100000000000000000000,-157401205977492520101029493203701000000000000000000000,-7121592766930500923190959874361617900000000000000000000,459257469748618388422917469131835100000000000000000000,-6898544977063367940336123770935923300000000000000000000,602473376141107888988118552977435700000000000000000000,-5066407063629842897814169689838287700000000000000000000,372946492641393180969273344696347500000000000000000000,-4090375184427680324829527302646250400000000000000000000,185500033510536645349066174717562000000000000000000000,-3306803475414128281516781122373212900000000000000000000,158714866078795236380357424564462600000000000000000000,-3135519697226161504516696132917913200000000000000000000,113723100002016234805971644228349500000000000000000000,999997264685373828147159649045300316769600000000000000000000,87864285060230186220959852296862500000000000000000000,-2435343292822576532198976994872057300000000000000000000,74861068586617897263638607766539400000000000000000000,-2273090004509884909941945109494713000000000000000000000],
  ![50250165578174132887251920018645700000000000000000000,39948338956764723416948721615082000000000000000000000,1938128805249290908767943392532800000000000000000000,94034520836249998870901566561802200000000000000000000,-6242683184875904452927530190062400000000000000000000,90927032350179052729886218390477300000000000000000000,-8180460398976887340944268997642800000000000000000000,66118221841088909030948359096581100000000000000000000,-5145728928396250552371780616230400000000000000000000,52778633358863965295378257610151300000000000000000000,-2613748872029530021524234599366600000000000000000000,41840778612610472346185391829435300000000000000000000,-2231047043024232138826388873121200000000000000000000,39428923461971862965020819532366600000000000000000000,-1532245221830296863430405259999100000000000000000000,33890681470083317162271151557486200000000000000000000,999999998920815019975449064992503399033700000000000000000000,30006853929409066550724451153283600000000000000000000,-842053677398861958583100809788400000000000000000000,28093900058913324643930051948999900000000000000000000],
  ![558918465106164369597684185276154200000000000000000000,444661582126520011861837361718886300000000000000000000,23286869626258574909294002376467600000000000000000000,1048066547261497264495530114417218200000000000000000000,-66774554942961355345205012722466600000000000000000000,1015689859663855356104464107433538200000000000000000000,-85652562518493522036264070975749300000000000000000000,751941551469104574336345926203122600000000000000000000,-50855980025815832806703977500800100000000000000000000,615420660460234208428723343470104200000000000000000000,-22769635540290628253273677185934900000000000000000000,513279758172913901005421183036687000000000000000000000,-18962243802568692734176397355382700000000000000000000,492547405613468045843168155664463500000000000000000000,-13551016808517614063866253081090000000000000000000000,445296189646811648466721982512610800000000000000000000,-11775128992804256470930759318524600000000000000000000,1000000407790486379617549027022091488471300000000000000000000,-11361264088614740971815158388470200000000000000000000,384722245353698591586666553482658700000000000000000000],
  ![31249363178715523060891905486759000000000000000000000,24899277263437916382359272149585100000000000000000000,1258452773534575527912477945668100000000000000000000,58600939914213871670909889842251000000000000000000000,-3790018750248176581740134235715900000000000000000000,56739762372788767138452287778886100000000000000000000,-4863462048089345378153651547221700000000000000000000,41792980575596633392002432129367900000000000000000000,-2918026345159210334356056269916300000000000000000000,34008948471675173599484944983910800000000000000000000,-1329286987133356626782758347549800000000000000000000,28096999734431000592934977626284000000000000000000000,-1106424810595135206424044372758700000000000000000000,26886484017572199955129872688358600000000000000000000,-767327648713386689510926938199000000000000000000000,24159035927215486639878250409224300000000000000000000,-630007654332452653482123029961700000000000000000000,22091032952659779016459778211133100000000000000000000,999999999414293926050886376290079534933500000000000000000000,20879978352224189896044020632891000000000000000000000],
  ![17740445137132513392665066383776700000000000000000000,14236458119826561148008745272747700000000000000000000,736207368338463115143673126407400000000000000000000,33414800008054131007110834672775000000000000000000000,-2096782015500165697473150059368100000000000000000000,32394077503620615606485682023203000000000000000000000,-2570676221047375234431724622622900000000000000000000,24281667235644494600090795066805000000000000000000000,-1398949624174680445901385984007700000000000000000000,20315513034670739418172245008355500000000000000000000,-462472154713170912269353536695600000000000000000000,17805499622063523176261863750374000000000000000000000,-343534177315003967648464090966800000000000000000000,17407442097527417616642109107338500000000000000000000,-225512419480207097170227758425500000000000000000000,16619087851382901937796227455497200000000000000000000,-278966371358918193751428356568600000000000000000000,15888249566093437526870572533385300000000000000000000,-354902222595586584331640508815500000000000000000000,1000000015257464400659643883145034411879400000000000000000000]]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real

lemma mul_exp_neg_le {x y δ : ℝ} (hx : 0<x) (hxy : x≤y) (hδ : 1≤δ*x) :
    y*exp (-δ*y)≤x*exp (-δ*x) := by
  have hx0 : x≠0 := ne_of_gt hx
  have hr : y/x≤δ*(y-x)+1 := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hδ)]
  have he : y/x≤exp (δ*(y-x)) := hr.trans (add_one_le_exp _)
  calc
    y*exp (-δ*y) = (y/x)*(x*exp (-δ*y)) := by field_simp
    _ ≤ exp (δ*(y-x))*(x*exp (-δ*y)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = x*exp (-δ*x) := by
      rw [mul_left_comm,←exp_add]
      congr 2
      ring

lemma sqrt_prefactor_identity {x a p c d δ : ℝ} (hx : 0<x) :
    (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) =
      (a/sqrt x+p*sqrt (c/x+d))*(x*exp (-δ*x)) := by
  have hs : sqrt x≠0 := ne_of_gt (sqrt_pos.mpr hx)
  have he : c/x+d=(c+d*x)/x := by field_simp
  rw [he,sqrt_div' _ hx.le]
  have hh := sq_sqrt hx.le
  field_simp
  rw [hh]
  ring

lemma sqrt_exp_antitone {x y a p c d δ : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hp : 0≤p) (hc : 0 ≤ c) (hδ : 1≤δ*x) :
    (a+p*sqrt (c+d*y))*sqrt y*exp (-δ*y) ≤
      (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) := by
  have hy : 0<y := hx.trans_le hxy
  rw [sqrt_prefactor_identity hy,sqrt_prefactor_identity hx]
  have hfactor : a/sqrt y+p*sqrt (c/y+d) ≤ a/sqrt x+p*sqrt (c/x+d) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_left ha (sqrt_pos.mpr hx) (sqrt_le_sqrt hxy)
    · apply mul_le_mul_of_nonneg_left _ hp
      apply sqrt_le_sqrt
      simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_left hc hx hxy) d
  exact mul_le_mul hfactor (mul_exp_neg_le hx hxy hδ) (by positivity) (by positivity)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def jetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t))*
    Real.sqrt (Xwave k t)/Q n*Real.exp (-Real.pi*(k*Xwave k t-v)*n)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def frequencyDistance (l : Fin 31) : ℕ := Int.natAbs ((l.val:ℤ)-15)
def fullTailW (i : Fin 15) (d : Fin 2) : ℝ :=
  if d.val=0 then Real.pi^2/18^2 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then
      ((frequencyDistance l:ℝ)-i.val-1/2)*‖fourierCoeff l‖ else 0
  else Real.pi/18 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then ‖fourierCoeff l‖ else 0

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma continuous_intervalIntegral_complex {f : ℂ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℝ) :
    Continuous (fun s => ∫ t in a..b, f s t) := by
  have h₁ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  have h₂ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := b) (b := a))
  simpa only [intervalIntegral, integral_Icc_eq_integral_Ioc] using! h₁.sub h₂

lemma exponential_first_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    I*Real.pi * (∫ r in (0:ℝ)..t, exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1)/u := by
  have hc : I*(Real.pi:ℂ)*u ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  have hi := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, exp_zero] at hi
  simp_rw [show ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = (I*Real.pi*u)*(r:ℂ) by intro r; ring]
  rw [hi]
  field_simp

lemma exponential_second_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    -(Real.pi:ℂ)^2 * (∫ r in (0:ℝ)..t, ((t:ℂ)-r)*exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1-I*Real.pi*(t:ℂ)*u)/u^2 := by
  let c : ℂ := I*Real.pi*u
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  let F : ℝ → ℂ := fun r => (((t:ℂ)-(r:ℂ))/c+1/c^2)*exp (c*(r:ℂ))
  have hd (x : ℝ) : HasDerivAt F (((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) x := by
    have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    have hf := ((hx.const_sub (t:ℂ)).div_const c).add_const (1/c^2)
    have hh := hf.mul ((hx.const_mul c).cexp)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) volume 0 t from
      (by fun_prop : Continuous (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ)))).intervalIntegrable 0 t)
  have he : ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = c*(r:ℂ) := by intro r; dsimp [c] <;> ring
  simp_rw [he]
  rw [hi]
  dsimp [F]
  simp only [sub_self, zero_div, zero_add, mul_zero, exp_zero,
    mul_one, sub_zero]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  ring

def integralDBasis (n : Node) (s : ℂ) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (I*Real.pi * ∫ t in (0:ℝ)..frequency l, exp (I*Real.pi*(t:ℂ)*(s-n.val)))

def integralCBasis (n : Node) (s : ℂ) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (-(Real.pi:ℂ)^2 * ∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (I*Real.pi*(t:ℂ)*(s-n.val)))

lemma continuous_integralDBasis (n : Node) : Continuous (integralDBasis n) := by
  unfold integralDBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma continuous_integralCBasis (n : Node) : Continuous (integralCBasis n) := by
  unfold integralCBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma exp_frequency_sub (s n : ℂ) (l : Fin 31) :
    exp (I*Real.pi*frequency l*n) * exp (I*Real.pi*frequency l*(s-n)) =
      exp (I*Real.pi*frequency l*s) := by
  rw [← exp_add]
  congr 1
  ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev Spectrum := Set.Icc (-(5/6):ℝ) (5/6)

def coeffAbs (l : Fin 31) : ℝ := ‖fourierCoeff l‖
lemma fourierCoeff_norm (l : Fin 31) : ‖fourierCoeff l‖ = coeffAbs l := rfl
def dVariation : ℝ := (∑ l : Fin 31, coeffAbs l * |frequency l|)*Real.pi
def cVariation : ℝ := (∑ l : Fin 31, coeffAbs l * (frequency l)^2)*Real.pi^2/2

 def extend (f : C(Spectrum,ℂ)) (t : ℝ) : ℂ := f (Set.projIcc (-(5/6)) (5/6) (by norm_num) t)
lemma continuous_extend (f : C(Spectrum,ℂ)) : Continuous (extend f) := by
  exact f.continuous.comp continuous_projIcc
lemma norm_extend_le (f : C(Spectrum,ℂ)) (t : ℝ) : ‖extend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

def spectralC (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (-(Real.pi:ℂ)^2 * ∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

def spectralD (n : Node) (f : C(Spectrum,ℂ)) : ℂ :=
  ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) *
    (I*Real.pi * ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t)

lemma norm_exp_phase (t : ℝ) (n : ℤ) : ‖exp (I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_exp_neg_phase (t : ℝ) (n : ℤ) : ‖exp (-I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_first_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, f r‖ ≤ M*|t| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => hM r) (a := 0) (b := t)

lemma norm_second_integral_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖∫ r in (0:ℝ)..t, ((t:ℂ)-r)*f r‖ ≤ M*t^2/2 := by
  by_cases ht : 0 ≤ t
  · calc
      _ ≤ ∫ r in (0:ℝ)..t, (t-r)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hr.2)]
            exact mul_le_mul_of_nonneg_left (hM r) (sub_nonneg.mpr hr.2)
        · exact (show Continuous (fun r : ℝ => (t-r)*M) by fun_prop).intervalIntegrable 0 t
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun _ : ℝ => t) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _), integral_id]
        simp only [intervalIntegral.integral_const, sub_zero, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring
  · have ht' := le_of_not_ge ht
    rw [intervalIntegral.integral_symm, norm_neg]
    calc
      _ ≤ ∫ r in t..(0:ℝ), (r-t)*M := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht'
        · exact ae_of_all volume fun r hr => by
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr hr.1.le)]
            calc
              _ ≤ (-(t-r))*M := mul_le_mul_of_nonneg_left (hM r) (by linarith [hr.1])
              _ = _ := by ring
        · exact (show Continuous (fun r : ℝ => (r-t)*M) by fun_prop).intervalIntegrable t 0
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => t)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id]
        simp only [intervalIntegral.integral_const, zero_sub, zero_pow, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, smul_eq_mul]
        ring

lemma spectralD_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralD n f‖ ≤ dVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤ ‖f‖*|frequency l| := by
    apply norm_first_integral_le
    intro t
    rw [norm_mul,norm_exp_neg_phase,one_mul]
    exact norm_extend_le f t
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * |frequency l|) * (Real.pi*‖f‖) := by
      unfold spectralD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
      calc
        _ ≤ coeffAbs l * (Real.pi * (‖f‖*|frequency l|)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [dVariation] <;> ring

lemma spectralC_bound (n : Node) (f : C(Spectrum,ℂ)) :
    ‖spectralC n f‖ ≤ cVariation*‖f‖ := by
  have hb (l : Fin 31) : ‖∫ t in (0:ℝ)..frequency l,
      ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t‖ ≤
      ‖f‖*(frequency l)^2/2 := by
    have hi := norm_second_integral_le (fun t => exp (-I*Real.pi*(t:ℂ)*n.val)*extend f t) ‖f‖
      (fun t => by rw [norm_mul,norm_exp_neg_phase,one_mul]; exact norm_extend_le f t) (frequency l)
    simpa only [mul_assoc] using hi
  calc
    _ ≤ ∑ l : Fin 31, (coeffAbs l * (frequency l)^2) * (Real.pi^2/2*‖f‖) := by
      unfold spectralC
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_mul,norm_exp_phase,fourierCoeff_norm,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      calc
        _ ≤ coeffAbs l * (Real.pi^2 * (‖f‖*(frequency l)^2/2)) := by
          have hp : 0 ≤ coeffAbs l := by rw [←fourierCoeff_norm]; positivity
          gcongr
          exact hb l
        _ = _ := by ring
    _ = _ := by rw [←Finset.sum_mul]; dsimp [cVariation] <;> ring

def integralLinear (w : ℝ → ℂ) (hw : Continuous w) (t : ℝ) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ r in (0:ℝ)..t, w r * extend f r
  map_add' f g := by
    simp only [extend,ContinuousMap.add_apply,mul_add]
    apply intervalIntegral.integral_add
    · exact (hw.mul (continuous_extend f)).intervalIntegrable 0 t
    · exact (hw.mul (continuous_extend g)).intervalIntegrable 0 t
  map_smul' c f := by
    simp only [extend,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (w _) c]
    exact intervalIntegral.integral_const_mul _ _

def spectralCLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (-(Real.pi:ℂ)^2)) •
    integralLinear (fun t => ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

def spectralDLinear (n : Node) : C(Spectrum,ℂ) →ₗ[ℂ] ℂ :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n.val) * (I*Real.pi)) •
    integralLinear (fun t => exp (-I*Real.pi*(t:ℂ)*n.val))
      (by fun_prop) (frequency l)

lemma spectralCLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralCLinear n f = spectralC n f := by
  simp [spectralCLinear,spectralC,integralLinear,mul_assoc]
lemma spectralDLinear_apply (n : Node) (f : C(Spectrum,ℂ)) :
    spectralDLinear n f = spectralD n f := by
  simp [spectralDLinear,spectralD,integralLinear,mul_assoc]

def spectralCCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralCLinear n).mkContinuous cVariation (by
    intro f; rw [spectralCLinear_apply]; exact spectralC_bound n f)
def spectralDCLM (n : Node) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  (spectralDLinear n).mkContinuous dVariation (by
    intro f; rw [spectralDLinear_apply]; exact spectralD_bound n f)

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

def phaseFunction (s : ℂ) : C(Spectrum,ℂ) :=
  ⟨fun t => exp (I*Real.pi*(t.val:ℂ)*s), by fun_prop⟩

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

def frequencyFunction : C(Spectrum,ℂ) := ⟨fun t => I*Real.pi*(t.val:ℂ), by fun_prop⟩

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma frequencyDistance_le (l : Fin 31) : frequencyDistance l≤15 := by revert l; decide +kernel
lemma frequencyDistance_eq (l : Fin 31) : |frequency l| = (frequencyDistance l:ℝ)*(1/18) := by
  fin_cases l <;> (first | (simp [frequency,frequencyDistance]; all_goals first | (norm_num [frequency,frequencyDistance]; done) | rfl | decide) | (norm_num [frequency,frequencyDistance]; done) | norm_num [frequency,frequencyDistance])
lemma range_sum_15 (N : ℕ) (hN : N≤15) (F : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i) = ∑ i : Fin 15, if i.val<N then F i.val else 0 := by
  rw [show (∑ i : Fin 15, if i.val<N then F i.val else 0) = ∑ i ∈ Finset.range 15, if i<N then F i else 0 by
    exact Fin.sum_univ_eq_sum_range (fun i => if i<N then F i else 0) 15,←Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range,Finset.mem_filter]
  omega
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def spectralCVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
      (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))
def spectralDVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n) • f t)
omit [CompleteSpace E] in
lemma spectralCVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralCVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 0 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ ≤
      (1/18:ℝ)^2 * ∑ i : Fin 15, if i.val<frequencyDistance l then
        ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0 := by
    have hh := IntegralVectors.weighted_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralCVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
          (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi^2*((1/18:ℝ)^2 *
        ∑ i : Fin 15, if i.val<frequencyDistance l then ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi^2 by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
omit [CompleteSpace E] in
lemma spectralDVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralDVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 1 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t‖ ≤
      (1/18:ℝ) * ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0 := by
    have hh := IntegralVectors.norm_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralDVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi*((1/18:ℝ) *
        ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_one,one_ne_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev JetVector := PiLp 1 (fun _ : Fin 2 => ℂ)
def jetVector (k v : ℝ) (n : ℤ) (t : ℝ) : JetVector :=
  WithLp.toLp 1 (fun d => jetMultiplier k v n d t)

def tailJetVector (k v : ℝ) (m n : ℤ) (c : Fin 2) : JetVector :=
  if c.val=0 then spectralCVector n (jetVector k v m) else spectralDVector n (jetVector k v m)
def tailJet (k v : ℝ) (m n : ℤ) (c d : Fin 2) : ℝ :=
  (tailJetVector k v m n c d).re
lemma finiteEndpoint (i : Fin 15) :
    frequency ⟨i.val+16,by omega⟩ = (i.val+1:ℕ)/18 := by
  unfold frequency
  push_cast
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma finiteNode_node (i : Fin 10) : 0<finiteNode i ∧ (finiteNode i)%36 ∈ residues := by
  revert i; decide +kernel
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.MatrixBounds
abbrev FiniteCoefficients := ℓ¹(Fin 20,ℝ)
lemma sum_fin20_pairs (g : Fin 10 → Fin 2 → ℝ) :
    (∑ i : Fin 20, g ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩) =
      ∑ n : Fin 10, ∑ d : Fin 2, g n d := by
  simpa only [finProdFinEquiv_symm_apply,Fintype.sum_prod_type,Fin.divNat,Fin.modNat] using
    ((finProdFinEquiv (m:=10) (n:=2)).symm.sum_comp (fun p => g p.1 p.2))
def Bkernel (i : Fin 20) (p : TailNode × Fin 2) : ℝ :=
  tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩
def Ckernel (p : TailNode × Fin 2) (i : Fin 20) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val+2,by omega⟩)
def Dkernel (p q : TailNode × Fin 2) : ℝ :=
  tailJet h h p.1.val.val q.1.val.val q.2 p.2
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
def beta : ℝ := 3/10^10
def delta : ℝ := 3/10^8
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Param
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

def Wstar : ℝ := 61/10000
def DeltaStar : ℝ := 18/100000
def Ustar : ℝ := 48/100000
def Pstar : ℝ := 3/10000000

def ParameterPolytope (e : Fin 8 → ℝ) : Prop :=
  ∃ z w delta u a r p : ℝ,
    0 ≤ z ∧ z ≤ Z ∧ 0 ≤ w ∧ w ≤ Wstar ∧ 0 ≤ delta ∧ delta ≤ DeltaStar ∧
    0 ≤ u ∧ u ≤ Ustar ∧ 0 ≤ a ∧ a ≤ Z*u ∧ 0 ≤ r ∧ r ≤ Pstar ∧
    0 ≤ p ∧ p ≤ Pstar ∧ e = ![z,1,Z*w-delta,w,a,u,r,p]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma box_linear_lower {B x c : ℝ} (_hB : 0 ≤ B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    B * min 0 c ≤ c*x := by
  by_cases hc : 0 ≤ c
  · rw [min_eq_left hc]
    simpa using mul_nonneg hc hx
  · rw [min_eq_right (le_of_not_ge hc)]
    nlinarith

lemma triangle_linear_lower {B Z u a v c : ℝ} (_hB : 0 ≤ B) (hu : 0 ≤ u)
    (huB : u ≤ B) (ha : 0 ≤ a) (haZ : a ≤ Z*u) :
    B * min 0 (min v (v+Z*c)) ≤ v*u+c*a := by
  let q := min 0 (min v (v+Z*c))
  have hq0 : q ≤ 0 := min_le_left _ _
  have hqv : q ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hqc : q ≤ v+Z*c := (min_le_right _ _).trans (min_le_right _ _)
  have hqu : B*q ≤ u*q := mul_le_mul_of_nonpos_right huB hq0
  change B*q ≤ _
  by_cases hc : 0 ≤ c
  · have h1 := mul_le_mul_of_nonneg_right hqv hu
    have h2 := mul_nonneg hc ha
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hqc hu
    have h2 := mul_le_mul_of_nonpos_left haZ (le_of_not_ge hc)
    nlinarith

def rowLower (row : Fin 8 → ℝ) : ℝ :=
  row 1 + Z*min 0 (row 0) + DeltaStar*min 0 (-row 2) +
    Wstar*min 0 (row 3+Z*row 2) + Ustar*min 0 (min (row 5) (row 5+Z*row 4)) +
    Pstar*(min 0 (row 6)+min 0 (row 7))
lemma rowLower_le (row e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    rowLower row ≤ ∑ j : Fin 8, row j*e j := by
  rcases he with ⟨z,w,d,u,a,r,p,hz,hzB,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,rfl⟩
  have h1 := box_linear_lower (by norm_num [Z] : 0 ≤ Z) hz hzB (c := row 0)
  have h2 := box_linear_lower (by norm_num [DeltaStar] : 0 ≤ DeltaStar) hd hdB (c := -row 2)
  have h3 := box_linear_lower (by norm_num [Wstar] : 0 ≤ Wstar) hw hwB (c := row 3+Z*row 2)
  have h4 := triangle_linear_lower (by norm_num [Ustar] : 0 ≤ Ustar) hu huB ha haB (v := row 5) (c := row 4)
  have h5 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hr hrB (c := row 6)
  have h6 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hp hpB (c := row 7)
  norm_num [Fin.sum_univ_succ, Fin.succ]
  change rowLower row ≤ row 0*z + (row 1 + (row 2*(Z*w-d) + (row 3*w + (row 4*a + (row 5*u + (row 6*r + row 7*p))))))
  unfold rowLower
  nlinarith [h1,h2,h3,h4,h5,h6]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma exp_neg_one_bound : Real.exp (-1) < 369/1000 := by
  have he := Real.exp_one_gt_d9
  rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma exp_parameter_mono {z : ℝ} (hz : 0<z) (hzB : z≤Z) {k : ℝ} (hk : 0≤k) :
    Real.exp (-k/z) ≤ Real.exp (-k/Z) := by
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div,neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hk hz hzB

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def A1AbsNumerators : Fin 23 → ℤ := ![440000000000000000000000000000000000000000000000000000000001,0,506577505428133277725966475437659806584283989084294867243756,302774817060523226008427819375140853579223338747880481900281,387457243193308200069636705474069589107674040706856315643116,258333268405700108415766990932050848493543155072123131754165,117474530319733233171216765313719887584341491266670302584683,267114984143389787040856194121942352815924686473407109538211,5867927195876975597649742368649551994382111264673349312243,12944987069239917597719635291971760783647267965868133639386,3152548882827220012091733562729852804240191957738578973085,5898957614123196260712065177997627471962474307313637191910,6657883877874406312434089197997863018342852833751586438255,6072657285660172563745517157184353641597379776984290457798,1303629711157254650064623395194376583059664981077272453465,23702296982889290892760129759822299069220097287315935232418,63954022032344962578190938607445857412929993400725542075,1528929237228086938660276170299412803686943689405875186396,129193445812548364138952264914196165139128456923010956072,882180701134836745429375233669978135228974937424221274178,30591020547536644027372479626744269335380118685516276292,615258605672107878598391040390489397249836382026702415079,6000000000000000000000000000000000000000000000000000000001]
def A2AbsNumerators : Fin 23 → ℤ := ![440000000000000000000000000000000000000000000000000000000001,0,454738816242940346172438066397940051888021288814472588570751,1369216078939506848957928799800550912466197839167609454312517,48680193988305558232813101436011536089534122008575612020381,231324924966709612485096049689756405659716613972249598433513,7826673288598839060198282850036124521734117670941668548790,107081442809825171995724041042623375755129300089963184788649,4147722486977679401690787571499073784427933809462713435724,7644904754493197779312564244221933208689987342527361008971,3153676366794617534396323915984987414968500084253615686199,4167684378427698269131479896681917875739511139690945267191,6652355282101411748055494535108523580712606266379674520253,6050565315457372142957477777883501775844793820451394458134,1300528567138802498727229172242983993185843117246599946727,23704078333111410350210715898104025906948672443169504809706,63912650063055205849222550570418250970943528605273893134,1525932097780078207513875441918362091078110909680030049043,129191319831833161398174027987012959980568858284022368633,882155670508504212828356335401623932764076341893877556233,30589610036542050931828982663128825282036863356731377769,615244335165763033627719424276730057858090662671075964848,6000000000000000000000000000000000000000000000000000000001]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction
open Complex

lemma sineFactor_deriv (a : Fin 15) : deriv (sineFactor a) =
    fun s => 2*(kappa:ℂ)*cos ((kappa:ℂ)*(s-(residue a:ℂ))) := by
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).csin.const_mul 2).deriv
  change deriv (fun y => 2*sin ((kappa:ℂ)*(y-(residue a:ℂ)))) s = _
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using hh
lemma sineFactor_second (a : Fin 15) : iteratedDeriv 2 (sineFactor a) =
    fun s => -(kappa:ℂ)^2*sineFactor a s := by
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,sineFactor_deriv]
  funext s
  have hh := ((((hasDerivAt_id s).sub_const (residue a:ℂ)).const_mul
    (kappa:ℂ)).ccos.const_mul (2*(kappa:ℂ))).deriv
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [sineFactor,id_eq,mul_one])
  ring

lemma square_zero_jets (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℂ)
    (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 0 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 1 (fun s => f s*f s) n=0 ∧
    iteratedDeriv 2 (fun s => f s*f s) n=2*(deriv f n)^2 ∧
    iteratedDeriv 3 (fun s => f s*f s) n=0 := by
  constructor
  · simp [iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,iteratedDeriv_zero,h0]
  constructor
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]
    ring
  · rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hf.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one,h0,h2]

lemma square_zero_product_jets (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (n : ℂ) (h0 : f n=0) (h2 : iteratedDeriv 2 f n=0) :
    iteratedDeriv 2 (fun s => f s^2*g s) n=2*(deriv f n)^2*g n ∧
    iteratedDeriv 3 (fun s => f s^2*g s) n=6*(deriv f n)^2*deriv g n := by
  obtain ⟨hj0,hj1,hj2,hj3⟩ := square_zero_jets f hf n h0 h2
  have hh : (fun s => f s^2) = (fun s => f s*f s) := by funext s; ring
  have hd : Differentiable ℂ (fun s => f s^2) := hf.pow 2
  constructor
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hd.contDiff.contDiffAt hg.contDiff.contDiffAt,hh]
    norm_num [Finset.sum_range_succ,hj0,hj1,hj2,hj3,iteratedDeriv_one]
    ring_nf
    simp

lemma sineFactor_at_residue (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    sineFactor a n=0 := by
  have he : (kappa:ℂ)*((n:ℂ)-(residue a:ℂ))=(n/36:ℤ)*(Real.pi:ℂ) := by
    have hh := congrArg (fun z : ℤ => (z:ℂ)) (Int.emod_add_mul_ediv n 36)
    rw [hn] at hh
    push_cast at hh
    unfold kappa
    push_cast
    linear_combination -(Real.pi:ℂ)/36*hh
  unfold sineFactor
  rw [he]
  have hz := congrArg Complex.ofReal (Real.sin_int_mul_pi (n/36))
  have hh : Complex.sin ((n/36:ℤ)*(Real.pi:ℂ))=0 := by
    simpa only [Complex.ofReal_zero,Complex.ofReal_sin,Complex.ofReal_mul,Complex.ofReal_intCast] using hz
  simp [hh]

lemma kappa_ne_zero : (kappa:ℂ)≠0 := by
  unfold kappa
  exact_mod_cast div_ne_zero Real.pi_ne_zero (by norm_num : (36:ℝ)≠0)
lemma residue_bounds (a : Fin 15) : 0 ≤ residue a ∧ residue a<36 := by
  fin_cases a <;> (first | (simp [residue]; all_goals first | (norm_num [residue]; done) | rfl | decide) | (norm_num [residue]; done) | norm_num [residue])
lemma sineFactor_ne_zero {a : Fin 15} {n : ℤ} (hn : n%36≠residue a) :
    sineFactor a n≠0 := by
  intro hz
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hprod : ((n:ℂ)-(residue a:ℂ)-36*(k:ℂ))*(Real.pi:ℂ)=0 := by
    unfold kappa at hk
    push_cast at hk
    linear_combination 36*hk
  have hzero := (mul_eq_zero.mp hprod).resolve_right (by exact_mod_cast Real.pi_ne_zero)
  have hnint : n-residue a-36*k=0 := by exact_mod_cast hzero
  obtain ⟨hr0,hr36⟩ := residue_bounds a
  have hh := Int.emod_add_mul_ediv n 36
  omega

lemma finiteC_P (a : Fin 15) :
    (fun s => (sineFactor a s)^2*finiteC a s) = fun s => 4*(kappa:ℂ)^2*P s := by
  funext s
  rw [P_factor a]
  unfold finiteC
  ring

def finiteRatio (a : Fin 15) (s : ℂ) : ℂ :=
  sin ((kappa:ℂ)*(s-(residue a:ℂ)))*cos ((kappa:ℂ)*(s-(residue a:ℂ)))/(kappa:ℂ)
lemma finiteD_eq_ratio (a : Fin 15) : finiteD a =fun s => finiteRatio a s*finiteC a s := by
  funext s
  unfold finiteD finiteRatio finiteC sineFactor
  field_simp [kappa_ne_zero]
  ring
lemma differentiable_finiteRatio (a : Fin 15) : Differentiable ℂ (finiteRatio a) := by
  unfold finiteRatio
  fun_prop
lemma finiteRatio_matching (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    finiteRatio a n=0 ∧ deriv (finiteRatio a) n=1 := by
  have hz := sineFactor_at_residue a n hn
  have hsin : sin ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))=0 := by simpa [sineFactor] using hz
  have hc : cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2=1 := by
    simpa [hsin] using sin_sq_add_cos_sq ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))
  constructor
  · simp [finiteRatio,hsin]
  · have hθ := ((hasDerivAt_id (n:ℂ)).sub_const (residue a:ℂ)).const_mul (kappa:ℂ)
    have hh := ((hθ.csin.mul hθ.ccos).div_const (kappa:ℂ)).deriv
    change deriv (finiteRatio a) n = _ at hh
    rw [hh]
    simp only [id_eq,mul_one,hsin,zero_mul,add_zero]
    calc
      _ = ((kappa:ℂ)*cos ((kappa:ℂ)*((n:ℂ)-(residue a:ℂ)))^2)/(kappa:ℂ) := by ring
      _ = _ := by rw [mul_div_cancel_left₀ _ kappa_ne_zero,hc]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def otherSide (i : Fin 2) : Fin 2 := if i.val=0 then 1 else 0

def finiteSpectrum (side q : Fin 2) (j : Fin 31) (r : Fin 8) : ℂ :=
  if q.val=0 then fourierCoeff j*(Acoefficient side 22 r:ℂ)
  else ∑ col : Fin 22, finiteColumn ⟨col.val,by omega⟩ j*(Acoefficient side ⟨col.val,by omega⟩ r:ℂ)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def nearNode (n : Fin 7) : ℤ := finiteNode ⟨n.val,by omega⟩

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def curvaturePoint : Fin 5 → ℝ := ![0,1,2,29/2,23]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

def atomFunction (k : ℝ) (x : Plane) : C(Spectrum,ℂ) :=
  exp (-(Real.pi:ℂ)*k*(radial x:ℂ)) • phaseFunction (radial x:ℂ)
def gaussian (k : ℝ) (x : Plane) : ℝ := Real.exp (-Real.pi*k*radial x)
lemma atomFunction_apply (k : ℝ) (x : Plane) (t : Spectrum) :
    atomFunction k x t = exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ)) := rfl
lemma continuous_atomFunction (k : ℝ) : Continuous (atomFunction k) := by
  have hs : Continuous (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))) := by
    unfold radial; fun_prop
  have ht : Continuous (fun x : Plane => phaseFunction (radial x:ℂ)) := by
    apply differentiable_phaseFunction.continuous.comp
    unfold radial; fun_prop
  simpa only [atomFunction] using! hs.smul ht
lemma atomFunction_bound (k : ℝ) (x : Plane) : ‖atomFunction k x‖ ≤ gaussian k x := by
  apply (ContinuousMap.norm_le _ (by unfold gaussian; positivity)).mpr
  intro t
  rw [atomFunction_apply,norm_mul]
  have hp : ‖exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp,mul_one,Complex.norm_exp]
  simp [gaussian]
lemma integrable_gaussian {k : ℝ} (hk : 0 < k) : Integrable (gaussian k) := by
  have hc : 0 < ((Real.pi*k*b:ℝ):ℂ).re := by
    simpa only [Complex.ofReal_re] using mul_pos (mul_pos Real.pi_pos hk) b_pos
  have hi := (integrable_cexp_neg_mul_sq_norm_add hc 0 (0:Plane)).norm
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [gaussian,radial,Complex.norm_exp,mul_assoc,pow_two]
lemma integrable_atomFunction {k : ℝ} (hk : 0 < k) : Integrable (atomFunction k) :=
  (integrable_gaussian hk).mono' (continuous_atomFunction k).aestronglyMeasurable
    (ae_of_all _ (atomFunction_bound k))
lemma clm_fourier {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : Plane → E) (hf : Integrable f) (w : Plane) :
    𝓕 (fun x => L (f x)) w = L (𝓕 f w) := by
  simp only [Real.fourier_eq]
  have hh := L.integral_comp_comm ((Real.fourierIntegral_convergent_iff w).mpr hf)
  simpa only [Circle.smul_def,map_smul] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

def tailVariation : ℝ := cVariation+dVariation
lemma tailSpectral_term_bound (a : InputCoefficients) (n : TailNode) :
    ‖(a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val‖ ≤
      (|a.tailC n|+|a.tailD n|)*tailVariation := by
  have hc : cVariation ≤ tailVariation := by
    exact le_add_of_nonneg_right (by unfold dVariation coeffAbs; positivity)
  have hd : dVariation ≤ tailVariation := by
    exact le_add_of_nonneg_left (by unfold cVariation coeffAbs; positivity)
  calc
    _ ≤ ‖(a.tailC n:ℂ) • spectralCCLM n.val‖ + ‖(a.tailD n:ℂ) • spectralDCLM n.val‖ := by
      convert! norm_add_le ((a.tailC n:ℂ) • spectralCCLM n.val) ((a.tailD n:ℂ) • spectralDCLM n.val) using 1
      all_goals try with_reducible_and_instances rfl
    _ ≤ |a.tailC n| * ‖spectralCCLM n.val‖ + |a.tailD n| * ‖spectralDCLM n.val‖ := by
      have hn (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
        intro f
        change ‖(r:ℂ) * T f‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
      exact add_le_add (hn _ _) (hn _ _)
    _ ≤ |a.tailC n| *tailVariation+|a.tailD n| *tailVariation :=
      add_le_add (mul_le_mul_of_nonneg_left ((spectralCCLM_norm n.val).trans hc) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((spectralDCLM_norm n.val).trans hd) (abs_nonneg _))
    _ = _ := by ring

lemma summable_tailSpectral (a : InputCoefficients) :
    Summable (fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val) :=
  Summable.of_norm_bounded (E := C(Spectrum,ℂ) →L[ℂ] ℂ)
    (f := fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)
    (a.summable.mul_right tailVariation) (tailSpectral_term_bound a)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def gaussianTarget (v z : ℝ) (n : ℤ) (d : Fin 2) : ℝ :=
  Q 1/Q n * Real.exp (Real.pi*(v-h)*n+(1-n)/z) *
    (if d.val=0 then z else -1+(Real.pi*(v-h)-D n)*z)
def targetEnvelope (v : ℝ) (n : ℤ) : ℝ :=
  Q 1/Q n * (1+Z+Z*|Real.pi*(v-h)-D n|) *
    Real.exp (Real.pi*(v-h)*n+(1-n)/Z)
lemma targetRatio_lt : Real.exp (-36/Z)<1 := by
  rw [Real.exp_lt_one_iff]; norm_num [Z]
def finiteTargetEnvelope : ℝ := ∑ i : Fin 6, targetEnvelope H (finiteNode ⟨i.val+4,by omega⟩)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def neumann (T : F →L[ℝ] F) : F →L[ℝ] F := ∑' n : ℕ, T^n
omit [CompleteSpace F] in
lemma neumann_norm (T : F →L[ℝ] F) {q : ℝ} (hq0 : 0≤q) (hq : q<1)
    (hT : ‖T‖≤q) : ‖neumann T‖ ≤ 1/(1-q) := by
  have hs := summable_geometric_of_lt_one hq0 hq
  have hb (n : ℕ) : ‖T^n‖ ≤ q^n := by
    cases n with
    | zero =>
      rw [pow_zero,pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n =>
      exact (norm_pow_le' T (Nat.succ_pos n)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hT (n+1))
  have ht : Summable (fun n : ℕ => ‖T^n‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    ‖neumann T‖ ≤ ∑' n : ℕ, ‖T^n‖ := norm_tsum_le_tsum_norm ht
    _ ≤ ∑' n : ℕ, q^n := ht.tsum_le_tsum hb hs
    _ = 1/(1-q) := by rw [tsum_geometric_of_lt_one hq0 hq,one_div]

def tailOperator (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) : F →L[ℝ] F := D+K.comp (L.comp B)
def tailSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : F :=
  neumann (tailOperator L B K D) (s+K (L r))
def finiteSolution (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) : E :=
  L (r+B (tailSolution L B K D r s))
end AtomicTriangular.Schur
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitN (e : Fin 2) : ℝ := if e.val=0 then 17 else 5
def splitQ (e : Fin 2) : ℝ := delta+340*beta*splitN e
lemma splitN_nonneg (e : Fin 2) : 0 ≤ splitN e := by fin_cases e <;> (first | (simp [splitN]; all_goals first | (norm_num [splitN]; done) | rfl | decide) | (norm_num [splitN]; done) | norm_num [splitN])
lemma splitQ_nonneg (e : Fin 2) : 0 ≤ splitQ e := by fin_cases e <;> (first | (simp [splitQ,splitN,beta,delta]; all_goals first | (norm_num [splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [splitQ,splitN,beta,delta]; done) | norm_num [splitQ,splitN,beta,delta])
lemma splitQ_lt (e : Fin 2) : splitQ e<1 := by fin_cases e <;> (first | (simp [splitQ,splitN,beta,delta]; all_goals first | (norm_num [splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [splitQ,splitN,beta,delta]; done) | norm_num [splitQ,splitN,beta,delta])

def finiteResidualBound : ℝ := 82/10^9
def tailResidualBound (e : Fin 2) : ℝ := 1/10^26+6*beta+(if e.val=0 then 0 else (12/1000)*(13/10^8))
def tailErrorBound (e : Fin 2) : ℝ := if e.val=0 then 1801/10^12 else 3361/10^12
def finiteErrorBound (e : Fin 2) : ℝ := if e.val=0 then 11804/10^9 else 6124/10^9
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate
lemma finiteColumn_even (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val,by omega⟩ l=cCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val<22 by omega,↓reduceDIte,
    show 2*j.val%2=0 by omega,↓reduceIte]
  congr 2
  omega
lemma finiteColumn_odd (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val+1,by omega⟩ l=dCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val+1<22 by omega,↓reduceDIte,
    show ¬((2*j.val+1)%2=0) by omega,↓reduceIte]
  congr 2
  omega
lemma sum_fin22_pairs {M : Type*} [AddCommMonoid M] (g : Fin 22 → M) :
    (∑ c : Fin 22, g c)=∑ j : Fin 11, (g ⟨2*j.val,by omega⟩+g ⟨2*j.val+1,by omega⟩) := by
  have hh := (finProdFinEquiv (m:=11) (n:=2)).sum_comp g
  rw [Fintype.sum_prod_type] at hh
  simp only [Fin.sum_univ_two] at hh
  convert hh.symm using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> apply Fin.ext <;> simp [finProdFinEquiv, mul_comm, add_comm]
lemma complex_smul_clm_bound (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) :
    ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
  intro f
  change ‖(r:ℂ) * T f‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
lemma norm_series_bound {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι → E) (v : ι → ℝ) (hv : Summable v) (M : ℝ)
    (hb : ∀ i, ‖g i‖≤M*v i) : ‖∑' i, g i‖≤M*∑' i,v i := by
  have hs : Summable (fun i => ‖g i‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hv.mul_left M)
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb (hv.mul_left M)).trans_eq (tsum_mul_left))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_NormalizedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction

def negativeJet (v : ℝ) (n : ℤ) (d : Fin 2) (a b : ℂ) : ℂ :=
  exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹*
    (if d.val=0 then -a else ((D n:ℂ)-Real.pi*(v-h))*a-b)
lemma zeta_change (k v t : ℝ) : I*Real.pi*zeta k v t =
    (Real.pi*(v-h):ℂ)+I*Real.pi*zeta k h t := by
  unfold zeta
  push_cast
  ring_nf
  simp [I_sq]
  ring
lemma transformedWave_change (k v t : ℝ) (s : ℂ) : transformedWave k v t s=
    exp (Real.pi*(v-h)*s)*transformedWave k h t s := by
  unfold transformedWave
  rw [zeta_change,add_mul,exp_add]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_DirectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma negativeJet_re (v : ℝ) (n : ℤ) (d : Fin 2) (a b : ℂ) :
    (negativeJet v n d a b).re=
      Real.exp (Real.pi*(v-h)*n)/(Q n)*
        (if d.val=0 then -a.re else (D n-Real.pi*(v-h))*a.re-b.re) := by
  have he : exp (Real.pi*(v-h)*(n:ℂ))=(Real.exp (Real.pi*(v-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  unfold negativeJet
  rw [he,←ofReal_inv]
  split_ifs <;> simp only [mul_re,mul_im,ofReal_re,ofReal_im,neg_re,sub_re,sub_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  all_goals ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_SpectralJetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma spectralCVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralCVector n f)=spectralCVector n (fun t => L (f t)) := by
  unfold spectralCVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ =>
    (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  change L (((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)) =
    ((frequency l-t:ℝ):ℂ) • (exp (-I*Real.pi*(t:ℂ)*n) • L (f t))
  simp only [map_smul]
lemma spectralDVector_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (n : ℤ) (f : ℝ → E) (hf : Continuous f) :
    L (spectralDVector n f)=spectralDVector n (fun t => L (f t)) := by
  unfold spectralDVector
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [←L.intervalIntegral_comp_comm ((by fun_prop : Continuous (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t)).intervalIntegrable 0 (frequency l))]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [map_smul]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_SpectralProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def tailColumnSpectral (p : TailNode × Fin 2) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  if p.2.val=0 then spectralCCLM p.1.val else spectralDCLM p.1.val
lemma tsum_prod_fin_two {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι × Fin 2 → E) (hg : Summable g) :
    (∑' p, g p)=∑' i, (g (i,0)+g (i,1)) := by
  rw [hg.tsum_prod]
  simp only [tsum_fintype,Fin.sum_univ_two]
lemma negativeJet_add (v : ℝ) (n : ℤ) (d : Fin 2) (a b c e : ℂ) :
    negativeJet v n d (a+c) (b+e)=negativeJet v n d a b+negativeJet v n d c e := by
  unfold negativeJet
  split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
def rowNode (i : Fin 20) : Node := ⟨finiteNode ⟨i.val/2,by omega⟩,by
  have hh : ∀ n : Fin 10,0<finiteNode n ∧ finiteNode n%36∈residues := by decide +kernel
  exact hh _⟩
def rowDerivative (i : Fin 20) : Fin 2 := ⟨i.val%2,by omega⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.MatrixBounds
lemma finiteRow_sum (C : ℝ) (a : Fin 22 → ℝ) (i : Fin 20) :
    C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩))=
    (∑ j : Fin 20,R i j*a ⟨j.val+2,by omega⟩)+
      R0 i 0*a 0+R0 i 1*a 1+R0 i 2*C := by
  have hR (j : Fin 20) : R i j=jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩) := by
    simp only [R,fullJetMatrix,show j.val+2≠22 by omega,↓reduceIte,rowNode,rowDerivative]
  simp_rw [hR]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hh : (∑ j : Fin 20,a j.succ.succ*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨j.succ.succ.val,by omega⟩))=
      ∑ j : Fin 20,jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨j.val+2,by omega⟩)*a ⟨j.val+2,by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    have he : j.succ.succ=(⟨j.val+2,by omega⟩:Fin 22) := Fin.ext (by simp)
    simp only [he]
    exact mul_comm _ _
  rw [hh]
  simp only [R0,fullJetMatrix,Fin.val_zero,Fin.val_one,Fin.val_two,show 0<2 by omega,
    show 1<2 by omega,lt_self_iff_false,↓reduceIte,show (0:ℕ)≠22 by omega,show (1:ℕ)≠22 by omega]
  change _= _
  dsimp [rowNode,rowDerivative]
  ring
lemma gamma_actual (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z)= ![11/25,0,if side.val=0 then -(3/500) else 3/500] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,gamma,Fin.sum_univ_succ,actualParameter]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteTargetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Matrix
namespace AtomicTriangular.Construction
lemma gaussianTarget_factor (z : ℝ) (n : Fin 10) (d : Fin 2) :
    gaussianTarget H z (finiteNode n) d=targetCoefficient n * Real.exp ((1-finiteNode n)/z)*
      (if d.val=0 then z else -1+(Real.pi*eta-D (finiteNode n))*z) := by
  have he : H-h=eta := by norm_num [H,h,eta]
  simp only [gaussianTarget,targetCoefficient,he,Real.exp_add]
  ring
lemma Yf_actual (z : ℝ) (i : Fin 20) :
    (Yf *ᵥ actualParameter z) i=
      if i.val<8 then gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ else 0 := by
  rw [gaussianTarget_factor]
  fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Yf,actualParameter,Fin.sum_univ_succ,
    finiteNode,residue] <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
def gaussianG (z s : ℝ) : ℝ := Q 1*z*Real.exp ((1-s)/z)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_AtomicCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real Set

lemma linear_sqrt_exp_hasDerivAt {a b δ x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y : ℝ => (a+b*y)*sqrt y*exp (-δ*y))
      ((b*sqrt x+(a+b*x)/(2*sqrt x)-δ*((a+b*x)*sqrt x))*exp (-δ*x)) x := by
  have hd := (((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).mul
    (hasDerivAt_sqrt (ne_of_gt hx))).mul
    (((hasDerivAt_id x).const_mul (-δ)).exp)
  convert hd using 1 <;> first | rfl | (dsimp; ring)

lemma linear_sqrt_exp_antitone {a b δ x y : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hb : 0≤b) (hδ : 3/2≤δ*x) :
    (a+b*y)*sqrt y*exp (-δ*y) ≤ (a+b*x)*sqrt x*exp (-δ*x) := by
  have hδ0 : 0<δ := by nlinarith
  have hanti : AntitoneOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici x)
    · exact (by fun_prop : ContinuousOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x))
    · intro u hu
      exact (linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) (hx.trans_le (mem_Ici.mp (interior_subset hu)))).differentiableAt.differentiableWithinAt
    · intro u hu
      have hux : x≤u := mem_Ici.mp (interior_subset hu)
      have hu0 := hx.trans_le hux
      rw [(linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) hu0).deriv]
      apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
      have hs := sq_sqrt hu0.le
      have hsp : 0 < sqrt u := sqrt_pos.mpr hu0
      have hδu : 3/2≤δ*u := hδ.trans (mul_le_mul_of_nonneg_left hux hδ0.le)
      apply nonpos_of_mul_nonpos_left (b:=2*sqrt u) _ (by positivity)
      have he : (b*sqrt u+(a+b*u)/(2*sqrt u)-δ*((a+b*u)*sqrt u))*(2*sqrt u) =
          a+3*b*u-2*δ*u*(a+b*u) := by
        field_simp
        rw [hs]
        ring
      rw [he]
      have h1 := mul_nonneg (show 0≤2*δ*u-1 by linarith) ha
      have h2 := mul_nonneg (show 0≤2*δ*u-3 by linarith) (mul_nonneg hb hu0.le)
      nlinarith
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hxy) hxy
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FinitePairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma Acoefficient_constant (side : Fin 2) (r : Fin 8) : Acoefficient side 22 r=gamma side 2 r := by
  simp [Acoefficient]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CoefficientAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma gamma_actual_constant (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500:ℝ) else 3/500 := by
  rw [gamma_actual]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

def finiteCurvatureCap (br : Fin 2) : Fin 5 → ℝ :=
  if br.val=0 then ![828/10,44164/1000,23561/1000,9147/1000000,43834/1000000000]
  else ![291294/100,45877/1000,3893/1000,635/10000000000,167/100000000000000]
def finiteCurvatureEnvelope : Fin 5 → ℝ := ![1510,46,14,465/100000,23/1000000]
def tailCurvatureEnvelope : Fin 5 → ℝ := ![26500,1160,800,800,800]
lemma finiteCurvatureCap_sum (i : Fin 5) :
    (finiteCurvatureCap 0 i+finiteCurvatureCap 1 i)/2≤finiteCurvatureEnvelope i := by
  fin_cases i <;> (first | (simp [finiteCurvatureCap,finiteCurvatureEnvelope]; all_goals first | (norm_num [finiteCurvatureCap,finiteCurvatureEnvelope]; done) | rfl | decide) | (norm_num [finiteCurvatureCap,finiteCurvatureEnvelope]; done) | norm_num [finiteCurvatureCap,finiteCurvatureEnvelope])
lemma finiteCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤finiteCurvatureCap br i := by
  fin_cases br <;> fin_cases i <;> (first | (simp [finiteCurvatureCap]; all_goals first | (norm_num [finiteCurvatureCap]; done) | rfl | decide) | (norm_num [finiteCurvatureCap]; done) | norm_num [finiteCurvatureCap])
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def localCenter (u : Fin 30) : ℤ := residue ⟨u.val/2,by omega⟩
def localNeighbor : Fin 30 → ℤ := ![-5,1,0,3,1,4,3,7,4,9,7,12,9,13,12,16,13,19,16,21,19,25,21,27,25,28,27,31,28,36]
def localHalf (u : Fin 30) : ℚ := ((localNeighbor u:ℚ)-localCenter u)/2
def cellLo (u : Fin 30) (k : Fin 100) : ℚ := min (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellHi (u : Fin 30) (k : Fin 100) : ℚ := max (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellMagnitude (u : Fin 30) (k : Fin 100) : ℚ := max |cellLo u k| |cellHi u k|
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def realP (s : ℝ) : ℝ := ∏ a : Fin 15,(2*Real.sin (Real.pi*(s-residue a)/36))^2
lemma P_ofReal (s : ℝ) : P (s:ℂ)=(realP s:ℂ) := by
  unfold P realP sineFactor kappa
  push_cast
  congr 1
  funext a
  ring_nf
lemma abs_cell_le (u : Fin 30) (k : Fin 100) {y : ℝ}
    (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) : |y|≤(cellMagnitude u k:ℝ) := by
  unfold cellMagnitude
  push_cast
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (cellLo u k:ℝ),le_max_left |(cellLo u k:ℝ)| |(cellHi u k:ℝ)|,hy.1]
  · exact hy.2.trans ((le_abs_self _).trans (le_max_right _ _))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma realP_contDiff : ContDiff ℝ ⊤ realP := by unfold realP; fun_prop

def sideConstant (side : Fin 2) : ℝ := if side.val=0 then -(3/500) else 3/500
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma norm_two_sin_le (z : ℂ) : ‖2 * sin z‖ ≤ 2 * Real.exp |z.im| := by
  rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  calc
    ‖exp (-z * I) - exp (z * I)‖ ≤ ‖exp (-z * I)‖ + ‖exp (z * I)‖ := norm_sub_le _ _
    _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _))
        (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = 2 * Real.exp |z.im| := by ring

def stripBound (R : ℝ) : ℝ := (2 * Real.exp (Real.pi * R / 36))^30

lemma stripBound_nonneg (R : ℝ) : 0 ≤ stripBound R := by unfold stripBound; positivity

lemma P_strip_bound (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) : ‖P s‖ ≤ stripBound R := by
  unfold P sineFactor
  rw [norm_prod]
  calc
    ∏ a : Fin 15, ‖(2 * sin ((kappa : ℂ) * (s-residue a)))^2‖ ≤
        ∏ _a : Fin 15, (2 * Real.exp (Real.pi * R / 36))^2 := by
      apply Finset.prod_le_prod (by intros; positivity)
      intro a _
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine (norm_two_sin_le _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have he : (((kappa : ℂ) * (s-residue a))).im = Real.pi * s.im / 36 := by
        simp [kappa, div_eq_mul_inv] <;> ring
      rw [he, abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 36)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (by norm_num)
    _ = stripBound R := by simp [stripBound, ← pow_mul]

lemma im_le_dist_int (w : ℂ) (n : ℤ) : |w.im| ≤ dist w (n : ℂ) := by
  simpa [dist_eq_norm] using Complex.abs_im_le_norm (w - (n : ℂ))

def spectralBound (S : Fin 31 → ℂ) (R : ℝ) : ℝ :=
  ∑ j : Fin 31, ‖S j‖*Real.exp (|Real.pi*frequency j| *R)
lemma finiteSpectral_strip (S : Fin 31 → ℂ) (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖∑ j : Fin 31, S j*exp (I*Real.pi*frequency j*s)‖ ≤ spectralBound S R := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hi : (I*Real.pi*frequency j*s).re = -(Real.pi*frequency j)*s.im := by simp
  rw [hi]
  calc
    -(Real.pi*frequency j)*s.im ≤ |-(Real.pi*frequency j)*s.im| := le_abs_self _
    _ = |Real.pi*frequency j| *|s.im| := by rw [abs_mul,abs_neg]
    _ ≤ |Real.pi*frequency j| *R := mul_le_mul_of_nonneg_left hs (abs_nonneg _)

lemma tail_summand_norm_bound (a : InputCoefficients) {R M : ℝ}
    (hM : ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M)
    (n : TailNode) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖(a.tailC n:ℂ)*cBasis n.val s+(a.tailD n:ℂ)*dBasis n.val s‖ ≤
      (|a.tailC n|+|a.tailD n|)*M := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |a.tailC n| *M+|a.tailD n| *M :=
      add_le_add (mul_le_mul_of_nonneg_left (hM n.val s hs).1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hM n.val s hs).2 (abs_nonneg _))
    _ = _ := by ring

lemma differentiable_finiteInput (a : InputCoefficients) : Differentiable ℂ (finiteInput a) := by
  unfold finiteInput
  apply Differentiable.fun_sum
  intro j _
  exact ((differentiable_finiteC _).const_mul _).add ((differentiable_finiteD _).const_mul _)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma P_conj (s : ℂ) : conj (P s) = P (conj s) := by
  simp only [P,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]

lemma dslope_conj_real {f : ℂ → ℂ} (hf : ∀ s, conj (f s) = f (conj s))
    (r : ℝ) (s : ℂ) : conj (dslope f (r:ℂ) s) = dslope f (r:ℂ) (conj s) := by
  have he : conj ∘ f ∘ conj = f := by
    ext z
    simp only [Function.comp_apply,hf,RCLike.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := f)) (r:ℂ)
  rw [he] at hd
  simp only [Function.comp_apply,Complex.conj_ofReal] at hd
  by_cases hs : s = (r:ℂ)
  · subst s
    simpa only [Complex.conj_ofReal,dslope_same] using hd.symm
  · have hc : conj s ≠ (r:ℂ) := by
      intro h; apply hs
      have hh := congrArg conj h
      simpa using hh
    rw [dslope_of_ne _ hs,dslope_of_ne _ hc]
    simp only [slope_def_field,map_div₀,map_sub,hf,Complex.conj_ofReal]

lemma dBasis_conj (n : Node) (s : ℂ) : conj (dBasis n s) = dBasis n (conj s) := by
  simpa only [dBasis,Complex.ofReal_intCast] using dslope_conj_real P_conj (n.val:ℝ) s
lemma cBasis_conj (n : Node) (s : ℂ) : conj (cBasis n s) = cBasis n (conj s) := by
  simpa only [cBasis,Complex.ofReal_intCast] using dslope_conj_real (dBasis_conj n) (n.val:ℝ) s
lemma finiteC_conj (j : Fin 15) (s : ℂ) : conj (finiteC j s) = finiteC j (conj s) := by
  simp only [finiteC,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma finiteD_conj (j : Fin 15) (s : ℂ) : conj (finiteD j s) = finiteD j (conj s) := by
  simp only [finiteD,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,← Complex.cos_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma tailInput_conj (a : InputCoefficients) (s : ℂ) : conj (tailInput a s) = tailInput a (conj s) := by
  simp only [tailInput,map_add,map_mul,Complex.conj_ofReal,P_conj,Complex.conj_tsum,cBasis_conj,dBasis_conj]
lemma finiteInput_conj (a : InputCoefficients) (s : ℂ) : conj (finiteInput a s) = finiteInput a (conj s) := by
  simp only [finiteInput,map_sum,map_add,map_mul,Complex.conj_ofReal,finiteC_conj,finiteD_conj]

lemma inputComplex_real (a : InputCoefficients) (x : Plane) : conj (inputComplex a x) = inputComplex a x := by
  simp only [inputComplex,map_add,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal,tailInput_conj,finiteInput_conj]

lemma radial_neg (x : Plane) : radial (-x) = radial x := by simp [radial]
lemma inputComplex_even (a : InputCoefficients) (x : Plane) : inputComplex a (-x) = inputComplex a x := by
  simp only [inputComplex,radial_neg]
lemma fourier_conj_even (f : Plane → ℂ) (hre : ∀ x, conj (f x) = f x)
    (hev : ∀ x, f (-x) = f x) (w : Plane) : conj (𝓕 f w) = 𝓕 f w := by
  have he : (fun x => f (-x)) = f := funext hev
  have hi : conj (𝓕 f w) = 𝓕⁻ f w := by
    simp only [Real.fourier_eq',Real.fourierInv_eq',smul_eq_mul,← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [← Complex.exp_conj,hre,map_ofNat]
  rw [hi,Real.fourierInv_eq_fourier_comp_neg,he]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma h_pos : 0 < h := by norm_num [h]
lemma H_pos : 0 < H := by norm_num [H]

lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def nearDisplacementNum : Fin 7 → Fin 2 → ℤ :=
  ![![-2,2],![-2,1],![-1,3],![-3,2],![-2,3],![-3,1],![-1,3]]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def deletedSecond (f : ℝ → ℝ) (m s : ℝ) : ℝ :=
  if s=m then iteratedDeriv 2 f m/2 else (f s-f m-deriv f m*(s-m))/(s-m)^2

lemma taylor_one_eval {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    taylorWithinEval f 1 (uIcc m s) m s=f m+deriv f m*(s-m) := by
  have he : iteratedDerivWithin 1 f (uIcc m s) m=iteratedDeriv 1 f m :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hms)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  rw [show (1:ℕ)=0+1 from rfl,taylorWithinEval_succ,he]
  simp [mul_comm]

lemma deletedSecond_eq_at_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    ∃ c∈uIoo m s,deletedSecond f m s=iteratedDeriv 2 f c/2 := by
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hms hf.contDiffOn
  refine ⟨c,hc,?_⟩
  rw [taylor_one_eval hf hms] at he
  have hn : s-m≠0 := sub_ne_zero.mpr hms.symm
  rw [deletedSecond,ite_eq_right hms.symm]
  norm_num at he
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  linarith

lemma deletedSecond_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s C : ℝ}
    (hb : ∀ t∈uIcc m s,|iteratedDeriv 2 f t|≤C) : |deletedSecond f m s|≤C/2 := by
  by_cases h : m=s
  · subst s
    rw [deletedSecond,ite_eq_left rfl,abs_div,show |(2:ℝ)|=2 by norm_num]
    exact div_le_div_of_nonneg_right (hb m (left_mem_uIcc)) (by norm_num)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf h
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact hb c (Ioo_subset_Icc_self hc)

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
def farK (i : Fin 5) : ℝ :=
  (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma complex_fourier_smul (c : ℂ) (f : Plane → ℂ) : 𝓕 (c • f)=c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq,Pi.smul_apply,smul_comm _ c,MeasureTheory.integral_smul]
end AtomicTriangular.Construction
end

end OAI
end


