-- Prove2me | Definitions.Def_OAIQ262T001
-- name    : OAIQ262T001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:40:06.142274+00:00
-- url     : https://prove2.me/theorems/0024fcc1-cb83-475f-a30e-cad24f0dc777
-- title:
--   Definitions bundle OAIQ262T001 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 46 definitions and 76 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Bkernel`, `OAI.AtomicTriangular.Construction.Ckernel`, `OAI.AtomicTriangular.Construction.DeltaStar`, `OAI.AtomicTriangular.Construction.Dkernel`, `OAI.AtomicTriangular.Construction.FiniteCoefficients`, `OAI.AtomicTriangular.Construction.HasAtomicConstruction`, `OAI.AtomicTriangular.Construction.JetVector`, `OAI.AtomicTriangular.Construction.ParameterPolytope`, `OAI.AtomicTriangular.Construction.Pstar`, `OAI.AtomicTriangular.Construction.Spectrum`, `OAI.AtomicTriangular.Construction.Ustar`, `OAI.AtomicTriangular.Construction.Wstar`, `OAI.AtomicTriangular.Construction.Z`, `OAI.AtomicTriangular.Construction.beta`, `OAI.AtomicTriangular.Construction.cellHi`, `OAI.AtomicTriangular.Construction.cellLo`, `OAI.AtomicTriangular.Construction.cellMagnitude`, `OAI.AtomicTriangular.Construction.finiteCoordinates`, `OAI.AtomicTriangular.Construction.frequencyDistance`, `OAI.AtomicTriangular.Construction.fullTailW`, `OAI.AtomicTriangular.Construction.gaussianTarget`, `OAI.AtomicTriangular.Construction.jetEnvelope`, `OAI.AtomicTriangular.Construction.jetVector`, `OAI.AtomicTriangular.Construction.localCenter`, `OAI.AtomicTriangular.Construction.localHalf`, `OAI.AtomicTriangular.Construction.localNeighbor`, `OAI.AtomicTriangular.Construction.realP`, `OAI.AtomicTriangular.Construction.rootProduct`, `OAI.AtomicTriangular.Construction.rowLower`, `OAI.AtomicTriangular.Construction.spectralCVector`, `OAI.AtomicTriangular.Construction.spectralDVector`, `OAI.AtomicTriangular.Construction.spectralParameter`, `OAI.AtomicTriangular.Construction.stripBound`, `OAI.AtomicTriangular.Construction.tailJet`, `OAI.AtomicTriangular.Construction.tailJetVector`, `OAI.AtomicTriangular.Construction.targetEnvelope`, `OAI.AtomicTriangular.FiniteCertificate.A1AbsNumerators`, `OAI.AtomicTriangular.FiniteCertificate.plusApproxNum`, `OAI.AtomicTriangular.FiniteCertificate.restPolynomial`, `OAI.AtomicTriangular.MatrixBounds.colNorm` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_IntegralBounds`, `Triangular_Auxiliary_MatrixNorm`, `Triangular_Basic`, `Triangular_Certificate_Inverse`, `Triangular_Certificate_MatrixInterval`, `Triangular_Certificate_Param`, `Triangular_Certificate_ParamActual`, `Triangular_Certificate_ParamNorm`, `Triangular_Certificate_Polytope`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_FinitePairBridge`, `Triangular_Construction_FiniteTargetBridge`, `Triangular_Construction_RepetitionOperators`, `Triangular_Construction_Schur`, `Triangular_Construction_TailJetVector`, `Triangular_Envelope_Analytic`, `Triangular_Envelope_Basic`, `Triangular_Envelope_EnvelopeBoxes`, `Triangular_Envelope_KernelBounds`, `Triangular_Envelope_TargetEnvelope`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_Realness`, `Triangular_Schwartz_Regularity`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_SpectralEnvelope`, `Triangular_Signs_SineGridAnalytic`, `Triangular_Signs_SineGridDefs`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T009`, `OAIQ262T011`, `OAIQ262T012`, `OAIQ262T013`, `OAIQ262T014`, `OAIQ262T015`, `OAIQ262T016`, `OAIQ262T018`, `OAIQ262T019`, `OAIQ262T034` and `OAIQ262T055`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian

section
-- module Solutions.OAIQ262_TG.Triangular_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular.Construction

def Z : ℝ := 391/1000

end AtomicTriangular.Construction

namespace AtomicTriangular.Construction

def finiteCoordinates (a : InputCoefficients) (i : Fin 22) : ℝ :=
  if i.val % 2 = 0 then a.finiteC ⟨i.val / 2, by omega⟩
  else a.finiteD ⟨i.val / 2, by omega⟩

def HasAtomicConstruction (α : ℝ) (f : Plane → ℝ) : Prop :=
  IsUnit (1 - R) ∧ IsUnit (1 + R) ∧
  (1 - R) * Uplus = Yf + R0 * (gamma 1 + gamma 0) ∧
  (1 + R) * Uminus = Yf + R0 * (gamma 1 - gamma 0) ∧
  ∃ (a : Fin 2 → InputCoefficients) (u : Fin 2 → Fin 20 → ℝ),
    (∀ side,
      (a side).C = (if side.val = 0 then -(3/500) else 3/500) ∧
      (a side).finiteC 0 = 11/25 ∧ (a side).finiteD 0 = 0 ∧
      ∀ i : Fin 22,
        finiteCoordinates (a side) i =
          (∑ j : Fin 8, Acoefficient side ⟨i.val, by omega⟩ j *
            actualParameter (gaussianZ α) j) +
          (if hi : i.val < 2 then 0 else u side ⟨i.val - 2, by omega⟩)) ∧
    (∀ side,
      (∑ i : Fin 20, |u side i|) < 1/10^5 ∧
      Summable (fun n : TailNode => |(a side).tailC n| + |(a side).tailD n|) ∧
      (∑' n : TailNode, (|(a side).tailC n| + |(a side).tailD n|)) < 3/10^9) ∧
    (∀ x : Plane, (f x : ℂ) =
      (inputComplex (a 0) x + 𝓕 (inputComplex (a 1)) x) /
        (normalizingDen (gaussianZ α) : ℂ))

end AtomicTriangular.Construction

end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Auxiliary_IntegralBounds
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
-- module Solutions.OAIQ262_TG.Triangular_Auxiliary_MatrixNorm
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
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

theorem differentiable_finiteC (a : Fin 15) : Differentiable ℂ (finiteC a) := by
  unfold finiteC sineFactor
  fun_prop

theorem P_factor (a : Fin 15) (s : ℂ) :
    P s = (sineFactor a s)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

open Polynomial

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

lemma mul_bounds {a b x t : ℝ} (h : a ≤ x ∧ x ≤ b) :
    min (a*t) (b*t) ≤ x*t ∧ x*t ≤ max (a*t) (b*t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 ht),
      (mul_le_mul_of_nonneg_right h.2 ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 ht),
      (mul_le_mul_of_nonpos_right h.1 ht).trans (le_max_left _ _)⟩

lemma four_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hxy := mul_bounds (t := y) hx
  have ha := mul_bounds (t := a) hy
  have hb := mul_bounds (t := b) hy
  simp only [mul_comm c,mul_comm d,mul_comm y] at ha hb
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)
  · apply le_trans hxy.2
    exact max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _))

lemma div_floor_bounds (a n : ℤ) (hn : 0 < n) :
    ((a/n:ℤ):ℝ)*(n:ℝ) ≤ a ∧ (a:ℝ) ≤ ((a/n+1:ℤ):ℝ)*(n:ℝ) := by
  constructor
  · exact_mod_cast Int.ediv_mul_le a (ne_of_gt hn)
  · exact_mod_cast (Int.lt_ediv_add_one_mul_self a hn).le

end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial

lemma coeff_X_mul' (p : Polynomial ℂ) (n : ℕ) :
    (X*p).coeff n = if n=0 then 0 else p.coeff (n-1) := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul]

lemma coeff_X_sq_mul (p : Polynomial ℂ) (n : ℕ) :
    (X^2*p).coeff n = if n<2 then 0 else p.coeff (n-2) := by
  rw [pow_two, mul_assoc, coeff_X_mul']
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [coeff_X_mul]

end AtomicTriangular.FiniteCertificate

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

def restPolynomial (a : Fin 15) : Polynomial ℂ :=
  ∏ r ∈ Finset.univ.erase a, atomFactor r

lemma atomPolynomial_factor (a : Fin 15) :
    atomPolynomial = atomFactor a * restPolynomial a := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

lemma cCoefficient_eq (a : Fin 15) (j : Fin 31) :
    cCoefficient a j = if j.val=0 then 0
      else 4*(kappa:ℂ)^2*(restPolynomial a).coeff (j.val-1) := by
  simp only [cCoefficient, cShiftPolynomial, coeff_X_mul', cAtomPolynomial, coeff_C_mul,
    restPolynomial]

end AtomicTriangular.FiniteCertificate

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

lemma waveDen_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < waveDen k t := by
  unfold waveDen
  positivity

def spectralParameter (k t : ℝ) : ℂ := (b:ℂ)*((k:ℂ)-I*t)

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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_MatrixInterval
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_Basic
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma Xwave_pos {k : ℝ} (hk : 0<k) (t : ℝ) : 0<Xwave k t := by
  unfold Xwave
  exact div_pos (by norm_num) (waveDen_pos hk t)
lemma Xwave_square {k : ℝ} (hk : 0<k) (t : ℝ) :
    (k^2+t^2)*Xwave k t=4/3 := by
  unfold Xwave waveDen
  field_simp [ne_of_gt (waveDen_pos hk t)]
lemma normSq_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : normSq (lambda k t)=Xwave k t := by
  unfold lambda
  rw [map_div₀]
  simp only [normSq_apply,add_re,ofReal_re,mul_re,I_re,zero_mul,I_im,ofReal_im,
    mul_zero,sub_zero,add_zero,add_im,mul_im,one_mul,zero_add]
  dsimp [Xwave,waveDen]
  have hb := b_sq
  have hd : k^2+t^2≠0 := ne_of_gt (waveDen_pos hk t)
  field_simp [ne_of_gt b_pos, hd]
  nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg t)]
lemma norm_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : ‖lambda k t‖=Real.sqrt (Xwave k t) := by
  rw [Complex.norm_def,normSq_lambda hk]
lemma normSq_zeta {k : ℝ} (hk : 0<k) (v t : ℝ) :
    normSq (zeta k v t)=v^2+(4/3-2*k*v)*Xwave k t := by
  unfold zeta
  simp only [normSq_apply,add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,
    sub_zero,I_re,zero_mul,I_im,one_mul,add_zero,add_im,neg_im,mul_im,zero_add]
  linear_combination Xwave k t * Xwave_square hk t
lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]
lemma norm_wavePhase {k : ℝ} (hk : 0<k) (v t : ℝ) :
    ‖I*Real.pi*zeta k v t‖=Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t) := by
  rw [norm_mul,norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_def,normSq_zeta hk]

def jetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t))*
    Real.sqrt (Xwave k t)/Q n*Real.exp (-Real.pi*(k*Xwave k t-v)*n)

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeBoxes
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
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_SpectralCLM
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

lemma frequency_mem (l : Fin 31) : frequency l ∈ Set.Icc (-(5/6):ℝ) (5/6) := by
  unfold frequency
  have hn : (l.val:ℝ) ≤ 30 := by exact_mod_cast (show l.val ≤ 30 by omega)
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) l.val]

lemma norm_exp_phase (t : ℝ) (n : ℤ) : ‖exp (I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_exp_neg_phase (t : ℝ) (n : ℤ) : ‖exp (-I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_SpectralEnvelope
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailJetVector
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
lemma continuous_jetMultiplier {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (d : Fin 2) :
    Continuous (jetMultiplier k v n d) := by
  have hl : Continuous (lambda k) := by
    unfold lambda
    apply Continuous.div
    · fun_prop
    · unfold waveDen; fun_prop
    · intro t; exact_mod_cast (mul_pos b_pos (waveDen_pos hk t)).ne'
  have hX : Continuous (Xwave k) := by
    unfold Xwave
    exact continuous_const.div (by unfold waveDen; fun_prop) (fun t => (waveDen_pos hk t).ne')
  have hz : Continuous (zeta k v) := by unfold zeta; fun_prop
  unfold jetMultiplier transformedWave
  split_ifs <;> fun_prop
lemma continuous_jetVector {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) :
    Continuous (jetVector k v n) := by
  exact (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
    (continuous_pi (fun d => continuous_jetMultiplier hk v n d))

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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_KernelBounds
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_BlockOperators
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_RepetitionOperators
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Param
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Polytope
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

def rowLower (row : Fin 8 → ℝ) : ℝ :=
  row 1 + Z*min 0 (row 0) + DeltaStar*min 0 (-row 2) +
    Wstar*min 0 (row 3+Z*row 2) + Ustar*min 0 (min (row 5) (row 5+Z*row 4)) +
    Pstar*(min 0 (row 6)+min 0 (row 7))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamActual
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamNorm
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
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_TargetEnvelope
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_Schur
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_FinitePairBridge
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteTargetBridge
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
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Regularity
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

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Realness
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

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma H_pos : 0 < H := by norm_num [H]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridDefs
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridAnalytic
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


