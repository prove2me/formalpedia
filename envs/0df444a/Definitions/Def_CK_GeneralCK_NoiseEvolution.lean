-- Prove2me | Definitions.Def_CK_GeneralCK_NoiseEvolution
-- name    : CK_GeneralCK_NoiseEvolution
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:20:16.776472+00:00
-- url     : https://prove2.me/theorems/ccda343b-3eb9-4907-9d0c-b6e1a3ee84a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.NoiseEvolution` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.NoiseEvolution` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.NoiseEvolution` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.NoiseEvolution (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/NoiseEvolution.lean)

import Definitions.Def_CK_GeneralCK_InformationIdentity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_GeneralCK_noise_evolution

namespace GeneralCK.Noise
open scoped BigOperators








theorem hasDerivAt_crossover (t : ℝ) :
    HasDerivAt crossover (Real.exp (-2 * t)) t := by
  have h := (((hasDerivAt_id t).const_mul (-2)).exp.const_sub 1).div_const 2
  convert! h using 1; dsimp [crossover]; ring



theorem factor_derivative (a b : Bool) (t : ℝ) :
    HasDerivAt (fun s => factor (crossover s) a b)
      (factor (crossover t) a (!b) - factor (crossover t) a b) t := by
  cases a <;> cases b <;> simp only [factor, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_false, Bool.not_true, ite_true, ite_false]
  · convert! (hasDerivAt_crossover t).const_sub 1 using 1; dsimp [crossover]; ring
  · convert! hasDerivAt_crossover t using 1; dsimp [crossover]; ring
  · convert! hasDerivAt_crossover t using 1; dsimp [crossover]; ring
  · convert! (hasDerivAt_crossover t).const_sub 1 using 1; dsimp [crossover]; ring

theorem kernel_flip_difference {n : ℕ} (p : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel p x (flip y i) - noiseKernel p x y =
      (∏ j ∈ Finset.univ.erase i, factor p (x j) (y j)) *
        (factor p (x i) (!(y i)) - factor p (x i) (y i)) := by
  classical
  change (∏ j, factor p (x j) (flip y i j)) - (∏ j, factor p (x j) (y j)) = _
  rw [← Finset.prod_erase_mul _ (fun j => factor p (x j) (flip y i j)) (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ (fun j => factor p (x j) (y j)) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, factor p (x j) (flip y i j)) =
      ∏ j ∈ Finset.univ.erase i, factor p (x j) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [flip, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp only [flip, Function.update_self]
  ring

theorem hasDerivAt_kernel {n : ℕ} (x y : Cube n) (t : ℝ) :
    HasDerivAt (fun s => noiseKernel (crossover s) x y)
      (∑ i, (noiseKernel (crossover t) x (flip y i) - noiseKernel (crossover t) x y)) t := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun (i : Fin n) _ => factor_derivative (x i) (y i) t)
  convert! h using 1
  simp only [smul_eq_mul, ← kernel_flip_difference]

/-- The generator is the sum of coordinate differences, with one subtraction per coordinate. -/
theorem hasDerivAt_applyNoise {n : ℕ} (v : Cube n → ℝ) (y : Cube n) (t : ℝ) :
    HasDerivAt (fun s => applyNoise (crossover s) v y)
      (∑ i, (applyNoise (crossover t) v (flip y i) - applyNoise (crossover t) v y)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (x : Cube n) _ => (hasDerivAt_kernel x y t).mul_const (v x))
  convert! h using 1
  simp only [applyNoise, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

@[simp] theorem crossover_zero : crossover 0 = 0 := by simp [crossover]

theorem crossover_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ crossover t := by
  unfold crossover
  have h : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  positivity

theorem crossover_lt_half (t : ℝ) : crossover t < 1 / 2 := by
  have h := Real.exp_pos (-2 * t)
  unfold crossover
  linarith

theorem applyNoise_const {n : ℕ} (p c : ℝ) (y : Cube n) :
    applyNoise p (fun _ => c) y = c := by
  simp [applyNoise, ← Finset.sum_mul, Information.kernel_column_sum]

theorem applyNoise_bounds {n : ℕ} {p a b : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (v : Cube n → ℝ) (hv : ∀ x, a ≤ v x ∧ v x ≤ b) (y : Cube n) :
    a ≤ applyNoise p v y ∧ applyNoise p v y ≤ b := by
  constructor
  · rw [← applyNoise_const p a y]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hv x).1 (noiseKernel_nonneg h₀ h₁ x y)
  · rw [← applyNoise_const p b y]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hv x).2 (noiseKernel_nonneg h₀ h₁ x y)

theorem applyNoise_indicator {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    applyNoise p (fun x => if f x = true then 1 else 0) y = Information.posterior f p y := by
  classical
  unfold applyNoise Information.posterior
  apply Finset.sum_congr rfl
  intro x _
  cases h : f x <;> simp [h]

theorem applyNoise_sum {n : ℕ} (p : ℝ) (v : Cube n → ℝ) :
    ∑ y, applyNoise p v y = ∑ x, v x := by
  unfold applyNoise
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, noiseKernel_sum]

theorem applyNoise_affine {n : ℕ} (p a b : ℝ) (v : Cube n → ℝ) (y : Cube n) :
    applyNoise p (fun x => a + b * v x) y = a + b * applyNoise p v y := by
  unfold applyNoise
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Information.kernel_column_sum, one_mul]
  simp_rw [mul_left_comm _ b, ← Finset.mul_sum]

theorem applyNoise_mean {n : ℕ} (p : ℝ) (v : Cube n → ℝ) :
    (2 : ℝ) ^ (-(n : ℤ)) * ∑ y, applyNoise p v y =
      (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, v x := by rw [applyNoise_sum]

theorem kernel_zero {n : ℕ} (x y : Cube n) :
    noiseKernel 0 x y = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp [noiseKernel]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

@[simp] theorem applyNoise_zero {n : ℕ} (v : Cube n → ℝ) (y : Cube n) :
    applyNoise 0 v y = v y := by
  classical
  simp [applyNoise, kernel_zero]














theorem sum_flip {n : ℕ} (v : Cube n → ℝ) (i : Fin n) :
    ∑ y, v (flip y i) = ∑ y, v y := (flipEquiv i).sum_comp v

end GeneralCK.Noise


