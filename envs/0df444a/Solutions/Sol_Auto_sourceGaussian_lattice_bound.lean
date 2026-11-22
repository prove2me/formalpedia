-- Prove2me | solution 1 for Auto.sourceGaussian_lattice_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:49:12.843805+00:00
-- url     : https://prove2.me/submissions/e7cfc1a0-71c3-43d5-8182-8aaaf21f05c5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gridGaussianForm_bound
public import Theorems.Thm_Auto_exists_fin_shift
public import Theorems.Thm_Auto_sum_eq_tsum_of_injective
public import Theorems.Thm_Auto_int_bounds_of_ne_zero

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (F : Fin 3 → ℝ × ℝ → ℂ) {ρ : ℝ}
    (_hρ : 0 ≤ ρ) (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : ((N : ℝ)⁻¹) ^ 2 ≤ a) (hab : a ≤ b) :
    ‖((N : ℝ)⁻¹) ^ 3 • ∑' z : Fin 3 → ℤ,
        sourceGaussianIntegrand F a b (fun i => (z i : ℝ) / N)‖ ≤
      3 * heatBoundConstant *
        ∏ v, (((N : ℝ)⁻¹) ^ 2 *
          ∑' z : Fin 2 → ℤ, ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3) ^
            (1 / 3 : ℝ) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let R : ℕ := ⌈ρ * N⌉₊
  let kk : Fin (2 * R + 1) → ℤ := fun i => (i : ℤ) - R
  have hk : Function.Injective kk := by
    intro i j hij
    simp only [kk, sub_left_inj] at hij
    exact Fin.ext (by exact_mod_cast hij)
  have hfind : ∀ w : ℤ, (|w| : ℝ) ≤ ρ * N → ∃ i, kk i = w := by
    intro w hw
    exact exists_fin_shift (by exact_mod_cast hw.trans (Nat.le_ceil _))
  let u : Fin (2 * R + 1) → ℝ := fun i => (kk i : ℝ) / N
  let Hd : HeatData (Fin (2 * R + 1)) :=
    ⟨u, (N : ℝ)⁻¹, fun v i j => F v (u i, u j)⟩
  have hn (v : Fin 3) : nNorm Hd.h (Hd.A v) =
      (((N : ℝ)⁻¹) ^ 2 *
        ∑' z : Fin 2 → ℤ, ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3) ^
          (1 / 3 : ℝ) := by
    let e : Fin (2 * R + 1) × Fin (2 * R + 1) → (Fin 2 → ℤ) :=
      fun t => ![kk t.1, kk t.2]
    have he : Function.Injective e := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ hij
      have h0 := congrFun hij 0
      have h1 := congrFun hij 1
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [hk h0, hk h1]
    have hs : ∀ z : Fin 2 → ℤ,
        ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3 ≠ 0 → z ∈ Set.range e := by
      intro z hz
      obtain ⟨b0, b1⟩ := int_bounds_of_ne_zero (hF v) hN
        (a := z 0) (b := z 1) (fun h => hz (by simp [h]))
      obtain ⟨i, hi⟩ := hfind (z 0) b0
      obtain ⟨j, hj⟩ := hfind (z 1) b1
      refine ⟨(i, j), ?_⟩
      funext l
      fin_cases l <;> simp [e, hi, hj]
    unfold nNorm
    rw [← sum_eq_tsum_of_injective e he _ hs, Fintype.sum_prod_type]
    rfl
  have hsum : gridGaussianForm Hd a b =
      ((N : ℝ)⁻¹) ^ 3 • ∑' z : Fin 3 → ℤ,
        sourceGaussianIntegrand F a b (fun i => (z i : ℝ) / N) := by
    let e : Fin (2 * R + 1) × Fin (2 * R + 1) × Fin (2 * R + 1) →
        (Fin 3 → ℤ) := fun t => ![kk t.1, kk t.2.1, kk t.2.2]
    have he : Function.Injective e := by
      rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hij
      have h0 := congrFun hij 0
      have h1 := congrFun hij 1
      have h2 := congrFun hij 2
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] at h0 h1 h2
      rw [hk h0, hk h1, hk h2]
    have hs : ∀ z, sourceGaussianIntegrand F a b
        (fun i => (z i : ℝ) / N) ≠ 0 → z ∈ Set.range e := by
      intro z hz
      have hp := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1
      obtain ⟨b0, b1⟩ := int_bounds_of_ne_zero (hF 0) hN
        (mul_ne_zero_iff.mp hp.1).1
      obtain ⟨_, b2⟩ := int_bounds_of_ne_zero (hF 1) hN
        (mul_ne_zero_iff.mp hp.1).2
      obtain ⟨i, hi⟩ := hfind (z 0) b0
      obtain ⟨j, hj⟩ := hfind (z 1) b1
      obtain ⟨k, hk'⟩ := hfind (z 2) b2
      refine ⟨(i, j, k), ?_⟩
      funext l
      fin_cases l <;> simp [e, hi, hj, hk']
    rw [← sum_eq_tsum_of_injective e he _ hs, Fintype.sum_prod_type,
      Fintype.sum_congr _ _ fun i => Fintype.sum_prod_type _]
    simp only [gridGaussianForm, sourceGaussianIntegrand, Hd, u, e,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Complex.real_smul, Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_pow]
  have h := gridGaussianForm_bound Hd hk (fun i => by dsimp [Hd, u]; ring)
    (inv_pos.mpr hN') ha hab
  rw [hsum, hn, hn, hn] at h
  simpa [Fin.prod_univ_succ, mul_assoc] using h
end Auto
