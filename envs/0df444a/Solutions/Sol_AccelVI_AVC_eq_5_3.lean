-- Prove2me | solution 1 for AccelVI.AVC.eq_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:06:56.55107+00:00
-- url     : https://prove2.me/submissions/376253b5-d7e0-4e9d-ac48-7eda575be5b0

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

set_option autoImplicit false
open AccelVI.AVC

section mmD
variable {S : Type*} [Fintype S] [DecidableEq S]

lemma mmD_eig (M : Matrix S S ℂ) (μ : ℂ) (h : μ ∈ spectrum ℂ M) :
    ∃ v : S → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  have : (algebraMap ℂ (Matrix S S ℂ) μ - M).mulVec v = μ • v - M.mulVec v := by
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [this] at hv0
  exact (sub_eq_zero.mp hv0).symm

lemma mmD_eig_conv (M : Matrix S S ℂ) (μ : ℂ) (v : S → ℂ) (hv : v ≠ 0) (h : M.mulVec v = μ • v) :
    μ ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, h,
    sub_self]

lemma mmD_theta_pos (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) : 0 < theta lam := by
  unfold theta kappa
  have h2 : 1 / ((1 + lam) / (1 - lam)) < 1 := by
    rw [one_div_div, div_lt_one (by linarith)]
    linarith
  have h3 : Real.sqrt (1 / ((1 + lam) / (1 - lam))) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using h2
  linarith

end mmD

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) :
    ∀ ω ∈ spectrum ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)),
      ∃ μ ∈ spectrum ℂ ((LPol M pol).map (algebraMap ℝ ℂ)),
        ω ^ 2 - (μ + 1) * (theta M.lam : ℂ) * ω + 1 / 2 * (μ + 1) * (theta M.lam : ℂ) ^ 2 = 0 := by
  intro ω hω
  obtain ⟨-, h0, h1⟩ := hM
  have hθ : theta M.lam ≠ 0 := (mmD_theta_pos _ h0 h1).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (theta M.lam : ℂ) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast hθ
  obtain ⟨Lc, hLc⟩ : ∃ Lc : Matrix S S ℂ, Lc = (LPol M pol).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  rw [← hLc]
  rw [← hc]
  obtain ⟨w, hw, hBw⟩ := mmD_eig _ ω hω
  have hB : (Bpol M pol).map (algebraMap ℝ ℂ) =
      Matrix.fromBlocks (c • (1 + Lc)) (-(c ^ 2 / 2) • (1 + Lc)) 1 0 := by
    unfold Bpol
    rw [Matrix.fromBlocks_map]
    congr 1
    · ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul, hLc, hc]
      split_ifs <;> simp
    · ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul, hLc, hc]
      split_ifs <;> simp
    · ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
  rw [hB] at hBw
  obtain ⟨x, hx⟩ : ∃ x : S → ℂ, x = w ∘ Sum.inl := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : S → ℂ, y = w ∘ Sum.inr := ⟨_, rfl⟩
  have hwxy : w = Sum.elim x y := by rw [hx, hy]; exact (Sum.elim_comp_inl_inr w).symm
  rw [hwxy, Matrix.fromBlocks_mulVec] at hBw
  have e1 : (c • (1 + Lc)).mulVec x + (-(c ^ 2 / 2) • (1 + Lc)).mulVec y = ω • x := by
    funext i
    have := congrFun hBw (Sum.inl i)
    simpa using this
  have e2 : x = ω • y := by
    funext i
    have := congrFun hBw (Sum.inr i)
    simpa [Matrix.one_mulVec] using this
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hw
    have hx0 : x = 0 := by rw [e2, hy0, smul_zero]
    rw [hwxy, hx0, hy0]
    funext i; rcases i with i | i <;> simp
  have hK : (c * ω - c ^ 2 / 2) • (y + Lc.mulVec y) = (ω ^ 2) • y := by
    rw [e2] at e1
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.add_mulVec, Matrix.one_mulVec] at e1
    calc (c * ω - c ^ 2 / 2) • (y + Lc.mulVec y)
        = ω • c • (y + Lc.mulVec y) + (-(c ^ 2 / 2)) • (y + Lc.mulVec y) := by module
      _ = ω • ω • y := e1
      _ = (ω ^ 2) • y := by module
  have hk : c * ω - c ^ 2 / 2 ≠ 0 := by
    intro hk0
    rw [hk0, zero_smul] at hK
    have : ω ^ 2 • y = 0 := hK.symm
    rcases smul_eq_zero.mp this with h | h
    · have : ω = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
      rw [this] at hk0
      have : c ^ 2 = 0 := by linear_combination (-2 : ℂ) * hk0
      exact hc0 (pow_eq_zero_iff two_ne_zero |>.mp this)
    · exact hy0 h
  refine ⟨ω ^ 2 / (c * ω - c ^ 2 / 2) - 1, ?_, ?_⟩
  · apply mmD_eig_conv _ _ y hy0
    have : Lc.mulVec y = (ω ^ 2 / (c * ω - c ^ 2 / 2) - 1) • y := by
      have h2 : y + Lc.mulVec y = (ω ^ 2 / (c * ω - c ^ 2 / 2)) • y := by
        have := congrArg (fun z => (c * ω - c ^ 2 / 2)⁻¹ • z) hK
        simp only [smul_smul, inv_mul_cancel₀ hk] at this
        rw [one_smul] at this
        rw [this, ← div_eq_inv_mul]
      rw [sub_smul, one_smul, ← h2]; abel
    rw [this]
  · rw [sub_add_cancel]
    linear_combination (-1 : ℂ) * (div_mul_cancel₀ (ω ^ 2) hk)
