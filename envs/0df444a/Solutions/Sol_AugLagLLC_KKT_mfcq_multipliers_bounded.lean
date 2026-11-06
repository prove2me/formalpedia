-- Prove2me | solution 1 for AugLagLLC.KKT.mfcq_multipliers_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:36:03.671629+00:00
-- url     : https://prove2.me/submissions/c4e3d8e4-71c9-4cff-9bf6-3344a65b4593

import Mathlib
import Definitions.Def_AugLagLLC_KKT_ConstraintQualifications

open Filter Topology
open scoped InnerProductSpace

namespace AugLagFJ

lemma continuous_gradient_of_C1 {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) : Continuous (gradient F) := by
  have h := hF.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp h

/-- Fritz–John type limit extraction: normalizing by `1 + max ‖aₖ‖ ‖bₖ‖`. -/
lemma fj_limit {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : Continuous (gradient F)) (hH : ∀ i, Continuous (gradient (H i)))
    (hG : ∀ j, Continuous (gradient (G j)))
    {xs : EuclideanSpace ℝ (Fin n)}
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (t : ℝ) (ah : ι → ℝ) (bh : κ → ℝ),
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹) atTop (𝓝 t) ∧
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹ • a (ψ j)) atTop (𝓝 ah) ∧
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹ • b (ψ j)) atTop (𝓝 bh) ∧
      t + max ‖ah‖ ‖bh‖ = 1 ∧
      t • gradient F xs + ∑ i, ah i • gradient (H i) xs + ∑ j, bh j • gradient (G j) xs = 0 := by
  set M : ℕ → ℝ := fun k => max ‖a k‖ ‖b k‖ with hM
  set s : ℕ → ℝ := fun k => (1 + M k)⁻¹ with hs
  have hM0 : ∀ k, 0 ≤ M k := fun k => le_trans (norm_nonneg _) (le_max_left _ _)
  have hs0 : ∀ k, 0 < s k := fun k => inv_pos.2 (by linarith [hM0 k])
  have hsM : ∀ k, s k + s k * M k = 1 := fun k => by
    have : (1 + M k) ≠ 0 := by linarith [hM0 k]
    simp only [hs]; field_simp
  have hs1 : ∀ k, s k ≤ 1 := fun k => by nlinarith [hsM k, hs0 k, hM0 k]
  have hsM1 : ∀ k, s k * M k ≤ 1 := fun k => by nlinarith [hsM k, hs0 k, hM0 k]
  have hna : ∀ k, ‖s k • a k‖ = s k * ‖a k‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 k)]
  have hnb : ∀ k, ‖s k • b k‖ = s k * ‖b k‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 k)]
  have hmax : ∀ k, max ‖s k • a k‖ ‖s k • b k‖ = s k * M k := fun k => by
    rw [hna, hnb, mul_max_of_nonneg _ _ (hs0 k).le]
  set z : ℕ → ℝ × (ι → ℝ) × (κ → ℝ) := fun k => (s k, s k • a k, s k • b k) with hz
  have hzb : ∀ k, z k ∈ Metric.closedBall (0 : ℝ × (ι → ℝ) × (κ → ℝ)) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def]
    simp only [hz, Real.norm_eq_abs, abs_of_pos (hs0 k)]
    refine max_le (hs1 k) (max_le ?_ ?_)
    · rw [hna]; exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (hs0 k).le) (hsM1 k)
    · rw [hnb]; exact le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (hs0 k).le) (hsM1 k)
  obtain ⟨⟨t, ah, bh⟩, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hzb
  have ht : Tendsto (fun j => s (ψ j)) atTop (𝓝 t) := (continuous_fst.tendsto _).comp hlim
  have ha : Tendsto (fun j => s (ψ j) • a (ψ j)) atTop (𝓝 ah) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hb : Tendsto (fun j => s (ψ j) • b (ψ j)) atTop (𝓝 bh) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  refine ⟨ψ, hψ, t, ah, bh, ht, ha, hb, ?_, ?_⟩
  · have h1 : Tendsto (fun j => s (ψ j) + max ‖s (ψ j) • a (ψ j)‖ ‖s (ψ j) • b (ψ j)‖) atTop
        (𝓝 (t + max ‖ah‖ ‖bh‖)) :=
      ht.add ((continuous_norm.tendsto _).comp ha |>.max ((continuous_norm.tendsto _).comp hb))
    have h2 : (fun j => s (ψ j) + max ‖s (ψ j) • a (ψ j)‖ ‖s (ψ j) • b (ψ j)‖) = fun _ => 1 := by
      funext j; rw [hmax]; exact hsM _
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  · have hyψ : Tendsto (fun j => y (ψ j)) atTop (𝓝 xs) := hy.comp hψ.tendsto_atTop
    have h1 : Tendsto (fun j => s (ψ j) • (gradient F (y (ψ j))
        + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
        + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) atTop (𝓝 (t • (0 : EuclideanSpace ℝ (Fin n)))) :=
      ht.smul (hres.comp hψ.tendsto_atTop)
    rw [smul_zero] at h1
    have h2 : Tendsto (fun j => s (ψ j) • (gradient F (y (ψ j))
        + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
        + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) atTop
        (𝓝 (t • gradient F xs + ∑ i, ah i • gradient (H i) xs + ∑ j, bh j • gradient (G j) xs)) := by
      have e : (fun j => s (ψ j) • (gradient F (y (ψ j))
          + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
          + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) = fun j =>
          s (ψ j) • gradient F (y (ψ j)) + ∑ i, (s (ψ j) • a (ψ j)) i • gradient (H i) (y (ψ j))
          + ∑ j', (s (ψ j) • b (ψ j)) j' • gradient (G j') (y (ψ j)) := by
        funext j
        simp only [smul_add, Finset.smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]
      rw [e]
      refine (ht.smul ((hF.tendsto _).comp hyψ)).add ?_ |>.add ?_
      · refine tendsto_finsetSum _ fun i _ => ?_
        exact ((tendsto_pi_nhds.1 ha) i).smul (((hH i).tendsto _).comp hyψ)
      · refine tendsto_finsetSum _ fun i _ => ?_
        exact ((tendsto_pi_nhds.1 hb) i).smul (((hG i).tendsto _).comp hyψ)
    exact tendsto_nhds_unique h2 h1


end AugLagFJ

open AugLagFJ AugLagLLC.KKT

theorem solution {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) (hH : ∀ i, ContDiff ℝ 1 (H i)) (hG : ∀ j, ContDiff ℝ 1 (G j))
    {xs : EuclideanSpace ℝ (Fin n)} (hHx : ∀ i, H i xs = 0) (hGx : ∀ j, G j xs ≤ 0)
    (hmfcq : MFCQAt H G xs)
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ) (hb : ∀ k j, 0 ≤ b k j)
    (hbG : ∀ k j, G j xs < 0 → b k j = 0)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ k, ‖a k‖ ≤ C ∧ ‖b k‖ ≤ C := by
  by_contra hcon
  set M : ℕ → ℝ := fun k => max ‖a k‖ ‖b k‖ with hM
  have hM0 : ∀ k, 0 ≤ M k := fun k => le_trans (norm_nonneg _) (le_max_left _ _)
  have hunb : ∀ C : ℝ, ∃ k, C < M k := by
    intro C
    by_contra h
    push Not at h
    exact hcon ⟨C, fun k => ⟨le_trans (le_max_left _ _) (h k), le_trans (le_max_right _ _) (h k)⟩⟩
  choose σ hσ using fun j : ℕ => hunb (j : ℝ)
  have hσt : Tendsto σ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro K
    set B : ℝ := ∑ i ∈ Finset.range (K + 1), M i with hB
    refine ⟨⌈B⌉₊, fun j hj => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 : M (σ j) ≤ B :=
      Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_range.2 (by omega))
    have h2 : B ≤ (j : ℝ) := le_trans (Nat.le_ceil B) (by exact_mod_cast hj)
    linarith [hσ j]
  have cF := continuous_gradient_of_C1 hF
  have cH := fun i => continuous_gradient_of_C1 (hH i)
  have cG := fun j => continuous_gradient_of_C1 (hG j)
  obtain ⟨ψ, hψ, t, ah, bh, ht, ha, hbt, hnorm, heq⟩ :=
    fj_limit cF cH cG (hy.comp hσt) (fun k => a (σ k)) (fun k => b (σ k)) (hres.comp hσt)
  -- t = 0
  have ht0 : t = 0 := by
    have hsq : Tendsto (fun j => (1 + max ‖a (σ (ψ j))‖ ‖b (σ (ψ j))‖)⁻¹) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => (inv_pos.2 (by linarith [hM0 (σ (ψ j))])).le) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : (j : ℝ) ≤ ψ j := by exact_mod_cast hψ.id_le j
      have h2 := hσ (ψ j)
      rw [one_div, add_comm (j : ℝ)]
      exact inv_anti₀ (by positivity) (by simp only [hM] at h2; linarith)
    exact tendsto_nhds_unique ht hsq
  subst ht0
  simp only [zero_smul, zero_add] at heq hnorm
  -- sign properties of the limit
  have hbh0 : ∀ j, 0 ≤ bh j := fun j =>
    ge_of_tendsto' ((tendsto_pi_nhds.1 hbt) j) fun k => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_pos.2 (by linarith [hM0 (σ (ψ k))])).le (hb _ _)
  have hbhG : ∀ j, G j xs < 0 → bh j = 0 := fun j hj => by
    have := (tendsto_pi_nhds.1 hbt) j
    simp only [Pi.smul_apply, smul_eq_mul, hbG _ j hj, mul_zero] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  obtain ⟨hli, d, hd1, hd2⟩ := hmfcq
  -- inner product with d
  have hin : ∑ j, bh j * ⟪gradient (G j) xs, d⟫_ℝ = 0 := by
    have := congrArg (fun w => ⟪w, d⟫_ℝ) heq
    simp only [inner_add_left, sum_inner, real_inner_smul_left, hd1, mul_zero,
      Finset.sum_const_zero, zero_add, inner_zero_left] at this
    exact this
  have hterm : ∀ j, bh j * ⟪gradient (G j) xs, d⟫_ℝ ≤ 0 := by
    intro j
    rcases lt_or_eq_of_le (hGx j) with hj | hj
    · rw [hbhG j hj, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hbh0 j) (hd2 j hj).le
  have hbz : ∀ j, bh j = 0 := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).1 hin j (Finset.mem_univ _)
    rcases lt_or_eq_of_le (hGx j) with hj | hj
    · exact hbhG j hj
    · rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hd2 j hj).ne
  have hbh : bh = 0 := funext hbz
  subst hbh
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at heq
  have hah : ah = 0 := funext (Fintype.linearIndependent_iff.1 hli ah heq)
  subst hah
  simp at hnorm
