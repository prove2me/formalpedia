-- Prove2me | solution 1 for AdaGradDHS.Diag.theorem_5_diagonal_adagrad_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T20:02:56.003952+00:00
-- url     : https://prove2.me/submissions/76d3f164-b430-4a76-8a03-845a0e9bfa1d

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_IsSubgradFeedback
import Definitions.Def_AdaGradDHS_Diag_IsPrimalDualRun
import Definitions.Def_AdaGradDHS_Diag_IsCompositeMDRun
import Definitions.Def_AdaGradDHS_Diag_regret
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm
import Definitions.Def_AdaGradDHS_Diag_maxSupDev

set_option autoImplicit false

namespace AdaGradDHS.Diag.T5Aux

open AdaGradDHS.Diag

variable {d : ℕ}

/-- Diagonal quadratic distance `½ Σ a_i (u_i - v_i)²`. -/
noncomputable def qd (a : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / 2 * ∑ i, a i * (u i - v i) ^ 2

lemma qd_nonneg (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (u v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ qd a u v := by
  unfold qd
  have : 0 ≤ ∑ i, a i * (u i - v i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
  linarith

lemma qd_mono (a b : Fin d → ℝ) (hab : ∀ i, a i ≤ b i) (u v : EuclideanSpace ℝ (Fin d)) :
    qd a u v ≤ qd b u v := by
  unfold qd
  have : ∑ i, a i * (u i - v i) ^ 2 ≤ ∑ i, b i * (u i - v i) ^ 2 :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hab i) (sq_nonneg _))
  linarith

lemma inner_eq_sum (u v : EuclideanSpace ℝ (Fin d)) : inner ℝ u v = ∑ i, u i * v i := by
  simp [PiLp.inner_apply, mul_comm]

lemma norm_sq_sum (u : EuclideanSpace ℝ (Fin d)) : ‖u‖ ^ 2 = ∑ i, (u i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

lemma expand_qd (a : Fin d → ℝ) (z y c : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    qd a (z + s • (y - z)) c
      = qd a z c + s * ∑ i, a i * (z i - c i) * (y i - z i) + s ^ 2 * qd a y z := by
  unfold qd
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

lemma gap {X : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ConvexOn ℝ X φ) (w : EuclideanSpace ℝ (Fin d)) {k : ℝ} (hk : 0 ≤ k)
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (c z y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ X) (hy : y ∈ X)
    (hmin : ∀ v ∈ X, inner ℝ w z + k * φ z + qd a z c ≤ inner ℝ w v + k * φ v + qd a v c) :
    inner ℝ w z + k * φ z + qd a z c + qd a y z ≤ inner ℝ w y + k * φ y + qd a y c := by
  set α := ∑ i, a i * (z i - c i) * (y i - z i) with hα
  set β := qd a y z with hβ
  have hβ0 : 0 ≤ β := qd_nonneg a ha y z
  set K := inner ℝ w (y - z) + k * (φ y - φ z) + α with hK
  have hinner : inner ℝ w (y - z) = inner ℝ w y - inner ℝ w z := inner_sub_right _ _ _
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ K + s * β := by
    intro s hs0 hs1
    have hzs : z + s • (y - z) ∈ X := hφ.1.add_smul_sub_mem hz hy ⟨hs0.le, hs1⟩
    have hle := hmin _ hzs
    have hφs : φ (z + s • (y - z)) ≤ (1 - s) * φ z + s * φ y := by
      have h := hφ.2 hz hy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      have e : (1 - s) • z + s • y = z + s • (y - z) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [e] at h
      simpa [smul_eq_mul] using h
    rw [expand_qd, inner_add_right, real_inner_smul_right] at hle
    have h3 : k * φ (z + s • (y - z)) ≤ k * ((1 - s) * φ z + s * φ y) :=
      mul_le_mul_of_nonneg_left hφs hk
    have h4 : 0 ≤ s * (K + s * β) := by
      rw [hK]; nlinarith
    by_contra hneg
    rw [not_le] at hneg
    have : s * (K + s * β) < 0 := mul_neg_of_pos_of_neg hs0 hneg
    linarith
  have hK0 : 0 ≤ K := by
    by_contra hneg
    rw [not_le] at hneg
    set s := min 1 (-K / (β + 1)) with hsdef
    have hc1 : 0 < β + 1 := by linarith
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hc1)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ -K / (β + 1) := min_le_right _ _
    have h5 := key s hs0 hs1
    have h6 : s * (β + 1) ≤ -K := (le_div_iff₀ hc1).mp hs2
    nlinarith
  have e2 : z + (1 : ℝ) • (y - z) = y := by rw [one_smul]; abel
  have hq := expand_qd a z y c 1
  rw [e2] at hq
  nlinarith

lemma hasFDerivAt_quad (a : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => 1 / 2 * ∑ i, a i * (x i) ^ 2)
      ((1 / 2 : ℝ) • ∑ i, (a i * (2 * v i)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) v := by
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.fun_sum
  intro i _
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => x i)
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt
  have h2 := (h1.pow 2).const_mul (a i)
  refine h2.congr_fderiv ?_
  ext w
  norm_num [smul_eq_mul] <;> ring

lemma fderiv_quad (a : Fin d → ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => 1 / 2 * ∑ i, a i * (x i) ^ 2) v w
      = ∑ i, a i * v i * w i := by
  rw [(hasFDerivAt_quad a v).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) w = w i from rfl]
  ring

lemma psi_eq (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    adagradPsi δ g t = fun x => 1 / 2 * ∑ i, (δ + accNorm g t i) * (x i) ^ 2 := by
  funext x; rfl

lemma psi_eq_qd (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    adagradPsi δ g t y = qd (fun i => δ + accNorm g t i) y 0 := by
  rw [psi_eq]; unfold qd; simp

lemma bregman_psi (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    bregman (adagradPsi δ g t) u v = qd (fun i => δ + accNorm g t i) u v := by
  have hg : inner ℝ (gradient (adagradPsi δ g t) v) (u - v)
      = ∑ i, (δ + accNorm g t i) * v i * (u - v) i := by
    rw [gradient, InnerProductSpace.toDual_symm_apply, psi_eq, fderiv_quad]
  unfold bregman
  rw [hg]
  simp only [psi_eq, qd, PiLp.sub_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma accNorm_nonneg (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    0 ≤ accNorm g t i := Real.sqrt_nonneg _

lemma accNorm_zero (g : ℕ → EuclideanSpace ℝ (Fin d)) (i : Fin d) : accNorm g 0 i = 0 := by
  simp [accNorm]

lemma accNorm_sq (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    accNorm g (t + 1) i ^ 2 = accNorm g t i ^ 2 + (g (t + 1) i) ^ 2 := by
  unfold accNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Finset.sum_Icc_succ_top (by omega)]

lemma accNorm_mono (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    accNorm g t i ≤ accNorm g (t + 1) i := by
  have h1 := accNorm_sq g t i
  have h2 := accNorm_nonneg g (t + 1) i
  have h3 := accNorm_nonneg g t i
  nlinarith [sq_nonneg (g (t + 1) i)]

lemma accNorm_succ_le (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) (i : Fin d) {δ : ℝ}
    (hδ : |g (n + 1) i| ≤ δ) : accNorm g (n + 1) i ≤ δ + accNorm g n i := by
  have h1 := accNorm_sq g n i
  have h2 := accNorm_nonneg g (n + 1) i
  have h3 := accNorm_nonneg g n i
  have h0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have h4 : (g (n + 1) i) ^ 2 ≤ δ ^ 2 := by
    have := sq_abs (g (n + 1) i)
    nlinarith [abs_nonneg (g (n + 1) i)]
  nlinarith [sq_nonneg (accNorm g (n + 1) i - δ - accNorm g n i)]

lemma abs_le_supNorm (u : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |u i| ≤ supNorm u := by
  unfold supNorm
  have h : ‖u i‖₊ ≤ Finset.univ.sup (fun j => ‖u j‖₊) :=
    Finset.le_sup (f := fun j => ‖u j‖₊) (Finset.mem_univ i)
  have h2 : ((‖u i‖₊ : NNReal) : ℝ) ≤ ((Finset.univ.sup (fun j => ‖u j‖₊) : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  rw [coe_nnnorm, Real.norm_eq_abs] at h2
  exact h2

lemma abs_le_maxSupDev (x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    (T t : ℕ) (ht : t ∈ Finset.Icc 1 T) (i : Fin d) :
    |xstar i - x t i| ≤ maxSupDev x xstar T := by
  unfold maxSupDev
  have h1 : ‖xstar i - x t i‖₊ ≤ Finset.univ.sup (fun j => ‖xstar j - x t j‖₊) :=
    Finset.le_sup (f := fun j => ‖xstar j - x t j‖₊) (Finset.mem_univ i)
  have h2 : Finset.univ.sup (fun j => ‖xstar j - x t j‖₊)
      ≤ (Finset.Icc 1 T).sup (fun s => Finset.univ.sup fun j => ‖xstar j - x s j‖₊) :=
    Finset.le_sup (f := fun s => Finset.univ.sup fun j => ‖xstar j - x s j‖₊) ht
  have h3 : ((‖xstar i - x t i‖₊ : NNReal) : ℝ)
      ≤ (((Finset.Icc 1 T).sup (fun s => Finset.univ.sup fun j => ‖xstar j - x s j‖₊) : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (h1.trans h2)
  rw [coe_nnnorm, Real.norm_eq_abs] at h3
  exact h3

lemma sq_le_of_abs_le {r D : ℝ} (h : |r| ≤ D) : r ^ 2 ≤ D ^ 2 := by
  have h2 := pow_le_pow_left₀ (abs_nonneg r) h 2
  rwa [sq_abs] at h2

lemma step_bound {η g u H s s' : ℝ} (hs' : 0 ≤ s') (hs : 0 ≤ s) (hH : s ≤ H)
    (hsq : s ^ 2 = s' ^ 2 + g ^ 2) : η * g * u - 1 / 2 * H * u ^ 2 ≤ η ^ 2 * (s - s') := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have hg2 : g ^ 2 = 0 := by nlinarith [sq_nonneg g, sq_nonneg s']
    have hs2 : s' ^ 2 = 0 := by nlinarith [sq_nonneg g, sq_nonneg s']
    have hg : g = 0 := pow_eq_zero_iff two_ne_zero |>.mp hg2
    have hs0 : s' = 0 := pow_eq_zero_iff two_ne_zero |>.mp hs2
    subst hg; subst hs0
    nlinarith [mul_nonneg hH (sq_nonneg u)]
  · have e : η ^ 2 * g ^ 2 = η ^ 2 * (s ^ 2 - s' ^ 2) := by rw [hsq]; ring
    have key : 0 ≤ s * (η ^ 2 * (s - s') - (η * g * u - 1 / 2 * H * u ^ 2)) := by
      nlinarith [sq_nonneg (s * u - η * g), sq_nonneg (η * (s - s')),
        mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg u))]
    have := (mul_nonneg_iff_of_pos_left hpos).mp key
    linarith

lemma step_vec (η : ℝ) (gv p q : EuclideanSpace ℝ (Fin d)) (H s s' : Fin d → ℝ)
    (hs' : ∀ i, 0 ≤ s' i) (hs : ∀ i, 0 ≤ s i) (hH : ∀ i, s i ≤ H i)
    (hsq : ∀ i, s i ^ 2 = s' i ^ 2 + gv i ^ 2) :
    η * inner ℝ gv (p - q) - qd H q p ≤ η ^ 2 * ∑ i, (s i - s' i) := by
  rw [inner_eq_sum]; unfold qd
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := step_bound (η := η) (u := p i - q i) (hs' i) (hs i) (hH i) (hsq i)
  simp only [PiLp.sub_apply]
  nlinarith [h]

lemma qd_diff (a b : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) (D : ℝ)
    (hab : ∀ i, a i ≤ b i) (hD : ∀ i, (u i - v i) ^ 2 ≤ D ^ 2) :
    qd b u v - qd a u v ≤ 1 / 2 * D ^ 2 * ∑ i, (b i - a i) := by
  unfold qd
  have h : ∑ i, b i * (u i - v i) ^ 2 - ∑ i, a i * (u i - v i) ^ 2
      ≤ D ^ 2 * ∑ i, (b i - a i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have := mul_le_mul_of_nonneg_left (hD i) (sub_nonneg.2 (hab i))
    nlinarith [this]
  nlinarith [h]

lemma psi_bound (δ : ℝ) (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i) (u : EuclideanSpace ℝ (Fin d))
    (N : ℝ) (hN : ∀ i, (u i) ^ 2 ≤ N ^ 2) :
    qd (fun i => δ + s i) u 0 ≤ δ / 2 * ‖u‖ ^ 2 + 1 / 2 * N ^ 2 * ∑ i, s i := by
  rw [norm_sq_sum]
  unfold qd
  have h : ∑ i, (δ + s i) * (u i - (0 : EuclideanSpace ℝ (Fin d)) i) ^ 2
      ≤ ∑ i, (δ * (u i) ^ 2 + N ^ 2 * s i) := by
    apply Finset.sum_le_sum
    intro i _
    have := mul_le_mul_of_nonneg_left (hN i) (hs i)
    simp only [PiLp.zero_apply, sub_zero]
    nlinarith [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  nlinarith [h]

lemma sum_shift (F : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, F t + F (T + 1) = F 1 + ∑ t ∈ Finset.Icc 1 T, F (t + 1) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

lemma regret_le {X : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (g x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d))
    (hx1 : x 1 = 0) (hxX : ∀ t ∈ Finset.Icc 1 T, x (t + 1) ∈ X)
    (hfb : IsSubgradFeedback X f g x T) (hxs : xstar ∈ X) :
    regret f φ x xstar T
      ≤ ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (x t - xstar) + φ (x (t + 1)) - φ xstar) := by
  have hshift : ∑ t ∈ Finset.Icc 1 T, φ (x t) ≤ ∑ t ∈ Finset.Icc 1 T, φ (x (t + 1)) := by
    have h := sum_shift (fun t => φ (x t)) T
    have h2 : φ (x 1) ≤ φ (x (T + 1)) := by
      rcases Nat.eq_zero_or_pos T with h0 | hpos
      · subst h0; exact le_rfl
      · rw [hx1]; exact hφ0 _ (hxX T (Finset.mem_Icc.2 ⟨hpos, le_refl _⟩))
    linarith
  have hf : ∀ t ∈ Finset.Icc 1 T, f t (x t) - f t xstar ≤ inner ℝ (g t) (x t - xstar) := by
    intro t ht
    have := hfb t ht xstar hxs
    have e : inner ℝ (g t) (xstar - x t) = - inner ℝ (g t) (x t - xstar) := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have hsum := Finset.sum_le_sum hf
  unfold regret
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum ⊢
  linarith

theorem clause2 {X : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ X φ) (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (T : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx1 : x 1 = 0) (hrun : IsCompositeMDRun X φ (adagradPsi δ g) η g x T)
    (hfb : IsSubgradFeedback X f g x T) (xstar : EuclideanSpace ℝ (Fin d)) (hxs : xstar ∈ X) :
    regret f φ x xstar T ≤
      δ / (2 * η) * ‖xstar‖ ^ 2 + 1 / (2 * η) * maxSupDev x xstar T ^ 2 * ∑ i, accNorm g T i +
        η * ∑ i, accNorm g T i := by
  set D := maxSupDev x xstar T with hD
  have hnorm : ‖xstar‖ ^ 2 = ∑ i, (xstar i) ^ 2 := norm_sq_sum xstar
  have inv : ∀ n, n ≤ T →
      η * ∑ t ∈ Finset.Icc 1 n, (inner ℝ (g t) (x t - xstar) + φ (x (t + 1)) - φ xstar)
        + qd (fun i => δ + accNorm g n i) xstar (x (n + 1))
        ≤ δ / 2 * ‖xstar‖ ^ 2 + 1 / 2 * D ^ 2 * ∑ i, accNorm g n i
          + η ^ 2 * ∑ i, accNorm g n i := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : qd (fun i => δ + accNorm g 0 i) xstar (x (0 + 1)) = δ / 2 * ‖xstar‖ ^ 2 := by
        rw [hnorm, Nat.zero_add, hx1]
        unfold qd
        simp only [accNorm_zero, add_zero, PiLp.zero_apply, sub_zero, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [Finset.Icc_eq_empty (by norm_num), h0]
      simp [accNorm_zero]
    | succ n ih =>
      intro hn
      have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨by omega, hn⟩
      have ih' := ih (by omega)
      obtain ⟨hxX, hmin⟩ := hrun.2 (n + 1) ht
      have hHn : ∀ i, 0 ≤ δ + accNorm g (n + 1) i := fun i => by
        have := accNorm_nonneg g (n + 1) i; linarith
      have hgap := gap hφ (η • g (n + 1)) hη.le (fun i => δ + accNorm g (n + 1) i) hHn
        (x (n + 1)) (x (n + 1 + 1)) xstar hxX hxs (by
          intro v hv
          have := hmin v hv
          rw [bregman_psi, bregman_psi] at this
          rw [real_inner_smul_left, real_inner_smul_left]
          linarith)
      rw [real_inner_smul_left, real_inner_smul_left] at hgap
      have hstep := step_vec η (g (n + 1)) (x (n + 1)) (x (n + 1 + 1))
        (fun i => δ + accNorm g (n + 1) i) (fun i => accNorm g (n + 1) i)
        (fun i => accNorm g n i) (fun i => accNorm_nonneg _ _ _) (fun i => accNorm_nonneg _ _ _)
        (fun i => by linarith) (fun i => accNorm_sq g n i)
      have hdiff := qd_diff (fun i => δ + accNorm g n i) (fun i => δ + accNorm g (n + 1) i)
        xstar (x (n + 1)) D (fun i => by have := accNorm_mono g n i; linarith)
        (fun i => sq_le_of_abs_le (abs_le_maxSupDev x xstar T (n + 1) ht i))
      have e3 : ∑ i, (accNorm g (n + 1) i - accNorm g n i)
          = ∑ i, accNorm g (n + 1) i - ∑ i, accNorm g n i := Finset.sum_sub_distrib _ _
      have e2 : ∑ i, (δ + accNorm g (n + 1) i - (δ + accNorm g n i))
          = ∑ i, accNorm g (n + 1) i - ∑ i, accNorm g n i := by
        rw [← e3]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
      rw [e3] at hstep
      rw [e2] at hdiff
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e1 : inner ℝ (g (n + 1)) (x (n + 1) - xstar)
          = inner ℝ (g (n + 1)) (x (n + 1) - x (n + 1 + 1)) + inner ℝ (g (n + 1)) (x (n + 1 + 1))
            - inner ℝ (g (n + 1)) xstar := by
        rw [inner_sub_right, inner_sub_right]; ring
      rw [e1]
      nlinarith [ih', hgap, hstep, hdiff]
  have hT := inv T le_rfl
  have hB : 0 ≤ qd (fun i => δ + accNorm g T i) xstar (x (T + 1)) :=
    qd_nonneg _ (fun i => by have := accNorm_nonneg g T i; linarith) _ _
  have hreg := regret_le hφ0 f g x T xstar hx1 (fun t ht => (hrun.2 t ht).1) hfb hxs
  have hη0 : η ≠ 0 := hη.ne'
  have key : η * ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (x t - xstar) + φ (x (t + 1)) - φ xstar)
      ≤ η * (δ / (2 * η) * ‖xstar‖ ^ 2 + 1 / (2 * η) * D ^ 2 * ∑ i, accNorm g T i
        + η * ∑ i, accNorm g T i) := by
    have e : η * (δ / (2 * η) * ‖xstar‖ ^ 2 + 1 / (2 * η) * D ^ 2 * ∑ i, accNorm g T i
        + η * ∑ i, accNorm g T i)
        = δ / 2 * ‖xstar‖ ^ 2 + 1 / 2 * D ^ 2 * ∑ i, accNorm g T i
          + η ^ 2 * ∑ i, accNorm g T i := by
      field_simp
    rw [e]; linarith
  have := le_of_mul_le_mul_left key hη
  linarith

theorem clause1 {X : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ X φ) (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (T : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx1 : x 1 = 0) (hrun : IsPrimalDualRun X φ (adagradPsi δ g) η g x T)
    (hfb : IsSubgradFeedback X f g x T) (hg : ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxs : xstar ∈ X) :
    regret f φ x xstar T ≤
      δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, accNorm g T i +
        η * ∑ i, accNorm g T i := by
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    have h1 : regret f φ x xstar 0 = 0 := by
      unfold regret; rw [Finset.Icc_eq_empty (by norm_num)]; simp
    have h2 : ∑ i, accNorm g 0 i = 0 := by simp [accNorm_zero]
    rw [h1, h2]
    have : 0 ≤ δ / η * ‖xstar‖ ^ 2 := mul_nonneg (div_nonneg hδ hη.le) (sq_nonneg _)
    linarith
  have hmin : ∀ t ∈ Finset.Icc 1 T, x (t + 1) ∈ X ∧ ∀ y ∈ X,
      inner ℝ (η • ∑ τ ∈ Finset.Icc 1 t, g τ) (x (t + 1)) + ((t : ℝ) * η) * φ (x (t + 1))
        + qd (fun i => δ + accNorm g t i) (x (t + 1)) 0
      ≤ inner ℝ (η • ∑ τ ∈ Finset.Icc 1 t, g τ) y + ((t : ℝ) * η) * φ y
        + qd (fun i => δ + accNorm g t i) y 0 := by
    intro t ht
    obtain ⟨hxX, h⟩ := hrun.2 t ht
    refine ⟨hxX, fun y hy => ?_⟩
    have h1 := h y hy
    have htpos : (0 : ℝ) < t := by
      have := (Finset.mem_Icc.1 ht).1
      exact_mod_cast this
    have htne : (t : ℝ) ≠ 0 := htpos.ne'
    rw [real_inner_smul_left, real_inner_smul_left, psi_eq_qd, psi_eq_qd] at h1
    rw [real_inner_smul_left, real_inner_smul_left]
    have h2 := mul_le_mul_of_nonneg_left h1 htpos.le
    have e : ∀ A P Q : ℝ, (t : ℝ) * (η * (1 / (t : ℝ) * A) + η * P + 1 / (t : ℝ) * Q)
        = η * A + ((t : ℝ) * η) * P + Q := by
      intro A P Q; field_simp
    rw [e, e] at h2
    exact h2
  have gapF : ∀ n, n < T → ∀ v ∈ X,
      inner ℝ (η • ∑ τ ∈ Finset.Icc 1 n, g τ) (x (n + 1)) + ((n : ℝ) * η) * φ (x (n + 1))
        + qd (fun i => δ + accNorm g n i) (x (n + 1)) 0
        + qd (fun i => δ + accNorm g n i) v (x (n + 1))
      ≤ inner ℝ (η • ∑ τ ∈ Finset.Icc 1 n, g τ) v + ((n : ℝ) * η) * φ v
        + qd (fun i => δ + accNorm g n i) v 0 := by
    intro n hn v hv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Finset.Icc_eq_empty (by norm_num), Nat.zero_add, hx1]
      simp [qd]
    · have hn' : n ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨hpos, hn.le⟩
      obtain ⟨hxX, hm⟩ := hmin n hn'
      exact gap hφ _ (mul_nonneg (Nat.cast_nonneg n) hη.le) _
        (fun i => by have := accNorm_nonneg g n i; linarith) 0 (x (n + 1)) v hxX hv hm
  have inv : ∀ n, n ≤ T →
      η * ∑ t ∈ Finset.Icc 1 n, (inner ℝ (g t) (x t) + φ (x (t + 1)))
        - η ^ 2 * ∑ i, accNorm g n i
      ≤ inner ℝ (η • ∑ τ ∈ Finset.Icc 1 n, g τ) (x (n + 1)) + ((n : ℝ) * η) * φ (x (n + 1))
        + qd (fun i => δ + accNorm g n i) (x (n + 1)) 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Finset.Icc_eq_empty (by norm_num), Nat.zero_add, hx1]
      simp [qd, accNorm_zero]
    | succ n ih =>
      intro hn
      have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨by omega, hn⟩
      have ih' := ih (by omega)
      have hxX := (hmin (n + 1) ht).1
      have hg' := gapF n (by omega) (x (n + 1 + 1)) hxX
      have hstep := step_vec η (g (n + 1)) (x (n + 1)) (x (n + 1 + 1))
        (fun i => δ + accNorm g n i) (fun i => accNorm g (n + 1) i)
        (fun i => accNorm g n i) (fun i => accNorm_nonneg _ _ _) (fun i => accNorm_nonneg _ _ _)
        (fun i => accNorm_succ_le g n i ((abs_le_supNorm _ i).trans (hg (n + 1) ht)))
        (fun i => accNorm_sq g n i)
      have hmono := qd_mono (fun i => δ + accNorm g n i) (fun i => δ + accNorm g (n + 1) i)
        (fun i => by have := accNorm_mono g n i; linarith) (x (n + 1 + 1)) 0
      have e3 : ∑ i, (accNorm g (n + 1) i - accNorm g n i)
          = ∑ i, accNorm g (n + 1) i - ∑ i, accNorm g n i := Finset.sum_sub_distrib _ _
      rw [e3] at hstep
      have hW : inner ℝ (η • ∑ τ ∈ Finset.Icc 1 (n + 1), g τ) (x (n + 1 + 1))
          = inner ℝ (η • ∑ τ ∈ Finset.Icc 1 n, g τ) (x (n + 1 + 1))
            + η * inner ℝ (g (n + 1)) (x (n + 1 + 1)) := by
        rw [Finset.sum_Icc_succ_top (by omega), smul_add, inner_add_left, real_inner_smul_left
          (g (n + 1))]
      have e1 : inner ℝ (g (n + 1)) (x (n + 1) - x (n + 1 + 1))
          = inner ℝ (g (n + 1)) (x (n + 1)) - inner ℝ (g (n + 1)) (x (n + 1 + 1)) :=
        inner_sub_right _ _ _
      rw [e1] at hstep
      rw [Finset.sum_Icc_succ_top (by omega), hW]
      push_cast
      nlinarith [ih', hg', hstep, hmono]
  have hT := inv T le_rfl
  have hTmem : T ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨hTpos, le_rfl⟩
  have hFmin := (hmin T hTmem).2 xstar hxs
  have hFstar : inner ℝ (η • ∑ τ ∈ Finset.Icc 1 T, g τ) xstar + ((T : ℝ) * η) * φ xstar
      = η * ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) xstar + φ xstar) := by
    rw [real_inner_smul_left, sum_inner, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    ring
  have hpsi := psi_bound δ (fun i => accNorm g T i) (fun i => accNorm_nonneg g T i) xstar
    (supNorm xstar) (fun i => sq_le_of_abs_le (abs_le_supNorm xstar i))
  have hreg := regret_le hφ0 f g x T xstar hx1 (fun t ht => (hmin t ht).1) hfb hxs
  have hsplit : ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (x t - xstar) + φ (x (t + 1)) - φ xstar)
      = ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (x t) + φ (x (t + 1)))
        - ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) xstar + φ xstar) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [inner_sub_right]; ring
  have hS : 0 ≤ ∑ i, accNorm g T i := Finset.sum_nonneg (fun i _ => accNorm_nonneg g T i)
  have hN : 0 ≤ supNorm xstar ^ 2 * ∑ i, accNorm g T i := mul_nonneg (sq_nonneg _) hS
  have hx2 : 0 ≤ δ * ‖xstar‖ ^ 2 := mul_nonneg hδ (sq_nonneg _)
  have hη0 : η ≠ 0 := hη.ne'
  have key : η * ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (x t - xstar) + φ (x (t + 1)) - φ xstar)
      ≤ η * (δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, accNorm g T i
        + η * ∑ i, accNorm g T i) := by
    have e : η * (δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, accNorm g T i
        + η * ∑ i, accNorm g T i)
        = δ * ‖xstar‖ ^ 2 + supNorm xstar ^ 2 * ∑ i, accNorm g T i
          + η ^ 2 * ∑ i, accNorm g T i := by
      field_simp
    rw [e, hsplit]
    nlinarith [hT, hFmin, hFstar, hpsi]
  have := le_of_mul_le_mul_left key hη
  linarith

end AdaGradDHS.Diag.T5Aux

open AdaGradDHS.Diag in
theorem solution {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ X φ) (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (T : ℕ) :
    (∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d)),
        x 1 = 0 → IsPrimalDualRun X φ (adagradPsi δ g) η g x T → IsSubgradFeedback X f g x T →
        (∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) →
        ∀ xstar ∈ X, regret f φ x xstar T ≤
          δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, accNorm g T i +
            η * ∑ i, accNorm g T i) ∧
      (∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d)),
        x 1 = 0 → IsCompositeMDRun X φ (adagradPsi δ g) η g x T → IsSubgradFeedback X f g x T →
        ∀ xstar ∈ X, regret f φ x xstar T ≤
          δ / (2 * η) * ‖xstar‖ ^ 2 + 1 / (2 * η) * maxSupDev x xstar T ^ 2 * ∑ i, accNorm g T i +
            η * ∑ i, accNorm g T i) := by
  exact ⟨fun f g x hx1 hrun hfb hg xstar hxs =>
      AdaGradDHS.Diag.T5Aux.clause1 hφ hφ0 hη hδ T f g x hx1 hrun hfb hg xstar hxs,
    fun f g x hx1 hrun hfb xstar hxs =>
      AdaGradDHS.Diag.T5Aux.clause2 hφ hφ0 hη hδ T f g x hx1 hrun hfb xstar hxs⟩
