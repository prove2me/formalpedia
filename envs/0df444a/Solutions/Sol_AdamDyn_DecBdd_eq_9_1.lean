-- Prove2me | solution 1 for AdamDyn.DecBdd.eq_9_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:25:54.353241+00:00
-- url     : https://prove2.me/submissions/0b6a771e-17b5-4c53-b035-6a036d32f7a9

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_Assumptions
import Definitions.Def_AdamDyn_DecBdd_ProofQuantities

open Filter Topology

namespace Aux_ADB_91

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma descent (f : H → ℝ) (g : H → H) (hd : ∀ z, HasFDerivAt f (toDual ℝ H (g z)) z) (L : ℝ)
    (hS : ∀ a b : H, ‖g a - g b‖ ≤ L * ‖a - b‖) (x z : H) :
    f z ≤ f x + inner ℝ (g x) (z - x) + L / 2 * ‖z - x‖ ^ 2 := by
  set v := z - x with hv
  set c := inner ℝ (g x) v with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - L / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt ψ (inner ℝ (g (x + t • v)) v - c - L * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h1 := (hd (x + t • v)).comp_hasDerivAt t hline
    rw [toDual_apply_apply] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hL := hS (x + t • v) x
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hi : inner ℝ (g (x + t • v)) v - c ≤ ‖g (x + t • v) - g x‖ * ‖v‖ := by
        rw [hc, ← inner_sub_left]
        exact real_inner_le_norm _ _
      rw [hn] at hL
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hL (norm_nonneg v)]
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = z := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  linarith

lemma bias (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1) :
    ∀ n, AdamDyn.DecConv.biasWeight α n ≤ 1 ∧
      (1 ≤ n → 1 - α 1 ≤ AdamDyn.DecConv.biasWeight α n) := by
  intro n
  induction n with
  | zero => simp [AdamDyn.DecConv.biasWeight]
  | succ k ih =>
    have e : AdamDyn.DecConv.biasWeight α (k + 1) =
        α (k + 1) * AdamDyn.DecConv.biasWeight α k + (1 - α (k + 1)) := rfl
    obtain ⟨h0, h1⟩ := hα (k + 1)
    refine ⟨?_, fun _ => ?_⟩
    · rw [e]; nlinarith [ih.1]
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [e]; simp [AdamDyn.DecConv.biasWeight]
      · have := ih.2 hk
        rw [e]; nlinarith [ih.1]

end Aux_ADB_91

open AdamDyn.DecBdd Aux_ADB_91 InnerProductSpace in
theorem solution {d : ℕ} {Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (F : AdamDyn.ConstStep.E d → ℝ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hε : 0 < ε) (h51 : AdamDyn.DecConv.Assumption51 γ α β a b) (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hF : Differentiable ℝ F) (hL : ∃ L : NNReal, LipschitzWith L (gradient F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξs : ℕ → Ξ) (n : ℕ), α (n + 2) < 1 →
      F (adamRun gf γ α β ε x0 ξs (n + 1)).1 ≤
        F (adamRun gf γ α β ε x0 ξs n).1
          - γ (n + 1) * inner ℝ (gradient F (adamRun gf γ α β ε x0 ξs (n + 1)).1)
              (adamDir α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)))
          + C * γ (n + 1) ^ 2 * potP γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs (n + 1)) := by
  obtain ⟨L, hLip⟩ := hL
  have hLg : ∀ u w, ‖gradient F u - gradient F w‖ ≤ (L : ℝ) * ‖u - w‖ := fun u w => by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hLip.dist_le_mul u w
  have hd : ∀ z, HasFDerivAt F (toDual ℝ _ (gradient F z)) z := fun z =>
    hasGradientAt_iff_hasFDerivAt.mp (hF z).hasGradientAt
  have low : ∀ x z, F x + inner ℝ (gradient F x) (z - x) - (L : ℝ) / 2 * ‖z - x‖ ^ 2 ≤ F z := by
    intro x z
    have := descent (fun y => -F y) (fun y => -gradient F y)
      (fun y => by have := (hd y).neg; rwa [← map_neg] at this) L
      (fun u w => by rw [neg_sub_neg, norm_sub_rev u w]; exact hLg w u) x z
    simp only [inner_neg_left] at this
    linarith
  have hr := bias α h51.α_mem
  have hAt : Tendsto (fun n => aSeq γ α n) atTop (𝓝 a) := by
    have h1 : Tendsto (fun n => (1 - α (n + 1)) / γ (n + 1)) atTop (𝓝 a) :=
      h51.α_lim.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.mul h51.γ_ratio
    rw [mul_one] at h2
    refine h2.congr (fun n => ?_)
    have g0 := (h51.γ_pos n).ne'
    have g1 := (h51.γ_pos (n + 1)).ne'
    simp only [aSeq]
    field_simp
  obtain ⟨A, hA⟩ := hAt.bddAbove_range
  have hr1 : 0 < 1 - α 1 := by linarith
  refine ⟨L * max A 0 / (ε * (1 - α 1)) + 1, by positivity, ?_⟩
  intro ξs n hαn
  obtain ⟨z, hz⟩ : ∃ z, z = adamRun gf γ α β ε x0 ξs (n + 1) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = (adamRun gf γ α β ε x0 ξs n).1 := ⟨_, rfl⟩
  rw [← hz, ← hx]
  have hstep : z.1 = x - γ (n + 1) • adamDir α β ε (n + 1) z := by
    rw [hz, hx]; rfl
  obtain ⟨dir, hdir⟩ : ∃ dir, dir = adamDir α β ε (n + 1) z := ⟨_, rfl⟩
  rw [← hdir] at hstep ⊢
  have hlow := low z.1 x
  have hxz : x - z.1 = γ (n + 1) • dir := by rw [hstep]; abel
  rw [hxz, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hlow
  obtain ⟨rr, hrrd⟩ : ∃ rr, rr = AdamDyn.DecConv.biasWeight α (n + 1) := ⟨_, rfl⟩
  obtain ⟨aa, haad⟩ : ∃ aa, aa = aSeq γ α (n + 1) := ⟨_, rfl⟩
  have hrr : 1 - α 1 ≤ rr := by rw [hrrd]; exact (hr (n + 1)).2 (by omega)
  have hrr0 : 0 < rr := lt_of_lt_of_le hr1 hrr
  have haa : 0 < aa := by
    rw [haad, aSeq]
    exact div_pos (by linarith) (h51.γ_pos _)
  have haA : aa ≤ max A 0 := le_trans (by rw [haad]; exact hA ⟨n + 1, rfl⟩) (le_max_left _ _)
  obtain ⟨S, hSd⟩ : ∃ S, S = ∑ i, z.2.1 i ^ 2 / (ε + Real.sqrt (vHat β (n + 1) z i)) :=
    ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSd]
    exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by positivity))
  have hP : potP γ α β ε (n + 1) z = 1 / (2 * aa * rr) * S := by
    rw [hSd, haad, hrrd]; rfl
  have hdn : ‖dir‖ ^ 2 ≤ S / (rr ^ 2 * ε) := by
    rw [EuclideanSpace.norm_sq_eq, hSd, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    rw [hdir]
    simp only [adamDir, mHat, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    rw [← hrrd]
    obtain ⟨e, hed⟩ : ∃ e, e = ε + Real.sqrt (vHat β (n + 1) z i) := ⟨_, rfl⟩
    rw [← hed]
    have he : ε ≤ e := by rw [hed]; exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have he0 : 0 < e := lt_of_lt_of_le hε he
    rw [div_pow, div_pow, div_div, div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have : 0 ≤ rr ^ 2 * e * (e - ε) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have c1 : (L : ℝ) * aa / (rr * ε) ≤ L * max A 0 / (ε * (1 - α 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul haA hrr hr1.le (le_max_right A 0)
    have hL0 : (0 : ℝ) ≤ L * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hL0]
  have e1 : (L : ℝ) / 2 * (S / (rr ^ 2 * ε)) = L * aa / (rr * ε) * (1 / (2 * aa * rr) * S) := by
    field_simp
  have hP0 : 0 ≤ 1 / (2 * aa * rr) * S := by positivity
  have hγ2 : 0 ≤ γ (n + 1) ^ 2 := sq_nonneg _
  have k1 : (L : ℝ) / 2 * (γ (n + 1) ^ 2 * ‖dir‖ ^ 2) ≤
      (L * max A 0 / (ε * (1 - α 1)) + 1) * γ (n + 1) ^ 2 * (1 / (2 * aa * rr) * S) := by
    have s1 : (L : ℝ) / 2 * ‖dir‖ ^ 2 ≤ L / 2 * (S / (rr ^ 2 * ε)) :=
      mul_le_mul_of_nonneg_left hdn (by positivity)
    rw [e1] at s1
    have s2 : (L : ℝ) * aa / (rr * ε) * (1 / (2 * aa * rr) * S) ≤
        (L * max A 0 / (ε * (1 - α 1)) + 1) * (1 / (2 * aa * rr) * S) :=
      mul_le_mul_of_nonneg_right (by linarith) hP0
    have s3 := mul_le_mul_of_nonneg_left (le_trans s1 s2) hγ2
    nlinarith
  rw [hP]
  nlinarith
