-- Prove2me | solution 1 for AhlforsComplexAnalysis.rmt_extremal_onto
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:35:30.310968+00:00
-- url     : https://prove2.me/submissions/1b147403-2874-49fe-8cf8-057fa67d0912

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_schwarz_lemma

set_option autoImplicit false

open AhlforsComplexAnalysis

/-!
Ahlfors Ch. 6 §1.1, step 4: an extremal injective map `Ω → D` is onto the disk (the square-root
trick).  The disk automorphisms `rmtO_mob a w = (w - a) / (1 - conj a * w)` are developed in the
helper namespace `AhlforsOnto`; the only external dependency is `schwarz_lemma`.
-/

namespace AhlforsOnto

open ComplexConjugate

/-! ### Disk automorphisms -/

/-- The disk automorphism `w ↦ (w - a) / (1 - conj a * w)`; its inverse is `rmtO_mob (-a)`. -/
noncomputable def rmtO_mob (a w : ℂ) : ℂ := (w - a) / (1 - conj a * w)

lemma rmtO_mem_ball {w : ℂ} : w ∈ Metric.ball (0 : ℂ) 1 ↔ ‖w‖ < 1 := by simp

lemma rmtO_norm_sq_identity (a w : ℂ) :
    ‖1 - conj a * w‖ ^ 2 - ‖w - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma rmtO_den_ne {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : 1 - conj a * w ≠ 0 := by
  intro h
  have h1 := rmtO_norm_sq_identity a w
  rw [h, norm_zero] at h1
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg w])
  nlinarith [sq_nonneg ‖w - a‖]

lemma rmtO_mob_norm_lt {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : ‖rmtO_mob a w‖ < 1 := by
  have hd := rmtO_den_ne ha hw
  unfold rmtO_mob
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have h := rmtO_norm_sq_identity a w
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg w])
  by_contra hcon
  have hcon := not_lt.mp hcon
  nlinarith [norm_nonneg (1 - conj a * w), norm_nonneg (w - a)]

lemma rmtO_mob_inv {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    rmtO_mob (-a) (rmtO_mob a w) = w := by
  have hD := rmtO_den_ne ha hw
  have hc : (1 : ℂ) - a * conj a ≠ 0 := by
    rw [Complex.mul_conj]
    intro h
    have h1 : (Complex.normSq a : ℂ) = 1 := by linear_combination -h
    have h2 : Complex.normSq a = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg a]
  unfold rmtO_mob
  have e1 : 1 - conj (-a) * ((w - a) / (1 - conj a * w)) =
      (1 - a * conj a) / (1 - conj a * w) := by
    rw [map_neg]
    field_simp
    ring
  have e2 : (w - a) / (1 - conj a * w) - -a = w * (1 - a * conj a) / (1 - conj a * w) := by
    rw [eq_div_iff hD, sub_neg_eq_add, add_mul, div_mul_cancel₀ _ hD]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hD, mul_div_assoc, div_self hc, mul_one]

lemma rmtO_mob_self (a : ℂ) : rmtO_mob a a = 0 := by simp [rmtO_mob]

lemma rmtO_mob_zero (a : ℂ) : rmtO_mob a 0 = -a := by simp [rmtO_mob]

lemma rmtO_mob_eq_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) (h : rmtO_mob a w = 0) :
    w = a := by
  have hd := rmtO_den_ne ha hw
  unfold rmtO_mob at h
  rcases div_eq_zero_iff.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hd

lemma rmtO_mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (rmtO_mob a) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  have hx' := rmtO_mem_ball.mp hx
  have hy' := rmtO_mem_ball.mp hy
  have := congrArg (rmtO_mob (-a)) hxy
  rwa [rmtO_mob_inv ha hx', rmtO_mob_inv ha hy'] at this

lemma rmtO_mob_analyticOnNhd {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (rmtO_mob a) (Metric.ball 0 1) := by
  intro w hw
  unfold rmtO_mob
  exact (analyticAt_id.sub analyticAt_const).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (rmtO_den_ne ha (rmtO_mem_ball.mp hw))

lemma rmtO_sq_norm_lt {x : ℂ} (hx : ‖x‖ < 1) : ‖x ^ 2‖ < 1 := by
  rw [norm_pow]
  nlinarith [norm_nonneg x]

lemma rmtO_norm_lt_of_sq {x : ℂ} (hx : ‖x ^ 2‖ < 1) : ‖x‖ < 1 := by
  rw [norm_pow] at hx
  nlinarith [norm_nonneg x]

end AhlforsOnto

open AhlforsOnto

theorem solution {Ω : Set ℂ} (hΩ : IsRegion Ω)
    (hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) (hfmap : ∀ z ∈ Ω, ‖f z‖ < 1)
    (hf0 : f z₀ = 0) (hfinj : Set.InjOn f Ω) (hfd : deriv f z₀ ≠ 0)
    (hmax : ∀ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω → (∀ z ∈ Ω, ‖h z‖ < 1) → h z₀ = 0 → Set.InjOn h Ω →
      ‖deriv h z₀‖ ≤ ‖deriv f z₀‖) :
    f '' Ω = Metric.ball 0 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact rmtO_mem_ball.mpr (hfmap z hz)
  by_contra hsub
  obtain ⟨w₁, hw₁D, hw₁⟩ := Set.not_subset.mp hsub
  have hw₁n : ‖w₁‖ < 1 := rmtO_mem_ball.mp hw₁D
  -- `T ∘ f` is analytic and nowhere zero, so it has an analytic square root `g`.
  have hu : AnalyticOnNhd ℂ (fun z => rmtO_mob w₁ (f z)) Ω :=
    (rmtO_mob_analyticOnNhd hw₁n).comp hf (fun z hz => rmtO_mem_ball.mpr (hfmap z hz))
  have hu0 : ∀ z ∈ Ω, rmtO_mob w₁ (f z) ≠ 0 := by
    intro z hz h
    exact hw₁ ⟨z, hz, rmtO_mob_eq_zero hw₁n (hfmap z hz) h⟩
  obtain ⟨g, hg, hg2⟩ := hroot _ hu hu0
  have hg2' : ∀ z ∈ Ω, g z ^ 2 = rmtO_mob w₁ (f z) := hg2
  have hgD : ∀ z ∈ Ω, ‖g z‖ < 1 := fun z hz =>
    rmtO_norm_lt_of_sq (by rw [hg2' z hz]; exact rmtO_mob_norm_lt hw₁n (hfmap z hz))
  have hginj : Set.InjOn g Ω := by
    intro x hx y hy hxy
    apply hfinj hx hy
    apply rmtO_mob_injOn hw₁n (rmtO_mem_ball.mpr (hfmap x hx)) (rmtO_mem_ball.mpr (hfmap y hy))
    rw [← hg2' x hx, ← hg2' y hy, hxy]
  -- `F̃ = S ∘ g` is an admissible competitor.
  have hw₂n : ‖g z₀‖ < 1 := hgD z₀ hz₀
  have hw₂sq : g z₀ ^ 2 = -w₁ := by rw [hg2' z₀ hz₀, hf0, rmtO_mob_zero]
  have hFa : AnalyticOnNhd ℂ (fun z => rmtO_mob (g z₀) (g z)) Ω :=
    (rmtO_mob_analyticOnNhd hw₂n).comp hg (fun z hz => rmtO_mem_ball.mpr (hgD z hz))
  have hFD : ∀ z ∈ Ω, ‖rmtO_mob (g z₀) (g z)‖ < 1 := fun z hz =>
    rmtO_mob_norm_lt hw₂n (hgD z hz)
  have hF0 : rmtO_mob (g z₀) (g z₀) = 0 := rmtO_mob_self _
  have hFinj : Set.InjOn (fun z => rmtO_mob (g z₀) (g z)) Ω := fun x hx y hy hxy =>
    hginj hx hy (rmtO_mob_injOn hw₂n (rmtO_mem_ball.mpr (hgD x hx))
      (rmtO_mem_ball.mpr (hgD y hy)) hxy)
  have hFmax := hmax _ hFa hFD hF0 hFinj
  -- `Φ = T⁻¹ ∘ (·)² ∘ S⁻¹` with `f = Φ ∘ F̃`.
  have hw₁n' : ‖-w₁‖ < 1 := by rwa [norm_neg]
  have hw₂n' : ‖-g z₀‖ < 1 := by rwa [norm_neg]
  have hsqD : ∀ u ∈ Metric.ball (0 : ℂ) 1, ‖(rmtO_mob (-g z₀) u) ^ 2‖ < 1 := fun u hu =>
    rmtO_sq_norm_lt (rmtO_mob_norm_lt hw₂n' (rmtO_mem_ball.mp hu))
  have hΦa : AnalyticOnNhd ℂ (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2))
      (Metric.ball 0 1) :=
    (rmtO_mob_analyticOnNhd hw₁n').comp ((rmtO_mob_analyticOnNhd hw₂n').pow 2)
      (fun u hu => rmtO_mem_ball.mpr (hsqD u hu))
  have hΦD : ∀ u ∈ Metric.ball (0 : ℂ) 1,
      ‖rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)‖ ≤ 1 := fun u hu =>
    (rmtO_mob_norm_lt hw₁n' (hsqD u hu)).le
  have hΦ0 : rmtO_mob (-w₁) ((rmtO_mob (-g z₀) 0) ^ 2) = 0 := by
    rw [rmtO_mob_zero, neg_neg, hw₂sq]
    exact rmtO_mob_self _
  have hΦF : ∀ z ∈ Ω, rmtO_mob (-w₁) ((rmtO_mob (-g z₀) (rmtO_mob (g z₀) (g z))) ^ 2) = f z := by
    intro z hz
    rw [rmtO_mob_inv hw₂n (hgD z hz), hg2' z hz]
    exact rmtO_mob_inv hw₁n (hfmap z hz)
  -- `Φ` is not injective, so Schwarz's lemma gives `‖Φ'(0)‖ < 1`.
  have hp : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hp' : ‖-(1 / 2 : ℂ)‖ < 1 := by rwa [norm_neg]
  have hu₁ := rmtO_mob_norm_lt hw₂n hp
  have hu₂ := rmtO_mob_norm_lt hw₂n hp'
  have hΦ12 : rmtO_mob (-w₁) ((rmtO_mob (-g z₀) (rmtO_mob (g z₀) (1 / 2))) ^ 2) =
      rmtO_mob (-w₁) ((rmtO_mob (-g z₀) (rmtO_mob (g z₀) (-(1 / 2)))) ^ 2) := by
    rw [rmtO_mob_inv hw₂n hp, rmtO_mob_inv hw₂n hp', neg_sq]
  have hne12 : rmtO_mob (g z₀) (1 / 2) ≠ rmtO_mob (g z₀) (-(1 / 2)) := by
    intro h
    have := rmtO_mob_injOn hw₂n (rmtO_mem_ball.mpr hp) (rmtO_mem_ball.mpr hp') h
    norm_num at this
  obtain ⟨-, hle, himp⟩ := AhlforsComplexAnalysis.schwarz_lemma hΦa hΦD hΦ0
  have hlt : ‖deriv (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)) 0‖ < 1 := by
    refine lt_of_le_of_ne hle fun h => ?_
    obtain ⟨c, hc, hrot⟩ := himp (Or.inr h)
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc
      exact zero_ne_one hc
    have h1 := hrot _ (rmtO_mem_ball.mpr hu₁)
    have h2 := hrot _ (rmtO_mem_ball.mpr hu₂)
    rw [hΦ12] at h1
    exact hne12 (mul_left_cancel₀ hc0 (h1.symm.trans h2))
  -- Chain rule `f'(z₀) = Φ'(0) F̃'(z₀)` gives the contradiction with maximality.
  have hderiv : deriv f z₀ =
      deriv (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)) 0 *
        deriv (fun z => rmtO_mob (g z₀) (g z)) z₀ := by
    have heq : f =ᶠ[nhds z₀] ((fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)) ∘
        (fun z => rmtO_mob (g z₀) (g z))) := by
      filter_upwards [hΩ.1.mem_nhds hz₀] with z hz
      exact (hΦF z hz).symm
    rw [heq.deriv_eq]
    have hFd := (hFa z₀ hz₀).differentiableAt
    have hΦd : DifferentiableAt ℂ (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2))
        ((fun z => rmtO_mob (g z₀) (g z)) z₀) := by
      show DifferentiableAt ℂ _ (rmtO_mob (g z₀) (g z₀))
      rw [hF0]
      exact (hΦa 0 (Metric.mem_ball_self one_pos)).differentiableAt
    rw [deriv_comp z₀ hΦd hFd, hF0]
  have hpos : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr hfd
  have hmul : ‖deriv f z₀‖ ≤
      ‖deriv (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)) 0‖ * ‖deriv f z₀‖ := by
    calc ‖deriv f z₀‖
        = ‖deriv (fun u => rmtO_mob (-w₁) ((rmtO_mob (-g z₀) u) ^ 2)) 0‖ *
            ‖deriv (fun z => rmtO_mob (g z₀) (g z)) z₀‖ := by rw [hderiv, norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hFmax (norm_nonneg _)
  nlinarith

#print axioms solution
