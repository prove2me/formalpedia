-- Prove2me | solution 1 for Arxiv2111_09089.ppw_green_pole_locations
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:30:18.862571+00:00
-- url     : https://prove2.me/submissions/8b268672-3cb3-4e77-97c4-0b232b361ec2

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex Filter Topology

noncomputable section
namespace PG
open Arxiv2111_09089

def Ψ (k0 d : ℝ) (ε a b : ℂ) (r : ℂ) : ℂ :=
  -(freeSpaceImpedance * r / ε / 2) / (1 - exp (-2 * I * (k0 * r) * d)) *
    (exp (-I * (k0 * r) * a) - exp (-I * (k0 * r) * b) -
      exp (-I * (k0 * r) * (2 * d - b)) + exp (-I * (k0 * r) * (2 * d - a)))

lemma hG (k0 d : ℝ) (ε : ℂ) (z z' : ℝ) :
    ppwGreen k0 d ε z z' = fun ξ => Ψ k0 d ε (|z - z'| : ℝ) ((z : ℂ) + z') ((ε - ξ ^ 2) ^ (1 / 2 : ℂ)) := by
  funext ξ; simp only [ppwGreen, ppwKz, ppwZTM, Ψ]

lemma even (k0 d : ℝ) (ε a b r : ℂ) : Ψ k0 d ε a b (-r) = Ψ k0 d ε a b r := by
  unfold Ψ
  set k : ℂ := k0 * r
  have hk : (k0 : ℂ) * -r = -k := by simp [k]
  rw [hk]
  set u := exp (-I * k * d)
  have e1 : ∀ x : ℂ, exp (-I * -k * x) = (exp (-I * k * x))⁻¹ := by
    intro x; rw [← exp_neg]; ring_nf
  have e2 : ∀ x : ℂ, exp (-I * k * (2 * d - x)) = u * u * (exp (-I * k * x))⁻¹ := by
    intro x; rw [← exp_neg, show -I * k * (2 * d - x) = -I * k * d + -I * k * d + -(-I * k * x) by ring,
      exp_add, exp_add]
  have e3 : ∀ x : ℂ, exp (-I * -k * (2 * d - x)) = (u * u)⁻¹ * (exp (-I * k * x)) := by
    intro x; rw [show -I * -k * (2 * d - x) = -(-I * k * d + -I * k * d) + (-I * k * x) by ring,
      exp_add, exp_neg, exp_add]
  have e4 : exp (-2 * I * k * d) = u * u := by
    rw [show -2 * I * k * d = -I * k * d + -I * k * d by ring, exp_add]
  have e5 : exp (-2 * I * -k * d) = (u * u)⁻¹ := by
    rw [show -2 * I * -k * d = -(-I * k * d + -I * k * d) by ring, exp_neg, exp_add]
  rw [e1, e1, e2, e2, e3, e3, e4, e5]
  rw [show (freeSpaceImpedance : ℂ) * -r / ε / 2 = -(freeSpaceImpedance * r / ε / 2) by ring]
  have hu : u ≠ 0 := exp_ne_zero _
  have hA : exp (-I * k * a) ≠ 0 := exp_ne_zero _
  have hB : exp (-I * k * b) ≠ 0 := exp_ne_zero _
  generalize (freeSpaceImpedance : ℂ) * r / ε / 2 = C
  generalize exp (-I * k * a) = A at hA ⊢
  generalize exp (-I * k * b) = B at hB ⊢
  by_cases h : 1 - u * u = 0
  · have h1 : u * u = 1 := by linear_combination -h
    rw [h1]; simp
  · have h' : 1 - (u * u)⁻¹ ≠ 0 := by
      intro hh; apply h
      have : (u * u)⁻¹ = 1 := by linear_combination -hh
      have : u * u = 1 := by simpa using congrArg (·⁻¹) this
      rw [this]; simp
    have h2 : (1 - (u * u)⁻¹) = -(1 - u * u) / (u * u) := by field_simp; ring
    rw [h2]
    have h3 : (1 - u * u) ≠ 0 := h
    field_simp
    ring


def Dn (k0 d : ℝ) (r : ℂ) : ℂ := 1 - exp (-2 * I * (k0 * r) * d)
def Nm (k0 d : ℝ) (ε a b : ℂ) (r : ℂ) : ℂ :=
  -(freeSpaceImpedance * r / ε / 2) *
    (exp (-I * (k0 * r) * a) - exp (-I * (k0 * r) * b) -
      exp (-I * (k0 * r) * (2 * d - b)) + exp (-I * (k0 * r) * (2 * d - a)))

lemma Ψ_eq (k0 d : ℝ) (ε a b r : ℂ) : Ψ k0 d ε a b r = Nm k0 d ε a b r / Dn k0 d r := by
  unfold Ψ Nm Dn; ring

lemma sq_half (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [one_div]; exact cpow_ofNat_inv_pow x 2

lemma branch (ε ξ0 : ℂ) (h : ε - ξ0 ^ 2 ≠ 0) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s ξ0 ∧ ∀ ξ, s ξ ^ 2 = ε - ξ ^ 2 := by
  by_cases hs : ε - ξ0 ^ 2 ∈ slitPlane
  · refine ⟨fun ξ => (ε - ξ ^ 2) ^ (1 / 2 : ℂ), ?_, fun ξ => sq_half _⟩
    exact (analyticAt_const.sub (analyticAt_id.pow 2)).cpow analyticAt_const hs
  · refine ⟨fun ξ => I * (ξ ^ 2 - ε) ^ (1 / 2 : ℂ), ?_, fun ξ => ?_⟩
    · have hm : ξ0 ^ 2 - ε ∈ slitPlane := by
        rw [mem_slitPlane_iff] at hs ⊢
        push Not at hs
        have hre : (ε - ξ0 ^ 2).re ≠ 0 := by
          intro h0; apply h; apply Complex.ext <;> simp_all
        left
        have : (ξ0 ^ 2 - ε).re = -(ε - ξ0 ^ 2).re := by simp
        rw [this]; exact neg_pos.2 (lt_of_le_of_ne hs.1 hre)
      exact analyticAt_const.mul ((analyticAt_id.pow 2).sub analyticAt_const |>.cpow analyticAt_const hm)
    · rw [mul_pow, sq_half, I_sq]; ring

lemma comp_eq (k0 d : ℝ) (ε a b : ℂ) (s : ℂ → ℂ) (hs : ∀ ξ, s ξ ^ 2 = ε - ξ ^ 2) (ξ : ℂ) :
    Ψ k0 d ε a b ((ε - ξ ^ 2) ^ (1 / 2 : ℂ)) = Ψ k0 d ε a b (s ξ) := by
  have : ((ε - ξ ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = (s ξ) ^ 2 := by rw [sq_half, hs]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · rw [h]
  · rw [h, even]

lemma an_N (k0 d : ℝ) (ε a b : ℂ) (s : ℂ → ℂ) (ξ0 : ℂ) (hs : AnalyticAt ℂ s ξ0) :
    AnalyticAt ℂ (fun ξ => Nm k0 d ε a b (s ξ)) ξ0 := by
  unfold Nm; fun_prop

lemma an_D (k0 d : ℝ) (s : ℂ → ℂ) (ξ0 : ℂ) (hs : AnalyticAt ℂ s ξ0) :
    AnalyticAt ℂ (fun ξ => Dn k0 d (s ξ)) ξ0 := by
  unfold Dn; fun_prop

lemma D_ne (k0 d : ℝ) (hk0 : 0 < k0) (hd : 0 < d) (ε ξ s : ℂ) (hs : s ^ 2 = ε - ξ ^ 2)
    (hξ : ∀ n : ℕ, ξ ^ 2 ≠ ε - ((n * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2) : Dn k0 d s ≠ 0 := by
  intro h0
  unfold Dn at h0
  have h1 : exp (-2 * I * (k0 * s) * d) = 1 := by linear_combination -h0
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 h1
  have hk : (k0 : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsv : s = -(n * Real.pi / (k0 * d) : ℝ) := by
    push_cast
    field_simp
    have := hn
    apply mul_left_cancel₀ (show (2 * I : ℂ) ≠ 0 by simp)
    linear_combination (-1) * this
  apply hξ n.natAbs
  have e : (((n.natAbs : ℕ) : ℝ)) ^ 2 = ((n : ℝ)) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have : ((n.natAbs * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2 = s ^ 2 := by
    rw [hsv, neg_sq]
    have : ((n.natAbs * Real.pi / (k0 * d) : ℝ)) ^ 2 = ((n * Real.pi / (k0 * d) : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, mul_pow, mul_pow, e]; ring
    exact_mod_cast this
  rw [this, hs]; ring

lemma analytic_pt (k0 d : ℝ) (hk0 : 0 < k0) (hd : 0 < d) (ε a b ξ0 : ℂ)
    (hξ : ∀ n : ℕ, ξ0 ^ 2 ≠ ε - ((n * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2) :
    AnalyticAt ℂ (fun ξ => Ψ k0 d ε a b ((ε - ξ ^ 2) ^ (1 / 2 : ℂ))) ξ0 := by
  have h0 : ε - ξ0 ^ 2 ≠ 0 := by
    intro h; apply hξ 0; simp; linear_combination -h
  obtain ⟨s, hsa, hs⟩ := branch ε ξ0 h0
  have : (fun ξ => Ψ k0 d ε a b ((ε - ξ ^ 2) ^ (1 / 2 : ℂ))) =
      fun ξ => Nm k0 d ε a b (s ξ) / Dn k0 d (s ξ) := by
    funext ξ; rw [comp_eq k0 d ε a b s hs, Ψ_eq]
  rw [this]
  exact (an_N k0 d ε a b s ξ0 hsa).div (an_D k0 d s ξ0 hsa) (D_ne k0 d hk0 hd ε ξ0 _ (hs ξ0) hξ)

lemma Ψ_cont0 (k0 d : ℝ) (hk0 : 0 < k0) (hd : 0 < d) (ε a b : ℂ) :
    ContinuousAt (Ψ k0 d ε a b) 0 := by
  have h1 : HasDerivAt (fun r : ℂ => -2 * I * (k0 * r) * d) (-2 * I * k0 * d) 0 := by
    have := (hasDerivAt_id (0:ℂ)).const_mul (-2 * I * k0 * d)
    have e : (fun r : ℂ => -2 * I * (k0 * r) * d) = fun r => (-2 * I * k0 * d) * id r := by
      funext r; rw [id]; ring
    rw [e]; simpa using this
  have h2 := (h1.cexp).const_sub 1
  have hD : HasDerivAt (Dn k0 d) (2 * I * k0 * d) 0 := by
    have e : (Dn k0 d) = fun r => 1 - exp (-2 * I * (k0 * r) * d) := rfl
    have h3 : -(exp (-2 * I * ((k0 : ℂ) * 0) * d) * (-2 * I * k0 * d)) = 2 * I * k0 * d := by
      simp only [mul_zero, zero_mul, exp_zero]; ring
    rw [h3] at h2; rw [e]; exact h2
  have hsl := hasDerivAt_iff_tendsto_slope_zero.1 hD
  have hD0 : Dn k0 d 0 = 0 := by simp [Dn]
  simp only [zero_add, hD0, sub_zero, smul_eq_mul] at hsl
  have hne : (2 * I * k0 * d : ℂ) ≠ 0 := by
    have : (k0 : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp_all
  have hinv := hsl.inv₀ hne
  have hS : Tendsto (fun r : ℂ => exp (-I * (k0 * r) * a) - exp (-I * (k0 * r) * b) -
      exp (-I * (k0 * r) * (2 * d - b)) + exp (-I * (k0 * r) * (2 * d - a))) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℂ => exp (-I * (k0 * r) * a) - exp (-I * (k0 * r) * b) -
      exp (-I * (k0 * r) * (2 * d - b)) + exp (-I * (k0 * r) * (2 * d - a))) := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, zero_mul, neg_zero, exp_zero, sub_self, zero_add] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds (this.mono_right (le_of_eq (by rw [sub_add_cancel])))
  have hT := (tendsto_const_nhds (x := -((freeSpaceImpedance : ℂ) / ε / 2))).mul (hinv.mul hS)
  rw [mul_zero, mul_zero] at hT
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have hΨ0 : Ψ k0 d ε a b 0 = 0 := by simp [Ψ]
  rw [hΨ0]
  refine hT.congr (fun r => ?_)
  unfold Ψ Dn
  by_cases hr : r = 0
  · subst hr; simp
  · field_simp

end PG

open Arxiv2111_09089 PG in
theorem solution (k0 d : ℝ) (hk0 : 0 < k0) (hd : 0 < d) (ε : ℂ) (hε : ε ≠ 0)
    (z z' : ℝ) (hz : z ∈ Set.Icc 0 d) (hz' : z' ∈ Set.Icc 0 d) :
    MeromorphicOn (ppwGreen k0 d ε z z') Set.univ ∧
    ∀ ξ : ℂ, (∀ n : ℕ, ξ ^ 2 ≠ ε - ((n * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2) →
      AnalyticAt ℂ (ppwGreen k0 d ε z z') ξ := by
  rw [hG]
  generalize ((|z - z'| : ℝ) : ℂ) = a
  generalize (z : ℂ) + z' = b
  refine ⟨fun ξ0 _ => ?_, fun ξ hξ => analytic_pt k0 d hk0 hd ε a b ξ hξ⟩
  by_cases h0 : ε - ξ0 ^ 2 = 0
  · apply AnalyticAt.meromorphicAt
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · have hε0 : ε = ξ0 ^ 2 := by linear_combination h0
      have hξ0 : ξ0 ≠ 0 := by rintro rfl; apply hε; simpa using hε0
      have hne : ξ0 ≠ -ξ0 := by
        intro h; apply hξ0; linear_combination h / 2
      set c : ℝ := (Real.pi / (k0 * d)) ^ 2 with hc
      have hcpos : 0 < c := by positivity
      have hcont : ContinuousAt (fun ξ : ℂ => ε - ξ ^ 2) ξ0 := by fun_prop
      have e1 : ∀ᶠ ξ in 𝓝 ξ0, ‖ε - ξ ^ 2‖ < c := by
        filter_upwards [hcont.eventually_mem (Metric.ball_mem_nhds _ hcpos)] with ξ hξ
        simp only [Set.mem_preimage, Metric.mem_ball, h0, dist_zero_right] at hξ
        exact hξ
      have e2 : ∀ᶠ ξ in 𝓝 ξ0, ξ ≠ -ξ0 := eventually_ne_nhds hne
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
        with ξ h1 h2 h3
      apply (analytic_pt k0 d hk0 hd ε a b ξ ?_).differentiableAt
      intro n hn
      rcases n with _ | m
      · simp at hn
        have : (ξ0 - ξ) * (ξ0 + ξ) = 0 := by linear_combination (-1 : ℂ) * hε0 - hn
        rcases mul_eq_zero.1 this with h | h
        · exact h3 (Set.mem_singleton_iff.2 (by linear_combination -h))
        · exact h2 (by linear_combination h)
      · have : ε - ξ ^ 2 = (((m + 1 : ℕ) * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2 := by
          rw [hn]; ring
        rw [this, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
        have hge : Real.pi / (k0 * d) ≤ ((m + 1 : ℕ) * Real.pi / (k0 * d) : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 m
          nlinarith [Real.pi_pos]
        have : c ≤ (((m + 1 : ℕ) * Real.pi / (k0 * d) : ℝ)) ^ 2 := by
          rw [hc]; exact pow_le_pow_left₀ (by positivity) hge 2
        linarith
    · have hr : ContinuousAt (fun ξ : ℂ => (ε - ξ ^ 2) ^ (1 / 2 : ℂ)) ξ0 := by
        have hb : ContinuousAt (fun ξ : ℂ => ε - ξ ^ 2) ξ0 := by fun_prop
        have hp : ContinuousAt (fun x : ℂ => x ^ (1 / 2 : ℂ)) (ε - ξ0 ^ 2) :=
          continuousAt_cpow_const_of_re_pos (Or.inl (by rw [h0]; simp)) (by norm_num)
        exact ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ)) (f := fun ξ : ℂ => ε - ξ ^ 2) hp hb
      have hr0 : (ε - ξ0 ^ 2) ^ (1 / 2 : ℂ) = 0 := by
        rw [h0]; exact zero_cpow (by norm_num)
      exact (Ψ_cont0 k0 d hk0 hd ε a b).comp_of_eq hr hr0
  · obtain ⟨s, hsa, hs⟩ := branch ε ξ0 h0
    have : (fun ξ => Ψ k0 d ε a b ((ε - ξ ^ 2) ^ (1 / 2 : ℂ))) =
        fun ξ => Nm k0 d ε a b (s ξ) / Dn k0 d (s ξ) := by
      funext ξ; rw [comp_eq k0 d ε a b s hs, Ψ_eq]
    rw [this]
    exact (an_N k0 d ε a b s ξ0 hsa).meromorphicAt.div (an_D k0 d s ξ0 hsa).meromorphicAt
