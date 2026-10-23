-- Prove2me | solution 1 for AccelScal.UCRace.eq_A28
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:44:18.205775+00:00
-- url     : https://prove2.me/submissions/27455f8b-565c-46e4-b7a3-2fa06e4863d1

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section


namespace AccelScal.UCRace

theorem a28_abs (N L M : ℝ → ℝ) (r R1 R2 : ℝ) (hN : DifferentiableAt ℝ N R1)
    (hL : DifferentiableAt ℝ L R1) (hM : DifferentiableAt ℝ M R2)
    (hD : ∀ᶠ b in nhds R2, 0 < r + L R1 + M b) :
    N R1 / (r + L R1 + M R2) * deriv (fun b => deriv (fun a => N a / (r + L a + M b)) R1) R2
      - deriv (fun a => N a / (r + L a + M R2)) R1 * deriv (fun b => N R1 / (r + L R1 + M b)) R2
      = deriv M R2 * N R1 ^ 2 / (r + L R1 + M R2) ^ 4 * deriv L R1 := by
  have key : ∀ b, 0 < r + L R1 + M b →
      HasDerivAt (fun a => N a / (r + L a + M b))
        ((deriv N R1 * (r + L R1 + M b) - N R1 * deriv L R1) / (r + L R1 + M b) ^ 2) R1 := by
    intro b hb
    exact hN.hasDerivAt.div ((hL.hasDerivAt.const_add r).add_const (M b)) hb.ne'
  have e1 : (fun b => deriv (fun a => N a / (r + L a + M b)) R1)
      =ᶠ[nhds R2] fun b => (deriv N R1 * (r + L R1 + M b) - N R1 * deriv L R1) / (r + L R1 + M b) ^ 2 := by
    filter_upwards [hD] with b hb using (key b hb).deriv
  have hD0 : 0 < r + L R1 + M R2 := hD.self_of_nhds
  have hMd := hM.hasDerivAt
  have hDb : HasDerivAt (fun b => r + L R1 + M b) (deriv M R2) R2 := hMd.const_add _
  have h1 : HasDerivAt (fun b => (deriv N R1 * (r + L R1 + M b) - N R1 * deriv L R1) / (r + L R1 + M b) ^ 2)
      (((deriv N R1 * deriv M R2) * (r + L R1 + M R2) ^ 2 -
        (deriv N R1 * (r + L R1 + M R2) - N R1 * deriv L R1) * (2 * (r + L R1 + M R2) * deriv M R2)) /
        ((r + L R1 + M R2) ^ 2) ^ 2) R2 := by
    have a := ((hDb.const_mul (deriv N R1)).sub_const (N R1 * deriv L R1))
    have b := hDb.pow 2
    have := a.div b (pow_pos hD0 2).ne'
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    norm_num
  have h2 : HasDerivAt (fun b => N R1 / (r + L R1 + M b))
      (-(N R1) * deriv M R2 / (r + L R1 + M R2) ^ 2) R2 := by
    have := (hasDerivAt_const R2 (N R1)).div hDb hD0.ne'
    exact this.congr_deriv (by ring)
  rw [e1.deriv_eq, h1.deriv, (key R2 hD0).deriv, h2.deriv]
  field_simp
  ring

theorem eq_A28_core (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    (let V := V1 T1 T2 r
     let lhs := V R1 R2 * deriv (fun b => deriv (fun a => V a b) R1) R2
       - deriv (fun a => V a R2) R1 * deriv (fun b => V R1 b) R2
     lhs = deriv T2.lam R2 * (T1.u R1 * T1.lam R1 - R1) ^ 2 /
         (r + T1.lam R1 + T2.lam R2) ^ 4 * deriv T1.lam R1 ∧
       (0 < T1.γ → 0 < T2.γ → T1.u R1 * T1.lam R1 ≠ R1 → 0 < lhs)) := by
  obtain ⟨hA1, hη1, hβ1, hβ1', hγ1, hγ1', -, -⟩ := h1
  obtain ⟨hA2, hη2, hβ2, hβ2', hγ2, hγ2', -, -⟩ := h2
  have dlam : ∀ (T : Tech) (x : ℝ), 0 < x → HasDerivAt T.lam (T.η * (T.γ * x ^ (T.γ - 1))) x := by
    intro T x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul T.η
  have du : ∀ (T : Tech) (x : ℝ), 0 < x → HasDerivAt T.u (T.A * (T.β * x ^ (T.β - 1))) x := by
    intro T x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul T.A
  have lampos : ∀ (T : Tech) (x : ℝ), 0 < T.η → 0 < x → 0 < T.lam x := by
    intro T x h hx
    exact mul_pos h (Real.rpow_pos_of_pos hx _)
  have hNd : DifferentiableAt ℝ (fun a => T1.u a * T1.lam a - a) R1 :=
    (((du T1 R1 hR1).mul (dlam T1 R1 hR1)).sub (hasDerivAt_id R1)).differentiableAt
  have hLd : DifferentiableAt ℝ T1.lam R1 := (dlam T1 R1 hR1).differentiableAt
  have hMd : DifferentiableAt ℝ T2.lam R2 := (dlam T2 R2 hR2).differentiableAt
  have hD : ∀ᶠ b in nhds R2, 0 < r + T1.lam R1 + T2.lam b := by
    have : ∀ᶠ b in nhds R2, 0 < b := lt_mem_nhds hR2
    filter_upwards [this] with b hb
    have := lampos T1 R1 hη1 hR1
    have := lampos T2 b hη2 hb
    linarith
  have core := a28_abs (fun a => T1.u a * T1.lam a - a) T1.lam T2.lam r R1 R2 hNd hLd hMd hD
  have hD0 : 0 < r + T1.lam R1 + T2.lam R2 := hD.self_of_nhds
  simp only [V1]
  refine ⟨core, ?_⟩
  intro hg1 hg2 hne
  rw [core]
  have hL' : 0 < deriv T1.lam R1 := by
    rw [(dlam T1 R1 hR1).deriv]
    have := Real.rpow_pos_of_pos hR1 (T1.γ - 1)
    positivity
  have hM' : 0 < deriv T2.lam R2 := by
    rw [(dlam T2 R2 hR2).deriv]
    have := Real.rpow_pos_of_pos hR2 (T2.γ - 1)
    positivity
  have hN2 : 0 < (T1.u R1 * T1.lam R1 - R1) ^ 2 := by
    have : T1.u R1 * T1.lam R1 - R1 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  positivity

end AccelScal.UCRace

open AccelScal.UCRace


theorem solution (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    (let V := V1 T1 T2 r
     let lhs := V R1 R2 * deriv (fun b => deriv (fun a => V a b) R1) R2
       - deriv (fun a => V a R2) R1 * deriv (fun b => V R1 b) R2
     lhs = deriv T2.lam R2 * (T1.u R1 * T1.lam R1 - R1) ^ 2 /
         (r + T1.lam R1 + T2.lam R2) ^ 4 * deriv T1.lam R1 ∧
       (0 < T1.γ → 0 < T2.γ → T1.u R1 * T1.lam R1 ≠ R1 → 0 < lhs)) := by
  exact eq_A28_core T1 T2 h1 h2 r hr R1 R2 hR1 hR2
