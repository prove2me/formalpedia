-- Prove2me | solution 1 for AKR2008.hybrid_Nc_solves_eq46
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:01:21.083561+00:00
-- url     : https://prove2.me/submissions/0ba11b1c-165a-4190-9c8f-ef5f86dd3e05

import Definitions.Def_AKR2008_HybridDefs
set_option autoImplicit false
open AKR2008

private theorem nc_deriv {ι : Type*} [Fintype ι] (k : ι → ℝ) (t : ℝ)
    (hcos : ∀ i, Real.cos (k i*t) ≠ 0) :
    deriv (fun s => hybridNc k s) t / hybridNc k t + ∑ i, hybridModeF (k i) t = 0 := by
  classical
  have hd (i : ι) : HasDerivAt (fun s => Real.cos (k i*s))
      (hybridModeF (k i) t * Real.cos (k i*t)) t := by
    convert (Real.hasDerivAt_cos (k i*t)).comp t ((hasDerivAt_id t).const_mul (k i)) using 1 <;> try rfl
    dsimp [hybridModeF]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos i]
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i)
  have he : (∑ i, (∏ j ∈ Finset.univ.erase i, Real.cos (k j*t)) •
      (hybridModeF (k i) t * Real.cos (k i*t))) =
      (∑ i, hybridModeF (k i) t) * ∏ j, Real.cos (k j*t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_mul]
    calc
      _ = hybridModeF (k i) t * (Real.cos (k i*t) * ∏ j ∈ Finset.univ.erase i, Real.cos (k j*t)) := by ring
      _ = _ := by rw [Finset.mul_prod_erase Finset.univ (fun j => Real.cos (k j*t)) hi]
  rw [he] at hp
  have hn : (∏ j, Real.cos (k j*t)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hcos i)
  have hncd := ((hasDerivAt_const t (1:ℝ)).fun_div hp hn).deriv
  change deriv (fun s => 1 / ∏ i, Real.cos (k i*s)) t / (1 / ∏ i, Real.cos (k i*t)) + _ = 0
  rw [hncd]
  generalize hq : (∏ i, Real.cos (k i*t)) = q at *
  field_simp [hn] <;> ring

private theorem betaKbeta_deriv {ι : Type*} [Fintype ι] (k τ w : ι → ℝ) (t : ℝ)
    (hcos : ∀ i, Real.cos (k i*t) ≠ 0) :
    deriv (fun s => ∑ i, hybridModeBeta (w i) (k i) s *
      hybridModeK (τ i) (k i) s * hybridModeBeta (w i) (k i) s) t = 0 := by
  have hnear : ∀ᶠ s in nhds t, ∀ i, Real.cos (k i*s) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt).eventually_ne (hcos i)
  have he : (fun s => ∑ i, hybridModeBeta (w i) (k i) s *
      hybridModeK (τ i) (k i) s * hybridModeBeta (w i) (k i) s) =ᶠ[nhds t]
      (fun _ : ℝ => ∑ i, τ i*(w i)^2) := by
    filter_upwards [hnear] with s hs
    apply Finset.sum_congr rfl
    intro i _
    dsimp [hybridModeBeta, hybridModeK]
    field_simp [hs i] <;> ring
  rw [he.deriv_eq]
  simp

theorem solution {ι : Type*} [Fintype ι] (k τ w : ι → ℝ) (t : ℝ)
    (hcos : ∀ i, Real.cos (k i * t) ≠ 0) :
    deriv (fun s => hybridNc k s) t / hybridNc k t
      - (1 / 2) * deriv (fun s => ∑ i, hybridModeBeta (w i) (k i) s *
          hybridModeK (τ i) (k i) s * hybridModeBeta (w i) (k i) s) t
      + ∑ i, hybridModeF (k i) t = 0 := by
  rw [betaKbeta_deriv k τ w t hcos]
  simpa using nc_deriv k t hcos
