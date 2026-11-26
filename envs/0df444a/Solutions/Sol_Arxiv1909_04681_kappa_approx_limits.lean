-- Prove2me | solution 1 for Arxiv1909_04681.kappa_approx_limits
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:48:36.278529+00:00
-- url     : https://prove2.me/submissions/141afb85-dd28-43d3-9dcb-43f218da9af5

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace S81KA
open Arxiv1909_04681

lemma erf_cont : Continuous erf := by
  unfold erf
  exact continuous_const.mul (intervalIntegral.continuous_primitive
    (fun a b => (by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2)).intervalIntegrable a b) 0)

lemma erf_zero : erf 0 = 0 := by simp [erf]

lemma erf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ erf x := by
  unfold erf
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le))

noncomputable def D (S : ℝ) : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (S ^ 2 / 2) * (1 + erf (S / Real.sqrt 2))

lemma D_cont : Continuous D := by
  unfold D
  exact (continuous_const.mul (by fun_prop)).mul (continuous_const.add (erf_cont.comp (by fun_prop)))

lemma D_ge (S : ℝ) (hS : 0 ≤ S) : Real.sqrt (2 * Real.pi) ≤ D S := by
  unfold D
  have h1 : 1 ≤ Real.exp (S ^ 2 / 2) := Real.one_le_exp (by positivity)
  have h2 : 0 ≤ erf (S / Real.sqrt 2) := erf_nonneg _ (by positivity)
  have h3 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have : 1 ≤ Real.exp (S ^ 2 / 2) * (1 + erf (S / Real.sqrt 2)) := by nlinarith
  nlinarith

lemma kform (S : ℝ) : kappaOfSNR S = S * (2 * S + D S * (1 + S ^ 2)) / (S * D S + 2) := by
  unfold kappaOfSNR erfc D
  rw [show Real.sqrt (2 * Real.pi) * S * Real.exp (S ^ 2 / 2) * (erf (S / Real.sqrt 2) + 1) + 2 =
    S * (Real.sqrt (2 * Real.pi) * Real.exp (S ^ 2 / 2) * (1 + erf (S / Real.sqrt 2))) + 2 by ring]
  ring

lemma ra : Real.sqrt (2 * Real.pi) = 2 * Real.sqrt (Real.pi / 2) := by
  rw [show 2 * Real.pi = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

end S81KA

open Arxiv1909_04681 S81KA in
theorem solution :
    IsEquivalent (𝓝[>] 0) kappaOfSNR (fun S => Real.sqrt (Real.pi / 2) * S) ∧
    IsEquivalent (𝓝[>] 0) kappaApprox (fun S => Real.sqrt (Real.pi / 2) * S) ∧
    Tendsto (fun S => kappaOfSNR S - (1 + S ^ 2)) atTop (𝓝 0) ∧
    Tendsto (fun S => kappaApprox S - (1 + S ^ 2)) atTop (𝓝 0) := by
  set a := Real.sqrt (Real.pi / 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hne : ∀ᶠ S in 𝓝[>] (0:ℝ), a * S ≠ 0 :=
    eventually_nhdsWithin_of_forall (fun S hS => (mul_pos ha0 hS).ne')
  have hD0 : D 0 = Real.sqrt (2 * Real.pi) := by simp [D, erf_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isEquivalent_iff_tendsto_one hne]
    have hc : ContinuousAt (fun S => (2 * S + D S * (1 + S ^ 2)) / ((S * D S + 2) * a)) 0 := by
      apply ContinuousAt.div
      · exact (by fun_prop : Continuous fun S : ℝ => 2 * S).continuousAt.add
          ((D_cont.continuousAt).mul (by fun_prop))
      · exact (((continuous_id.mul D_cont).add continuous_const).mul continuous_const).continuousAt
      · simp; exact ha0.ne'
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [show (2 * 0 + D 0 * (1 + 0 ^ 2)) / ((0 * D 0 + 2) * a) = (1:ℝ) by
      rw [hD0, ra]; field_simp; ring] at h
    refine h.congr' (eventually_nhdsWithin_of_forall (fun S hS => ?_))
    have hS : 0 < S := hS
    have hDS := D_ge S hS.le
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hden : S * D S + 2 ≠ 0 := by nlinarith
    simp only [Pi.div_apply, kform]
    field_simp
  · rw [isEquivalent_iff_tendsto_one hne]
    have hc : ContinuousAt (fun S => 1 / (1 + a * S) + S / a) 0 := by
      apply ContinuousAt.add
      · apply ContinuousAt.div continuousAt_const (by fun_prop); simp
      · exact (continuous_id.div_const a).continuousAt
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [show 1 / (1 + a * 0) + 0 / a = (1:ℝ) by simp] at h
    refine h.congr' (eventually_nhdsWithin_of_forall (fun S hS => ?_))
    have hS : 0 < S := hS
    simp only [Pi.div_apply, kappaApprox, ← ha]
    have : 0 < 1 + a * S := by positivity
    field_simp
  · have hden : Tendsto (fun S => S * D S + 2) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ 2
        (tendsto_id.const_mul_atTop (Real.sqrt_pos.2 (by positivity : (0:ℝ) < 2 * Real.pi))))
      filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
      have := D_ge S hS
      simp only [id]
      nlinarith
    have h := (tendsto_const_nhds (x := (-2:ℝ))).div_atTop hden
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
    have hDS := D_ge S hS
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hd : S * D S + 2 ≠ 0 := by nlinarith
    rw [kform]
    field_simp
    ring
  · have hden : Tendsto (fun S => 1 + a * S) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop ha0)
    have h := (tendsto_const_nhds (x := (-1:ℝ))).div_atTop hden
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
    have : 0 < 1 + a * S := by positivity
    simp only [kappaApprox, ← ha]
    field_simp
    ring
