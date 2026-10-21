-- Prove2me | solution 1 for AVRideHail.MonopolyCapacity.lemma1_nMin_strictMono_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:53:17.034436+00:00
-- url     : https://prove2.me/submissions/89b49a5c-48d9-4684-b0fe-5e6bd5369b7d

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

set_option autoImplicit false
open AVRideHail.PureHV AVRideHail.MonopolyCapacity

lemma av_aTilde_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) : 0 < aTilde P := by
  unfold aTilde
  have h1 : 0 ≤ P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) :=
    mul_nonneg (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg ha.le _)
  have h2 : 0 < P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by
    apply mul_pos _ (Real.rpow_pos_of_pos ha _)
    rcases hr0.lt_or_eq with h | h
    · exact Real.rpow_pos_of_pos h _
    · rw [← h]; simp
  linarith

lemma av_e_pos (P : MarketParams) (hr0 : 0 ≤ P.r) : 0 < 1 / (P.r + 1) :=
  div_pos one_pos (by linarith)

lemma av_nMin_cont (P : MarketParams) (hr0 : 0 ≤ P.r) : Continuous (nMin P) := by
  unfold nMin
  have : Continuous fun d : ℝ => d ^ (1 / (P.r + 1)) :=
    Real.continuous_rpow_const (le_of_lt (av_e_pos P hr0))
  fun_prop

lemma av_nMin_zero (P : MarketParams) (hr0 : 0 ≤ P.r) : nMin P 0 = 0 := by
  unfold nMin
  rw [Real.zero_rpow (ne_of_gt (av_e_pos P hr0))]
  simp

lemma av_nMin_sm (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) :
    StrictMonoOn (nMin P) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold nMin
  have h1 : x ^ (1 / (P.r + 1)) < y ^ (1 / (P.r + 1)) :=
    Real.rpow_lt_rpow hx hxy (av_e_pos P hr0)
  have h2 := av_aTilde_pos P ha hr0
  nlinarith [mul_lt_mul_of_pos_left h1 h2, mul_lt_mul_of_pos_left hxy ht2]

lemma av_nMin_ge (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (d : ℝ) (hd : 0 ≤ d) :
    P.t2 * d ≤ nMin P d := by
  unfold nMin
  have h1 : 0 ≤ d ^ (1 / (P.r + 1)) := Real.rpow_nonneg hd _
  have h2 := av_aTilde_pos P ha hr0
  nlinarith [mul_nonneg h2.le h1]

lemma av_nMin_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) (d : ℝ)
    (hd : 0 < d) : 0 < nMin P d := by
  have := av_nMin_ge P ha hr0 d hd.le
  nlinarith [mul_pos ht2 hd]

lemma av_bij (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) :
    Set.BijOn (nMin P) (Set.Ici 0) (Set.Ici 0) := by
  have hsm := av_nMin_sm P ha hr0 ht2
  refine ⟨?_, hsm.injOn, ?_⟩
  · intro d hd
    have := av_nMin_ge P ha hr0 d hd
    have : 0 ≤ P.t2 * d := mul_nonneg ht2.le hd
    show 0 ≤ nMin P d
    linarith [av_nMin_ge P ha hr0 d hd]
  · intro y hy
    have hy0 : 0 ≤ y := hy
    have hle : (0:ℝ) ≤ y / P.t2 := by positivity
    have hivt := intermediate_value_Icc hle (av_nMin_cont P hr0).continuousOn
    have hmem : y ∈ Set.Icc (nMin P 0) (nMin P (y / P.t2)) := by
      rw [av_nMin_zero P hr0]
      refine ⟨hy0, ?_⟩
      have := av_nMin_ge P ha hr0 (y / P.t2) hle
      have e : P.t2 * (y / P.t2) = y := by field_simp
      linarith
    obtain ⟨d, hd, hdy⟩ := hivt hmem
    exact ⟨d, hd.1, hdy⟩

theorem solution (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) :
    StrictMonoOn (AVRideHail.PureHV.nMin P) (Set.Ici 0) ∧ Set.BijOn (AVRideHail.PureHV.nMin P) (Set.Ici 0) (Set.Ici 0) :=
  ⟨av_nMin_sm P ha hr0 ht2, av_bij P ha hr0 ht2⟩
