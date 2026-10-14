-- Prove2me | Definitions.Def_dusart_psi_433_20261014_AllHeights
-- name    : dusart_psi_433_20261014_AllHeights
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:28:12.705528+00:00
-- url     : https://prove2.me/theorems/8b32a85a-c088-4bfd-abfd-9575824ddd2c
-- title:
--   Dusart smoothing: All Heights
-- statement:
--   This module gives the complete all heights component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroCount
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set Topology Filter Real

lemma right_zero_free_neighborhood {T : ℝ} (hT : 4 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioo T (T + ε),
      GoodHeight t ∧ Ncount 4 t = Ncount 4 T := by
  classical
  let S : Set ℝ := Complex.im '' zerosIn T (T + 1)
  have hS : S.Finite := (finite_zero_window (b := T + 1) (by linarith : 0 < T)).image _
  have hnot : T ∉ S := by
    rintro ⟨ρ, ⟨_, hρ, _⟩, he⟩
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl T hnot
  let ε : ℝ := min r 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have htε : t - T < ε := by linarith [ht.2]
  have hεr : ε ≤ r := by dsimp [ε]; linarith [min_le_left r 1]
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith [min_le_right r 1]
  have havoid : ∀ u ∈ Set.Ioc T t, u ∉ S := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
    linarith [hu.2]
  have hg : GoodHeight t := by
    intro ρ hρ he
    apply havoid t ⟨ht.1, le_rfl⟩
    exact ⟨ρ, ⟨hρ, by rw [he]; exact ht.1, by rw [he]; linarith [ht.2]⟩, he⟩
  refine ⟨hg, ?_⟩
  have hset : zerosIn 4 t = zerosIn 4 T := by
    ext ρ
    constructor
    · rintro ⟨hz, hi1, hi2⟩
      refine ⟨hz, hi1, ?_⟩
      by_contra hh
      have hh' : T < ρ.im := lt_of_not_ge hh
      apply havoid ρ.im ⟨hh', hi2⟩
      exact ⟨ρ, ⟨hz, hh', by linarith [ht.2]⟩, rfl⟩
    · rintro ⟨hz, hi1, hi2⟩
      exact ⟨hz, hi1, hi2.trans ht.1.le⟩
  simp only [Ncount, hset]

lemma Ncount_four_error (T : ℝ) (hT : 4 ≤ T) :
    |(Ncount 4 T : ℝ) - countingMain T| ≤ 9 * Real.log (T + 5) + 79 := by
  obtain ⟨ε, hε, hg⟩ := right_zero_free_neighborhood hT
  let E : ℝ → ℝ := fun t => |(Ncount 4 T : ℝ) - countingMain t| -
    (9 * Real.log (t + 5) + 79)
  have hEc : ContinuousAt E T := by
    have hf := (hasDerivAt_countingMain T (by linarith : 0 < T)).continuousAt
    have hl := (Real.continuousAt_log (by linarith : T + 5 ≠ 0)).comp (f := fun t : ℝ => t + 5)
      (continuousAt_id.add_const 5)
    exact (continuousAt_const.sub hf).abs.sub ((hl.const_mul 9).add_const 79)
  have he : ∀ᶠ t in 𝓝[>] T, E t ≤ 0 := by
    have hu : Set.Iio (T + ε) ∈ 𝓝 T := Iio_mem_nhds (by linarith)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with t ht1 ht2
    change T < t at ht1
    change t < T + ε at ht2
    obtain ⟨htg, heq⟩ := hg t ⟨ht1, ht2⟩
    have hb := Ncount_four_error_good (by linarith : 4 < t) htg
    rw [heq] at hb
    dsimp [E]
    linarith
  have hle : E T ≤ 0 := le_of_tendsto (hEc.tendsto.mono_left nhdsWithin_le_nhds) he
  dsimp [E] at hle
  linarith

end DusartSmoothing.RvM


