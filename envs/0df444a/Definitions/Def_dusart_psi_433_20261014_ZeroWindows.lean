-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroWindows
-- name    : dusart_psi_433_20261014_ZeroWindows
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:51.217415+00:00
-- url     : https://prove2.me/theorems/cec81e5a-a3dc-46d8-98cc-1053a1c0c199
-- title:
--   Dusart smoothing: Zero Windows
-- statement:
--   This module gives the complete zero windows component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_CompletedZeta
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set Topology Filter Real MeromorphicOn
open DusartSmoothing.Contour

lemma finite_zeros_rectangle {f : ℂ → ℂ} {z w p : ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hp : p ∈ Rectangle z w)
    (hfp : f p ≠ 0) : {s | s ∈ Rectangle z w ∧ f s = 0}.Finite := by
  have hconn : IsPreconnected (Rectangle z w) := by
    rw [Complex.rectangle_eq_convexHull]
    exact (convex_convexHull ℝ _).isPreconnected
  have hcompact : IsCompact (Rectangle z w) :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  refine ((divisor f (Rectangle z w)).finiteSupport hcompact).subset ?_
  rintro s ⟨hs, hz⟩
  have htop := hf.analyticOrderAt_ne_top_of_isPreconnected hconn hp hs
    (by rw [(hf p hp).analyticOrderAt_eq_zero.mpr hfp]; exact ENat.zero_ne_top)
  have hn0 := (hf s hs).analyticOrderAt_ne_zero.mpr hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hnpos : n ≠ 0 := by intro h; subst n; simp [← hn] at hn0
  rw [Function.mem_support, hf.divisor_apply hs]
  simp [← hn, hnpos]

lemma finite_zero_window {a b : ℝ} (ha : 0 < a) : (zerosIn a b).Finite := by
  by_cases hab : a ≤ b
  · let z : ℂ := -1 + a * I
    let w : ℂ := 2 + b * I
    have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
        (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (a ≤ s.im ∧ s.im ≤ b) := by
      intro s
      simp [Rectangle, z, w, Complex.mem_reProdIm, Set.mem_Icc,
        Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w) := by
      intro s hs
      have hi : 0 < s.im := ha.trans_le ((hmem s).mp hs).2.1
      exact analyticAt_completedRiemannZeta (fun h => by simp [h] at hi)
        (fun h => by simp [h] at hi)
    have hp : (2 : ℂ) + a * I ∈ Rectangle z w :=
      (hmem _).mpr (by simpa using And.intro (by norm_num : (-1 : ℝ) ≤ 2) hab)
    have hfin := finite_zeros_rectangle hf hp
      (completedRiemannZeta_ne_zero_of_one_le_re (by simp))
    refine hfin.subset ?_
    rintro s ⟨hz, hi1, hi2⟩
    exact ⟨(hmem s).mpr ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩,
      hi1.le, hi2⟩, completedRiemannZeta_eq_zero_iff.mpr hz⟩
  · have he : zerosIn a b = ∅ := by
      ext s
      simp only [zerosIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hi1, hi2⟩
      exact hab (hi1.le.trans hi2)
    rw [he]
    exact Set.finite_empty

end DusartSmoothing.RvM


