-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroCard
-- name    : dusart_psi_433_20261014_ZeroCard
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:36:55.818155+00:00
-- url     : https://prove2.me/theorems/8dcf660f-fff2-4d7c-869d-0e55b127a134
-- title:
--   Dusart smoothing: Zero Card
-- statement:
--   This module gives the complete zero card component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WeightedCount
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set Filter Topology
open DusartSmoothing.Contour

lemma zeroMult_pos_of_positive_height (ρ : ℂ) (hρ : IsNontrivialZero ρ) (hi : 0 < ρ.im) :
    0 < zeroMult ρ := by
  let z : ℂ := (ρ.im / 2 : ℝ) * I
  let w : ℂ := 2 + (ρ.im + 1 : ℝ) * I
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (0 ≤ s.re ∧ s.re ≤ 2) ∧ (ρ.im / 2 ≤ s.im ∧ s.im ≤ ρ.im + 1) := by
    intro s
    simp [Rectangle, z, w, Complex.mem_reProdIm,
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2),
      Set.uIcc_of_le (by linarith : ρ.im / 2 ≤ ρ.im + 1)]
  have hf : AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
    intro s hs
    have him : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    exact analyticAt_riemannZeta (fun h => by simp [h] at him)
  have hp : (2 : ℂ) + ρ.im * I ∈ Rectangle z w := by
    apply (hmem _).2
    norm_num
    linarith
  have hr : ρ ∈ Rectangle z w := (hmem ρ).2
    ⟨⟨hρ.2.1.le, by linarith [hρ.2.2]⟩, by constructor <;> linarith⟩
  have ht := hf.analyticOrderAt_ne_top_of_isPreconnected
    (by rw [Complex.rectangle_eq_convexHull]; exact (convex_convexHull ℝ _).isPreconnected)
    hp hr (by
      rw [(hf _ hp).analyticOrderAt_eq_zero.mpr
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))]
      exact ENat.zero_ne_top)
  have hz := (hf ρ hr).analyticOrderAt_ne_zero.mpr hρ.1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
  have hn0 : n ≠ 0 := by intro h; subst n; simp [← hn] at hz
  simp only [zeroMult, analyticOrderNatAt, ← hn, ENat.toNat_coe]
  exact Nat.pos_of_ne_zero hn0

lemma positive_zero_window_card_bound (b : ℝ) (hb : 4 ≤ b) :
    ((finite_zero_window (b := b) (by norm_num : (0 : ℝ) < 4)).toFinset.card : ℝ) ≤
      16 * b ^ 2 := by
  classical
  let hf := finite_zero_window (b := b) (by norm_num : (0 : ℝ) < 4)
  let Z := hf.toFinset
  have hZ : ∀ ρ ∈ Z, IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨h, hi, _⟩ := hf.mem_toFinset.mp hρ
    exact ⟨h, by linarith⟩
  have hcount := DusartSmoothing.finite_actual_zero_count_le_square Z hZ b hb
  have he : DusartSmoothing.finiteZeroCount Z zeroMult Complex.im b =
      ∑ ρ ∈ Z, (zeroMult ρ : ℝ) := by
    unfold DusartSmoothing.finiteZeroCount
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hu := (hf.mem_toFinset.mp hρ).2.2
    simp [DusartSmoothing.primeStep, hu]
  rw [he] at hcount
  have hc : (Z.card : ℝ) ≤ ∑ ρ ∈ Z, (zeroMult ρ : ℝ) := by
    calc (Z.card : ℝ) = ∑ ρ ∈ Z, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ Z, (zeroMult ρ : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact_mod_cast zeroMult_pos_of_positive_height ρ (hZ ρ hρ).1 (hZ ρ hρ).2
  exact hc.trans hcount

end DusartSmoothing.RvM


