-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Jensen
-- name    : dusart_psi_433_20261014_Jensen
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:16:06.991715+00:00
-- url     : https://prove2.me/theorems/ccc80618-38fa-46e1-96b3-295eb413fb2d
-- title:
--   Dusart smoothing: Jensen
-- statement:
--   This module gives the complete jensen component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Complex Set Metric MeromorphicOn
open scoped BigOperators

noncomputable section
namespace DusartSmoothing.RvM

def diskZeros (r : ℝ) (f : ℂ → ℂ) : Set ℂ := {z | ‖z‖ ≤ r ∧ f z = 0}

lemma divisor_eq_natOrder {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) (hf0 : f 0 ≠ 0)
    (hR : 0 ≤ R) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    divisor f (closedBall (0 : ℂ) R) z = (analyticOrderNatAt f z : ℤ) := by
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by simpa using hR
  have htop := hf.analyticOrderAt_ne_top_of_isPreconnected (x := 0)
    (convex_closedBall (0 : ℂ) R).isPreconnected h0 hz
    (by rw [(hf 0 h0).analyticOrderAt_eq_zero.mpr hf0]; exact ENat.zero_ne_top)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [hf.divisor_apply hz]
  simp [analyticOrderNatAt, ← hn]

lemma diskZeros_finite {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) (hf0 : f 0 ≠ 0)
    (hR : 0 ≤ R) : (diskZeros R f).Finite := by
  refine ((divisor f (closedBall (0 : ℂ) R)).finiteSupport
    (isCompact_closedBall (0 : ℂ) R)).subset ?_
  rintro z ⟨hz, hzero⟩
  have hzball : z ∈ closedBall (0 : ℂ) R := by simpa using hz
  rw [Function.mem_support, divisor_eq_natOrder hf hf0 hR hzball]
  have hn0 := (hf z hzball).analyticOrderAt_ne_zero.mpr hzero
  have htop := hf.analyticOrderAt_ne_top_of_isPreconnected (x := 0)
    (convex_closedBall (0 : ℂ) R).isPreconnected
    (by simpa using hR) hzball
    (by rw [(hf 0 (by simpa using hR)).analyticOrderAt_eq_zero.mpr hf0]
        exact ENat.zero_ne_top)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hnpos : n ≠ 0 := by intro h; subst n; simp [← hn] at hn0
  simp [analyticOrderNatAt, ← hn, hnpos]

/-- Jensen's weighted zero count, with the logarithm of the growth bound retained. -/
lemma disk_zero_order_bound {B r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) (hf0 : f 0 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∃ hfin : (diskZeros r f).Finite,
      ((∑ z ∈ hfin.toFinset, analyticOrderNatAt f z : ℕ) : ℝ) ≤
        Real.log B / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf0ne : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfr := hf.mono (closedBall_subset_closedBall hrR.le)
  have hfin := diskZeros_finite hfr hf0ne hr.le
  refine ⟨hfin, ?_⟩
  have hB : 1 ≤ B := by simpa [hf0] using hbound 0 (by simpa using hR.le)
  have hfabs : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := by
    simpa [abs_of_pos hR] using hf
  have hJ := hfabs.sum_divisor_le (r := r) (R := R) (M := B)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hR] using hrR) hB hf0ne
    (by intro z hz; exact hbound z (by simpa [abs_of_pos hR] using hz.le))
  rw [abs_of_pos hr, hf0, norm_one, div_one] at hJ
  have hsupport : (divisor f (closedBall (0 : ℂ) r)).support ⊆
      (hfin.toFinset : Set ℂ) := by
    intro z hz
    have hzball := (divisor f (closedBall (0 : ℂ) r)).supportWithinDomain hz
    have hzero : f z = 0 := by
      by_contra hn
      have he := (hfr z hzball).analyticOrderAt_eq_zero.mpr hn
      have : divisor f (closedBall (0 : ℂ) r) z = 0 := by
        rw [hfr.divisor_apply hzball, he]; simp
      exact hz this
    change z ∈ hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨by simpa using hzball, hzero⟩
  rw [finsum_eq_sum_of_support_subset _ hsupport] at hJ
  have heq : (∑ z ∈ hfin.toFinset, divisor f (closedBall (0 : ℂ) r) z) =
      ((∑ z ∈ hfin.toFinset, analyticOrderNatAt f z : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro z hz
    exact divisor_eq_natOrder hfr hf0ne hr.le
      (by simpa using (hfin.mem_toFinset.mp hz).1)
  rw [heq] at hJ
  exact_mod_cast hJ

end DusartSmoothing.RvM


