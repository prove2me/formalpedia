-- Prove2me | Definitions.Def_CK_E8EntropyQuotientBound
-- name    : CK_E8EntropyQuotientBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:52:45.884988+00:00
-- url     : https://prove2.me/theorems/d7394473-576d-4daa-8744-12e589c4eb29
-- title:
--   Courtade–Kumar proof module `E8EntropyQuotientBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8EntropyQuotientBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8EntropyQuotientBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8EntropyQuotientBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8EntropyQuotientBound.lean)

import Definitions.Def_CK_E8RatioFactor

-- ===== source module E8EntropyQuotientBound =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Filter SmallMean
open Certificates.E8TAxisStableScalar
open Certificates.E8HistoricalLogConvexityBridge

private noncomputable def biasSlack (x : ℝ) : ℝ :=
  3 / 2 * ((1 - x) * ((1 + x) * Real.log (1 + x)) -
    (1 + x) * ((1 - x) * Real.log (1 - x))) -
    4 * x * (Real.log 2 - Cn x)

private noncomputable def biasSlackPrime (x : ℝ) : ℝ :=
  3 - 2 * x * A x - 4 * Real.log 2 + 4 * Cn x

private theorem biasSlack_eq {x : ℝ} (hx : -1 < x) (hx1 : x < 1) :
    biasSlack x = 3 * (1 - x ^ 2) * A x - 4 * x * (Real.log 2 - Cn x) := by
  unfold biasSlack A
  rw [Real.log_div (by linarith : 1 + x ≠ 0) (by linarith : 1 - x ≠ 0)]
  ring

private theorem hasDerivAt_biasSlack {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt biasSlack (biasSlackPrime x) x := by
  have hq := ((hasDerivAt_id x).pow 2).const_sub 1
  have hA := hasDerivAt_A (by linarith) hx1
  have hC := hasDerivAt_Cn (by linarith) hx1
  have hd := ((hq.mul hA).const_mul 3).sub
    (((hasDerivAt_id x).const_mul 4).mul (hC.const_sub (Real.log 2)))
  have heq : biasSlack =ᶠ[nhds x]
      (fun y => 3 * (1 - y ^ 2) * A y - 4 * y * (Real.log 2 - Cn y)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -1 < x) hx1] with y hy
    exact biasSlack_eq hy.1 hy.2
  have hi := hd.congr_deriv (show _ = biasSlackPrime x from by
    simp only [Pi.pow_apply, id_eq, biasSlackPrime]
    field_simp [show 1 - x ^ 2 ≠ 0 by nlinarith]
    <;> ring)
  have hj := hi.congr_of_eventuallyEq
    (heq.trans (Filter.Eventually.of_forall (fun y => by dsimp; ring)))
  rw [hasDerivAt_iff_isLittleO] at hj ⊢
  simpa only [smul_eq_mul] using hj

private theorem hasDerivAt_biasSlackPrime {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt biasSlackPrime (2 * A x - 2 * x / (1 - x ^ 2)) x := by
  have hd := ((((hasDerivAt_id x).mul (hasDerivAt_A (by linarith) hx1)).const_mul 2).const_sub 3).sub_const (4 * Real.log 2) |>.add
      ((hasDerivAt_Cn (by linarith) hx1).const_mul 4)
  have hi := hd.congr_deriv (show _ = 2 * A x - 2 * x / (1 - x ^ 2) from by
    simp only [id_eq]
    ring)
  rw [hasDerivAt_iff_isLittleO] at hi ⊢
  simpa only [biasSlackPrime, smul_eq_mul, Pi.add_apply, Pi.mul_apply, id_eq, mul_assoc] using hi

private theorem biasSlack_nonnegative {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ biasSlack x := by
  have hcont : Continuous biasSlack := by
    have hp : Continuous (fun x : ℝ => (1 + x) * Real.log (1 + x)) :=
      Real.continuous_mul_log.comp (continuous_const.add continuous_id)
    have hm : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
      Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
    exact (((continuous_const.sub continuous_id).mul hp).sub
      ((continuous_const.add continuous_id).mul hm)).const_mul (3 / 2) |>.sub
        ((continuous_id.const_mul 4).mul (continuous_const.sub Cn_continuous))
  have hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) biasSlack := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) hcont.continuousOn
      (f' := biasSlackPrime) (f'' := fun x => 2 * A x - 2 * x / (1 - x ^ 2))
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) 1 := by simpa using hy
      exact (hasDerivAt_biasSlack hy'.1 hy'.2).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) 1 := by simpa using hy
      exact (hasDerivAt_biasSlackPrime hy'.1 hy'.2).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) 1 := by simpa using hy
      rw [mul_div_assoc]
      linarith [A_upper hy'.1.le hy'.2]
  have hv := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (sub_nonneg.mpr hx1) hx
    (show 1 - x + x = 1 by ring)
  simpa [biasSlack, Cn_zero, Cn_one] using hv

/-- A uniform analytic lower bound, independent of interval arithmetic. -/
theorem entropyQuotient_ge_third {a : ℝ} (ha : 0 < a) :
    (1 / 3 : ℝ) ≤ entropyQuotient a := by
  have hr := r_pos ha
  have hr1 := r_lt_one a
  have hC : Real.log 2 - Cn (r a) = h a := by
    rw [← biasE_r]
    rw [Reflection.biasE_eq_log_mul_E (by linarith) hr1]
    unfold Cn Reflection.E
    ring
  have hf := biasSlack_nonnegative hr.le hr1.le
  rw [biasSlack_eq (by linarith) hr1, A_r, hC] at hf
  have hh := h_add_a_mul_r a
  unfold entropyQuotient
  apply (le_div_iff₀ (h_pos ha)).2
  have hgoal : h a / 3 + ell a ≤ a / r a := by
    apply (le_div_iff₀ hr).2
    nlinarith
  linarith

#print axioms entropyQuotient_ge_third

end GeneralCK.E8RatioMonotonicity

end


