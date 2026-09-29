-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerLeftMinor
-- name    : CK_GeneralCK_CorrectionHighUNearCornerLeftMinor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:37:30.790583+00:00
-- url     : https://prove2.me/theorems/ad3e83a4-c380-499d-a140-f50e29d9d0bb
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerLeftMinor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerLeftMinor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerLeftMinor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerLeftMinor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerLeftMinor.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerLeftScalar
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRadialBounds

/-! An unconditional lower bound for the actual natural left Hessian minor. -/

namespace GeneralCK.Correction.HighU

theorem nearCorner_au_lower
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    2 * (1 / 4 - t ^ 2) - t ^ 2 * (1 / 6000 + rho ^ 3) ≤
      Natural.au (1 / 2 - t) (1 / 2 - (1 - rho) * t) := by
  let u : ℝ := 1 / 2 - t
  let w : ℝ := 1 / 2 - (1 - rho) * t
  let p : ℝ := 1 / 4 - t ^ 2
  let J := Natural.jn u
  let K := Natural.jn w
  let F := Natural.Fs (Natural.contact u w)
  let A := Natural.au u w
  let E : ℝ := 1 / 6000 + rho ^ 3
  have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 / 4 := by dsimp [p]; nlinarith only [sq_nonneg t]
  have hJ := nearCorner_jn_enclosure ht.le ht1
  change 4 * t + (16 / 3 : ℝ) * t ^ 3 ≤ J ∧
    J ≤ 4 * t + (667 / 125 : ℝ) * t ^ 3 at hJ
  have hJlo : 4 * t ≤ J := by nlinarith only [hJ.1, pow_nonneg ht.le 3]
  have hJ0 : 0 < J := by linarith
  have hK := nearCorner_second_jn_lower ht.le ht1 hr.le hr1
  change 4 * t * (1 - rho) + 4 * t ^ 3 * ((4 / 3 : ℝ) - 4 * rho) ≤ K at hK
  have hF := nearCorner_Fs_contact_lower ht ht1 hr hr1
  change 4 * rho * t - 8 * rho ^ 3 * t ^ 3 ≤ F at hF
  have hcomb : 4 * rho * t + 4 * t ^ 3 * (-1 / 1500 - 4 * rho - 4 * rho ^ 3) ≤
      K - J + 2 * F := by nlinarith only [hK, hJ.2, hF]
  have hnum : (A - 2 * p) * J =
      p * (K - J + 2 * F) + rho * t * (2 * t * J - 1) := by
    dsimp [A]
    unfold Natural.au
    rw [show Natural.qp u = p by dsimp [Natural.qp, u, p]; ring,
      show w - u = rho * t by dsimp [u, w]; ring,
      show 1 - 2 * u = 2 * t by dsimp [u]; ring]
    change ((_ / J) - 2 * p) * J = _
    field_simp [hJ0.ne']
    <;> ring
  have hpcomb := mul_le_mul_of_nonneg_left hcomb hp0
  have hpJ := mul_le_mul_of_nonneg_left hJlo
    (show 0 ≤ 2 * rho * t ^ 2 by positivity)
  have hpE : 0 ≤ E := by dsimp [E]; positivity
  have hsmall := mul_nonneg (sub_nonneg.mpr hp1)
    (show 0 ≤ 4 * t ^ 3 * (1 / 1500 + 4 * rho ^ 3) by positivity)
  have hpos : 0 ≤ 16 * rho * t ^ 5 := by positivity
  have hid :
      p * (4 * rho * t + 4 * t ^ 3 * (-1 / 1500 - 4 * rho - 4 * rho ^ 3)) +
        rho * t * (8 * t ^ 2 - 1) =
      -4 * p * t ^ 3 * (1 / 1500 + 4 * rho ^ 3) + 16 * rho * t ^ 5 := by
    dsimp [p]
    ring
  have hN : -4 * t ^ 3 * E ≤ (A - 2 * p) * J := by
    dsimp [E]
    nlinarith only [hnum, hpcomb, hpJ, hsmall, hpos, hid]
  have hcancel := mul_nonneg (sub_nonneg.mpr hJlo)
    (mul_nonneg (sq_nonneg t) hpE)
  have hmul : (2 * p - t ^ 2 * E) * J ≤ A * J := by
    nlinarith only [hN, hcancel]
  exact (mul_le_mul_iff_left₀ hJ0).mp hmul

theorem nearCorner_zu_factor
    {t rho : ℝ} :
    Natural.zu (1 / 2 - t) (1 / 2 - (1 - rho) * t) =
      -(1 / 4 - t ^ 2) *
        (1 + rho * t * Natural.jn (1 / 2 - t) /
          Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t)) := by
  unfold Natural.zu Natural.qp
  ring

theorem nearCorner_rank_coordinate_bounds
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    0 ≤ rho * t * Natural.jn (1 / 2 - t) /
        Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t) ∧
      rho * t * Natural.jn (1 / 2 - t) /
        Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t) ≤
          3 * rho * t ^ 2 := by
  let J := Natural.jn (1 / 2 - t)
  let S := Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - rho) * t)
  have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
  have hS := nearCorner_entropySum_enclosure ht.le ht1 hr.le hr1
  change 2 * Real.log 2 - (2001 / 500 : ℝ) * t ^ 2 ≤ S ∧ S ≤ 2 * Real.log 2 at hS
  have hSlow : (1379 / 1000 : ℝ) ≤ S := by
    nlinarith only [hS.1, ht2, nearCorner_log_two_lower]
  have hS0 : 0 < S := by linarith
  have hJ := nearCorner_jn_enclosure ht.le ht1
  change 4 * t + (16 / 3 : ℝ) * t ^ 3 ≤ J ∧
    J ≤ 4 * t + (667 / 125 : ℝ) * t ^ 3 at hJ
  have hJ0 : 0 ≤ J := by nlinarith only [hJ.1, pow_nonneg ht.le 3, ht.le]
  have hJup : J ≤ (4001 / 1000 : ℝ) * t := by
    have hp := mul_le_mul_of_nonneg_left ht2 ht.le
    nlinarith only [hJ.2, hp, ht.le]
  change 0 ≤ rho * t * J / S ∧ rho * t * J / S ≤ 3 * rho * t ^ 2
  refine ⟨div_nonneg (by positivity) hS0.le, (div_le_iff₀ hS0).2 ?_⟩
  have hp := mul_le_mul_of_nonneg_left hJup (mul_nonneg hr.le ht.le)
  have hq := mul_le_mul_of_nonneg_left hSlow (show 0 ≤ 3 * rho * t ^ 2 by positivity)
  have hn : 0 ≤ rho * t ^ 2 := by positivity
  nlinarith only [hp, hq, hn]

/-- The first raw near-corner wedge inequality is unconditional. -/
theorem nearCorner_m11_lower
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    t ^ 2 / 2 ≤ Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) := by
  have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
  have hA := nearCorner_au_lower ht ht1 hr hr1
  have hW := nearCorner_weight_upper ht ht1 hr hr1
  obtain ⟨he0, he1⟩ := nearCorner_rank_coordinate_bounds ht ht1 hr hr1
  have h := nearCorner_left_minor_scalar_bound (sq_nonneg t) ht2 hr.le hr1 hA hW he0 he1
  unfold Natural.m11
  rw [nearCorner_zu_factor]
  convert h using 1 <;> ring

#print axioms nearCorner_au_lower
#print axioms nearCorner_zu_factor
#print axioms nearCorner_rank_coordinate_bounds
#print axioms nearCorner_m11_lower

end GeneralCK.Correction.HighU


