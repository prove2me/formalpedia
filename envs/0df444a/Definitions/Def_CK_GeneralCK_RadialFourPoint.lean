-- Prove2me | Definitions.Def_CK_GeneralCK_RadialFourPoint
-- name    : CK_GeneralCK_RadialFourPoint
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:35:41.463572+00:00
-- url     : https://prove2.me/theorems/43c350f2-b208-42fc-b425-35979b5d0e6c
-- title:
--   Courtade–Kumar proof module `GeneralCK.RadialFourPoint` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RadialFourPoint` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RadialFourPoint` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RadialFourPoint (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RadialFourPoint.lean)

import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_BellmanAssembly

namespace GeneralCK
open Set

theorem F_sqrt_add_le {h x y : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    F (Real.sqrt (x+y)) h ≤ F (Real.sqrt x) h + F (Real.sqrt y) h := by
  by_cases hs : x+y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst x; subst y
    simp [F]
  have hs0 : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hw : y/(x+y)+x/(x+y) = 1 := by field_simp; ring
  have h₁ := (concaveOn_F_sqrt hh).2 (show (0:ℝ) ∈ Ici 0 by simp)
    (show x+y ∈ Ici 0 from hs0.le) (div_nonneg hy hs0.le) (div_nonneg hx hs0.le) hw
  have h₂ := (concaveOn_F_sqrt hh).2 (show (0:ℝ) ∈ Ici 0 by simp)
    (show x+y ∈ Ici 0 from hs0.le) (div_nonneg hx hs0.le) (div_nonneg hy hs0.le)
    (by linarith : x/(x+y)+y/(x+y)=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sqrt_zero,
    show F 0 h = 0 by simp [F], div_mul_cancel₀ _ hs] at h₁ h₂
  have he : y/(x+y)*F (Real.sqrt (x+y)) h + x/(x+y)*F (Real.sqrt (x+y)) h =
      F (Real.sqrt (x+y)) h := by rw [← add_mul, hw, one_mul]
  linarith

/-- The radial four-point inequality, including radii crossing zero. -/
theorem F_four_point {h : ℝ} (hh : 0 < h) (r d : ℝ) :
    (F |r-d| h + F |r+d| h)/2 ≤ F |r| h + F |d| h := by
  have hs := F_sqrt_add_le hh (sq_nonneg r) (sq_nonneg d)
  simp only [Real.sqrt_sq_eq_abs] at hs
  exact (F_average_le_sqrt hh r d).trans hs

theorem equal_entropy_phi_gap_le_radial {e : ℝ} (he : 0 < e) (a b : ℝ) :
    candidateGap phi a b e e ≤ F |a-b| e := by
  have hf := F_four_point he (1-a-b) (b-a)
  have h₁ : 1-a-b-(b-a) = 1-2*b := by ring
  have h₂ : 1-a-b+(b-a) = 1-2*a := by ring
  have h₃ : 1-2*((a+b)/2) = 1-a-b := by ring
  rw [h₁,h₂,abs_sub_comm b a] at hf
  unfold candidateGap phi
  rw [show (e+e)/2=e by ring,h₃]
  linarith

end GeneralCK


