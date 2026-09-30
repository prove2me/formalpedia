-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:31:48.066103+00:00
-- url     : https://prove2.me/theorems/8be98607-863d-4f71-9ac8-49be1617c1b7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/CoverageKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel

open E8ComplexBallKernel E8GaussianRatBall

def InSquare (x y h : ℝ) (tau : ℂ) : Prop :=
  x - h ≤ tau.re ∧ tau.re ≤ x + h ∧ y - h ≤ tau.im ∧ tau.im ≤ y + h

theorem childLL {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : tau.re ≤ x) (hy : tau.im ≤ y) :
    InSquare (x-h/2) (y-h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childLR {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : x ≤ tau.re) (hy : tau.im ≤ y) :
    InSquare (x+h/2) (y-h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childUL {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : tau.re ≤ x) (hy : y ≤ tau.im) :
    InSquare (x-h/2) (y+h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childUR {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : x ≤ tau.re) (hy : y ≤ tau.im) :
    InSquare (x+h/2) (y+h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem inBall_of_inSquare {x y h : ℝ} {tau : ℂ}
    (hs : InSquare x y h tau) (hh : 0 ≤ h) :
    InBall tau (x + y * Complex.I) (3/2*h) := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  unfold InBall
  have hre : (tau.re-x)^2 ≤ h^2 := by nlinarith
  have him : (tau.im-y)^2 ≤ h^2 := by nlinarith
  have hsquare : ‖tau - (x + y * Complex.I)‖^2 ≤ (3/2*h)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg h]
  nlinarith [norm_nonneg (tau - (x + y * Complex.I))]

theorem disc_in_root {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ)) :
    InSquare 0 0 (2/5) tau := by
  have hre := Complex.abs_re_le_norm tau
  have him := Complex.abs_im_le_norm tau
  rw [abs_le] at hre him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel

end


