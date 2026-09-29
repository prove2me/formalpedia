-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapRightRadialTangentBound
-- name    : CK_GeneralCK_PureGapZeroCapRightRadialTangentBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:22.987016+00:00
-- url     : https://prove2.me/theorems/a6259f05-7abf-4d4d-a85e-9787c7bec229
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapRightRadialTangentBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapRightRadialTangentBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapRightRadialTangentBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapRightRadialTangentBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapRightRadialTangentBound.lean)

import Definitions.Def_CK_GeneralCK_RadialConvexity
import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Mathlib.Tactic.Linarith

-- ===== source module GeneralCK.PureGapZeroCapRightRadialTangentBound =====
section

/-! A convex supporting-line bound at a positive radial profile radius.
This source is unaudited until a direct named Lean compile. -/

namespace GeneralCK

theorem rightCap_F_supporting_tangent {r s h : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hh : 0 < h) :
    F s h - F r h ≤
      (s - r) * radialSlope (radialContact s h) := by
  let f : ℝ → ℝ := fun z => F z h
  have hconv : ConvexOn ℝ (Set.Ici 0) f := convexOn_F_radius hh
  have hderiv : deriv f s = radialSlope (radialContact s h) :=
    deriv_F_radius_slope hs hh
  rcases lt_trichotomy r s with hrs | heq | hsr
  · have hsec := hconv.slope_le_deriv
      (show r ∈ Set.Ici (0 : ℝ) from hr)
      (show s ∈ Set.Ici (0 : ℝ) from hs.le)
      hrs (hasDerivAt_F_radius hs hh).differentiableAt
    rw [slope_def_field, hderiv] at hsec
    have hmul := (div_le_iff₀ (sub_pos.mpr hrs)).1 hsec
    dsimp [f] at hmul
    nlinarith only [hmul]
  · subst r
    simp
  · have hsec := hconv.deriv_le_slope
      (show s ∈ Set.Ici (0 : ℝ) from hs.le)
      (show r ∈ Set.Ici (0 : ℝ) from hr)
      hsr (hasDerivAt_F_radius hs hh).differentiableAt
    rw [slope_def_field, hderiv] at hsec
    have hmul := (le_div_iff₀ (sub_pos.mpr hsr)).1 hsec
    dsimp [f] at hmul
    nlinarith only [hmul]

#print axioms rightCap_F_supporting_tangent

end GeneralCK

end


