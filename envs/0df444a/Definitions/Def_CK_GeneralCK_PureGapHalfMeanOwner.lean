-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapHalfMeanOwner
-- name    : CK_GeneralCK_PureGapHalfMeanOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:34:45.357983+00:00
-- url     : https://prove2.me/theorems/b1ab1ac5-e9c4-442c-856a-4b6c14730d37
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapHalfMeanOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapHalfMeanOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapHalfMeanOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapHalfMeanOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapHalfMeanOwner.lean)

import Definitions.Def_CK_GeneralCK_PureGapMinimizerLedger
import Definitions.Def_CK_GeneralCK_PureGapHalfMeanCurve

-- ===== source module GeneralCK.PureGapHalfMeanOwner =====
section

/-!
# Half-mean minimizer owner

This module packages the manuscript's transverse curvature conclusion in the
exact shape required by `CanonicalPureGapMinimizerExclusions.rightHalf`.
-/

namespace GeneralCK

/-- The analytic conclusion needed from the scalar `D₀` certificate. -/
def HalfMeanCurvatureNegative : Prop :=
  ∀ a e f : ℝ, a < 1 / 2 → 0 < e → 0 < f →
    e < H a → f < H (1 / 2) →
    e8Theta ((1 / 2 - a) / e) =
      2 * e8Theta ((1 / 2 - a) / (e + f)) →
    deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) < 0

/-- The exact transverse second-derivative identity from Appendix R.3.  It is
separated from the scalar sign certificate so each analytic component can be
verified independently. -/
def HalfMeanSecondDerivativeFormula (theta0 : ℝ) : Prop :=
  ∀ a e f : ℝ, a < 1 / 2 → 0 < e → 0 < f →
    e8Theta ((1 / 2 - a) / e) =
      2 * e8Theta ((1 / 2 - a) / (e + f)) →
    deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) =
      (1 / f) *
        (2 * deriv e8Theta ((1 / 2 - a) / (e + f)) *
          (1 - ((1 / 2 - a) / (e + f)) / ((1 / 2 - a) / e)) - theta0)

/-- A global positive `D₀` certificate and the exact derivative formula imply
the stationary negative-curvature owner consumed by the minimizer ledger. -/
theorem halfMeanCurvatureNegative_of_D0 {q0 theta0 : ℝ}
    (htheta0 : 0 < theta0) (hq0 : q0 = theta0⁻¹)
    (hD0 : ∀ s : ℝ, 0 < s → 0 < e8D0 e8Q q0 s)
    (hformula : HalfMeanSecondDerivativeFormula theta0) :
    HalfMeanCurvatureNegative := by
  intro a e f ha he hf _ _ hstationary
  let x : ℝ := (1 / 2 - a) / (e + f)
  let y : ℝ := (1 / 2 - a) / e
  let s : ℝ := e8Theta x
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hspos : 0 < s := e8Theta_pos hx
  have hstat : e8Theta y = 2 * s := by
    simpa only [x, y, s] using hstationary
  have hs : s ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  have h2s : 2 * s ∈ e8SlopeRange := ⟨y, hy, hstat⟩
  have hgapQ := e8D0_pos_implies_halfMean_slope_lt hs h2s
    htheta0 hq0 (hD0 s hspos)
  have hcoords := halfMean_stationarity_e8Q_coordinates hx hy hstat
  have hgap : 2 * deriv e8Theta x * (1 - x / y) < theta0 := by
    simpa only [s, hcoords.1, hcoords.2] using hgapQ
  rw [hformula a e f ha he hf hstationary]
  exact halfMean_transverse_curvature_neg hf hgap

/-- Negative transverse curvature discharges the exact right-half field of
the fixed-entropy minimizer ledger.  The negative value assumption is unused:
such a smooth constrained minimum cannot exist at any value. -/
theorem rightHalf_minimizer_exclusion_of_curvature
    (hcurv : HalfMeanCurvatureNegative) :
    ∀ S e f p, 0 < e → 0 < f → e < f →
      p ∈ retainedMeanSet S e f →
      p.2 = 1 / 2 → p.1 < p.2 → S < p.1 + p.2 →
      e < H p.1 → f < H p.2 →
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p →
      canonicalPureGap p.1 p.2 e f < 0 → False := by
  intro S e f p he hf _ hp hhalf hmean hseam hecap hfcap hmin _
  rcases p with ⟨a, c⟩
  simp only at hhalf
  subst c
  have hstationary := rightHalf_isMinOn_stationarity hp hmean he hf
    hseam hecap hmin
  exact (not_isMinOn_rightHalf_of_deriv2_neg hp hmean he hf hseam
    hecap hfcap (hcurv a e f hmean he hf hecap hfcap hstationary)) hmin

/-- The four minimizer owners left after the half-mean owner has been supplied
by `D₀` and the transverse derivative formula. -/
structure CanonicalPureGapNonHalfExclusions (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → p.1 < p.2 → p.2 < 1 / 2 →
    e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  leftCap : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    e = H p.1 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  rightCap : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    f = H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False

/-- Add the analytic half-mean curvature owner to the other four retained
owners, producing the exact ledger consumed by the global pure-gap theorem. -/
theorem CanonicalPureGapNonHalfExclusions.withHalfMeanCurvature {S : ℝ}
    (h : CanonicalPureGapNonHalfExclusions S)
    (hcurv : HalfMeanCurvatureNegative) :
    CanonicalPureGapMinimizerExclusions S where
  small := h.small
  seam := h.seam
  rightHalf := by
    intro e f p he hf hef hp hhalf hmean hseam hecap hfcap hmin hneg
    exact rightHalf_minimizer_exclusion_of_curvature hcurv S e f p he hf hef
      hp hhalf hmean hseam hecap hfcap hmin hneg
  leftCap := h.leftCap
  rightCap := h.rightCap

end GeneralCK

end


