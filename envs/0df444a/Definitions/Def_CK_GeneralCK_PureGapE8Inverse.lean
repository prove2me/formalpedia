-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8Inverse
-- name    : CK_GeneralCK_PureGapE8Inverse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:47:17.144873+00:00
-- url     : https://prove2.me/theorems/77eee485-27cc-455c-aa4b-caedfda2c931
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8Inverse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8Inverse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8Inverse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8Inverse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8Inverse.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8Bridge
import Definitions.Def_CK_GeneralCK_EntropyCurvatureStrict
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet

-- ===== source module GeneralCK.PureGapE8Inverse =====
section

/-!
# The positive inverse of the equation-(8) slope

Strict radial curvature makes `e8Theta` strictly increasing on the positive
axis.  This file constructs its inverse on its actual positive range and
replaces the abstract global-left-inverse premise of the algebraic bridge by
a concrete range-restricted equation-(8) statement.
-/

namespace GeneralCK
open Set

theorem hasDerivAt_e8Theta {x : ℝ} (hx : 0 < x) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (((NormedAlgebra.toNormedSpace ℝ) : NormedSpace ℝ ℝ).toModule) _ _
      e8Theta
      (2 * deriv (deriv (fun r => F r 1)) (2 * x)) x := by
  have hd := (hasDerivAt_deriv_F_radius (show 0 < 2 * x by positivity)
    (by norm_num : (0 : ℝ) < 1)).differentiableAt.hasDerivAt
  have h := hd.comp x ((hasDerivAt_id x).const_mul 2)
  have heq : (deriv (fun r => F r 1)) ∘ (fun y : ℝ => 2 * y) = e8Theta := by
    funext y
    rfl
  rw [← heq]
  convert h using 1 <;> ring

theorem deriv_e8Theta_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv e8Theta x := by
  rw [(hasDerivAt_e8Theta hx).deriv]
  exact mul_pos (by norm_num) (deriv2_F_radius_pos (by positivity) (by norm_num))

theorem continuousOn_e8Theta_pos : ContinuousOn e8Theta (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_e8Theta hx).continuousAt.continuousWithinAt

/-- The normalized slope is strictly increasing on precisely the positive
contact-coordinate domain used in equation (8). -/
theorem strictMonoOn_e8Theta_pos : StrictMonoOn e8Theta (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_e8Theta_pos
  intro x hx
  exact deriv_e8Theta_pos (by simpa using hx)




theorem e8SlopeRange_subset_pos : e8SlopeRange ⊆ Ioi 0 := by
  rintro y ⟨x, hx, rfl⟩
  exact e8Theta_pos hx

theorem e8SlopeRange_isPreconnected : IsPreconnected e8SlopeRange := by
  exact isPreconnected_Ioi.image _ continuousOn_e8Theta_pos








theorem e8Q_pos {y : ℝ} (hy : y ∈ e8SlopeRange) : 0 < e8Q y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).1

theorem e8Theta_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8Theta (e8Q y) = y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).2

/-- The constructed inverse is a left inverse at every positive contact
coordinate. -/
theorem e8Q_e8Theta {x : ℝ} (hx : 0 < x) : e8Q (e8Theta x) = x := by
  have hy : e8Theta x ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  apply strictMonoOn_e8Theta_pos.injOn (e8Q_pos hy) hx
  rw [e8Theta_e8Q hy]

theorem strictMonoOn_e8Q_range : StrictMonoOn e8Q e8SlopeRange := by
  intro s hs t ht hst
  have hqs := e8Q_pos hs
  have hqt := e8Q_pos ht
  by_contra hn
  have hle : e8Q t ≤ e8Q s := le_of_not_gt hn
  have htheta : e8Theta (e8Q t) ≤ e8Theta (e8Q s) :=
    strictMonoOn_e8Theta_pos.monotoneOn hqt hqs hle
  rw [e8Theta_e8Q ht, e8Theta_e8Q hs] at htheta
  exact (not_le_of_gt hst) htheta

/-- The exact numerical/analytic statement still required from E8, reduced
to the actual range of the now-constructed inverse. -/
def E8StrictOnSlopeRange : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t →
    s ∈ e8SlopeRange → t ∈ e8SlopeRange →
    s + t ∈ e8SlopeRange → 2 * s + t ∈ e8SlopeRange →
    0 < e8Delta e8Q s t

theorem stationarity_e8Q_delta_eq_zero {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1)
    (ha : a < 1 / 2) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hstat :
      e8Theta (e8C a c e f) =
          e8Theta (e8D a c e f) + e8Theta (e8A a c e f) ∧
        e8Theta (e8B a c e f) =
          e8Theta (e8D a c e f) + e8Theta (e8C a c e f)) :
    e8Delta e8Q (e8Theta (e8D a c e f))
      (e8Theta (e8A a c e f)) = 0 := by
  have hApos : 0 < e8A a c e f := e8A_pos hc hf
  have hBpos : 0 < e8B a c e f := by
    unfold e8B
    exact div_pos (by linarith) (by positivity)
  have hCpos : 0 < e8C a c e f := by
    unfold e8C
    exact div_pos (by linarith) (by linarith)
  have hDpos : 0 < e8D a c e f := e8D_pos hac he hf
  have hst := hstat.1.symm
  have h2st :
      2 * e8Theta (e8D a c e f) + e8Theta (e8A a c e f) =
        e8Theta (e8B a c e f) := by linarith [hstat.1, hstat.2]
  unfold e8Delta
  rw [hst, h2st, e8Q_e8Theta hApos, e8Q_e8Theta hBpos,
    e8Q_e8Theta hCpos, e8Q_e8Theta hDpos]
  exact sub_eq_zero.mpr
    (e8_cross_identity (a := a) (c := c) he.ne' hf.ne' (by linarith))

/-- The range-restricted strict E8 theorem is sufficient to discharge the
smooth-interior local-minimum owner, without assuming any global inverse. -/
theorem not_localMin_of_e8SlopeRange
    (hE8 : E8StrictOnSlopeRange) {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1)
    (ha : a < 1 / 2) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    ¬ IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c) := by
  intro hmin
  have hstat := stationarity_to_e8Theta hac hsum ha hc he hf
    (canonicalPureGap_left_stationarity hac hsum ha he hf hmin)
    (canonicalPureGap_right_stationarity hac hsum hc he hf hmin)
  have hApos : 0 < e8A a c e f := e8A_pos hc hf
  have hBpos : 0 < e8B a c e f := by
    unfold e8B
    exact div_pos (by linarith) (by positivity)
  have hCpos : 0 < e8C a c e f := by
    unfold e8C
    exact div_pos (by linarith) (by linarith)
  have hDpos : 0 < e8D a c e f := e8D_pos hac he hf
  let s := e8Theta (e8D a c e f)
  let t := e8Theta (e8A a c e f)
  have hs : 0 < s := e8Theta_pos hDpos
  have ht : 0 < t := e8Theta_pos hApos
  have hsRange : s ∈ e8SlopeRange := ⟨_, hDpos, rfl⟩
  have htRange : t ∈ e8SlopeRange := ⟨_, hApos, rfl⟩
  have hstRange : s + t ∈ e8SlopeRange := by
    refine ⟨e8C a c e f, hCpos, ?_⟩
    exact hstat.1
  have h2stRange : 2 * s + t ∈ e8SlopeRange := by
    refine ⟨e8B a c e f, hBpos, ?_⟩
    dsimp only [s, t]
    linarith [hstat.1, hstat.2]
  have hzero := stationarity_e8Q_delta_eq_zero hac hsum ha hc he hf hstat
  have hpos := hE8 s t hs ht hsRange htRange hstRange h2stRange
  dsimp only [s, t] at hpos
  linarith

end GeneralCK

end


