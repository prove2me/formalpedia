-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapMiddleDeterministic
-- name    : CK_GeneralCK_PureGapMiddleDeterministic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:50:06.816828+00:00
-- url     : https://prove2.me/theorems/77768724-62a1-45a8-989d-30b32781349e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapMiddleDeterministic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapMiddleDeterministic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapMiddleDeterministic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapMiddleDeterministic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapMiddleDeterministic.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8Inverse
import Definitions.Def_CK_GeneralCK_RadialZeroBoundary
import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_CorrectionGlobalConvexity

-- ===== source module GeneralCK.PureGapMiddleDeterministic =====
section

/-!
# Analytic middle deterministic ordering

This isolates the only scalar analytic input in manuscript Lemma 6.1:
concavity of `e8Theta` on the nonnegative ray.  Concavity and `Theta(0)=0`
give subadditivity; existing strict monotonicity then controls the cap-fiber
derivative.
-/

namespace GeneralCK
open Set

noncomputable def middleDeterministicGap (a b c : ℝ) : ℝ :=
  canonicalPureGap a c (H a) (H b)

def E8ThetaConcave : Prop := ConcaveOn ℝ (Ici 0) e8Theta

def E8ThetaSubadditiveOnNonneg : Prop :=
  ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → e8Theta (x + y) ≤ e8Theta x + e8Theta y

theorem e8Theta_zero : e8Theta 0 = 0 := by
  unfold e8Theta
  simpa using (hasDerivAt_F_zero (by norm_num : (0 : ℝ) < 1)).deriv

/-- The quotient `Theta(x)/x` decreases on the positive ray.  This is the
direct consequence of the already-certified radial concavity inequality
`z F''(z) ≤ F'(z)`. -/
theorem antitoneOn_e8Theta_div :
    AntitoneOn (fun x : ℝ => e8Theta x / x) (Ioi 0) := by
  intro x hx y hy hxy
  have h := antitoneOn_F_radius_ratio (h := (1 : ℝ)) (by norm_num)
    (show 2 * x ∈ Ioi (0 : ℝ) by
      exact mul_pos two_pos (show 0 < x by simpa using hx))
    (show 2 * y ∈ Ioi (0 : ℝ) by
      exact mul_pos two_pos (show 0 < y by simpa using hy))
    (mul_le_mul_of_nonneg_left hxy (by norm_num))
  unfold e8Theta
  convert mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 4 by norm_num) using 1 <;>
    field_simp <;> ring

theorem subadditiveOn_nonneg_of_antitone_div {f : ℝ → ℝ}
    (hzero : f 0 = 0)
    (hratio : AntitoneOn (fun x : ℝ => f x / x) (Ioi 0))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + f y := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simpa [hzero]
  rcases hy.eq_or_lt with rfl | hypos
  · simpa [hzero]
  have hspos : 0 < x + y := add_pos hxpos hypos
  have hxratio := hratio hxpos hspos (le_add_of_nonneg_right hy)
  have hyratio := hratio hypos hspos (le_add_of_nonneg_left hx)
  have hxbound : x * (f (x + y) / (x + y)) ≤ f x := by
    have h := mul_le_mul_of_nonneg_left hxratio hx
    calc
      x * (f (x + y) / (x + y)) ≤ x * (f x / x) := h
      _ = f x := by field_simp [hxpos.ne']
  have hybound : y * (f (x + y) / (x + y)) ≤ f y := by
    have h := mul_le_mul_of_nonneg_left hyratio hy
    calc
      y * (f (x + y) / (x + y)) ≤ y * (f y / y) := h
      _ = f y := by field_simp [hypos.ne']
  calc
    f (x + y) = x * (f (x + y) / (x + y)) +
        y * (f (x + y) / (x + y)) := by field_simp [hspos.ne']
    _ ≤ f x + f y := add_le_add hxbound hybound

/-- Unconditional subadditivity of the actual manuscript slope. -/
theorem e8Theta_subadditiveOn_nonneg_actual : E8ThetaSubadditiveOnNonneg := by
  intro x y hx hy
  exact subadditiveOn_nonneg_of_antitone_div e8Theta_zero
    antitoneOn_e8Theta_div hx hy

theorem subadditiveOn_nonneg_of_concaveOn_zero {f : ℝ → ℝ}
    (hconcave : ConcaveOn ℝ (Ici 0) f) (hzero : f 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + f y := by
  by_cases hs : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp only [hx0, hy0, add_zero, hzero]
    norm_num
  have hspos : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hcx := hconcave.2 (show x + y ∈ Ici (0 : ℝ) by exact hspos.le)
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show 0 ≤ x / (x + y) by positivity)
    (show 0 ≤ y / (x + y) by positivity)
    (show x / (x + y) + y / (x + y) = 1 by field_simp)
  have hcy := hconcave.2 (show x + y ∈ Ici (0 : ℝ) by exact hspos.le)
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show 0 ≤ y / (x + y) by positivity)
    (show 0 ≤ x / (x + y) by positivity)
    (show y / (x + y) + x / (x + y) = 1 by field_simp; ring)
  simp only [smul_eq_mul, hzero, mul_zero, add_zero] at hcx hcy
  have hxarg : x / (x + y) * (x + y) = x := by
    field_simp
  have hyarg : y / (x + y) * (x + y) = y := by
    field_simp
  rw [hxarg] at hcx
  rw [hyarg] at hcy
  have hden : 0 < x + y := hspos
  calc
    f (x + y) = x / (x + y) * f (x + y) + y / (x + y) * f (x + y) := by
      field_simp
    _ ≤ f x + f y := add_le_add hcx hcy

theorem e8Theta_subadditiveOn_nonneg (hconcave : E8ThetaConcave)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    e8Theta (x + y) ≤ e8Theta x + e8Theta y :=
  subadditiveOn_nonneg_of_concaveOn_zero hconcave e8Theta_zero hx hy

theorem e8ThetaSubadditiveOnNonneg_of_concave (hconcave : E8ThetaConcave) :
    E8ThetaSubadditiveOnNonneg := by
  intro x y hx hy
  exact e8Theta_subadditiveOn_nonneg hconcave hx hy

/-- Exact derivative identity used in the middle deterministic proof. -/
theorem deriv_middleDeterministicGap {a b c : ℝ}
    (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2) :
    deriv (middleDeterministicGap a b) c =
      e8Theta ((c - a) / (H a + H b)) -
      e8Theta ((1 - a - c) / (H a + H b)) +
      e8Theta ((1 - 2 * c) / (2 * H b)) := by
  have ha : 0 < a := hb.trans hba
  have ha' : a < 1 / 2 := hac.trans hc
  have hb' : b < 1 / 2 := hba.trans ha'
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb : 0 < H b := H_pos hb (by linarith)
  unfold middleDeterministicGap
  rw [deriv_canonicalPureGap_right hac (by linarith) hc hHa hHb,
    deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) (by linarith),
    deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
    deriv_F_radius_eq_e8Theta (by linarith) hHb]
  congr 1 <;> field_simp <;> ring

/-- The scalar ordering behind nonnegativity of the middle-cap derivative.
This exposes the weakest reusable analytic premise actually consumed by the
argument: subadditivity on the nonnegative ray. -/
theorem deriv_middleDeterministicGap_nonneg_of_subadditive
    (hsubadd : E8ThetaSubadditiveOnNonneg)
    {a b c : ℝ} (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2) :
    0 ≤ deriv (middleDeterministicGap a b) c := by
  rw [deriv_middleDeterministicGap hb hba hac hc]
  let E := H a + H b
  let U := (c - a) / E
  let V := (1 - a - c) / E
  let W := (1 - 2 * c) / (2 * H b)
  have ha : 0 < a := hb.trans hba
  have ha' : a < 1 / 2 := hac.trans hc
  have hb' : b < 1 / 2 := hba.trans ha'
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb : 0 < H b := H_pos hb (by linarith)
  have hE : 0 < E := by dsimp [E]; linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; exact div_pos (by linarith) hE
  have hW : 0 < W := by dsimp [W]; exact div_pos (by linarith) (mul_pos two_pos hHb)
  have horder : V ≤ U + W := by
    have hHab : H b < H a := H_strictMonoOn
      ⟨hb.le, hb'.le⟩ ⟨ha.le, ha'.le⟩ hba
    have hid : U + W - V =
        (1 - 2 * c) * (H a - H b) / (2 * H b * E) := by
      dsimp [U, V, W, E]
      field_simp [hHb.ne', hE.ne']
      ring
    rw [← sub_nonneg]
    rw [hid]
    exact div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hHab.le))
      (mul_nonneg (mul_nonneg (by norm_num) hHb.le) hE.le)
  have hmono : e8Theta V ≤ e8Theta (U + W) :=
    strictMonoOn_e8Theta_pos.monotoneOn hV (show 0 < U + W by linarith) horder
  have hsub := hsubadd hU.le hW.le
  dsimp [U, V, W, E] at hmono hsub ⊢
  linarith

theorem deriv_middleDeterministicGap_nonneg (hconcave : E8ThetaConcave)
    {a b c : ℝ} (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2) :
    0 ≤ deriv (middleDeterministicGap a b) c :=
  deriv_middleDeterministicGap_nonneg_of_subadditive
    (e8ThetaSubadditiveOnNonneg_of_concave hconcave) hb hba hac hc

theorem deriv_middleDeterministicGap_nonneg_actual
    {a b c : ℝ} (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2) :
    0 ≤ deriv (middleDeterministicGap a b) c :=
  deriv_middleDeterministicGap_nonneg_of_subadditive
    e8Theta_subadditiveOn_nonneg_actual hb hba hac hc

/-- Lemma 6.1 with its equal-mean endpoint isolated.  In the final assembly
that endpoint is supplied by the existing equal-mean owner. -/
theorem middleDeterministicGap_nonneg_of_endpoint_of_subadditive
    (hsubadd : E8ThetaSubadditiveOnNonneg) {a b c : ℝ}
    (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2)
    (hendpoint : 0 ≤ middleDeterministicGap a b a) :
    0 ≤ middleDeterministicGap a b c := by
  have ha : 0 < a := hb.trans hba
  have ha' : a < 1 / 2 := hac.trans hc
  have hb' : b < 1 / 2 := hba.trans ha'
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb : 0 < H b := H_pos hb (by linarith)
  have hcontinuous : ContinuousOn (middleDeterministicGap a b) (Icc a c) := by
    unfold middleDeterministicGap
    apply (continuousOn_canonicalPureGap hHa hHb).comp
      (show Continuous (fun x : ℝ => (a, x)) by fun_prop).continuousOn
    intro x hx
    refine ⟨ha.le, hx.1, hx.2.trans hc.le, le_rfl, ?_⟩
    have hbx : b ≤ x := hba.le.trans hx.1
    exact H_strictMonoOn.monotoneOn ⟨hb.le, hb'.le⟩
      ⟨ha.le.trans hx.1, hx.2.trans hc.le⟩ hbx
  have hdifferentiable : DifferentiableOn ℝ (middleDeterministicGap a b)
      (interior (Icc a c)) := by
    rw [interior_Icc]
    intro x hx
    have hxa : 0 < x - a := sub_pos.mpr hx.1
    have hcenter : 0 < 1 - a - x := by linarith [hx.2, hac]
    have hright : 0 < 1 - 2 * x := by linarith [hx.2, hc]
    have hef : 0 < (H a + H b) / 2 := by linarith
    have hFd := (hasDerivAt_F_radius hxa hef).differentiableAt.hasDerivAt
    have hFc := (hasDerivAt_F_radius hcenter hef).differentiableAt.hasDerivAt
    have hFr := (hasDerivAt_F_radius hright hHb).differentiableAt.hasDerivAt
    have hdiff := hFd.comp x ((hasDerivAt_id x).sub_const a)
    have hcenter' := hFc.comp x ((hasDerivAt_id x).const_sub (1 - a))
    have hleft := hasDerivAt_const x (radialPhi (1 - 2 * a) (H a))
    have hright' := hFr.comp x (((hasDerivAt_id x).const_mul 2).const_sub 1)
    have htotal :=
      ((hdiff.add (hasDerivAt_const x (entropyCorrection (H a) (H b)))).sub
        ((hasDerivAt_const x (eta ((H a + H b) / 2))).sub hcenter')).add
        ((hleft.add ((hasDerivAt_const x (eta (H b))).sub hright')).div_const 2)
    refine (htotal.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards with y
    simp [middleDeterministicGap, canonicalPureGap, radialPhi, Function.comp_apply]
  have hmonotone : MonotoneOn (middleDeterministicGap a b) (Icc a c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a c) hcontinuous hdifferentiable
    intro x hx
    rw [interior_Icc] at hx
    exact deriv_middleDeterministicGap_nonneg_of_subadditive
      hsubadd hb hba hx.1 (hx.2.trans hc)
  exact hendpoint.trans (hmonotone ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩ hac.le)

theorem middleDeterministicGap_nonneg_of_endpoint
    (hconcave : E8ThetaConcave) {a b c : ℝ}
    (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2)
    (hendpoint : 0 ≤ middleDeterministicGap a b a) :
    0 ≤ middleDeterministicGap a b c :=
  middleDeterministicGap_nonneg_of_endpoint_of_subadditive
    (e8ThetaSubadditiveOnNonneg_of_concave hconcave)
    hb hba hac hc hendpoint

/-- Unconditional analytic middle ordering.  Only the equal-mean endpoint
value remains to be supplied by the deterministic-cap boundary theorem. -/
theorem middleDeterministicGap_nonneg_of_endpoint_actual
    {a b c : ℝ}
    (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2)
    (hendpoint : 0 ≤ middleDeterministicGap a b a) :
    0 ≤ middleDeterministicGap a b c :=
  middleDeterministicGap_nonneg_of_endpoint_of_subadditive
    e8Theta_subadditiveOn_nonneg_actual hb hba hac hc hendpoint

/-- Correction-Hessian signs supply the equal-mean endpoint of the middle
deterministic cap fiber. -/
theorem middleDeterministicGap_endpoint_nonneg_of_correction
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha : a < 1 / 2) :
    0 ≤ middleDeterministicGap a b a := by
  have ha0 : 0 < a := hb.trans hba
  have hbHalf : b < 1 / 2 := hba.trans ha
  have hHa : 0 < H a := H_pos ha0 (by linarith)
  have hHb : 0 < H b := H_pos hb (by linarith)
  have hHba : H b ≤ H a :=
    H_strictMonoOn.monotoneOn ⟨hb.le, hbHalf.le⟩ ⟨ha0.le, ha.le⟩ hba.le
  unfold middleDeterministicGap
  rw [← pureGap_eq_canonicalPureGap (a := a) (c := a) le_rfl ha.le]
  exact pureGap_equal_mean_nonneg_of_convex
    (Correction.convexOn_entropyCorrection_square hleft hdet)
    ha0 (ha.trans (by norm_num)) ⟨hHa, le_rfl⟩ ⟨hHb, hHba⟩

/-- Manuscript Lemma 6.1, closed using the production correction signs. -/
theorem middleDeterministicGap_nonneg_of_correction
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    {a b c : ℝ} (hb : 0 < b) (hba : b < a) (hac : a < c) (hc : c < 1 / 2) :
    0 ≤ middleDeterministicGap a b c :=
  middleDeterministicGap_nonneg_of_endpoint_actual hb hba hac hc
    (middleDeterministicGap_endpoint_nonneg_of_correction
      hleft hdet hb hba (hac.trans hc))

#print axioms subadditiveOn_nonneg_of_concaveOn_zero
#print axioms deriv_middleDeterministicGap
#print axioms antitoneOn_e8Theta_div
#print axioms e8Theta_subadditiveOn_nonneg_actual
#print axioms deriv_middleDeterministicGap_nonneg_of_subadditive
#print axioms deriv_middleDeterministicGap_nonneg_actual
#print axioms middleDeterministicGap_nonneg_of_endpoint_actual
#print axioms middleDeterministicGap_endpoint_nonneg_of_correction
#print axioms middleDeterministicGap_nonneg_of_correction

end GeneralCK

end


