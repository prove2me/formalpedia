-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapMeanStationarity
-- name    : CK_GeneralCK_PureGapMeanStationarity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:41:07.80901+00:00
-- url     : https://prove2.me/theorems/28352e40-dbe2-4176-b6d0-8f0ac506e11a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapMeanStationarity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapMeanStationarity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapMeanStationarity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapMeanStationarity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapMeanStationarity.lean)

import Definitions.Def_CK_GeneralCK_PureGapFixedEntropyClosure

-- ===== source module GeneralCK.PureGapMeanStationarity =====
section

/-!
# Stationarity equations for a fixed-entropy pure-gap minimum

These are the calculus equations consumed by the manuscript's E8 argument.
-/

namespace GeneralCK

/-- The first-mean derivative of the canonical pure gap in the smooth lower-
half chamber. -/
theorem deriv_canonicalPureGap_left {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1) (ha : a < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    deriv (fun x => canonicalPureGap x c e f) a =
      -deriv (fun r => F r ((e + f) / 2)) (c - a) -
        deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
        deriv (fun r => F r e) (1 - 2 * a) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hFd := (hasDerivAt_F_radius (sub_pos.mpr hac) hef).differentiableAt.hasDerivAt
  have hFc := (hasDerivAt_F_radius (show 0 < 1 - a - c by linarith) hef).differentiableAt.hasDerivAt
  have hFl := (hasDerivAt_F_radius (show 0 < 1 - 2 * a by linarith) he).differentiableAt.hasDerivAt
  have hdiff := hFd.comp a ((hasDerivAt_id a).const_sub c)
  have hcenter := hFc.comp a (((hasDerivAt_id a).const_sub 1).sub_const c)
  have hleft := hFl.comp a (((hasDerivAt_id a).const_mul 2).const_sub 1)
  have hright := hasDerivAt_const a (radialPhi (1 - 2 * c) f)
  have htotal :=
    ((hdiff.add (hasDerivAt_const a (entropyCorrection e f))).sub
      ((hasDerivAt_const a (eta ((e + f) / 2))).sub hcenter)).add
      (((((hasDerivAt_const a (eta e)).sub hleft).add hright).div_const 2))
  have hderiv := htotal.deriv
  convert hderiv using 1
  case e'_2 =>
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards with x
    simp [canonicalPureGap, radialPhi, Function.comp_apply]
  case e'_3 => ring
/-- The second-mean derivative of the canonical pure gap in the smooth
lower-half chamber. -/
theorem deriv_canonicalPureGap_right {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    deriv (fun y => canonicalPureGap a y e f) c =
      deriv (fun r => F r ((e + f) / 2)) (c - a) -
        deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
        deriv (fun r => F r f) (1 - 2 * c) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hFd := (hasDerivAt_F_radius (sub_pos.mpr hac) hef).differentiableAt.hasDerivAt
  have hFc := (hasDerivAt_F_radius (show 0 < 1 - a - c by linarith) hef).differentiableAt.hasDerivAt
  have hFr := (hasDerivAt_F_radius (show 0 < 1 - 2 * c by linarith) hf).differentiableAt.hasDerivAt
  have hdiff := hFd.comp c ((hasDerivAt_id c).sub_const a)
  have hcenter := hFc.comp c ((hasDerivAt_id c).const_sub (1 - a))
  have hleft := hasDerivAt_const c (radialPhi (1 - 2 * a) e)
  have hright := hFr.comp c (((hasDerivAt_id c).const_mul 2).const_sub 1)
  have htotal :=
    ((hdiff.add (hasDerivAt_const c (entropyCorrection e f))).sub
      ((hasDerivAt_const c (eta ((e + f) / 2))).sub hcenter)).add
      (((hleft.add ((hasDerivAt_const c (eta f)).sub hright)).div_const 2))
  have hderiv := htotal.deriv
  convert hderiv using 1
  case e'_2 =>
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards with y
    simp [canonicalPureGap, radialPhi, Function.comp_apply]
  case e'_3 => ring

/-- At a smooth two-variable local minimum, the first mean satisfies the
first stationarity equation used in the E8 reduction. -/
theorem canonicalPureGap_left_stationarity {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1) (ha : a < 1 / 2)
    (he : 0 < e) (hf : 0 < f)
    (hmin : IsLocalMin (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c)) :
    -deriv (fun r => F r ((e + f) / 2)) (c - a) -
        deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
        deriv (fun r => F r e) (1 - 2 * a) = 0 := by
  have hs := hmin.comp_continuous (g := fun x : ℝ => (x, c)) (b := a)
    (show ContinuousAt (fun x : ℝ => (x, c)) a by fun_prop)
  rw [← deriv_canonicalPureGap_left hac hsum ha he hf]
  have hz := hs.deriv_eq_zero
  convert hz using 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards with x
  rfl

/-- At a smooth two-variable local minimum, the second mean satisfies the
second stationarity equation used in the E8 reduction. -/
theorem canonicalPureGap_right_stationarity {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f)
    (hmin : IsLocalMin (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c)) :
    deriv (fun r => F r ((e + f) / 2)) (c - a) -
        deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
        deriv (fun r => F r f) (1 - 2 * c) = 0 := by
  have hs := hmin.comp_continuous (g := fun y : ℝ => (a, y)) (b := c)
    (show ContinuousAt (fun y : ℝ => (a, y)) c by fun_prop)
  rw [← deriv_canonicalPureGap_right hac hsum hc he hf]
  have hz := hs.deriv_eq_zero
  convert hz using 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards with y
  rfl

end GeneralCK

end


