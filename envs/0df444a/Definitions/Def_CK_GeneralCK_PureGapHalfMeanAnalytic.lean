-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapHalfMeanAnalytic
-- name    : CK_GeneralCK_PureGapHalfMeanAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:57:05.092781+00:00
-- url     : https://prove2.me/theorems/8de11b5d-ace2-491f-bf97-9abfb8b8b4ea
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapHalfMeanAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapHalfMeanAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapHalfMeanAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapHalfMeanAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapHalfMeanAnalytic.lean)

import Definitions.Def_CK_GeneralCK_PureGapHalfMeanOwner
import Definitions.Def_CK_GeneralCK_ReflectionRegularDifference_v2

-- ===== source module GeneralCK.PureGapHalfMeanAnalytic =====
section

/-!
# Smooth even radial curvature and the half-mean formula

The totalized `F` is zero on negative radii, so its raw second derivative at
zero is not the physical even curvature. We use the proved signed regular
contact to identify `F |r| h` with a smooth function on the whole real line.
-/

namespace GeneralCK
open Set Filter
open scoped Topology

noncomputable def pureGapTheta0 : ℝ := 8 / Real.log 2
noncomputable def pureGapQ0 : ℝ := Real.log 2 / 8
noncomputable def pureGapSeamCutoff : ℝ := 1 / 10000

theorem pureGapTheta0_pos : 0 < pureGapTheta0 := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

theorem pureGapQ0_eq_inv : pureGapQ0 = pureGapTheta0⁻¹ := by
  simp [pureGapQ0, pureGapTheta0]

theorem pureGapSeamCutoff_bounds : 0 < pureGapSeamCutoff ∧ pureGapSeamCutoff < 1 / 2 := by
  norm_num [pureGapSeamCutoff]

namespace HalfMeanAnalytic
open Reflection Reflection.RegularDifference

noncomputable def contactLog (h r : ℝ) : ℝ :=
  SmallMean.A (regularContact (r / (Real.log 2 * h)))

noncomputable def contactLogFirst (h r : ℝ) : ℝ :=
  (1 / (1 - (regularContact (r / (Real.log 2 * h))) ^ 2)) *
    (regularContactFirst (r / (Real.log 2 * h)) / (Real.log 2 * h))

theorem hasDerivAt_contactLog (h r : ℝ) :
    HasDerivAt (contactLog h) (contactLogFirst h r) r := by
  have hc := regularContact_mem (r / (Real.log 2 * h))
  have hd := (hasDerivAt_regularContact (r / (Real.log 2 * h))).comp r
    ((hasDerivAt_id r).div_const (Real.log 2 * h))
  have ha := (SmallMean.hasDerivAt_A hc.1 hc.2).comp r hd
  convert! ha using 1
  simp [contactLogFirst, regularContactFirst, div_eq_mul_inv]

@[simp] theorem contactLog_zero (h : ℝ) : contactLog h 0 = 0 := by
  simp [contactLog]

theorem contactLogFirst_zero {h : ℝ} (hh : 0 < h) : contactLogFirst h 0 = 1 / h := by
  have hk : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp only [contactLogFirst, zero_div, regularContact_zero, regularContactFirst_zero]
  norm_num
  field_simp

theorem hasDerivAt_contactLogFirst_zero {h : ℝ} (_hh : 0 < h) :
    HasDerivAt (contactLogFirst h) 0 0 := by
  have hc := (hasDerivAt_regularContact (0 / (Real.log 2 * h))).comp (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).div_const (Real.log 2 * h))
  have hcf := (hasDerivAt_regularContactFirst (0 / (Real.log 2 * h))).comp (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).div_const (Real.log 2 * h))
  have hi := ((hc.pow 2).const_sub 1).inv (by simp)
  have hd := hi.mul (hcf.div_const (Real.log 2 * h))
  convert! hd using 1
  · funext r
    simp [contactLogFirst]
  · simp

noncomputable def evenRadial (h r : ℝ) : ℝ :=
  (2 * r * contactLog h r) / Real.log 2

theorem evenRadial_eq_abs {h : ℝ} (hh : 0 < h) (r : ℝ) :
    evenRadial h r = F |r| h := by
  have hk : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hnat : evenRadial h r = FNat r (Real.log 2 * h) / Real.log 2 := rfl
  rw [hnat]
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr, FNat_eq_F hr hh]
    field_simp
  · have hn : 0 ≤ -r := by linarith
    rw [abs_of_neg (lt_of_not_ge hr), ← FNat_neg r, FNat_eq_F hn hh]
    field_simp

theorem hasDerivAt_evenRadial (h r : ℝ) :
    HasDerivAt (evenRadial h)
      ((2 * contactLog h r + 2 * r * contactLogFirst h r) / Real.log 2) r := by
  convert! ((((hasDerivAt_id r).const_mul 2).mul
    (hasDerivAt_contactLog h r)).div_const (Real.log 2)) using 1
  simp

theorem hasDerivAt_deriv_evenRadial_zero {h : ℝ} (hh : 0 < h) :
    HasDerivAt (deriv (evenRadial h)) (4 / (Real.log 2 * h)) 0 := by
  have hu := hasDerivAt_contactLog h 0
  have hv := hasDerivAt_contactLogFirst_zero hh
  have hd := ((hu.const_mul 2).add
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul hv)).div_const (Real.log 2)
  have heq : deriv (evenRadial h) =ᶠ[nhds 0]
      (fun r => (2 * contactLog h r + 2 * r * contactLogFirst h r) / Real.log 2) :=
    Eventually.of_forall (fun r => (hasDerivAt_evenRadial h r).deriv)
  convert! hd.congr_of_eventuallyEq heq using 1
  rw [contactLogFirst_zero hh]
  ring

end HalfMeanAnalytic

theorem deriv2_F_radius_eq_e8Theta {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (deriv (fun r => F r h)) z = deriv e8Theta (z / (2 * h)) / (2 * h) := by
  rw [deriv2_F_radius_normalize hz hh,
    (hasDerivAt_e8Theta (div_pos hz (mul_pos two_pos hh))).deriv]
  rw [show 2 * (z / (2 * h)) = z / h by field_simp]
  ring

namespace HalfMeanAnalytic

theorem deriv_halfMeanPureGapCurve {a e f c : ℝ}
    (hac : a < c) (hcenter : c < 1 - a) (he : 0 < e) (hf : 0 < f) :
    deriv (halfMeanPureGapCurve a e f) c =
      deriv (fun r => F r ((e + f) / 2)) (c - a) -
      deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
      deriv (evenRadial f) (1 - 2 * c) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hdiff := (hasDerivAt_F_radius (sub_pos.mpr hac) hef).differentiableAt.hasDerivAt.comp c
    ((hasDerivAt_id c).sub_const a)
  have hcent := (hasDerivAt_F_radius (sub_pos.mpr hcenter) hef).differentiableAt.hasDerivAt.comp c
    ((hasDerivAt_id c).const_sub (1 - a))
  have hr := (hasDerivAt_evenRadial f (1 - 2 * c)).differentiableAt.hasDerivAt.comp c
    (((hasDerivAt_id c).const_mul 2).const_sub 1)
  have htotal := (((hdiff.add (hasDerivAt_const c (entropyCorrection e f))).sub
    (hcent.const_sub (eta ((e + f) / 2)))).add
    (((hasDerivAt_const c (radialPhi (1 - 2 * a) e)).add (hr.const_sub (eta f))).div_const 2))
  have heq : halfMeanPureGapCurve a e f =ᶠ[nhds c]
      (fun x => F (x - a) ((e + f) / 2) + entropyCorrection e f -
        (eta ((e + f) / 2) - F (1 - a - x) ((e + f) / 2)) +
        (radialPhi (1 - 2 * a) e + (eta f - evenRadial f (1 - 2 * x))) / 2) := by
    filter_upwards with x
    simp [halfMeanPureGapCurve, radialPhi, evenRadial_eq_abs hf]
  have hd := (htotal.congr_of_eventuallyEq heq).deriv
  convert hd using 1
  ring

theorem deriv2_halfMeanPureGapCurve {a e f : ℝ}
    (ha : a < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) =
      2 * deriv e8Theta ((1 / 2 - a) / (e + f)) / (e + f) -
        8 / (Real.log 2 * f) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hv : 0 < 1 / 2 - a := sub_pos.mpr ha
  have hcent : 0 < 1 - a - 1 / 2 := by linarith
  have hdiff := (hasDerivAt_deriv_F_radius hv hef).differentiableAt.hasDerivAt.comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℝ)).sub_const a)
  have hcenter := (hasDerivAt_deriv_F_radius hcent hef).differentiableAt.hasDerivAt.comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℝ)).const_sub (1 - a))
  have heven0 : HasDerivAt (deriv (evenRadial f)) (4 / (Real.log 2 * f))
      (1 - 2 * (1 / 2 : ℝ)) := by
    convert! hasDerivAt_deriv_evenRadial_zero hf using 1
    norm_num
  have heven := heven0.comp (1 / 2)
    (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).const_sub 1)
  have htotal := (hdiff.sub hcenter).add heven
  have heq : deriv (halfMeanPureGapCurve a e f) =ᶠ[nhds (1 / 2 : ℝ)]
      (fun c => deriv (fun r => F r ((e + f) / 2)) (c - a) -
        deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
        deriv (evenRadial f) (1 - 2 * c)) := by
    filter_upwards [Ioo_mem_nhds ha (show (1 / 2 : ℝ) < 1 - a by linarith)] with c hc
    exact deriv_halfMeanPureGapCurve hc.1 hc.2 he hf
  have hd := (htotal.congr_of_eventuallyEq heq).deriv
  rw [show 1 - a - 1 / 2 = 1 / 2 - a by ring,
    deriv2_F_radius_eq_e8Theta hv hef,
    show 2 * ((e + f) / 2) = e + f by ring] at hd
  convert hd using 1
  ring

end HalfMeanAnalytic

/-- The manuscript's exact transverse identity, now proved with its concrete
zero-radius curvature. The identity itself does not need stationarity. -/
theorem halfMeanSecondDerivativeFormula_actual : HalfMeanSecondDerivativeFormula pureGapTheta0 := by
  intro a e f ha he hf _
  rw [HalfMeanAnalytic.deriv2_halfMeanPureGapCurve ha he hf]
  have hk : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hv : 1 / 2 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  have hratio : ((1 / 2 - a) / (e + f)) / ((1 / 2 - a) / e) = e / (e + f) := by
    generalize hvdef : (1 / 2 - a) = v at *
    field_simp [hv]
  rw [hratio]
  unfold pureGapTheta0
  field_simp [he.ne', hf.ne', (add_pos he hf).ne', hk]
  ring

#print axioms HalfMeanAnalytic.hasDerivAt_deriv_evenRadial_zero
#print axioms halfMeanSecondDerivativeFormula_actual

end GeneralCK

end


