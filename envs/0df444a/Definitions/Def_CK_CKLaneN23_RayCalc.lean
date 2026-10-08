-- Prove2me | Definitions.Def_CK_CKLaneN23_RayCalc
-- name    : CK_CKLaneN23_RayCalc
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:41:24.915753+00:00
-- url     : https://prove2.me/theorems/9a1876c5-8fdf-4659-8439-e80e9e62f297
-- title:
--   Courtade–Kumar proof module `CKLaneN23.RayCalc` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.RayCalc` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.RayCalc` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.RayCalc (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/RayCalc.lean)

import Definitions.Def_CK_CKLaneN23_RSDefs
import Definitions.Def_CK_GeneralCK_PerspectiveCurve
import Definitions.Def_CK_GeneralCK_ProfileConvexity
import Definitions.Def_CK_GeneralCK_EntropyComparison
import Definitions.Def_CK_GeneralCK_ProfileDerivatives
import Definitions.Def_CK_GeneralCK_PureGapZeroCapRightHalfBoundaryRadialChart

-- ===== source module CKLaneN23.RayCalc =====
section

/-!
# Lane N23 — RA-stat ray calculus: `φ_{b,t}'' = rayGamma` on `0 < d < b`

For `0 < b ≤ 1/2`, `0 < t < 1`, the degenerate-edge ray
`φ(d) = canonicalPureGap (b - t d) b (H (b - d)) (H b)` agrees on `(0,b)` with the radial expression
`rayRadial b t d`; its derivative is `rayPhi1 b t d` and the derivative of `rayPhi1 b t` is exactly
`rayGamma b t d` (the shared definition in `CKLaneN23.RSDefs`).
-/

namespace CKLaneN23.RS

open GeneralCK

/-- Mean entropy along the ray. -/
noncomputable def rayE (b d : ℝ) : ℝ := (H (b - d) + H b) / 2

/-- Interior cost plus half the left cap value, along the ray. -/
noncomputable def rayA (b d : ℝ) : ℝ := ((1 - 2 * b + 3 * d) * J (b - d) - d * J b) / 2

/-- Radial form of the ray. -/
noncomputable def rayRadial (b t d : ℝ) : ℝ :=
  rayA b d + F (t * d) (rayE b d) - F d (rayE b d) + F (1 - 2 * b + t * d) (rayE b d)
    - eta (rayE b d) - F (1 - 2 * b + 2 * t * d) (H (b - d)) / 2

/-- First derivative of the ray. -/
noncomputable def rayPhi1 (b t d : ℝ) : ℝ :=
  (3 * J (b - d) - (1 - 2 * b + 3 * d) * Jd1 (b - d) - J b) / 2
  + perspectiveSlope (t * d) (rayE b d) t (-(J (b - d)) / 2)
  - perspectiveSlope d (rayE b d) 1 (-(J (b - d)) / 2)
  + perspectiveSlope (1 - 2 * b + t * d) (rayE b d) t (-(J (b - d)) / 2)
  - Scalar.etaSlope (rayE b d) * (-(J (b - d)) / 2)
  - perspectiveSlope (1 - 2 * b + 2 * t * d) (H (b - d)) (2 * t) (-(J (b - d))) / 2

section basic

variable {b t d : ℝ}

theorem ray_u_pos (hd : d < b) : 0 < b - d := by linarith

theorem ray_u_lt_half (hb : b ≤ 1 / 2) (hd0 : 0 < d) : b - d < 1 / 2 := by linarith

theorem ray_Hu_pos (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) : 0 < H (b - d) :=
  H_pos (ray_u_pos hd) (by linarith)

theorem ray_Hu_lt_one (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) : H (b - d) < 1 := by
  rw [← H_half]
  exact H_strictMonoOn ⟨(ray_u_pos hd).le, (ray_u_lt_half hb hd0).le⟩ ⟨by norm_num, le_rfl⟩
    (ray_u_lt_half hb hd0)

theorem ray_Hb_pos (hb0 : 0 < b) (hb : b ≤ 1 / 2) : 0 < H b := H_pos hb0 (by linarith)

theorem rayE_pos (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) : 0 < rayE b d := by
  unfold rayE
  have h1 := ray_Hu_pos hd0 hd hb
  have h2 := ray_Hb_pos (by linarith : 0 < b) hb
  linarith

theorem rayE_lt_one (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) : rayE b d < 1 := by
  unfold rayE
  have h1 := ray_Hu_lt_one hd0 hd hb
  have h2 := H_le_one b
  linarith

end basic

/-- `Jd2` is the derivative of `Jd1`. -/
theorem hasDerivAt_Jd1 {v : ℝ} (hv : 0 < v) (hv' : v < 1) : HasDerivAt Jd1 (Jd2 v) v := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have hden : HasDerivAt (fun w : ℝ => Real.log 2 * w * (1 - w))
      (Real.log 2 * (1 - v) + Real.log 2 * v * (-1)) v := by
    have h1 : HasDerivAt (fun w : ℝ => Real.log 2 * w) (Real.log 2) v := by
      simpa using (hasDerivAt_id v).const_mul (Real.log 2)
    have h2 : HasDerivAt (fun w : ℝ => 1 - w) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub 1
    have h3 := h1.mul h2
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp
  have hne : Real.log 2 * v * (1 - v) ≠ 0 := by positivity
  have hq := (hasDerivAt_const v (-1 : ℝ)).div hden hne
  refine (hq.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  · unfold Jd2
    field_simp
    ring
  · simp [Jd1]

theorem hasDerivAt_J_Jd1 {v : ℝ} (hv : 0 < v) (hv' : v < 1) : HasDerivAt J (Jd1 v) v := by
  have h := hasDerivAt_J hv hv'
  exact h.congr_deriv (by simp [Jd1])

section derivs

variable {b t d : ℝ}

theorem hasDerivAt_ray_u (b d : ℝ) : HasDerivAt (fun y : ℝ => b - y) (-1) d := by
  simpa using (hasDerivAt_id d).const_sub b

theorem hasDerivAt_ray_Hu (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => H (b - y)) (-(J (b - d))) d := by
  have h := (Comparison.hasDerivAt_H (ray_u_pos hd) (by linarith)).comp d (hasDerivAt_ray_u b d)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Function.comp_def]

theorem hasDerivAt_ray_Ju (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => J (b - y)) (-(Jd1 (b - d))) d := by
  have h := (hasDerivAt_J_Jd1 (ray_u_pos hd) (by linarith)).comp d (hasDerivAt_ray_u b d)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Function.comp_def]

theorem hasDerivAt_ray_negJu (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => -(J (b - y))) (Jd1 (b - d)) d := by
  have h := (hasDerivAt_ray_Ju hd0 hd hb).neg
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp

theorem hasDerivAt_ray_Jd1u (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => Jd1 (b - y)) (-(Jd2 (b - d))) d := by
  have h := (hasDerivAt_Jd1 (ray_u_pos hd) (by linarith)).comp d (hasDerivAt_ray_u b d)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Function.comp_def]

theorem hasDerivAt_rayE (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => rayE b y) (-(J (b - d)) / 2) d := by
  have h := ((hasDerivAt_ray_Hu hd0 hd hb).add_const (H b)).div_const 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [rayE]

theorem hasDerivAt_rayE1 (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => -(J (b - y)) / 2) (Jd1 (b - d) / 2) d :=
  (hasDerivAt_ray_negJu hd0 hd hb).div_const 2

theorem hasDerivAt_rayA (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => rayA b y)
      ((3 * J (b - d) - (1 - 2 * b + 3 * d) * Jd1 (b - d) - J b) / 2) d := by
  have hJ := hasDerivAt_ray_Ju hd0 hd hb
  have hlin : HasDerivAt (fun y : ℝ => 1 - 2 * b + 3 * y) 3 d := by
    simpa using ((hasDerivAt_id d).const_mul 3).const_add (1 - 2 * b)
  have hid : HasDerivAt (fun y : ℝ => y * J b) (J b) d := by
    simpa using (hasDerivAt_id d).mul_const (J b)
  have h := ((hlin.mul hJ).sub hid).div_const 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [rayA]

theorem hasDerivAt_rayA1 (hd0 : 0 < d) (hd : d < b) (hb : b ≤ 1 / 2) :
    HasDerivAt (fun y : ℝ => (3 * J (b - y) - (1 - 2 * b + 3 * y) * Jd1 (b - y) - J b) / 2)
      (-3 * Jd1 (b - d) + (1 - 2 * b + 3 * d) / 2 * Jd2 (b - d)) d := by
  have hJ := hasDerivAt_ray_Ju hd0 hd hb
  have hJ1 := hasDerivAt_ray_Jd1u hd0 hd hb
  have hlin : HasDerivAt (fun y : ℝ => 1 - 2 * b + 3 * y) 3 d := by
    simpa using ((hasDerivAt_id d).const_mul 3).const_add (1 - 2 * b)
  have h := (((hJ.const_mul 3).sub (hlin.mul hJ1)).sub_const (J b)).div_const 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp

/-- The ray agrees with its radial form on `0 < d < b`. -/
theorem ray_eq_radial (hb : b ≤ 1 / 2) (ht0 : 0 < t) (ht1 : t < 1) (hd0 : 0 < d) (hd : d < b) :
    canonicalPureGap (b - t * d) b (H (b - d)) (H b) = rayRadial b t d := by
  have hu := ray_u_pos hd
  have hua : b - d < b - t * d := by nlinarith
  have hab : b - t * d < b := by nlinarith
  rw [canonicalPureGap_rightCap_full_radial_eq_le_half hu hua hab hb,
    Comparison.eta_H hu (ray_u_lt_half hb hd0)]
  unfold rayRadial rayA rayE interiorCost
  have e1 : b - (b - t * d) = t * d := by ring
  have e2 : b - (b - d) = d := by ring
  have e3 : 1 - (b - t * d) - b = 1 - 2 * b + t * d := by ring
  have e4 : 1 - 2 * (b - t * d) = 1 - 2 * b + 2 * t * d := by ring
  rw [e1, e2, e3, e4]
  ring

/-- First derivative of the radial form. -/
theorem hasDerivAt_rayRadial (hb : b ≤ 1 / 2) (ht0 : 0 < t) (ht1 : t < 1) (hd0 : 0 < d) (hd : d < b) :
    HasDerivAt (fun y => rayRadial b t y) (rayPhi1 b t d) d := by
  have hE := hasDerivAt_rayE hd0 hd hb
  have hEpos := rayE_pos hd0 hd hb
  have hElt := rayE_lt_one hd0 hd hb
  have hHu := hasDerivAt_ray_Hu hd0 hd hb
  have hHupos := ray_Hu_pos hd0 hd hb
  have hr : 0 ≤ 1 - 2 * b := by linarith
  have hs1 : HasDerivAt (fun y : ℝ => t * y) t d := by simpa using (hasDerivAt_id d).const_mul t
  have hs2 : HasDerivAt (fun y : ℝ => y) 1 d := hasDerivAt_id d
  have hs3 : HasDerivAt (fun y : ℝ => 1 - 2 * b + t * y) t d := by
    simpa using ((hasDerivAt_id d).const_mul t).const_add (1 - 2 * b)
  have hs4 : HasDerivAt (fun y : ℝ => 1 - 2 * b + 2 * t * y) (2 * t) d := by
    simpa using ((hasDerivAt_id d).const_mul (2 * t)).const_add (1 - 2 * b)
  have hF1 := hasDerivAt_F_curve (s := fun y => t * y) (e := fun y => rayE b y) hs1 hE
    (by positivity) hEpos
  have hF2 := hasDerivAt_F_curve (s := fun y => y) (e := fun y => rayE b y) hs2 hE hd0 hEpos
  have hF3 := hasDerivAt_F_curve (s := fun y => 1 - 2 * b + t * y) (e := fun y => rayE b y) hs3 hE
    (by positivity) hEpos
  have hF4 := hasDerivAt_F_curve (s := fun y => 1 - 2 * b + 2 * t * y) (e := fun y => H (b - y)) hs4 hHu
    (by positivity) hHupos
  have heta := (hasDerivAt_eta hEpos hElt).comp d hE
  have hA := hasDerivAt_rayA hd0 hd hb
  have h := ((((hA.add hF1).sub hF2).add hF3).sub heta).sub (hF4.div_const 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold rayPhi1 Scalar.etaSlope
    ring
  · simp [rayRadial, Function.comp_def]

/-- Second derivative of the ray: exactly `rayGamma`. -/
theorem hasDerivAt_rayPhi1 (hb : b ≤ 1 / 2) (ht0 : 0 < t) (ht1 : t < 1) (hd0 : 0 < d) (hd : d < b) :
    HasDerivAt (fun y => rayPhi1 b t y) (rayGamma b t d) d := by
  have hE := hasDerivAt_rayE hd0 hd hb
  have hE1 := hasDerivAt_rayE1 hd0 hd hb
  have hEpos := rayE_pos hd0 hd hb
  have hElt := rayE_lt_one hd0 hd hb
  have hHu := hasDerivAt_ray_Hu hd0 hd hb
  have hnJ := hasDerivAt_ray_negJu hd0 hd hb
  have hHupos := ray_Hu_pos hd0 hd hb
  have hr : 0 ≤ 1 - 2 * b := by linarith
  have hs1 : HasDerivAt (fun y : ℝ => t * y) ((fun _ : ℝ => t) d) d := by
    simpa using (hasDerivAt_id d).const_mul t
  have hs2 : HasDerivAt (fun y : ℝ => y) ((fun _ : ℝ => (1 : ℝ)) d) d := hasDerivAt_id d
  have hs3 : HasDerivAt (fun y : ℝ => 1 - 2 * b + t * y) ((fun _ : ℝ => t) d) d := by
    simpa using ((hasDerivAt_id d).const_mul t).const_add (1 - 2 * b)
  have hs4 : HasDerivAt (fun y : ℝ => 1 - 2 * b + 2 * t * y) ((fun _ : ℝ => 2 * t) d) d := by
    simpa using ((hasDerivAt_id d).const_mul (2 * t)).const_add (1 - 2 * b)
  have hc1 : HasDerivAt (fun _ : ℝ => t) 0 d := hasDerivAt_const d t
  have hc2 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 d := hasDerivAt_const d 1
  have hc4 : HasDerivAt (fun _ : ℝ => 2 * t) 0 d := hasDerivAt_const d (2 * t)
  have hEd : HasDerivAt (fun y : ℝ => rayE b y) ((fun y : ℝ => -(J (b - y)) / 2) d) d := hE
  have hHud : HasDerivAt (fun y : ℝ => H (b - y)) ((fun y : ℝ => -(J (b - y))) d) d := hHu
  have hP1 := hasDerivAt_perspectiveSlope (s := fun y => t * y) (e := fun y => rayE b y)
    (ds := fun _ => t) (de := fun y => -(J (b - y)) / 2) hs1 hEd hc1 hE1 (by positivity) hEpos
  have hP2 := hasDerivAt_perspectiveSlope (s := fun y => y) (e := fun y => rayE b y)
    (ds := fun _ => 1) (de := fun y => -(J (b - y)) / 2) hs2 hEd hc2 hE1 hd0 hEpos
  have hP3 := hasDerivAt_perspectiveSlope (s := fun y => 1 - 2 * b + t * y) (e := fun y => rayE b y)
    (ds := fun _ => t) (de := fun y => -(J (b - y)) / 2) hs3 hEd hc1 hE1 (by positivity) hEpos
  have hP4 := hasDerivAt_perspectiveSlope (s := fun y => 1 - 2 * b + 2 * t * y) (e := fun y => H (b - y))
    (ds := fun _ => 2 * t) (de := fun y => -(J (b - y))) hs4 hHud hc4 hnJ (by positivity) hHupos
  have hslope := (Scalar.hasDerivAt_etaSlope hEpos hElt).comp d hE
  have hetaT := hslope.mul hE1
  have hA1 := hasDerivAt_rayA1 hd0 hd hb
  have h := ((((hA1.add hP1).sub hP2).add hP3).sub hetaT).sub (hP4.div_const 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold rayGamma raySec rayE
    simp only [Function.comp_def]
    ring
  · simp [rayPhi1, Function.comp_def]

end derivs

end CKLaneN23.RS

end


