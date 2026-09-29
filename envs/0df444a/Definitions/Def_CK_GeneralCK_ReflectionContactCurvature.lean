-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionContactCurvature
-- name    : CK_GeneralCK_ReflectionContactCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:39:25.869683+00:00
-- url     : https://prove2.me/theorems/2698dc2d-4acb-4ab6-804e-29cd78883293
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionContactCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionContactCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionContactCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionContactCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionContactCurvature.lean)

import Definitions.Def_CK_GeneralCK_PerspectiveCurve
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK
open Certificates.Mixed








set_option maxHeartbeats 1200000 in
theorem reflection_curvature_eq_contact {s e : ℝ} (hs : 0 < s) (he : 0 < e)
    (A b0 : ℝ) :
    Real.log 2 *
      ((((1/2 : ℝ)-(s/e)*(-A/(2*Real.log 2)))^2/e)*
          deriv (deriv (fun r => F r 1)) (s/e)
        +(0-(s/e)*(-b0/(2*Real.log 2)))*deriv (fun r => F r 1) (s/e)
        +(-b0/(2*Real.log 2))*F (s/e) 1) =
      reflectionS (radialContact s e) e A b0 := by
  let v := radialContact s e
  have hv : 0 < v := radialContact_pos hs he
  have hv' : v < 1/2 := radialContact_lt_half hs he
  have hr : 0 < 1-2*v := by linarith
  have hv1 : 0 < 1-v := by linarith
  have hK := (kap_pos hv hv').ne'
  have hn0 : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hnz := hn0.ne'
  have heq : (s/e)*hn v = Real.log 2*(1-2*v) := by
    rw [hn_eq_H_mul_log]
    have hc := radialContact_equation hs he
    change s*H v=e*(1-2*v) at hc
    field_simp [he.ne']
    linear_combination hc
  have hratio : s/e = Real.log 2*(1-2*v)/hn v := (eq_div_iff hnz).mpr heq
  have hc : radialContact (s/e) 1 = v := (radialContact_normalize_entropy s he.ne').symm
  have hd := radius_mul_deriv2_F_eq_profile (div_pos hs he) (by norm_num : (0:ℝ)<1)
  rw [hc] at hd
  have hd' : deriv (deriv (fun r => F r 1)) (s/e) = profile v/(s/e) := by
    apply (eq_div_iff (div_pos hs he).ne').mpr
    simpa only [mul_comm] using hd
  rw [hd',deriv_F_radius_slope (div_pos hs he) (by norm_num),hc]
  have hF : F (s/e) 1 = (s/e)*J v := by rw [F,if_neg (div_pos hs he).ne',hc]
  rw [hF,hratio]
  change _ = reflectionS v e A b0
  unfold reflectionS radialSlope profile
  field_simp [log_two_pos.ne',he.ne',hnz,hK,hv.ne',hv1.ne',hr.ne']
  ring

end GeneralCK


