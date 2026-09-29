-- Prove2me | Definitions.Def_CK_GeneralCK_PerspectiveCurve
-- name    : CK_GeneralCK_PerspectiveCurve
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:38:34.823812+00:00
-- url     : https://prove2.me/theorems/68f65683-e50f-4a91-950e-8b0044e5f967
-- title:
--   Courtade–Kumar proof module `GeneralCK.PerspectiveCurve` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PerspectiveCurve` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PerspectiveCurve` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PerspectiveCurve (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PerspectiveCurve.lean)

import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_CK_GeneralCK_RadialZeroBoundary

namespace GeneralCK
open Filter Set
open scoped Topology

/-- First derivative of the homogeneous perspective along a scalar curve. -/
noncomputable def perspectiveSlope (s e ds de : ℝ) : ℝ :=
  (ds-(s/e)*de)*deriv (fun r => F r 1) (s/e)+de*F (s/e) 1

/-- The zero-radius first derivative is valid for the actual totalized function. -/
theorem hasDerivAt_F_curve_zero {s e : ℝ → ℝ} {x ds de : ℝ}
    (hs : HasDerivAt s ds x) (he : HasDerivAt e de x)
    (hs0 : s x = 0) (he0 : 0 < e x) :
    HasDerivAt (fun y => F (s y) (e y)) 0 x := by
  have hr := hs.div he he0.ne'
  have hf := (hasDerivAt_F_zero (by norm_num : (0:ℝ)<1))
  rw [← show s x/e x=0 by rw [hs0,zero_div]] at hf
  have hd := he.mul (hf.comp x hr)
  have heq : (fun y => F (s y) (e y)) =ᶠ[𝓝 x] (fun y => e y*F (s y/e y) 1) := by
    filter_upwards [he.continuousAt.eventually (Ioi_mem_nhds he0)] with y hy
    exact F_perspective (ne_of_gt hy) (s y)
  simpa [hs0,F] using hd.congr_of_eventuallyEq heq

theorem hasDerivAt_F_curve {s e : ℝ → ℝ} {x ds de : ℝ}
    (hs : HasDerivAt s ds x) (he : HasDerivAt e de x)
    (hs0 : 0 < s x) (he0 : 0 < e x) :
    HasDerivAt (fun y => F (s y) (e y)) (perspectiveSlope (s x) (e x) ds de) x := by
  have hr := hs.div he he0.ne'
  have hf := ((hasDerivAt_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hd := he.mul hf
  have heq : (fun y => F (s y) (e y)) =ᶠ[𝓝 x] (fun y => e y*F (s y/e y) 1) := by
    filter_upwards [he.continuousAt.eventually (Ioi_mem_nhds he0)] with y hy
    exact F_perspective (ne_of_gt hy) (s y)
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp [perspectiveSlope]
  field_simp
  ring

/-- Differentiating the explicit first derivative requires only scalar curve calculus. -/
theorem hasDerivAt_perspectiveSlope {s e ds de : ℝ → ℝ} {x dds dde : ℝ}
    (hs : HasDerivAt s (ds x) x) (he : HasDerivAt e (de x) x)
    (hds : HasDerivAt ds dds x) (hde : HasDerivAt de dde x)
    (hs0 : 0 < s x) (he0 : 0 < e x) :
    HasDerivAt (fun y => perspectiveSlope (s y) (e y) (ds y) (de y))
      (((ds x-(s x/e x)*de x)^2/e x)*deriv (deriv (fun r => F r 1)) (s x/e x)
        +(dds-(s x/e x)*dde)*deriv (fun r => F r 1) (s x/e x)
        +dde*F (s x/e x) 1) x := by
  have hr := hs.div he he0.ne'
  have hf := ((hasDerivAt_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hg := ((hasDerivAt_deriv_F_radius (div_pos hs0 he0) (by norm_num : (0:ℝ) < 1)).differentiableAt.hasDerivAt).comp x hr
  have hq := hds.sub (hr.mul hde)
  have hd := (hq.mul hg).add (hde.mul hf)
  convert! hd using 1
  simp only [Function.comp_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

end GeneralCK


