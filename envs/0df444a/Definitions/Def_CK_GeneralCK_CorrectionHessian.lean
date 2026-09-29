-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHessian
-- name    : CK_GeneralCK_CorrectionHessian
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:38:52.979973+00:00
-- url     : https://prove2.me/theorems/d6e04aae-af92-455c-a0e1-e73a8b7aeac9
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHessian` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHessian` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHessian` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHessian (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessian.lean)

import Definitions.Def_CK_GeneralCK_FourMomentDefs
import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_GeneralCK_correction_entries

namespace GeneralCK
open Set Filter
open scoped Topology

theorem hasDerivAt_deriv_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt (deriv entropyInverse)
      (1/(Real.log 2*entropyInverse h*(1-entropyInverse h)*(J (entropyInverse h))^3)) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hJ := J_pos hv hv'
  have hd := (((hasDerivAt_J hv (by linarith)).comp h
    (hasDerivAt_entropyInverse h0 h1)).inv hJ.ne')
  have heq : deriv entropyInverse =ᶠ[𝓝 h] (fun t => (J (entropyInverse t))⁻¹) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with t ht
    simpa only [one_div] using deriv_entropyInverse ht.1 ht.2
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [Function.comp_apply]
  field_simp [hJ.ne', hv.ne', log_two_pos.ne', show 1-entropyInverse h ≠ 0 by linarith]

namespace Correction




noncomputable def ordered (e f : ℝ) : ℝ :=
  (gap e f)*(J (entropyInverse e)-J (entropyInverse f))/2 -
    mid e f*F (normalized e f) 1

theorem gap_pos {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) : 0 < gap e f := by
  exact sub_pos.mpr (entropyInverse_strictMonoOn
    ⟨he.le, (hef.trans hf).le⟩ ⟨(he.trans hef).le, hf.le⟩ hef)

theorem mid_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < mid e f := by
  unfold mid
  linarith

theorem ordered_eq {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    entropyCorrection e f = ordered e f := by
  have hp := gap_pos he hef hf
  have hm := mid_pos he hef
  have hei := (entropyInverse_spec he.le (hef.trans hf).le).2.2
  have hfi := (entropyInverse_spec (he.trans hef).le hf.le).2.2
  unfold entropyCorrection atomCorrection interiorCost ordered
  rw [hei, hfi, abs_of_neg (by dsimp [gap] at hp; linarith),
    F_perspective (h := (e+f)/2) hm.ne']
  congr 2
  dsimp [gap, normalized, mid]
  ring_nf

noncomputable def leftSlope (e f : ℝ) : ℝ :=
  ((J (entropyInverse f)-J (entropyInverse e))/J (entropyInverse e) -
      gap e f/(Real.log 2*entropyInverse e*(1-entropyInverse e)*J (entropyInverse e)))/2 +
    (1/J (entropyInverse e)+normalized e f/2)*deriv (fun r => F r 1) (normalized e f) -
      F (normalized e f) 1/2

theorem hasDerivAt_ordered_left {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (fun t => ordered t f) (leftSlope e f) e := by
  have he1 := hef.trans hf
  have hu := entropyInverse_pos he he1.le
  have hu' := entropyInverse_lt_half he.le he1
  have hJu := J_pos hu hu'
  have hm := mid_pos he hef
  have ht : 0 < normalized e f := div_pos (gap_pos he hef hf) hm
  have hi := hasDerivAt_entropyInverse he he1
  have hs := hi.const_sub (entropyInverse f)
  have hj := (hasDerivAt_J hu (by linarith)).comp e hi
  have hdmid := ((hasDerivAt_id e).add_const f).div_const 2
  have ht' := hs.div hdmid hm.ne'
  have hF := (hasDerivAt_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hcost := (hs.mul (hj.sub_const (J (entropyInverse f)))).div_const 2
  have hd := hcost.sub (hdmid.mul (hF.comp e ht'))
  convert! hd using 1
  dsimp [leftSlope, gap, normalized, mid]
  field_simp [hJu.ne', hu.ne', log_two_pos.ne',
    show 1-entropyInverse e ≠ 0 by linarith, show e+f ≠ 0 by linarith]
  ring

theorem hasDerivAt_entropyCorrection_left {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (fun t => entropyCorrection t f) (leftSlope e f) e := by
  apply (hasDerivAt_ordered_left he hef hf).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he hef] with t ht
  exact ordered_eq ht.1 ht.2 hf

noncomputable def invSlope (e : ℝ) : ℝ := 1/J (entropyInverse e)
noncomputable def invSecond (e : ℝ) : ℝ :=
  1/(Real.log 2*entropyInverse e*(1-entropyInverse e)*(J (entropyInverse e))^3)
noncomputable def jSlope (e : ℝ) : ℝ :=
  -1/(Real.log 2*entropyInverse e*(1-entropyInverse e)*J (entropyInverse e))
noncomputable def jSecond (e : ℝ) : ℝ :=
  (Real.log 2*(1-2*entropyInverse e)*J (entropyInverse e)-1) /
    ((Real.log 2)^2*(entropyInverse e)^2*(1-entropyInverse e)^2*(J (entropyInverse e))^3)

theorem hasDerivAt_invSlope {e : ℝ} (he : 0 < e) (he' : e < 1) :
    HasDerivAt invSlope (invSecond e) e := by
  apply (hasDerivAt_deriv_entropyInverse he he').congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he he'] with t ht
  exact (deriv_entropyInverse ht.1 ht.2).symm

theorem hasDerivAt_entropyJ {e : ℝ} (he : 0 < e) (he' : e < 1) :
    HasDerivAt (fun t => J (entropyInverse t)) (jSlope e) e := by
  have hv := entropyInverse_pos he he'.le
  have hv' := entropyInverse_lt_half he.le he'
  convert! (hasDerivAt_J hv (by linarith)).comp e (hasDerivAt_entropyInverse he he') using 1
  unfold jSlope
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasDerivAt_jSlope {e : ℝ} (he : 0 < e) (he' : e < 1) :
    HasDerivAt jSlope (jSecond e) e := by
  have hv := entropyInverse_pos he he'.le
  have hv' := entropyInverse_lt_half he.le he'
  have hJ := J_pos hv hv'
  have hvc : 0 < 1-entropyInverse e := by linarith
  have hi := hasDerivAt_entropyInverse he he'
  have hd := (((hi.const_mul (Real.log 2)).mul (hi.const_sub 1)).mul
    (hasDerivAt_entropyJ he he')).inv (by
      change Real.log 2*entropyInverse e*(1-entropyInverse e)*J (entropyInverse e) ≠ 0
      exact ne_of_gt (by positivity)) |>.neg
  convert! hd using 1
  · funext t
    change -1/(Real.log 2*entropyInverse t*(1-entropyInverse t)*J (entropyInverse t)) = -(Real.log 2*entropyInverse t*(1-entropyInverse t)*J (entropyInverse t))⁻¹
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · dsimp [jSecond, jSlope]
    field_simp [log_two_pos.ne', hv.ne', hvc.ne', hJ.ne']
    ring

noncomputable def costLeft (e f : ℝ) : ℝ :=
  ((J (entropyInverse f)-J (entropyInverse e))*invSlope e + gap e f*jSlope e)/2
noncomputable def costLL (e f : ℝ) : ℝ :=
  (-2*invSlope e*jSlope e+(J (entropyInverse f)-J (entropyInverse e))*invSecond e+
    gap e f*jSecond e)/2
noncomputable def costLR (e f : ℝ) : ℝ :=
  (jSlope f*invSlope e+invSlope f*jSlope e)/2

theorem hasDerivAt_costLeft_left {e f : ℝ} (he : 0 < e) (he' : e < 1) :
    HasDerivAt (fun t => costLeft t f) (costLL e f) e := by
  have hd := (((hasDerivAt_entropyJ he he').const_sub (J (entropyInverse f))).mul
    (hasDerivAt_invSlope he he')).add
    (((hasDerivAt_entropyInverse he he').const_sub (entropyInverse f)).mul
      (hasDerivAt_jSlope he he')) |>.div_const 2
  convert! hd using 1
  dsimp [costLL, invSlope, gap]
  ring

theorem hasDerivAt_costLeft_right {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    HasDerivAt (costLeft e) (costLR e f) f := by
  have hd := (((hasDerivAt_entropyJ hf hf').sub_const (J (entropyInverse e))).mul_const
    (invSlope e)).add
    (((hasDerivAt_entropyInverse hf hf').sub_const (entropyInverse e)).mul_const (jSlope e)) |>.div_const 2
  convert! hd using 1

theorem leftSlope_eq (e f : ℝ) : leftSlope e f = costLeft e f +
    (invSlope e+normalized e f/2)*deriv (fun r => F r 1) (normalized e f)-
      F (normalized e f) 1/2 := by
  unfold leftSlope costLeft invSlope jSlope
  ring

noncomputable def hessianLL (e f : ℝ) : ℝ := costLL e f +
  invSecond e*deriv (fun r => F r 1) (normalized e f) -
    (invSlope e+normalized e f/2)^2/mid e f *
      deriv (deriv (fun r => F r 1)) (normalized e f)

noncomputable def hessianLR (e f : ℝ) : ℝ := costLR e f +
  (invSlope e+normalized e f/2)*(invSlope f-normalized e f/2)/mid e f *
    deriv (deriv (fun r => F r 1)) (normalized e f)

theorem hasDerivAt_leftSlope_left {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (fun t => leftSlope t f) (hessianLL e f) e := by
  have hi := hasDerivAt_entropyInverse he (hef.trans hf)
  have hm := mid_pos he hef
  have ht : 0 < normalized e f := div_pos (gap_pos he hef hf) hm
  have hs := hi.const_sub (entropyInverse f)
  have hmid := ((hasDerivAt_id e).add_const f).div_const 2
  have ht' := hs.div hmid hm.ne'
  have hdF := (hasDerivAt_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hddF := (hasDerivAt_deriv_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_costLeft_left (f := f) he (hef.trans hf)).add
    (((hasDerivAt_invSlope he (hef.trans hf)).add (ht'.div_const 2)).mul
      (hddF.comp e ht'))).sub ((hdF.comp e ht').div_const 2)
  rw [show (fun t => leftSlope t f) = fun t => costLeft t f +
    (invSlope t+normalized t f/2)*deriv (fun r => F r 1) (normalized t f)-F (normalized t f) 1/2
    from funext (fun t => leftSlope_eq t f)]
  convert! hd using 1
  dsimp [hessianLL, normalized, mid, gap, invSlope]
  field_simp [show e+f ≠ 0 by linarith]
  ring

theorem hasDerivAt_leftSlope_right {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (leftSlope e) (hessianLR e f) f := by
  have hi := hasDerivAt_entropyInverse (he.trans hef) hf
  have hm := mid_pos he hef
  have ht : 0 < normalized e f := div_pos (gap_pos he hef hf) hm
  have hs := hi.sub_const (entropyInverse e)
  have hmid := ((hasDerivAt_id f).const_add e).div_const 2
  have ht' := hs.div hmid hm.ne'
  have hdF := (hasDerivAt_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hddF := (hasDerivAt_deriv_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_costLeft_right (e := e) (he.trans hef) hf).add
    (((ht'.div_const 2).const_add (invSlope e)).mul (hddF.comp f ht'))).sub
      ((hdF.comp f ht').div_const 2)
  rw [show leftSlope e = fun t => costLeft e t +
    (invSlope e+normalized e t/2)*deriv (fun r => F r 1) (normalized e t)-F (normalized e t) 1/2
    from funext (leftSlope_eq e)]
  convert! hd using 1
  dsimp [hessianLR, normalized, mid, gap, invSlope]
  field_simp [show e+f ≠ 0 by linarith]
  ring

theorem hasDerivAt_deriv_entropyCorrection_left {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (deriv (fun t => entropyCorrection t f)) (hessianLL e f) e := by
  apply (hasDerivAt_leftSlope_left he hef hf).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he hef] with t ht
  exact (hasDerivAt_entropyCorrection_left ht.1 ht.2 hf).deriv

theorem hasDerivAt_entropyCorrection_left_right {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (fun t => deriv (fun x => entropyCorrection x t) e) (hessianLR e f) f := by
  apply (hasDerivAt_leftSlope_right he hef hf).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hef hf] with t ht
  exact (hasDerivAt_entropyCorrection_left he ht.1 ht.2).deriv












theorem scaled_hessianLL {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    2*Real.log 2*(J (entropyInverse e)*q e)^2*hessianLL e f =
      Aleft e f-2*Real.log 2*(deriv (deriv (fun r => F r 1)) (normalized e f)/mid e f)*
        (Zleft e f)^2 := by
  have hv := entropyInverse_pos he (hef.trans hf).le
  have hv' := entropyInverse_lt_half he.le (hef.trans hf)
  have hJ := J_pos hv hv'
  dsimp [hessianLL, costLL, invSlope, invSecond, jSlope, jSecond, Aleft, Zleft, q]
  field_simp [log_two_pos.ne', hv.ne', hJ.ne', show 1-entropyInverse e ≠ 0 by linarith]
  ring

theorem scaled_hessianLR {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    2*Real.log 2*(J (entropyInverse e)*q e)*(J (entropyInverse f)*q f)*hessianLR e f =
      -(q e+q f)-2*Real.log 2*(deriv (deriv (fun r => F r 1)) (normalized e f)/mid e f)*
        Zleft e f*Zright e f := by
  have hu := entropyInverse_pos he (hef.trans hf).le
  have hu' := entropyInverse_lt_half he.le (hef.trans hf)
  have hJu := J_pos hu hu'
  have hw := entropyInverse_pos (he.trans hef) hf.le
  have hw' := entropyInverse_lt_half (he.trans hef).le hf
  have hJw := J_pos hw hw'
  dsimp [hessianLR, costLR, invSlope, jSlope, Zleft, Zright, q]
  field_simp [log_two_pos.ne', hu.ne', hJu.ne', hw.ne', hJw.ne',
    show 1-entropyInverse e ≠ 0 by linarith, show 1-entropyInverse f ≠ 0 by linarith]
  ring


noncomputable def costRight (e f : ℝ) : ℝ :=
  ((J (entropyInverse e)-J (entropyInverse f))*invSlope f-gap e f*jSlope f)/2
noncomputable def costRR (e f : ℝ) : ℝ :=
  (-2*invSlope f*jSlope f+(J (entropyInverse e)-J (entropyInverse f))*invSecond f-
    gap e f*jSecond f)/2
noncomputable def rightSlope (e f : ℝ) : ℝ := costRight e f-
  (invSlope f-normalized e f/2)*deriv (fun r => F r 1) (normalized e f)-
    F (normalized e f) 1/2
noncomputable def hessianRR (e f : ℝ) : ℝ := costRR e f-
  invSecond f*deriv (fun r => F r 1) (normalized e f)-
    (invSlope f-normalized e f/2)^2/mid e f*
      deriv (deriv (fun r => F r 1)) (normalized e f)

theorem hasDerivAt_ordered_right {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (ordered e) (rightSlope e f) f := by
  have hi := hasDerivAt_entropyInverse (he.trans hef) hf
  have hs := hi.sub_const (entropyInverse e)
  have hj := (hasDerivAt_entropyJ (he.trans hef) hf).const_sub (J (entropyInverse e))
  have hm := mid_pos he hef
  have ht : 0 < normalized e f := div_pos (gap_pos he hef hf) hm
  have hmid := ((hasDerivAt_id f).const_add e).div_const 2
  have ht' := hs.div hmid hm.ne'
  have hF := (hasDerivAt_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hd := ((hs.mul hj).div_const 2).sub (hmid.mul (hF.comp f ht'))
  convert! hd using 1
  dsimp [rightSlope, costRight, invSlope, normalized, gap, mid]
  field_simp [show e+f ≠ 0 by linarith]
  ring

theorem hasDerivAt_entropyCorrection_right {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (entropyCorrection e) (rightSlope e f) f := by
  apply (hasDerivAt_ordered_right he hef hf).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hef hf] with t ht
  exact ordered_eq he ht.1 ht.2

theorem hasDerivAt_costRight_right {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    HasDerivAt (costRight e) (costRR e f) f := by
  have hd := (((hasDerivAt_entropyJ hf hf').const_sub (J (entropyInverse e))).mul
    (hasDerivAt_invSlope hf hf')).sub
    (((hasDerivAt_entropyInverse hf hf').sub_const (entropyInverse e)).mul
      (hasDerivAt_jSlope hf hf')) |>.div_const 2
  convert! hd using 1
  dsimp [costRR, invSlope, gap]
  ring

theorem hasDerivAt_rightSlope_right {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (rightSlope e) (hessianRR e f) f := by
  have hi := hasDerivAt_entropyInverse (he.trans hef) hf
  have hm := mid_pos he hef
  have ht : 0 < normalized e f := div_pos (gap_pos he hef hf) hm
  have hs := hi.sub_const (entropyInverse e)
  have hmid := ((hasDerivAt_id f).const_add e).div_const 2
  have ht' := hs.div hmid hm.ne'
  have hdF := (hasDerivAt_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hddF := (hasDerivAt_deriv_F_radius (h := 1) ht (by norm_num)).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_costRight_right (e := e) (he.trans hef) hf).sub
    (((hasDerivAt_invSlope (he.trans hef) hf).sub (ht'.div_const 2)).mul
      (hddF.comp f ht'))).sub ((hdF.comp f ht').div_const 2)
  convert! hd using 1
  dsimp [hessianRR, normalized, mid, gap, invSlope]
  field_simp [show e+f ≠ 0 by linarith]
  ring

theorem hasDerivAt_deriv_entropyCorrection_right {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    HasDerivAt (deriv (entropyCorrection e)) (hessianRR e f) f := by
  apply (hasDerivAt_rightSlope_right he hef hf).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hef hf] with t ht
  exact (hasDerivAt_entropyCorrection_right he ht.1 ht.2).deriv







theorem scaled_hessianRR {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    2*Real.log 2*(J (entropyInverse f)*q f)^2*hessianRR e f =
      Aright e f-2*Real.log 2*(deriv (deriv (fun r => F r 1)) (normalized e f)/mid e f)*
        (Zright e f)^2 := by
  have hv := entropyInverse_pos (he.trans hef) hf.le
  have hv' := entropyInverse_lt_half (he.trans hef).le hf
  have hJ := J_pos hv hv'
  dsimp [hessianRR, costRR, invSlope, invSecond, jSlope, jSecond, Aright, Zright, q]
  field_simp [log_two_pos.ne', hv.ne', hJ.ne', show 1-entropyInverse f ≠ 0 by linarith]
  ring


/-- The normalized curvature in the algebraic entries is the physical radial curvature. -/
theorem normalized_curvature_eq {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    deriv (deriv (fun r => F r 1)) (normalized e f)/mid e f =
      deriv (deriv (fun r => F r (mid e f))) (gap e f) := by
  rw [deriv2_F_radius_normalize (gap_pos he hef hf) (mid_pos he hef)]
  dsimp [normalized]
  ring

theorem Aleft_eq_physical {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    Aleft e f =
      (q e*(Real.log 2*J (entropyInverse e)+Real.log 2*J (entropyInverse f)+
        2*Real.log 2*deriv (fun r => F r (mid e f)) (gap e f))+
        gap e f*(Real.log 2*J (entropyInverse e)*(1-2*entropyInverse e)-1)) /
          (Real.log 2*J (entropyInverse e)) := by
  rw [deriv_F_radius_normalize (gap_pos he hef hf) (mid_pos he hef)]
  rfl

theorem Aright_eq_physical {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    Aright e f =
      (q f*(Real.log 2*J (entropyInverse e)+Real.log 2*J (entropyInverse f)-
        2*Real.log 2*deriv (fun r => F r (mid e f)) (gap e f))+
        gap e f*(1-Real.log 2*J (entropyInverse f)*(1-2*entropyInverse f))) /
          (Real.log 2*J (entropyInverse f)) := by
  rw [deriv_F_radius_normalize (gap_pos he hef hf) (mid_pos he hef)]
  rfl

/-- Exact source congruence for the actual entropy-coordinate Hessian. This identity
makes no positive-semidefiniteness assertion. The natural-unit factors are log 2. -/
theorem entropyCorrection_scaled_hessian {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1) :
    (2*Real.log 2*(J (entropyInverse e)*q e)^2*
        deriv (deriv (fun t => entropyCorrection t f)) e =
      Aleft e f-2*Real.log 2*deriv (deriv (fun r => F r (mid e f))) (gap e f)*(Zleft e f)^2) ∧
    (2*Real.log 2*(J (entropyInverse e)*q e)*(J (entropyInverse f)*q f)*
        deriv (fun t => deriv (fun x => entropyCorrection x t) e) f =
      -(q e+q f)-2*Real.log 2*deriv (deriv (fun r => F r (mid e f))) (gap e f)*Zleft e f*Zright e f) ∧
    (2*Real.log 2*(J (entropyInverse f)*q f)^2*
        deriv (deriv (entropyCorrection e)) f =
      Aright e f-2*Real.log 2*deriv (deriv (fun r => F r (mid e f))) (gap e f)*(Zright e f)^2) := by
  rw [(hasDerivAt_deriv_entropyCorrection_left he hef hf).deriv,
    (hasDerivAt_entropyCorrection_left_right he hef hf).deriv,
    (hasDerivAt_deriv_entropyCorrection_right he hef hf).deriv]
  exact ⟨by simpa only [normalized_curvature_eq he hef hf] using scaled_hessianLL he hef hf,
    by simpa only [normalized_curvature_eq he hef hf] using scaled_hessianLR he hef hf,
    by simpa only [normalized_curvature_eq he hef hf] using scaled_hessianRR he hef hf⟩

end Correction
end GeneralCK


