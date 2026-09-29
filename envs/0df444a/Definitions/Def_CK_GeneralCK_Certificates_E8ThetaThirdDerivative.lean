-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaThirdDerivative
-- name    : CK_GeneralCK_Certificates_E8ThetaThirdDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:01:30.814952+00:00
-- url     : https://prove2.me/theorems/121a11d3-4d0d-432f-b417-5e47d5207e8f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaThirdDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaThirdDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaThirdDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaThirdDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaThirdDerivative.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives

-- ===== source module GeneralCK.Certificates.E8ThetaThirdDerivative =====
section

/-! The unconditional third smoothness link for the E8 inverse bridge. -/

namespace GeneralCK

open Set Filter
open Certificates.Mixed

private noncomputable def profileR (v : ℝ) : ℝ := 1 - 2*v
private noncomputable def profileNu (v : ℝ) : ℝ := 4*v*(1-v)
private noncomputable def profileKPrime (v : ℝ) : ℝ :=
  -profileR v / (2*v*(1-v))
private noncomputable def profileA (v : ℝ) : ℝ :=
  2*profileR v*hn v^2*(2*kap v-profileR v^2)
private noncomputable def profileB (v : ℝ) : ℝ :=
  Real.log 2*(profileNu v^2*kap v^3)
private noncomputable def profileAPrime (v : ℝ) : ℝ :=
  2*((-2)*hn v^2 + profileR v*(2*hn v*(J v*Real.log 2))) *
      (2*kap v-profileR v^2) +
    2*profileR v*hn v^2*(2*profileKPrime v-2*profileR v*(-2))
private noncomputable def profileBPrime (v : ℝ) : ℝ :=
  Real.log 2 *
    (2*profileNu v*(4*(1-2*v))*kap v^3 +
      profileNu v^2*(3*kap v^2*profileKPrime v))
noncomputable def profilePrime (v : ℝ) : ℝ :=
  (profileAPrime v*profileB v-profileA v*profileBPrime v) / profileB v^2

/-- The compact profile is smooth to all orders away from its endpoint
singularities. -/
theorem contDiffAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    ContDiffAt ℝ ⊤ profile v := by
  have hv1 : v < 1 := by linarith
  have hkap : 0 < -Real.log (v*(1-v))/2 := by
    simpa [kap] using kap_pos hv hv'
  have hden :
      Real.log 2 * (4*v*(1-v))^2 * (-Real.log (v*(1-v))/2)^3 ≠ 0 := by
    positivity
  unfold profile hn kap
  fun_prop (disch := first | assumption | positivity)

theorem hasDerivAt_profile_explicit {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    HasDerivAt profile (profilePrime v) v := by
  have hv1 : v < 1 := by linarith
  have hr0 := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hr : HasDerivAt profileR _ v := hr0.congr_of_eventuallyEq (by
    filter_upwards with u
    simp [profileR])
  have hnu0 := ((hasDerivAt_id v).const_mul 4).mul ((hasDerivAt_id v).const_sub 1)
  have hnu : HasDerivAt profileNu _ v := hnu0.congr_of_eventuallyEq (by
    filter_upwards with u
    simp [profileNu])
  have hh := hasDerivAt_hn hv hv1
  have hk := hasDerivAt_kap hv hv1
  have hk' : HasDerivAt kap (profileKPrime v) v := by
    simpa [profileKPrime, profileR] using hk
  have hA := (((hr.mul (hh.pow 2)).const_mul 2).mul
    ((hk'.const_mul 2).sub (hr.pow 2)))
  have hB := ((hnu.pow 2).mul (hk'.pow 3)).const_mul (Real.log 2)
  have hBne : profileB v ≠ 0 := by
    unfold profileB profileNu
    exact mul_ne_zero log_two_pos.ne'
      (mul_ne_zero
        (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') (by linarith)))
        (pow_ne_zero _ (kap_pos hv hv').ne'))
  have hq := hA.div hB hBne
  have heq : profile =
      ((fun y => 2 * (profileR * hn ^ 2) y) *
        ((fun y => 2 * kap y) - profileR ^ 2)) /
        (fun y => Real.log 2 * (profileNu ^ 2 * kap ^ 3) y) := by
    funext u
    simp [profile, profileR, profileNu, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    ring
  rw [heq]
  refine hq.congr_deriv ?_
  simp [profilePrime, profileA, profileB, profileAPrime,
    profileBPrime, profileR, profileNu, profileKPrime]
  ring

theorem differentiableAt_profilePrime {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    DifferentiableAt ℝ profilePrime v := by
  have hv1 : v < 1 := by linarith
  have hhn := (hasDerivAt_hn hv hv1).differentiableAt
  have hkap := (hasDerivAt_kap hv hv1).differentiableAt
  have hJ := (hasDerivAt_J hv hv1).differentiableAt
  have hvne : v ≠ 0 := hv.ne'
  have hvc : 1-v ≠ 0 := by linarith
  have hkne : kap v ≠ 0 := (kap_pos hv hv').ne'
  unfold profilePrime profileAPrime profileB profileA profileBPrime profileKPrime
    profileR profileNu
  fun_prop (disch := positivity)

theorem differentiableAt_deriv_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    DifferentiableAt ℝ (deriv profile) v := by
  have heq : deriv profile =ᶠ[nhds v] profilePrime := by
    filter_upwards [Ioo_mem_nhds hv hv'] with u hu
    exact (hasDerivAt_profile_explicit hu.1 hu.2).deriv
  exact (differentiableAt_profilePrime hv hv').congr_of_eventuallyEq heq

noncomputable def thetaSecondFormula (x : ℝ) : ℝ :=
  let v := radialContact (2*x) 1
  ((((deriv profile v * (-H v / ((2*x)*J v+2)))*2)*x-profile v) / x^2)

theorem deriv2_e8Theta_eq_formula {x : ℝ} (hx : 0 < x) :
    deriv (deriv e8Theta) x = thetaSecondFormula x := by
  exact (hasDerivAt_deriv_e8Theta hx).deriv

theorem differentiableAt_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ thetaSecondFormula x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hinner : DifferentiableAt ℝ (fun u : ℝ => radialContact (2*u) 1) x := by
    exact ((hasDerivAt_radialContact_radius (z := 2*x) (h := 1)
      (by positivity) (by norm_num)).comp x
        ((hasDerivAt_id x).const_mul 2)).differentiableAt
  have hdp : DifferentiableAt ℝ
      (fun u : ℝ => deriv profile (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (differentiableAt_deriv_profile hv hvh).comp x hinner
  have hp : DifferentiableAt ℝ
      (fun u : ℝ => profile (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (differentiableAt_profile hv hvh).comp x hinner
  have hH : DifferentiableAt ℝ
      (fun u : ℝ => H (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (Comparison.hasDerivAt_H hv (by linarith)).differentiableAt.comp x hinner
  have hJ : DifferentiableAt ℝ
      (fun u : ℝ => J (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (hasDerivAt_J hv (by linarith)).differentiableAt.comp x hinner
  have hden : (2*x)*J v+2 ≠ 0 := by
    have := radialContact_denominator_pos (z := 2*x) (h := 1) (by positivity) (by norm_num)
    simpa [v] using this.ne'
  unfold thetaSecondFormula
  dsimp only
  fun_prop (disch := positivity)

/-- The d2→d3 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv2_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv e8Theta)) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_thetaSecondFormula hx).congr_of_eventuallyEq heq

end GeneralCK

end


