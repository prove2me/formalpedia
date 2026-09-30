-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TauDiscCertificateOfContraction
-- name    : CK_GeneralCK_Certificates_E8TauDiscCertificateOfContraction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:24:03.267763+00:00
-- url     : https://prove2.me/theorems/bdb6433e-f645-40f3-9192-d9686d33a6a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TauDiscCertificateOfContraction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TauDiscCertificateOfContraction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TauDiscCertificateOfContraction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TauDiscCertificateOfContraction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TauDiscCertificateOfContraction.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaTauDerivativeFormula

-- ===== source module GeneralCK.Certificates.E8TauDiscCertificateOfContraction =====
section

/-!
# A holomorphic inverse branch from the E8 contraction estimate

The pointwise Banach theorem is upgraded here to the quantitative branch
consumed by `E8QuantitativeBranchBridge`.  Uniqueness gives a canonical
selected inverse, while the unit Lipschitz estimate on the nonlinear
remainder gives a `1/3` Lipschitz estimate for that inverse.
-/

namespace GeneralCK.Certificates.E8TauDiscCertificateOfContraction

open Metric Set Filter Function
open scoped Topology
open E8AnalyticGerm
open Reflection.ComplexContactGerm
open Reflection.ComplexGlobalAnalytic
open E8QuantitativeBranchBridge
open E8TauInverseContraction
open E8ThetaTauAnalytic

private abbrev tauDisc : Set ℂ := closedBall 0 tauRadius

noncomputable def tauBranchOfLip
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    (y : ℂ) : ℂ :=
  if hy : ‖y‖ ≤ supportedYRadius then
    Classical.choose (exists_unique_thetaOfTau_inverse hLip hy)
  else 0

theorem tauBranchOfLip_mem
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    tauBranchOfLip hLip y ∈ tauDisc := by
  rw [tauBranchOfLip, dif_pos hy]
  exact (Classical.choose_spec (exists_unique_thetaOfTau_inverse hLip hy)).1.1

theorem thetaOfTau_tauBranchOfLip
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    thetaOfTau (tauBranchOfLip hLip y) = y := by
  rw [tauBranchOfLip, dif_pos hy]
  exact (Classical.choose_spec (exists_unique_thetaOfTau_inverse hLip hy)).1.2

theorem tauBranchOfLip_unique
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y tau : ℂ} (hy : ‖y‖ ≤ supportedYRadius)
    (htau : tau ∈ tauDisc) (heq : thetaOfTau tau = y) :
    tauBranchOfLip hLip y = tau := by
  rw [tauBranchOfLip, dif_pos hy]
  exact ((Classical.choose_spec (exists_unique_thetaOfTau_inverse hLip hy)).2 tau
    ⟨htau, heq⟩).symm

theorem tauBranchOfLip_dist_le
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y z : ℂ} (hy : ‖y‖ ≤ supportedYRadius)
    (hz : ‖z‖ ≤ supportedYRadius) :
    dist (tauBranchOfLip hLip y) (tauBranchOfLip hLip z) ≤
      (1 / 3 : ℝ) * dist y z := by
  let a := tauBranchOfLip hLip y
  let b := tauBranchOfLip hLip z
  have ha : a ∈ tauDisc := tauBranchOfLip_mem hLip hy
  have hb : b ∈ tauDisc := tauBranchOfLip_mem hLip hz
  have hR := hLip.dist_le_mul a ha b hb
  have hya := thetaOfTau_tauBranchOfLip hLip hy
  have hzb := thetaOfTau_tauBranchOfLip hLip hz
  change thetaOfTau a = y at hya
  change thetaOfTau b = z at hzb
  have hya' : (4 : ℂ) * a + thetaTauRemainder a = y := by
    rw [← hya]
    unfold thetaTauRemainder
    ring
  have hzb' : (4 : ℂ) * b + thetaTauRemainder b = z := by
    rw [← hzb]
    unfold thetaTauRemainder
    ring
  have hid : (4 : ℂ) * (a - b) =
      (y - z) - (thetaTauRemainder a - thetaTauRemainder b) := by
    linear_combination hya' - hzb'
  have hfour : 4 * ‖a - b‖ ≤ ‖y - z‖ + ‖thetaTauRemainder a - thetaTauRemainder b‖ := by
    calc
      4 * ‖a - b‖ = ‖(4 : ℂ) * (a - b)‖ := by norm_num [norm_mul]
      _ = ‖(y - z) - (thetaTauRemainder a - thetaTauRemainder b)‖ := by rw [hid]
      _ ≤ ‖y - z‖ + ‖thetaTauRemainder a - thetaTauRemainder b‖ := norm_sub_le _ _
  rw [dist_eq_norm] at hR
  norm_num at hR
  rw [dist_eq_norm] at hR
  have hthree : 3 * ‖a - b‖ ≤ ‖y - z‖ := by linarith
  have hab : ‖a - b‖ ≤ (1 / 3 : ℝ) * ‖y - z‖ := by linarith
  simpa only [a, b, dist_eq_norm] using hab

theorem tauBranchOfLip_lipschitzOn
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    LipschitzOnWith (1 / 3 : NNReal) (tauBranchOfLip hLip)
      (closedBall (0 : ℂ) supportedYRadius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  exact tauBranchOfLip_dist_le hLip
    (by simpa [mem_closedBall, dist_zero_right] using hy)
    (by simpa [mem_closedBall, dist_zero_right] using hz)

theorem tauBranchOfLip_norm_lt_tauRadius
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℂ} (hy : ‖y‖ < yOuterRadius) :
    ‖tauBranchOfLip hLip y‖ < tauRadius := by
  have hySupported : ‖y‖ ≤ supportedYRadius :=
    hy.le.trans (by norm_num [yOuterRadius, supportedYRadius])
  let a := tauBranchOfLip hLip y
  have ha : a ∈ tauDisc := tauBranchOfLip_mem hLip hySupported
  have hzero : (0 : ℂ) ∈ tauDisc := by
    simp [tauDisc, tauRadius]
    norm_num
  have hR := hLip.dist_le_mul a ha 0 hzero
  have hRnorm : ‖thetaTauRemainder a‖ ≤ ‖a‖ := by
    simpa [thetaTauRemainder_zero, dist_eq_norm] using hR
  have heq := thetaOfTau_tauBranchOfLip hLip hySupported
  change thetaOfTau a = y at heq
  have hlin : (4 : ℂ) * a = y - thetaTauRemainder a := by
    change (4 : ℂ) * a = y - (thetaOfTau a - 4 * a)
    linear_combination heq
  have hfour : 4 * ‖a‖ ≤ ‖y‖ + ‖thetaTauRemainder a‖ := by
    calc
      4 * ‖a‖ = ‖(4 : ℂ) * a‖ := by norm_num [norm_mul]
      _ = ‖y - thetaTauRemainder a‖ := by rw [hlin]
      _ ≤ ‖y‖ + ‖thetaTauRemainder a‖ := norm_sub_le _ _
  have : ‖a‖ < (2 / 5 : ℝ) := by
    rw [yOuterRadius] at hy
    linarith
  simpa [a, tauRadius] using this

theorem thetaOfTau_deriv_ne
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {tau : ℂ} (htau : ‖tau‖ < tauRadius) :
    deriv thetaOfTau tau ≠ 0 := by
  have htau' : ‖tau‖ ≤ (2 / 5 : ℝ) := by
    simpa [tauRadius] using htau.le
  have hnhds : tauDisc ∈ 𝓝 tau := by
    apply closedBall_mem_nhds_of_mem
    simpa [tauDisc, tauRadius, mem_ball, dist_zero_right] using htau
  have hfd := norm_fderiv_le_of_lipschitzOn ℂ hnhds hLip
  have hrem : ‖deriv thetaTauRemainder tau‖ ≤ (1 : ℝ) := by
    rw [norm_deriv_eq_norm_fderiv]
    exact_mod_cast hfd
  have htheta := (E8ThetaTauDerivativeFormula.hasDerivAt_thetaOfTau_expr htau').deriv
  have hrema := E8ThetaTauDerivativeFormula.deriv_thetaTauRemainder_eq htau'
  intro hzero
  have hexpr : E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau = 0 := by
    rw [← htheta]
    exact hzero
  have hbad : ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
    rw [← hrema]
    exact hrem
  rw [hexpr, zero_sub, norm_neg] at hbad
  norm_num at hbad

theorem analyticAt_tauBranchOfLip
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℂ} (hy : ‖y‖ < yOuterRadius) :
    AnalyticAt ℂ (tauBranchOfLip hLip) y := by
  have hySupported : ‖y‖ ≤ supportedYRadius :=
    hy.le.trans (by norm_num [yOuterRadius, supportedYRadius])
  let a := tauBranchOfLip hLip y
  have haNorm : ‖a‖ < tauRadius := by
    simpa only [a] using tauBranchOfLip_norm_lt_tauRadius hLip hy
  have haNorm' : ‖a‖ ≤ (2 / 5 : ℝ) := by
    simpa [tauRadius] using haNorm.le
  have hthetaAnalytic := analyticAt_thetaOfTau_of_norm_le haNorm'
  have hderiv : deriv thetaOfTau a ≠ 0 := thetaOfTau_deriv_ne hLip haNorm
  let g : ℂ → ℂ := hthetaAnalytic.hasStrictDerivAt.localInverse thetaOfTau
    (deriv thetaOfTau a) a hderiv
  have hthetaEq : thetaOfTau a = y := by
    simpa only [a] using thetaOfTau_tauBranchOfLip hLip hySupported
  have hgAnalytic : AnalyticAt ℂ g y := by
    simpa only [g, hthetaEq] using hthetaAnalytic.analyticAt_localInverse hderiv
  have hright : ∀ᶠ z in 𝓝 y, thetaOfTau (g z) = z := by
    have h := hthetaAnalytic.hasStrictDerivAt.eventually_right_inverse hderiv
    simpa only [g, hthetaEq] using h
  have hgY : g y = a := by
    have h := hthetaAnalytic.hasStrictDerivAt.eventually_left_inverse hderiv
    simpa only [g, hthetaEq] using h.self_of_nhds
  have hgTau : ∀ᶠ z in 𝓝 y, g z ∈ tauDisc := by
    apply hgAnalytic.continuousAt
    change closedBall 0 tauRadius ∈ 𝓝 (g y)
    rw [hgY]
    exact closedBall_mem_nhds_of_mem (by
      simpa [tauRadius, mem_ball, dist_zero_right] using haNorm)
  have hzSupported : ∀ᶠ z in 𝓝 y, ‖z‖ ≤ supportedYRadius := by
    apply mem_of_superset (isOpen_ball.mem_nhds (show y ∈ ball 0 supportedYRadius by
      simpa [mem_ball, dist_zero_right] using
        hy.trans_le (by norm_num [yOuterRadius, supportedYRadius])))
    intro z hz
    exact (show ‖z‖ < supportedYRadius by
      simpa [mem_ball, dist_zero_right] using hz).le
  have heq : tauBranchOfLip hLip =ᶠ[𝓝 y] g := by
    filter_upwards [hright, hgTau, hzSupported] with z hright hgTau hz
    exact tauBranchOfLip_unique hLip hz hgTau hright
  exact hgAnalytic.congr heq.symm

theorem tauBranchOfLip_diffCont
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    DiffContOnCl ℂ (tauBranchOfLip hLip) (ball 0 yOuterRadius) := by
  apply DiffContOnCl.mk_ball
  · intro y hy
    exact (analyticAt_tauBranchOfLip hLip (by
      simpa [mem_ball, dist_zero_right] using hy)).differentiableAt.differentiableWithinAt
  · exact (tauBranchOfLip_lipschitzOn hLip).continuousOn.mono (by
      intro y hy
      have hyn : ‖y‖ ≤ yOuterRadius := by
        simpa [mem_closedBall, dist_zero_right] using hy
      have : yOuterRadius ≤ supportedYRadius := by
        norm_num [yOuterRadius, supportedYRadius]
      simpa [mem_closedBall, dist_zero_right] using hyn.trans this)

theorem eventually_fixedPointOnDisc_eq_contactGerm :
    fixedPointOnDisc =ᶠ[𝓝 (0 : ℂ)] contactGerm := by
  have hsmall : ∀ᶠ tau : ℂ in 𝓝 0, ‖tau‖ < (7 / 10 : ℝ) := by
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  filter_upwards [hsmall, eventually_contactGerm_eq_fixedPoint]
      with tau htau hcontact
  rw [fixedPointOnDisc_eq htau]
  exact (hcontact htau.le).symm

theorem eventually_contactGerm_slopeMap :
    ∀ᶠ c : ℂ in 𝓝 0, contactGerm (slopeMap c) = c := by
  have hne : deriv slopeMap 0 ≠ 0 := by
    rw [(hasDerivAt_slopeMap_zero).deriv]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by norm_num))))
  have h := analyticAt_slopeMap.hasStrictDerivAt.eventually_left_inverse hne
  simpa [contactGerm] using h

theorem tauBranchOfLip_agreesNear
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    ∀ᶠ c : ℂ in 𝓝 0,
      tauBranchOfLip hLip (thetaParam c) = slopeMap c := by
  have hslopeTendsto : Tendsto slopeMap (𝓝 0) (𝓝 0) := by
    have h := analyticAt_slopeMap.continuousAt
    change Tendsto slopeMap (𝓝 0) (𝓝 (slopeMap 0)) at h
    simpa only [slopeMap_zero] using h
  have hfixed : ∀ᶠ c : ℂ in 𝓝 0,
      fixedPointOnDisc (slopeMap c) = c := by
    filter_upwards [hslopeTendsto.eventually eventually_fixedPointOnDisc_eq_contactGerm,
      eventually_contactGerm_slopeMap] with c hdisc hleft
    rw [hdisc, hleft]
  have hslopeDisc : ∀ᶠ c : ℂ in 𝓝 0, ‖slopeMap c‖ ≤ tauRadius := by
    have h := hslopeTendsto.eventually
      (closedBall_mem_nhds (0 : ℂ) (show 0 < tauRadius by norm_num [tauRadius]))
    filter_upwards [h] with c hc
    simpa [mem_closedBall, dist_zero_right] using hc
  have hthetaSupported : ∀ᶠ c : ℂ in 𝓝 0,
      ‖thetaParam c‖ ≤ supportedYRadius := by
    have ht : Tendsto thetaParam (𝓝 0) (𝓝 0) := by
      have h := analyticAt_thetaParam.continuousAt
      change Tendsto thetaParam (𝓝 0) (𝓝 (thetaParam 0)) at h
      simpa only [thetaParam_zero] using h
    have h := ht.eventually
      (closedBall_mem_nhds (0 : ℂ)
        (show 0 < supportedYRadius by norm_num [supportedYRadius]))
    filter_upwards [h] with c hc
    simpa [mem_closedBall, dist_zero_right] using hc
  filter_upwards [hfixed, hslopeDisc, hthetaSupported]
      with c hfixed hslope htheta
  apply tauBranchOfLip_unique hLip htheta
  · simpa [tauDisc, mem_closedBall, dist_zero_right] using hslope
  · unfold thetaOfTau
    rw [hfixed]

/-- The sole functional premise needed for the full quantitative branch is
the unit Lipschitz bound on the explicit nonlinear remainder. -/
noncomputable def tauDiscInverseCertificateOfLipschitz
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    TauDiscInverseCertificate where
  tauBranch := tauBranchOfLip hLip
  diffCont := tauBranchOfLip_diffCont hLip
  norm_le := by
    intro y hy
    have hy' : ‖y‖ ≤ supportedYRadius := by
      have hyr : ‖y‖ ≤ yOuterRadius := by
        simpa [mem_closedBall, dist_zero_right] using hy
      exact hyr.trans (by norm_num [yOuterRadius, supportedYRadius])
    have hm := tauBranchOfLip_mem hLip hy'
    have : ‖tauBranchOfLip hLip y‖ ≤ tauRadius := by
      simpa [tauDisc, mem_closedBall, dist_zero_right] using hm
    exact this.trans (by norm_num [tauRadius])
  agreesNear := tauBranchOfLip_agreesNear hLip

/-- Fully explicit numerical handoff: a pointwise enclosure for the displayed
elementary derivative expression constructs the holomorphic inverse branch. -/
noncomputable def tauDiscInverseCertificateOfExprBound
    (hExpr : ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)) :
    TauDiscInverseCertificate :=
  tauDiscInverseCertificateOfLipschitz
    (thetaTauRemainder_lipschitz_of_deriv_bound
      (E8ThetaTauDerivativeFormula.final_derivative_bound_of_expr_bound hExpr))

end GeneralCK.Certificates.E8TauDiscCertificateOfContraction

end


