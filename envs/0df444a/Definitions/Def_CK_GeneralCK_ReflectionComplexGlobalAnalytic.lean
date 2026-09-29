-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexGlobalAnalytic
-- name    : CK_GeneralCK_ReflectionComplexGlobalAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:36:32.82314+00:00
-- url     : https://prove2.me/theorems/043c5e94-e495-4439-974b-9abc302d0691
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexGlobalAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexGlobalAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexGlobalAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexGlobalAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexGlobalAnalytic.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexCubicBound

-- ===== source module GeneralCK.ReflectionComplexGlobalAnalytic =====
section

/-!
# Holomorphic contact point on the explicit parameter disc

The local analytic inverse construction is repeated at each Banach fixed
point.  The quantitative derivative bound makes the implicit Jacobian
nonzero throughout the open `7/10` parameter disc, and contraction uniqueness
patches the local inverses into one holomorphic function.
-/

namespace GeneralCK.Reflection.ComplexGlobalAnalytic

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint ComplexContactGerm ComplexCubicBound

/-- A proof-independent total representative of the chosen fixed point on
the open parameter disc. -/
noncomputable def fixedPointOnDisc (tau : ℂ) : ℂ :=
  if h : ‖tau‖ < (7 / 10 : ℝ) then fixedPoint tau h.le else 0

theorem fixedPointOnDisc_eq {tau : ℂ} (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    fixedPointOnDisc tau = fixedPoint tau htau.le := by
  simp [fixedPointOnDisc, htau]

theorem fixedPointOnDisc_mem_ball {tau : ℂ} (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    fixedPointOnDisc tau ∈ Metric.ball 0 (4 / 5 : ℝ) := by
  rw [fixedPointOnDisc_eq htau]
  exact fixedPoint_mem_ball htau.le

theorem fixedPointOnDisc_fixed {tau : ℂ} (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    fixedPointOnDisc tau = tau * entropyExt (fixedPointOnDisc tau) := by
  rw [fixedPointOnDisc_eq htau]
  have hfix := fixedPoint_isFixedPt htau.le
  change IsFixedPt (ComplexDiscElementary.contactMap entropyExt tau)
    (fixedPoint tau htau.le) at hfix
  exact hfix.symm

theorem entropyExt_fixedPointOnDisc_ne {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) : entropyExt (fixedPointOnDisc tau) ≠ 0 := by
  intro hzero
  have hc0 : fixedPointOnDisc tau = 0 := by
    rw [fixedPointOnDisc_fixed htau, hzero, mul_zero]
  have := congrArg entropyExt hc0
  rw [entropyExt_zero, hzero] at this
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num))) this.symm

theorem analyticAt_slopeMap {c : ℂ} (hc : ‖c‖ < 1)
    (hE : entropyExt c ≠ 0) : AnalyticAt ℂ slopeMap c := by
  unfold slopeMap
  exact analyticAt_id.div (ComplexContactGerm.analyticAt_entropyExt hc) hE

theorem hasDerivAt_slopeMap {c : ℂ} (hc : ‖c‖ < 1)
    (hE : entropyExt c ≠ 0) :
    @HasDerivAt ℂ _ ℂ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (((NormedAlgebra.toNormedSpace ℂ) : NormedSpace ℂ ℂ).toModule) _ _
      slopeMap
      ((entropyExt c - c * entropyDeriv c) / entropyExt c ^ 2) c := by
  unfold ComplexContactGerm.slopeMap
  have h := (hasDerivAt_id (𝕜 := ℂ) c).div (hasDerivAt_entropyExt hc) hE
  have heq : (fun z : ℂ => z / entropyExt z) =ᶠ[𝓝 c] id / entropyExt :=
    Eventually.of_forall fun _ => rfl
  simpa only [id_eq, one_mul] using h.congr_of_eventuallyEq heq

private theorem one_sub_tau_entropyDeriv_ne {tau c : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) (hc : ‖c‖ ≤ (4 / 5 : ℝ)) :
    1 - tau * entropyDeriv c ≠ 0 := by
  have hprod : ‖tau * entropyDeriv c‖ < 1 := by
    rw [norm_mul]
    calc
      ‖tau‖ * ‖entropyDeriv c‖ ≤ ‖tau‖ * (7 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_entropyDeriv_le_seven_fifths hc) (norm_nonneg _)
      _ < (7 / 10 : ℝ) * (7 / 5 : ℝ) :=
        mul_lt_mul_of_pos_right htau (by norm_num)
      _ < 1 := by norm_num
  intro hzero
  have heq : tau * entropyDeriv c = 1 := (sub_eq_zero.mp hzero).symm
  rw [heq, norm_one] at hprod
  exact lt_irrefl 1 hprod

private theorem slopeMap_deriv_ne_at_fixed {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    deriv slopeMap (fixedPointOnDisc tau) ≠ 0 := by
  let c := fixedPointOnDisc tau
  have hcBall := fixedPointOnDisc_mem_ball htau
  have hcLt : ‖c‖ < (4 / 5 : ℝ) := by
    simpa only [c, Metric.mem_ball, dist_zero_right] using hcBall
  have hc : ‖c‖ ≤ (4 / 5 : ℝ) := by
    exact hcLt.le
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hE : entropyExt c ≠ 0 := by
    simpa only [c] using entropyExt_fixedPointOnDisc_ne htau
  have hfixed : c = tau * entropyExt c := by
    simpa only [c] using fixedPointOnDisc_fixed htau
  have hderiv := (hasDerivAt_slopeMap hc1 hE).deriv
  rw [hderiv]
  apply div_ne_zero
  · have hnum : entropyExt c - c * entropyDeriv c =
        entropyExt c * (1 - tau * entropyDeriv c) := by
      calc
        entropyExt c - c * entropyDeriv c =
            entropyExt c - (tau * entropyExt c) * entropyDeriv c :=
          congrArg (fun z => entropyExt c - z * entropyDeriv c) hfixed
        _ = _ := by ring
    have hden := one_sub_tau_entropyDeriv_ne htau hc
    rw [hnum]
    exact mul_ne_zero hE hden
  · exact pow_ne_zero 2 hE

/-- The selected fixed point depends holomorphically on the parameter at
every point of the explicit open `7/10` disc. -/
theorem analyticAt_fixedPointOnDisc {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    AnalyticAt ℂ fixedPointOnDisc tau := by
  let c := fixedPointOnDisc tau
  have hcBall := fixedPointOnDisc_mem_ball htau
  have hcNorm : ‖c‖ < 1 := by
    have : ‖c‖ < (4 / 5 : ℝ) := by
      simpa only [c, Metric.mem_ball, dist_zero_right] using hcBall
    exact this.trans (by norm_num)
  have hE : entropyExt c ≠ 0 := by
    simpa only [c] using entropyExt_fixedPointOnDisc_ne htau
  have hslope := analyticAt_slopeMap hcNorm hE
  have hderiv : deriv slopeMap c ≠ 0 := by
    simpa only [c] using slopeMap_deriv_ne_at_fixed htau
  let g : ℂ → ℂ := hslope.hasStrictDerivAt.localInverse slopeMap
    (deriv slopeMap c) c hderiv
  have hslopeEq : slopeMap c = tau := by
    unfold slopeMap
    have hfixed : c = tau * entropyExt c := by
      simpa only [c] using fixedPointOnDisc_fixed htau
    calc
      c / entropyExt c = (tau * entropyExt c) / entropyExt c :=
        congrArg (fun z => z / entropyExt c) hfixed
      _ = tau := by field_simp
  have hgAnalytic : AnalyticAt ℂ g tau := by
    simpa only [g, hslopeEq] using hslope.analyticAt_localInverse hderiv
  have hinv : ∀ᶠ sigma in 𝓝 tau, slopeMap (g sigma) = sigma := by
    have := hslope.hasStrictDerivAt.eventually_right_inverse hderiv
    simpa only [g, hslopeEq] using this
  have hgTau : g tau = c := by
    have hleft := hslope.hasStrictDerivAt.eventually_left_inverse hderiv
    simpa only [g, hslopeEq] using hleft.self_of_nhds
  have hgBall : ∀ᶠ sigma in 𝓝 tau, g sigma ∈ Metric.ball 0 (4 / 5 : ℝ) := by
    have hgcont := hgAnalytic.continuousAt
    apply hgcont
    exact Metric.isOpen_ball.mem_nhds (by simpa only [hgTau] using hcBall)
  have hgE : ∀ᶠ sigma in 𝓝 tau, entropyExt (g sigma) ≠ 0 := by
    have hcont : ContinuousAt (fun sigma => entropyExt (g sigma)) tau :=
      (ComplexContactGerm.analyticAt_entropyExt hcNorm).continuousAt.comp_of_eq
        hgAnalytic.continuousAt hgTau
    exact hcont.eventually_ne (by simpa only [hgTau] using hE)
  have hsigma : ∀ᶠ sigma in 𝓝 tau, ‖sigma‖ < (7 / 10 : ℝ) := by
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds htau
  have heq : fixedPointOnDisc =ᶠ[𝓝 tau] g := by
    filter_upwards [hinv, hgBall, hgE, hsigma] with sigma hinv hball hE hsigma
    have hfix : g sigma = sigma * entropyExt (g sigma) := by
      unfold slopeMap at hinv
      exact (div_eq_iff hE).mp hinv
    rw [fixedPointOnDisc_eq hsigma]
    exact (eq_fixedPoint hsigma.le (Metric.ball_subset_closedBall hball) hfix.symm).symm
  exact hgAnalytic.congr heq.symm

/-- Holomorphy on the full explicit open parameter disc. -/
theorem analyticOnNhd_fixedPointOnDisc :
    AnalyticOnNhd ℂ fixedPointOnDisc (Metric.ball 0 (7 / 10 : ℝ)) := by
  intro tau htau
  apply analyticAt_fixedPointOnDisc
  simpa only [Metric.mem_ball, dist_zero_right] using htau

/-- Explicit derivative of the holomorphic fixed point throughout the open
parameter disc. -/
theorem hasDerivAt_fixedPointOnDisc {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    HasDerivAt fixedPointOnDisc
      (entropyExt (fixedPointOnDisc tau) /
        (1 - tau * entropyDeriv (fixedPointOnDisc tau))) tau := by
  have hbase := (analyticAt_fixedPointOnDisc htau).differentiableAt.hasDerivAt
  have hc : ‖fixedPointOnDisc tau‖ < 1 := by
    have hball := fixedPointOnDisc_mem_ball htau
    have : ‖fixedPointOnDisc tau‖ < (4 / 5 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hball
    exact this.trans (by norm_num)
  have hcClosed : ‖fixedPointOnDisc tau‖ ≤ (4 / 5 : ℝ) := by
    have hball := fixedPointOnDisc_mem_ball htau
    have hs : ‖fixedPointOnDisc tau‖ < (4 / 5 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hball
    exact hs.le
  have hden := one_sub_tau_entropyDeriv_ne htau hcClosed
  have heq : fixedPointOnDisc =ᶠ[𝓝 tau]
      fun sigma => sigma * entropyExt (fixedPointOnDisc sigma) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds htau]
      with sigma hsigma
    exact fixedPointOnDisc_fixed hsigma
  have hd := contact_deriv_eq hbase hc heq hden
  exact hbase.congr_deriv hd

/-- The cubic quotient, filled at the removable origin by the already
constructed local analytic remainder. -/
noncomputable def cubicRemainderOnDisc (tau : ℂ) : ℂ :=
  if tau = 0 then cubicRemainder 0 else
    (fixedPointOnDisc tau - (Real.log 2 : ℂ) * tau) / tau ^ 3

private theorem eventually_fixedPointOnDisc_eq_contactGerm :
    fixedPointOnDisc =ᶠ[𝓝 (0 : ℂ)] contactGerm := by
  have hsmall : ∀ᶠ tau in 𝓝 (0 : ℂ), ‖tau‖ < (7 / 10 : ℝ) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  filter_upwards [hsmall, eventually_contactGerm_eq_fixedPoint]
    with tau htau heq
  rw [fixedPointOnDisc_eq htau]
  exact (heq htau.le).symm

private theorem eventually_cubicRemainderOnDisc_eq_local :
    cubicRemainderOnDisc =ᶠ[𝓝 (0 : ℂ)] cubicRemainder := by
  filter_upwards [eventually_fixedPointOnDisc_eq_contactGerm,
      eventually_contactGerm_cubicRemainder] with tau hcontact hcubic
  by_cases htau : tau = 0
  · simp [cubicRemainderOnDisc, htau]
  · unfold cubicRemainderOnDisc
    rw [if_neg htau, hcontact, hcubic]
    field_simp [htau]
    ring

/-- The cubic remainder extends holomorphically across the full explicit
open `7/10` disc. -/
theorem analyticAt_cubicRemainderOnDisc {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    AnalyticAt ℂ cubicRemainderOnDisc tau := by
  by_cases htau0 : tau = 0
  · subst tau
    exact analyticAt_cubicRemainder.congr
      eventually_cubicRemainderOnDisc_eq_local.symm
  · have hquot : AnalyticAt ℂ
        (fun z => (fixedPointOnDisc z - (Real.log 2 : ℂ) * z) / z ^ 3) tau := by
      exact ((analyticAt_fixedPointOnDisc htau).sub
        (analyticAt_const.mul analyticAt_id)).div
          (analyticAt_id.pow 3) (pow_ne_zero 3 htau0)
    have heq : cubicRemainderOnDisc =ᶠ[𝓝 tau]
        fun z => (fixedPointOnDisc z - (Real.log 2 : ℂ) * z) / z ^ 3 := by
      filter_upwards [continuousAt_id.eventually_ne htau0] with z hz
      change z ≠ 0 at hz
      simp [cubicRemainderOnDisc, hz]
    exact hquot.congr heq.symm

theorem analyticOnNhd_cubicRemainderOnDisc :
    AnalyticOnNhd ℂ cubicRemainderOnDisc (Metric.ball 0 (7 / 10 : ℝ)) := by
  intro tau htau
  apply analyticAt_cubicRemainderOnDisc
  simpa only [Metric.mem_ball, dist_zero_right] using htau

/-- Uniform explicit bound for the analytic cubic remainder on the entire
open parameter disc. -/
theorem norm_cubicRemainderOnDisc_le {tau : ℂ}
    (htau : ‖tau‖ < (7 / 10 : ℝ)) :
    ‖cubicRemainderOnDisc tau‖ ≤ (15 / 4 : ℝ) := by
  by_cases htau0 : tau = 0
  · simpa [cubicRemainderOnDisc, htau0] using norm_cubicRemainder_zero_le
  · rw [cubicRemainderOnDisc, if_neg htau0, norm_div, norm_pow]
    have hbound := norm_fixedPoint_sub_linear_le htau.le
    rw [← fixedPointOnDisc_eq htau] at hbound
    have hpos : 0 < ‖tau‖ ^ 3 := pow_pos (norm_pos_iff.mpr htau0) _
    rw [div_le_iff₀ hpos]
    simpa only [mul_comm] using hbound

end GeneralCK.Reflection.ComplexGlobalAnalytic

end


