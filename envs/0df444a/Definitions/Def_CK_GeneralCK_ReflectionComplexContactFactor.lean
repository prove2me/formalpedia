-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexContactFactor
-- name    : CK_GeneralCK_ReflectionComplexContactFactor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:17:37.407957+00:00
-- url     : https://prove2.me/theorems/4cd13548-5f7f-4fb2-a59c-9c5d6318a98c
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexContactFactor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexContactFactor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexContactFactor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexContactFactor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexContactFactor.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexContactGerm
import Mathlib.Analysis.Analytic.Order

-- ===== source module GeneralCK.ReflectionComplexContactFactor =====
section

/-!
# Oddness and analytic factorization of the complex contact germ

The entropy is even, hence uniqueness makes the complex contact point odd in
the parameter.  We then remove its simple zero at the origin and expose an
analytic factor with constant term `log 2`.
-/

namespace GeneralCK.Reflection.ComplexContactFactor

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint ComplexContactGerm

/-- Exact even symmetry of the principal-log entropy extension. -/
theorem entropyExt_neg (c : ℂ) : entropyExt (-c) = entropyExt c := by
  unfold entropyExt
  rw [show 1 + -c = 1 - c by ring, show 1 - -c = 1 + c by ring]
  ring

/-- The chosen Banach fixed point is odd in the complex parameter. -/
theorem fixedPoint_neg {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ))
    (htau_neg : ‖-tau‖ ≤ (7 / 10 : ℝ)) :
    fixedPoint (-tau) htau_neg = -fixedPoint tau htau := by
  have hc := fixedPoint_mem_ball htau
  have hcNeg : -fixedPoint tau htau ∈ Metric.closedBall 0 (4 / 5 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using
      Metric.ball_subset_closedBall hc
  have hfix := fixedPoint_isFixedPt htau
  have hfixNeg : IsFixedPt
      (ComplexDiscElementary.contactMap entropyExt (-tau)) (-fixedPoint tau htau) := by
    change IsFixedPt (ComplexDiscElementary.contactMap entropyExt tau)
      (fixedPoint tau htau) at hfix
    unfold IsFixedPt ComplexDiscElementary.contactMap at hfix ⊢
    rw [entropyExt_neg]
    simpa using congrArg Neg.neg hfix
  exact (eq_fixedPoint htau_neg hcNeg hfixNeg).symm

/-- Locally, the holomorphic contact germ is odd. -/
theorem eventually_contactGerm_neg :
    ∀ᶠ tau in 𝓝 (0 : ℂ), contactGerm (-tau) = -contactGerm tau := by
  have hpos := eventually_contactGerm_eq_fixedPoint
  have hneg : ∀ᶠ tau in 𝓝 (0 : ℂ),
      ∀ htau : ‖-tau‖ ≤ (7 / 10 : ℝ),
        contactGerm (-tau) = fixedPoint (-tau) htau := by
    have htend : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.tendsto (0 : ℂ)
    exact htend hpos
  have hnorm : ∀ᶠ tau in 𝓝 (0 : ℂ), ‖tau‖ ≤ (7 / 10 : ℝ) := by
    have hball : Metric.ball (0 : ℂ) (7 / 10 : ℝ) ∈ 𝓝 0 :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with tau htau
    have hnorm : ‖tau‖ < (7 / 10 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using htau
    exact hnorm.le
  filter_upwards [hpos, hneg, hnorm] with tau hpos hneg htau
  have htauNeg : ‖-tau‖ ≤ (7 / 10 : ℝ) := by simpa using htau
  rw [hneg htauNeg, fixedPoint_neg htau htauNeg, ← hpos htau]

/-- Existence of an analytic factor after removing the simple zero of the
contact germ. -/
theorem exists_contactFactor :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      contactGerm =ᶠ[𝓝 0] fun tau => tau * q tau := by
  obtain ⟨q, hq, hfac⟩ :=
    analyticAt_contactGerm.exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨q, hq, ?_⟩
  filter_upwards [hfac] with tau htau
  simpa [contactGerm_zero] using htau

/-- A chosen analytic cofactor of the contact germ. -/
noncomputable def contactFactor : ℂ → ℂ := Classical.choose exists_contactFactor

theorem analyticAt_contactFactor : AnalyticAt ℂ contactFactor 0 :=
  (Classical.choose_spec exists_contactFactor).1

theorem eventually_contactGerm_eq_mul_contactFactor :
    contactGerm =ᶠ[𝓝 0] fun tau => tau * contactFactor tau :=
  (Classical.choose_spec exists_contactFactor).2

/-- The cofactor's constant term is the linear coefficient of the contact
germ, namely `log 2`. -/
theorem contactFactor_zero : contactFactor 0 = (Real.log 2 : ℂ) := by
  have hright := (hasDerivAt_id (𝕜 := ℂ) 0).mul
    analyticAt_contactFactor.differentiableAt.hasDerivAt
  have hcongr := hright.congr_of_eventuallyEq
    eventually_contactGerm_eq_mul_contactFactor
  have hright' : HasDerivAt contactGerm (contactFactor 0) 0 := by
    simpa using hcongr
  exact (hasDerivAt_contactGerm_zero.unique hright').symm

/-- The analytic cofactor is locally even. -/
theorem eventually_contactFactor_neg :
    ∀ᶠ tau in 𝓝 (0 : ℂ), contactFactor (-tau) = contactFactor tau := by
  have hfac := eventually_contactGerm_eq_mul_contactFactor
  have hfacNeg : ∀ᶠ tau in 𝓝 (0 : ℂ),
      contactGerm (-tau) = (-tau) * contactFactor (-tau) := by
    have htend : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.tendsto (0 : ℂ)
    exact htend hfac
  filter_upwards [eventually_contactGerm_neg, hfac, hfacNeg]
    with tau hodd hfac hfacNeg
  by_cases htau : tau = 0
  · simp [htau]
  · rw [hfacNeg, hfac] at hodd
    apply neg_injective
    apply (mul_left_cancel₀ htau)
    simpa using hodd

/-- The cofactor itself satisfies the entropy recursion locally. -/
theorem eventually_contactFactor_eq_entropyExt :
    ∀ᶠ tau in 𝓝 (0 : ℂ),
      contactFactor tau = entropyExt (tau * contactFactor tau) := by
  filter_upwards [eventually_contactGerm_fixed,
      eventually_contactGerm_eq_mul_contactFactor] with tau hfix hfac
  by_cases htau : tau = 0
  · simp [htau, contactFactor_zero, entropyExt_zero]
  · rw [hfac] at hfix
    exact (mul_left_cancel₀ htau) hfix

/-- Evenness forces the linear coefficient of the cofactor to vanish. -/
theorem hasDerivAt_contactFactor_zero : HasDerivAt contactFactor 0 0 := by
  let q' : ℂ := deriv contactFactor 0
  have hq : HasDerivAt contactFactor q' 0 :=
    analyticAt_contactFactor.differentiableAt.hasDerivAt
  have hneg := HasDerivAt.comp_of_eq (x := (0 : ℂ)) hq
    ((hasDerivAt_id (𝕜 := ℂ) 0).neg) (by simp)
  have heven : contactFactor =ᶠ[𝓝 (0 : ℂ)]
      (contactFactor ∘ fun z : ℂ => -z) :=
    eventually_contactFactor_neg.mono fun _ hz => hz.symm
  have hneg' : HasDerivAt contactFactor (-q') 0 := by
    simpa only [q', neg_zero, mul_neg, mul_one] using
      hneg.congr_of_eventuallyEq heven
  have hcoeff := hq.unique hneg'
  have hqzero : q' = 0 := by
    have htwo : (2 : ℂ) * q' = 0 := by
      linear_combination hcoeff
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa only [hqzero] using hq

/-- Cubic analytic factorization of the contact germ.  This is the direct
Taylor/Cauchy interface: all terms after the known linear coefficient are
absorbed into an analytic multiple of `tau^3`. -/
theorem exists_contactGerm_cubicRemainder :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      contactGerm =ᶠ[𝓝 0]
        fun tau => (Real.log 2 : ℂ) * tau + tau ^ 3 * r tau := by
  obtain ⟨r, hrAnalytic, hr⟩ :=
    analyticAt_contactFactor.exists_eventuallyEq_sum_add_pow_mul 2
  have hqderiv : deriv contactFactor 0 = 0 :=
    hasDerivAt_contactFactor_zero.deriv
  refine ⟨r, hrAnalytic, ?_⟩
  filter_upwards [eventually_contactGerm_eq_mul_contactFactor, hr]
    with tau hfac hr
  rw [hfac, hr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_smul,
    Nat.factorial_one, pow_one, iteratedDeriv_zero, contactFactor_zero,
    iteratedDeriv_one, hqderiv, smul_zero, add_zero]
  ring

end GeneralCK.Reflection.ComplexContactFactor

end


