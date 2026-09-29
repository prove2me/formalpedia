-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexContactGerm
-- name    : CK_GeneralCK_ReflectionComplexContactGerm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:07:49.209259+00:00
-- url     : https://prove2.me/theorems/dbda4f3a-57ce-4e16-b2c4-e4d7065ccac3
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexContactGerm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexContactGerm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexContactGerm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexContactGerm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexContactGerm.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexFixedPoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.ReflectionComplexContactGerm =====
section

/-!
# Holomorphic germ of the complex contact point

Near zero, the contact equation can be inverted in one complex variable:
`tau = c / entropyExt c`.  This gives a holomorphic germ directly from the
analytic inverse-function theorem and identifies it locally with the Banach
fixed point constructed on the quantitative disc.
-/

namespace GeneralCK.Reflection.ComplexContactGerm

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint






















private theorem entropyExt_zero_ne : entropyExt 0 ≠ 0 := by
  rw [entropyExt_zero]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))


























private theorem deriv_slopeMap_zero : deriv slopeMap 0 = (Real.log 2 : ℂ)⁻¹ :=
  hasDerivAt_slopeMap_zero.deriv

private theorem deriv_slopeMap_ne : deriv slopeMap 0 ≠ 0 := by
  rw [deriv_slopeMap_zero]
  exact inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num))))












/-- The contact germ is genuinely complex analytic at the origin. -/
theorem analyticAt_contactGerm : AnalyticAt ℂ contactGerm 0 := by
  simpa [contactGerm] using
    analyticAt_slopeMap.analyticAt_localInverse deriv_slopeMap_ne

/-- Its linear coefficient is `log 2`. -/
theorem hasDerivAt_contactGerm_zero :
    HasDerivAt contactGerm (Real.log 2 : ℂ) 0 := by
  have h := analyticAt_slopeMap.hasStrictDerivAt.to_localInverse deriv_slopeMap_ne
  simpa [contactGerm, deriv_slopeMap_zero] using h.hasDerivAt

/-- Reusable derivative formula for any differentiable local solution of the
complex contact equation. -/
theorem contact_deriv_eq {phi : ℂ → ℂ} {tau phi' : ℂ}
    (hphi : HasDerivAt phi phi' tau)
    (hdisc : ‖phi tau‖ < 1)
    (heq : phi =ᶠ[𝓝 tau] fun z => z * entropyExt (phi z))
    (hden : 1 - tau * entropyDeriv (phi tau) ≠ 0) :
    phi' = entropyExt (phi tau) /
      (1 - tau * entropyDeriv (phi tau)) := by
  have hEntropy := (hasDerivAt_entropyExt hdisc).comp tau hphi
  have hRight := (hasDerivAt_id tau).mul hEntropy
  have hRight' : HasDerivAt phi
      (1 * entropyExt (phi tau) + tau * (entropyDeriv (phi tau) * phi')) tau :=
    hRight.congr_of_eventuallyEq heq
  have hd := hphi.unique hRight'
  apply (eq_div_iff hden).2
  calc
    phi' * (1 - tau * entropyDeriv (phi tau)) =
        phi' - tau * (entropyDeriv (phi tau) * phi') := by ring
    _ = entropyExt (phi tau) := by
      nth_rw 1 [hd]
      ring

/-- Locally, the germ satisfies the exact complex entropy contact equation. -/
theorem eventually_contactGerm_fixed :
    ∀ᶠ tau in 𝓝 (0 : ℂ),
      contactGerm tau = tau * entropyExt (contactGerm tau) := by
  have hinv := analyticAt_slopeMap.hasStrictDerivAt.eventually_right_inverse
    deriv_slopeMap_ne
  simp only [slopeMap_zero] at hinv
  have hcont : ContinuousAt (fun tau => entropyExt (contactGerm tau)) 0 :=
    (analyticAt_entropyExt (c := 0) (by norm_num)).continuousAt.comp_of_eq
      analyticAt_contactGerm.continuousAt contactGerm_zero
  have hne : ∀ᶠ tau in 𝓝 (0 : ℂ), entropyExt (contactGerm tau) ≠ 0 := by
    apply hcont.eventually_ne
    simpa only [contactGerm_zero] using entropyExt_zero_ne
  filter_upwards [hinv, hne] with tau htau hE
  unfold slopeMap at htau
  exact (div_eq_iff hE).mp htau

/-- In a neighborhood of zero the holomorphic germ stays in the open
`4/5` contact disc. -/
theorem eventually_contactGerm_mem_ball :
    ∀ᶠ tau in 𝓝 (0 : ℂ), contactGerm tau ∈ Metric.ball 0 (4 / 5 : ℝ) := by
  apply analyticAt_contactGerm.continuousAt
  simpa using Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 4 / 5)

/-- Local compatibility with the quantitatively constructed Banach fixed
point.  The conclusion is independent of the proof of the norm bound. -/
theorem eventually_contactGerm_eq_fixedPoint :
    ∀ᶠ tau in 𝓝 (0 : ℂ), ∀ htau : ‖tau‖ ≤ (7 / 10 : ℝ),
      contactGerm tau = fixedPoint tau htau := by
  filter_upwards [eventually_contactGerm_fixed, eventually_contactGerm_mem_ball]
    with tau hfix hmem
  intro htau
  apply eq_fixedPoint htau (Metric.ball_subset_closedBall hmem)
  exact hfix.symm

end GeneralCK.Reflection.ComplexContactGerm

end


