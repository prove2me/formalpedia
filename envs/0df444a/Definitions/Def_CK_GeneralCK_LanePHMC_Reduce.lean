-- Prove2me | Definitions.Def_CK_GeneralCK_LanePHMC_Reduce
-- name    : CK_GeneralCK_LanePHMC_Reduce
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:46:42.216261+00:00
-- url     : https://prove2.me/theorems/cd999780-0df7-44ec-a08a-a69b871daf81
-- title:
--   Courtade–Kumar proof module `GeneralCK.LanePHMC.Reduce` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LanePHMC.Reduce` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LanePHMC.Reduce` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LanePHMC.Reduce (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LanePHMC/Reduce.lean)

import Definitions.Def_CK_GeneralCK_PureGapAnalyticClosure
import Definitions.Def_CK_GeneralCK_PureGapHalfMeanAnalytic
import Definitions.Def_CK_GeneralCK_PureGapHalfMeanOwner
import Definitions.Def_CK_GeneralCK_PureGapE8HalfMean
import Definitions.Def_CK_GeneralCK_PureGapE8Inverse

-- ===== source module GeneralCK.LanePHMC.Reduce =====
section
/-
Lane P-HMC — THE REDUCTION.  Eliminate `e8Q` from the remaining obligation.

WHY THIS EXISTS.
`PureGapD0CompactOwner` (kernel-printed, Probe01 log line 12-13) is
    ∀ s ∈ Set.Icc (2/25) (63/20), s ∈ e8SlopeRange → 2*s ∈ e8SlopeRange →
      0 < e8D0 e8Q pureGapQ0 s
and `e8D0 Q q0 s = deriv Q s * Q (2*s) - 2*q0*(Q (2*s) - Q s)` evaluates `Q = e8Q` AT `2*s`.
`e8Q` is `Classical.choose` (PureGapE8Inverse.lean:59-62), so its VALUES come only from the
explicit-coefficient remainder, whose radius is hardcoded at `E8OriginRemainder.lean:64
def radius : ℚ := 2/25`.  R-B1 measured that this caps the route at `s ≤ 1/25`, HALF the
already-proved region — which is why that lane stopped.

THE OBSERVATION.  `e8Q`'s value is FREE along the image of `e8Theta`:
    e8Q_e8Theta : 0 < x → e8Q (e8Theta x) = x          -- kernel-printed, Probe01 line 22
so if the obligation is reparametrised by the contact coordinate `x` rather than the slope
`s`, `e8Q` does not occur in it and the hardcoded radius bounds nothing that remains.

WHAT THIS FILE PROVES.  Exactly the reparametrisation, and nothing else:
    HalfMeanSlopeGapOnCompact → PureGapD0CompactOwner
`HalfMeanSlopeGapOnCompact` mentions only `e8Theta` and `deriv e8Theta`.

🔴 THIS IS NOT CLOSURE.  It is a REDUCTION: it replaces one unproved statement with another.
It is worth doing only because the new one is (a) free of `e8Q` and (b) MEASURED to be far
better conditioned — `M/x^4` has dynamic range 1.6196 over the compact interval versus 13.89
for the best previously known factorisation and 1.31e9 raw
(`~/gck_lanes/P-HMC/logs/phmc_xw_route.log`, rc=0, four controls fired).
`HalfMeanSlopeGapOnCompact` remains UNPROVED and I claim no owner for it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.LanePHMC

open Set

/-- The obligation with `e8Q` eliminated.  `x` is the contact coordinate and `w` its
doubling partner: `e8Theta w = 2 * e8Theta x`.  Only `e8Theta` and `deriv e8Theta` occur. -/
def HalfMeanSlopeGapOnCompact : Prop :=
  ∀ x w : ℝ, 0 < x → 0 < w →
    e8Theta w = 2 * e8Theta x →
    e8Theta x ∈ Icc (2 / 25 : ℝ) (63 / 20) →
    2 * deriv e8Theta x * (1 - x / w) < pureGapTheta0

/-- The exact converse of `halfMean_slope_lt_of_D0_pos`.  That lemma is stated one way only,
but every multiplier in its proof is strictly positive, so the implication reverses.  This is
the algebraic half of the reparametrisation. -/
theorem D0_expr_pos_of_slope_lt {x y theta0 thetaX : ℝ}
    (htheta0 : 0 < theta0) (hthetaX : 0 < thetaX) (hy : 0 < y)
    (hgap : 2 * thetaX * (1 - x / y) < theta0) :
    0 < thetaX⁻¹ * y - 2 * theta0⁻¹ * (y - x) := by
  have hscale : 0 < theta0 * thetaX / y := by positivity
  have hnum : 0 < theta0 - 2 * thetaX * (1 - x / y) := by linarith [hgap]
  have hrewrite :
      thetaX⁻¹ * y - 2 * theta0⁻¹ * (y - x) =
        (theta0 - 2 * thetaX * (1 - x / y)) / (theta0 * thetaX / y) := by
    field_simp <;> ring
  rw [hrewrite]
  exact div_pos hnum hscale

/-- **THE REDUCTION.**  The compact `D₀` owner follows from the `e8Q`-free slope gap. -/
theorem pureGapD0CompactOwner_of_slopeGap
    (hgap : HalfMeanSlopeGapOnCompact) : PureGapD0CompactOwner := by
  intro s hs hsRange h2sRange
  -- the two contact coordinates; both positive, and BOTH values of `e8Q` are pinned by
  -- corpus theorems rather than by any coefficient expansion
  have hx : 0 < e8Q s := e8Q_pos hsRange
  have hw : 0 < e8Q (2 * s) := e8Q_pos h2sRange
  have hthx : e8Theta (e8Q s) = s := e8Theta_e8Q hsRange
  have hthw : e8Theta (e8Q (2 * s)) = 2 * s := e8Theta_e8Q h2sRange
  -- the doubling constraint, in the contact coordinates
  have hcouple : e8Theta (e8Q (2 * s)) = 2 * e8Theta (e8Q s) := by
    rw [hthw, hthx]
  -- the interval condition, transported through `e8Theta (e8Q s) = s`
  have hmem : e8Theta (e8Q s) ∈ Icc (2 / 25 : ℝ) (63 / 20) := by
    rw [hthx]; exact hs
  have hslope := hgap (e8Q s) (e8Q (2 * s)) hx hw hcouple hmem
  -- convert the slope gap back into positivity of the `D₀` expression
  have hthetaX : 0 < deriv e8Theta (e8Q s) := deriv_e8Theta_pos hx
  have hD := D0_expr_pos_of_slope_lt pureGapTheta0_pos hthetaX hw hslope
  rw [e8D0_eq_inverse_formula hsRange, pureGapQ0_eq_inv]
  exact hD

#check @HalfMeanSlopeGapOnCompact
#check @D0_expr_pos_of_slope_lt
#check @pureGapD0CompactOwner_of_slopeGap
#print axioms D0_expr_pos_of_slope_lt
#print axioms pureGapD0CompactOwner_of_slopeGap

/-- Positive control: must appear in the log, so an empty log cannot read as success. -/
theorem phmc_reduce_positive_control : (3 : Nat) * 3 = 9 := by norm_num
#print axioms phmc_reduce_positive_control

end GeneralCK.LanePHMC

end


