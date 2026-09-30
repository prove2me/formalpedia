-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8LargeSLogConvex
-- name    : CK_GeneralCK_PureGapE8LargeSLogConvex
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:16:03.107233+00:00
-- url     : https://prove2.me/theorems/d47e348b-07b1-42ff-955e-e917ef8264b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8LargeSLogConvex` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8LargeSLogConvex` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8LargeSLogConvex` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8LargeSLogConvex (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8LargeSLogConvex.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8LargeSShift
import Mathlib.Analysis.Convex.Deriv

-- ===== source module GeneralCK.PureGapE8LargeSLogConvex =====
section

/-!
# One remaining analytic field for the large-s E8 owner

The scalar shift is now certified.  Local oddness forces the second derivative
of the regular inverse to vanish at the origin.  Consequently convexity of
its log derivative also supplies the monotonicity field of `E8LargeSStructure`.
The final theorem is conditional only on that log-convexity assertion.
-/

namespace GeneralCK
open Set Filter E8AnalyticGerm

theorem e8RegularQ_eventually_odd :
    (fun y : ℝ => e8RegularQ (-y)) =ᶠ[nhds 0] (fun y => -e8RegularQ y) := by
  have hneg : Tendsto (fun y : ℝ => -y) (nhds 0) (nhds 0) := by
    simpa using continuous_neg.tendsto (0 : ℝ)
  have hcast : Tendsto (fun y : ℝ => (y : ℂ)) (nhds 0) (nhds 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [e8RegularQ_eventually_eq_germ,
    hneg e8RegularQ_eventually_eq_germ, hcast eventually_qGerm_neg] with y hy hny hodd
  rw [hny, hy, Complex.ofReal_neg, hodd, Complex.neg_re]

theorem deriv2_e8RegularQ_zero : deriv (deriv e8RegularQ) 0 = 0 := by
  have h := e8RegularQ_eventually_odd.iteratedDeriv_eq 2
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at h
  norm_num only [neg_zero, even_two.neg_one_pow, one_smul,
    iteratedDeriv_succ, iteratedDeriv_zero] at h
  linarith

theorem hasDerivAt_log_deriv_e8RegularQ_zero :
    HasDerivAt (fun y => Real.log (deriv e8RegularQ y)) 0 0 := by
  have hd : DifferentiableAt ℝ (deriv e8RegularQ) 0 :=
    (e8RegularQ_contDiffAt_zero.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hp := deriv_e8RegularQ_pos (y := 0) (Or.inl rfl)
  simpa only [deriv2_e8RegularQ_zero, zero_div] using hd.hasDerivAt.log hp.ne'

theorem e8RegularQ_derivative_mono_of_log_convex {x : ℝ}
    (hx : x ∈ e8SlopeRange)
    (hc : ConvexOn ℝ (Icc 0 x) (fun y => Real.log (deriv e8RegularQ y))) :
    MonotoneOn (deriv e8RegularQ) (Icc 0 x) := by
  have hp (y : ℝ) (hy : y ∈ Icc 0 x) : 0 < deriv e8RegularQ y := by
    rcases hy.1.eq_or_lt with rfl | hpos
    · exact deriv_e8RegularQ_pos (Or.inl rfl)
    · exact deriv_e8RegularQ_pos (Or.inr (e8SlopeRange_downward hx hpos hy.2))
  have hd (y : ℝ) (hy : y ∈ Icc 0 x) :
      DifferentiableAt ℝ (fun z => Real.log (deriv e8RegularQ z)) y := by
    have hq := e8RegularQ_contDiffAt_interval hx hy
    exact (hq.derivWithin (m := 1) (by norm_num)).differentiableAt_one.log (hp y hy).ne'
  have hmono : MonotoneOn (fun y => Real.log (deriv e8RegularQ y)) (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (hd y (interior_subset hy)).differentiableWithinAt
    · intro y hy
      have hh := hc.monotoneOn_deriv hd
        (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, (e8SlopeRange_subset_pos hx).le⟩)
        (interior_subset hy) (interior_subset hy).1
      rwa [hasDerivAt_log_deriv_e8RegularQ_zero.deriv] at hh
  intro a ha b hb hab
  exact (Real.log_le_log_iff (hp a ha) (hp b hb)).mp (hmono ha hb hab)

/-- Only the actual log-convexity assertion remains in the large-s structure. -/
theorem e8LargeSStructure_of_log_derivative_convex
    (hc : ∀ x ∈ e8SlopeRange,
      ConvexOn ℝ (Icc 0 x) (fun y => Real.log (deriv e8RegularQ y))) :
    E8LargeSStructure where
  derivative_mono := fun x hx => e8RegularQ_derivative_mono_of_log_convex hx (hc x hx)
  log_derivative_convex := hc
  shift := Certificates.E8LargeSShift.shift

theorem e8_largeS_of_log_derivative_convex
    (hc : ∀ x ∈ e8SlopeRange,
      ConvexOn ℝ (Icc 0 x) (fun y => Real.log (deriv e8RegularQ y))) :
    E8PositiveOn (fun s _ => (63/20 : ℝ) ≤ s) :=
  e8_largeS_of_structure (e8LargeSStructure_of_log_derivative_convex hc)

#print axioms e8RegularQ_eventually_odd
#print axioms deriv2_e8RegularQ_zero
#print axioms hasDerivAt_log_deriv_e8RegularQ_zero
#print axioms e8RegularQ_derivative_mono_of_log_convex
#print axioms e8LargeSStructure_of_log_derivative_convex
#print axioms e8_largeS_of_log_derivative_convex

end GeneralCK

end


