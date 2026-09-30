-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QuantitativeBranchBridge
-- name    : CK_GeneralCK_Certificates_E8QuantitativeBranchBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:05:18.486672+00:00
-- url     : https://prove2.me/theorems/63c78c36-f684-4c36-a474-b12ffa0bbbe1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QuantitativeBranchBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QuantitativeBranchBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QuantitativeBranchBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QuantitativeBranchBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QuantitativeBranchBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8CauchyTailBound
import Definitions.Def_CK_GeneralCK_ReflectionComplexGlobalAnalytic

-- ===== source module GeneralCK.Certificates.E8QuantitativeBranchBridge =====
section

/-!
# Quantitative inverse-branch interface for the E8 origin chart

The existing contraction constructs the contact bias `c` holomorphically as
a function of `tau = c / entropyExt c` on `‖tau‖ < 7/10`.  Since
`xParam c = (log 2)/2 * tau`, it remains to invert the scalar holomorphic map
`tau ↦ thetaParam (fixedPointOnDisc tau)` on a sufficiently large `y` disc.

This file states precisely the quantitative data required of that last
inverse and proves that they imply both the intended local germ and the full
numerical Cauchy bound used by the origin checker.
-/

namespace GeneralCK.Certificates.E8QuantitativeBranchBridge

open Metric Set Filter Function
open E8AnalyticGerm
open E8OriginRemainder
open Reflection.ComplexContactGerm

/-- The outer `y` radius is chosen so that every point with norm at most
`4/25` admits a unit Cauchy circle inside it. -/
noncomputable def yOuterRadius : ℝ := 29 / 25

/-- Quantitative data still needed from inversion of
`thetaParam ∘ fixedPointOnDisc`.  `agreesNear` identifies the selected
inverse with the `tau = slopeMap c` parametrization near the origin. -/
structure TauDiscInverseCertificate where
  tauBranch : ℂ → ℂ
  diffCont : DiffContOnCl ℂ tauBranch (ball 0 yOuterRadius)
  norm_le : ∀ y ∈ closedBall (0 : ℂ) yOuterRadius,
    ‖tauBranch y‖ ≤ (7 / 10 : ℝ)
  agreesNear : ∀ᶠ c in nhds (0 : ℂ), tauBranch (thetaParam c) = slopeMap c

/-- The contact-coordinate formula is exactly linear in `tau = c/E(c)`. -/
theorem xParam_eq_logTwo_half_mul_slopeMap (c : ℂ) :
    xParam c = (Real.log 2 : ℂ) / 2 * slopeMap c := by
  unfold xParam slopeMap
  ring

/-- The quantitative inverse branch, expressed in the manuscript's `Q`
coordinate. -/
noncomputable def qDisc (cert : TauDiscInverseCertificate) (y : ℂ) : ℂ :=
  (Real.log 2 : ℂ) / 2 * cert.tauBranch y

theorem qDisc_diffCont (cert : TauDiscInverseCertificate) :
    DiffContOnCl ℂ (qDisc cert) (ball 0 yOuterRadius) := by
  have h := cert.diffCont.const_smul ((Real.log 2 : ℂ) / 2)
  convert h using 1
  ext y
  simp [qDisc, smul_eq_mul]

/-- The contraction disc itself supplies a simple uniform bound for `Q`.
The use of `7/20` is deliberately rational and conservative. -/
theorem qDisc_norm_le (cert : TauDiscInverseCertificate) :
    ∀ y ∈ closedBall (0 : ℂ) yOuterRadius, ‖qDisc cert y‖ ≤ (7 / 20 : ℝ) := by
  intro y hy
  have hlog : ‖(Real.log 2 : ℂ)‖ ≤ (1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by norm_num))]
    exact (Real.log_two_lt_d9.trans (by norm_num)).le
  rw [qDisc, norm_mul, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  calc
    ‖(Real.log 2 : ℂ)‖ / 2 * ‖cert.tauBranch y‖ ≤
        1 / 2 * (7 / 10 : ℝ) := by gcongr; exact cert.norm_le y hy
    _ = 7 / 20 := by norm_num

/-- Any quantitative branch satisfying the explicit inverse agreement is
the same analytic germ as the pre-existing nonquantitative `qGerm`. -/
theorem qDisc_eventuallyEq_qGerm (cert : TauDiscInverseCertificate) :
    qDisc cert =ᶠ[nhds (0 : ℂ)] qGerm := by
  have hbias : Tendsto biasGerm (nhds (0 : ℂ)) (nhds (0 : ℂ)) := by
    have hc := analyticAt_biasGerm.continuousAt
    change Tendsto biasGerm (nhds (0 : ℂ)) (nhds (biasGerm 0)) at hc
    simpa only [biasGerm_zero] using hc
  have hpull : ∀ᶠ y in nhds (0 : ℂ),
      cert.tauBranch (thetaParam (biasGerm y)) = slopeMap (biasGerm y) :=
    hbias.eventually cert.agreesNear
  filter_upwards [eventually_thetaParam_biasGerm, hpull] with y hright hagree
  have htau : cert.tauBranch y = slopeMap (biasGerm y) := by
    calc
      cert.tauBranch y = cert.tauBranch (thetaParam (biasGerm y)) :=
        congrArg cert.tauBranch hright.symm
      _ = slopeMap (biasGerm y) := hagree
  rw [qDisc, qGerm, xParam_eq_logTwo_half_mul_slopeMap, htau]

/-- Consequently every Taylor coefficient of the quantitative branch is
the already-defined coefficient of `qGerm`. -/
theorem iteratedDeriv_qDisc_zero (cert : TauDiscInverseCertificate) (n : ℕ) :
    iteratedDeriv n (qDisc cert) 0 = iteratedDeriv n qGerm 0 :=
  Filter.EventuallyEq.iteratedDeriv_eq n (qDisc_eventuallyEq_qGerm cert)

/-- All scalar Cauchy arithmetic is discharged here.  The sole remaining
object-level input is `TauDiscInverseCertificate`; no numerical derivative,
Taylor coefficient, or remainder premise remains. -/
theorem qDisc_seventeenth_derivative_le_source_bound
    (cert : TauDiscInverseCertificate) :
    ∀ y ∈ closedBall (0 : ℂ) (4 / 25 : ℝ),
      ‖iteratedDeriv 17 (qDisc cert) y‖ ≤ (q17AbsBound : ℝ) := by
  intro y hy
  have h := E8CauchyTailBound.norm_iteratedDeriv_le_on_inner_closedBall
    (f := qDisc cert) (outer := yOuterRadius) (inner := (4 / 25 : ℝ))
    (rho := 1) (C := (7 / 20 : ℝ)) 17 (by norm_num)
    (by norm_num [yOuterRadius]) (qDisc_diffCont cert) (qDisc_norm_le cert) y hy
  exact h.trans (by norm_num [q17AbsBound])

/-- The order-18 coefficient of the original germ inherits the quantitative
branch's explicit Cauchy enclosure. -/
theorem norm_qTaylorCoeff_eighteen_le (cert : TauDiscInverseCertificate) :
    ‖qTaylorCoeff 18‖ ≤ (7 / 20 : ℝ) / yOuterRadius ^ 18 := by
  have hbranch := E8CauchyTailBound.norm_iteratedDeriv_div_factorial_le
    18 (show 0 < yOuterRadius by norm_num [yOuterRadius])
    (qDisc_diffCont cert)
    (fun z hz => qDisc_norm_le cert z (sphere_subset_closedBall hz))
  unfold qTaylorCoeff
  rw [← iteratedDeriv_qDisc_zero cert 18]
  exact hbranch

end GeneralCK.Certificates.E8QuantitativeBranchBridge

end


