-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8RegularizedInverse
-- name    : CK_GeneralCK_PureGapE8RegularizedInverse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:14:37.584808+00:00
-- url     : https://prove2.me/theorems/9dcf2f0d-b26d-4e29-b463-f77f9721cb0e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8RegularizedInverse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8RegularizedInverse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8RegularizedInverse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8RegularizedInverse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8RegularizedInverse.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8PositiveAxisGermJet
import Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8RegularizedInverse =====
section

/-!
# A regular real inverse for the non-origin E8 certificates

The totalized `e8Q` vanishes at negative arguments and is not differentiable
at zero.  Axis certificates must instead differentiate its analytic extension.
This module constructs that extension and proves fourth-order regularity on
every nonnegative interval ending in the positive slope range.  All values
used by equation (8) agree with the original concrete inverse.
-/

namespace GeneralCK

open Set Filter
open Certificates Certificates.E8PositiveAxisGermJet
open Certificates.E8InverseJet5Bridge E8AnalyticGerm





theorem e8RegularQ_eq_e8Q {y : ℝ} (hy : 0 ≤ y) :
    e8RegularQ y = e8Q y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [e8RegularQ, e8Q_zero]
  · simp [e8RegularQ, hy]




theorem e8RegularQ_eventually_eq_germ :
    e8RegularQ =ᶠ[nhds (0 : ℝ)] (fun y => (qGerm (y : ℂ)).re) := by
  have h := eventually_qGerm_eq_e8Q
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with y hy
  by_cases hpos : 0 < y
  · simpa [e8RegularQ, hpos] using (congrArg Complex.re (hy hpos)).symm
  · simp [e8RegularQ, hpos]

theorem e8RegularQ_contDiffAt_zero : ContDiffAt ℝ 4 e8RegularQ 0 := by
  have hq : ContDiffAt ℂ 4 qGerm 0 := analyticAt_qGerm.contDiffAt
  have hcast : ContDiffAt ℝ 4 (⇑Complex.ofRealCLM) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hcomp : ContDiffAt ℝ 4 (qGerm ∘ (⇑Complex.ofRealCLM)) 0 :=
    ContDiffAt.comp (f := (⇑Complex.ofRealCLM)) 0
      (by simpa using hq.restrict_scalars ℝ) hcast
  have hreal : ContDiffAt ℝ 4 (fun y : ℝ => (qGerm (y : ℂ)).re) 0 :=
    (Complex.reCLM.contDiff.contDiffAt).comp 0 hcomp
  exact hreal.congr_of_eventuallyEq e8RegularQ_eventually_eq_germ

theorem hasDerivAt_e8RegularQ_zero :
    HasDerivAt e8RegularQ (Real.log 2 / 8) 0 := by
  have hreal : HasDerivAt (fun y : ℝ => (qGerm (y : ℂ)).re)
      (Real.log 2 / 8) 0 := by
    convert hasDerivAt_qGerm_zero.real_of_complex using 1
    norm_num [Complex.div_re]
    exact (Complex.log_ofReal_re 2).symm
  exact hreal.congr_of_eventuallyEq e8RegularQ_eventually_eq_germ

theorem e8SlopeRange_downward {x y : ℝ}
    (hx : x ∈ e8SlopeRange) (hy : 0 < y) (hyx : y ≤ x) :
    y ∈ e8SlopeRange := by
  have hsmallN : ∀ᶠ z : ℝ in nhds 0, z < y := Iio_mem_nhds hy
  have hsmall : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), z < y :=
    hsmallN.filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz, hzy⟩ := (eventually_mem_e8SlopeRange.and hsmall).exists
  exact e8SlopeRange_isPreconnected.ordConnected.out hz hx ⟨hzy.le, hyx⟩

private theorem contDiffOn_succ_of_derivative {U : Set ℝ} (hU : IsOpen U)
    {f g : ℝ → ℝ} {n : ℕ}
    (hd : ∀ x ∈ U, HasDerivAt f (g x) x)
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g U) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f U := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen hU).2
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    norm_cast at h
  · exact hg.congr (fun x hx => (hd x hx).deriv)

theorem e8Q_contDiffOn_four : ContDiffOn ℝ 4 e8Q e8SlopeRange := by
  have hopen : IsOpen e8SlopeRange := isOpen_iff_mem_nhds.mpr
    (fun _ hx => e8SlopeRange_mem_nhds hx)
  let j := e8QJet5 e8ThetaCanonicalJet5
  have hj : ∀ x ∈ e8SlopeRange, j.SoundAt x :=
    fun _ hx => e8QCanonicalJet5_soundAt_unconditional hx
  have h4 : ContDiffOn ℝ 0 j.d4 e8SlopeRange :=
    contDiffOn_zero.mpr (fun x hx =>
      (hj x hx).2.2.2.2.continuousAt.continuousWithinAt)
  have h3 : ContDiffOn ℝ 1 j.d3 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 0) (fun x hx => (hj x hx).2.2.2.1) h4
  have h2 : ContDiffOn ℝ 2 j.d2 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 1) (fun x hx => (hj x hx).2.2.1) h3
  have h1 : ContDiffOn ℝ 3 j.d1 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 2) (fun x hx => (hj x hx).2.1) h2
  exact contDiffOn_succ_of_derivative hopen (n := 3) (fun x hx => (hj x hx).1) h1

theorem e8RegularQ_contDiffAt_of_mem {y : ℝ} (hy : y ∈ e8SlopeRange) :
    ContDiffAt ℝ 4 e8RegularQ y := by
  have hq : ContDiffAt ℝ 4 e8Q y :=
    e8Q_contDiffOn_four.contDiffAt (e8SlopeRange_mem_nhds hy)
  apply hq.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
  exact e8RegularQ_eq_e8Q hz.le

/-- Regularity includes the axes and every intermediate integration point;
no global surjectivity premise for the inverse slope is needed. -/
theorem e8RegularQ_contDiffAt_interval {x y : ℝ}
    (hx : x ∈ e8SlopeRange) (hy : y ∈ Icc 0 x) :
    ContDiffAt ℝ 4 e8RegularQ y := by
  rcases hy.1.eq_or_lt with rfl | hpos
  · exact e8RegularQ_contDiffAt_zero
  · exact e8RegularQ_contDiffAt_of_mem (e8SlopeRange_downward hx hpos hy.2)

theorem e8Delta_regularQ_eq {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    e8Delta e8RegularQ s t = e8Delta e8Q s t := by
  unfold e8Delta
  rw [e8RegularQ_eq_e8Q hs, e8RegularQ_eq_e8Q ht,
    e8RegularQ_eq_e8Q (by positivity : 0 ≤ s + t),
    e8RegularQ_eq_e8Q (by positivity : 0 ≤ 2 * s + t)]

#print axioms e8RegularQ_contDiffAt_interval
#print axioms hasDerivAt_e8RegularQ_zero
#print axioms e8Delta_regularQ_eq

end GeneralCK

end


