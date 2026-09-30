-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8PositiveAxisGermJet
-- name    : CK_GeneralCK_Certificates_E8PositiveAxisGermJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:09:03.418988+00:00
-- url     : https://prove2.me/theorems/5178565f-0168-468e-bf27-0952a310b1d9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8PositiveAxisGermJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8PositiveAxisGermJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8PositiveAxisGermJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8PositiveAxisGermJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8PositiveAxisGermJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8InverseJet5AnalyticBridge
import Definitions.Def_CK_GeneralCK_PureGapE8AnalyticRealBridge
import Mathlib.Analysis.Calculus.DerivativeTest

-- ===== source module GeneralCK.Certificates.E8PositiveAxisGermJet =====
section

/-!
# Positive-axis identification of the E8 analytic inverse jet

This module transfers the stable real parametrization from the bias variable
to an ordinary punctured neighborhood of slope zero.  It then supplies the
local input needed to identify the concrete inverse recurrence with the
separate analytic germ.
-/

namespace GeneralCK.Certificates.E8PositiveAxisGermJet

open Set Filter SignType
open GeneralCK E8AnalyticGerm

theorem thetaParamReal_zero : thetaParamReal 0 = 0 := by
  have h := (param_ofReal (c := 0) (by norm_num) (by norm_num)).1
  norm_num [thetaParam_zero] at h
  exact_mod_cast h.symm

/-- The real stable slope parametrization is a local equivalence at the
origin, with its exact positive derivative. -/
theorem hasStrictDerivAt_thetaParamReal_zero :
    HasStrictDerivAt thetaParamReal (4 / Real.log 2) 0 := by
  have hcast : ((4 / Real.log 2 : ℝ) : ℂ) =
      (4 : ℂ) / (Real.log 2 : ℂ) := by
    exact_mod_cast rfl
  have hc : HasStrictDerivAt thetaParam
      ((4 / Real.log 2 : ℝ) : ℂ) 0 := by
    rw [hcast, ← hasDerivAt_thetaParam_zero.deriv]
    exact analyticAt_thetaParam.hasStrictDerivAt
  have hr := hc.real_of_complex
  have heq :
      (fun c : ℝ => (thetaParam (c : ℂ)).re) =ᶠ[nhds 0] thetaParamReal := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact congrArg Complex.re (param_ofReal hc.1 hc.2).1
  simpa only [Complex.ofReal_re] using hr.congr_of_eventuallyEq heq

/-- The parametrized real-axis identity fills an ordinary punctured
neighborhood of slope zero.  This is the form needed for local derivative
congruence. -/
theorem eventually_qGerm_eq_e8Q :
    ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      qGerm (y : ℂ) = (e8Q y : ℂ) := by
  let a : ℝ := 4 / Real.log 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hθ : HasStrictDerivAt thetaParamReal a 0 := by
    simpa [a] using hasStrictDerivAt_thetaParamReal_zero
  let g : ℝ → ℝ := hθ.localInverse thetaParamReal a 0 ha.ne'
  have hg : HasStrictDerivAt g a⁻¹ 0 := by
    simpa [g, thetaParamReal_zero] using hθ.to_localInverse ha.ne'
  have hg0 : g 0 = 0 := by
    simpa [g, thetaParamReal_zero] using
      (hθ.hasStrictFDerivAt_equiv ha.ne').localInverse_apply_image
  have hright : ∀ᶠ y in nhds (0 : ℝ), thetaParamReal (g y) = y := by
    simpa [g, thetaParamReal_zero] using hθ.eventually_right_inverse ha.ne'
  have hsign : ∀ᶠ y in nhds (0 : ℝ), sign (g y) = sign y := by
    simpa [hg0] using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := g) (x₀ := 0) (by simpa [hg.hasDerivAt.deriv] using inv_pos.mpr ha) hg0
  have hgpos : ∀ᶠ y in nhdsWithin (0 : ℝ) (Ioi 0), 0 < g y := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hsy hy
    rw [← sign_eq_one_iff, hsy, sign_eq_one_iff]
    exact hy
  have hgtend : Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa [hg0] using
          hg.hasDerivAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        hgpos⟩
  have hpull := hgtend.eventually eventually_qGerm_eq_e8Q_param
  filter_upwards [hpull, hright.filter_mono nhdsWithin_le_nhds] with y hy hrighty
  simpa [hrighty] using hy

/-- All sufficiently small positive slopes lie in the actual positive range
of `e8Theta`.  This removes the zero-filled branch before differentiating the
inverse recurrence. -/
theorem eventually_mem_e8SlopeRange :
    ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), y ∈ e8SlopeRange := by
  have hqder : HasDerivAt (fun y : ℝ => (qGerm (y : ℂ)).re)
      (Real.log 2 / 8) 0 := by
    convert hasDerivAt_qGerm_zero.real_of_complex using 1
    norm_num [Complex.div_re]
    exact (Complex.log_ofReal_re 2).symm
  have hqderpos : 0 < deriv (fun y : ℝ => (qGerm (y : ℂ)).re) 0 := by
    rw [hqder.deriv]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hsign : ∀ᶠ y : ℝ in nhds (0 : ℝ),
      sign ((qGerm (y : ℂ)).re) = sign y := by
    simpa using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := fun y : ℝ => (qGerm (y : ℂ)).re) (x₀ := 0)
      hqderpos
      (by simp)
  filter_upwards [eventually_qGerm_eq_e8Q,
    hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y heq hs hy
  have hqpos : 0 < (qGerm (y : ℂ)).re := by
    rw [← sign_eq_one_iff, hs, sign_eq_one_iff]
    exact hy
  have hey : e8Q y = (qGerm (y : ℂ)).re := by
    simpa using congrArg Complex.re heq.symm
  by_contra hn
  have hz : e8Q y = 0 := by simp [e8Q, hn]
  linarith

private theorem hasDerivAt_iteratedDeriv_qGerm (n : ℕ) {z : ℂ}
    (h : AnalyticAt ℂ qGerm z) :
    HasDerivAt (iteratedDeriv n qGerm) (iteratedDeriv (n + 1) qGerm z) z := by
  rw [iteratedDeriv_succ]
  have hcd : ContDiffAt ℂ (⊤ : WithTop ℕ∞) qGerm z := h.contDiffAt
  have hd : DifferentiableAt ℂ (iteratedDeriv n qGerm) z := by
    unfold iteratedDeriv
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ) ℂ
      (fun _ => 1)).hasFDerivAt.differentiableAt.comp z
          (hcd.differentiableAt_iteratedFDeriv (by norm_num))
  exact hd.hasDerivAt

/-- On a punctured positive neighborhood, the unconditional recurrence jet
is the restriction of the complex analytic inverse jet through order five. -/
structure EventuallyCanonicalEqualsAnalytic : Prop where
  d0 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d0 y : ℂ) = iteratedDeriv 0 qGerm (y : ℂ)
  d1 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d1 y : ℂ) = iteratedDeriv 1 qGerm (y : ℂ)
  d2 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d2 y : ℂ) = iteratedDeriv 2 qGerm (y : ℂ)
  d3 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d3 y : ℂ) = iteratedDeriv 3 qGerm (y : ℂ)
  d4 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d4 y : ℂ) = iteratedDeriv 4 qGerm (y : ℂ)
  d5 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
    ((E8InverseJet5Bridge.e8QJet5
        E8InverseJet5Bridge.e8ThetaCanonicalJet5).d5 y : ℂ) = iteratedDeriv 5 qGerm (y : ℂ)

theorem eventually_e8QCanonicalJet5_eq_analytic_all : EventuallyCanonicalEqualsAnalytic := by
  let j := E8InverseJet5Bridge.e8QJet5
    E8InverseJet5Bridge.e8ThetaCanonicalJet5
  have hsound : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), j.SoundAt y := by
    filter_upwards [eventually_mem_e8SlopeRange] with y hy
    exact E8InverseJet5Bridge.e8QCanonicalJet5_soundAt_unconditional hy
  have hcast : Tendsto ((↑) : ℝ → ℂ) (nhds (0 : ℝ)) (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have han : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      AnalyticAt ℂ qGerm (y : ℂ) :=
    (hcast.eventually analyticAt_qGerm.eventually_analyticAt).filter_mono
      nhdsWithin_le_nhds
  have h0 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d0 y : ℂ) = qGerm (y : ℂ) := by
    filter_upwards [eventually_qGerm_eq_e8Q] with y hy
    simpa [j, E8InverseJet5Bridge.e8QJet5] using hy.symm
  have h0loc : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (fun x : ℝ => (j.d0 x : ℂ)) =ᶠ[nhds y]
        (fun x : ℝ => qGerm (x : ℂ)) :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi).2 h0
  have h1 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d1 y : ℂ) = iteratedDeriv 1 qGerm (y : ℂ) := by
    filter_upwards [h0loc, hsound, han] with y heq hs ha
    have hj := hs.1.ofReal_comp.congr_of_eventuallyEq heq.symm
    have hq := (hasDerivAt_iteratedDeriv_qGerm 0 ha).comp_ofReal
    simpa using hj.unique hq
  have h1loc : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (fun x : ℝ => (j.d1 x : ℂ)) =ᶠ[nhds y]
        (fun x : ℝ => iteratedDeriv 1 qGerm (x : ℂ)) :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi).2 h1
  have h2 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d2 y : ℂ) = iteratedDeriv 2 qGerm (y : ℂ) := by
    filter_upwards [h1loc, hsound, han] with y heq hs ha
    have hj := hs.2.1.ofReal_comp.congr_of_eventuallyEq heq.symm
    have hq := (hasDerivAt_iteratedDeriv_qGerm 1 ha).comp_ofReal
    simpa using hj.unique hq
  have h2loc : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (fun x : ℝ => (j.d2 x : ℂ)) =ᶠ[nhds y]
        (fun x : ℝ => iteratedDeriv 2 qGerm (x : ℂ)) :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi).2 h2
  have h3 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d3 y : ℂ) = iteratedDeriv 3 qGerm (y : ℂ) := by
    filter_upwards [h2loc, hsound, han] with y heq hs ha
    have hj := hs.2.2.1.ofReal_comp.congr_of_eventuallyEq heq.symm
    have hq := (hasDerivAt_iteratedDeriv_qGerm 2 ha).comp_ofReal
    simpa using hj.unique hq
  have h3loc : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (fun x : ℝ => (j.d3 x : ℂ)) =ᶠ[nhds y]
        (fun x : ℝ => iteratedDeriv 3 qGerm (x : ℂ)) :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi).2 h3
  have h4 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d4 y : ℂ) = iteratedDeriv 4 qGerm (y : ℂ) := by
    filter_upwards [h3loc, hsound, han] with y heq hs ha
    have hj := hs.2.2.2.1.ofReal_comp.congr_of_eventuallyEq heq.symm
    have hq := (hasDerivAt_iteratedDeriv_qGerm 3 ha).comp_ofReal
    simpa using hj.unique hq
  have h4loc : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (fun x : ℝ => (j.d4 x : ℂ)) =ᶠ[nhds y]
        (fun x : ℝ => iteratedDeriv 4 qGerm (x : ℂ)) :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi).2 h4
  have h5 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (j.d5 y : ℂ) = iteratedDeriv 5 qGerm (y : ℂ) := by
    filter_upwards [h4loc, hsound, han] with y heq hs ha
    have hj := hs.2.2.2.2.ofReal_comp.congr_of_eventuallyEq heq.symm
    have hq := (hasDerivAt_iteratedDeriv_qGerm 4 ha).comp_ofReal
    simpa using hj.unique hq
  exact ⟨by simpa only [iteratedDeriv_zero] using h0, h1, h2, h3, h4, h5⟩

theorem eventually_e8QCanonicalJet5_eq_analytic :
    (∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((E8InverseJet5Bridge.e8QJet5
          E8InverseJet5Bridge.e8ThetaCanonicalJet5).d3 y : ℂ) =
        iteratedDeriv 3 qGerm (y : ℂ)) ∧
    (∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((E8InverseJet5Bridge.e8QJet5
          E8InverseJet5Bridge.e8ThetaCanonicalJet5).d5 y : ℂ) =
        iteratedDeriv 5 qGerm (y : ℂ)) :=
  ⟨eventually_e8QCanonicalJet5_eq_analytic_all.d3,
    eventually_e8QCanonicalJet5_eq_analytic_all.d5⟩

/-- The endpoint-patched canonical recurrence supplies the concrete
`EventuallyMatchesAnalyticQJet35` bridge without any smoothness premise. -/
theorem patchedCanonicalJet5_eventuallyMatchesAnalytic :
    E8InverseJet5AnalyticBridge.EventuallyMatchesAnalyticQJet35
      (E8InverseJet5AnalyticBridge.patchAnalyticQJet35AtZero
        (E8InverseJet5Bridge.e8QJet5
          E8InverseJet5Bridge.e8ThetaCanonicalJet5)) :=
  E8InverseJet5AnalyticBridge.eventuallyMatchesAnalyticQJet35_patch
    eventually_e8QCanonicalJet5_eq_analytic.1
    eventually_e8QCanonicalJet5_eq_analytic.2

end GeneralCK.Certificates.E8PositiveAxisGermJet

end


