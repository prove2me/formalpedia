-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8InverseJet5AnalyticBridge
-- name    : CK_GeneralCK_Certificates_E8InverseJet5AnalyticBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:03:16.29974+00:00
-- url     : https://prove2.me/theorems/d59c24bc-93ae-4a8c-87d7-25932edca244
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8InverseJet5AnalyticBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8InverseJet5AnalyticBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8InverseJet5AnalyticBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8InverseJet5AnalyticBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8InverseJet5AnalyticBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticCoefficientBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8InverseJet5Bridge

-- ===== source module GeneralCK.Certificates.E8InverseJet5AnalyticBridge =====
section

/-!
# Raw derivative to analytic Taylor bridge through order five

`Jet5` stores raw derivatives, while the origin source boxes store
factorial-normalized coefficients.  This module supplies the exact scaling
handoff for the concrete complex analytic germ.
-/

namespace GeneralCK.Certificates.E8InverseJet5AnalyticBridge

open E8AnalyticGerm E8AnalyticCoefficientBoxes Filter

theorem qTaylorCoeff_three :
    qTaylorCoeff 3 = iteratedDeriv 3 qGerm 0 / 6 := by
  norm_num [qTaylorCoeff]

theorem qTaylorCoeff_five :
    qTaylorCoeff 5 = iteratedDeriv 5 qGerm 0 / 120 := by
  norm_num [qTaylorCoeff]

/-- A real raw-derivative jet has been identified with the concrete analytic
germ at zero in precisely the components needed for the first nonlinear
source boxes. -/
structure MatchesAnalyticQJet35AtZero (j : Jet5) : Prop where
  d3 : (j.d3 0 : ℂ) = iteratedDeriv 3 qGerm 0
  d5 : (j.d5 0 : ℂ) = iteratedDeriv 5 qGerm 0

/-- Minimal positive-axis limit premise.  It asks only that the raw jet
components agree eventually with the analytic derivatives; continuity from
the closed right half-line supplies their values at the endpoint. -/
structure EventuallyMatchesAnalyticQJet35 (j : Jet5) : Prop where
  continuous3 : ContinuousWithinAt j.d3 (Set.Ici 0) 0
  continuous5 : ContinuousWithinAt j.d5 (Set.Ici 0) 0
  eventually3 : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    (j.d3 y : ℂ) = iteratedDeriv 3 qGerm (y : ℂ)
  eventually5 : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    (j.d5 y : ℂ) = iteratedDeriv 5 qGerm (y : ℂ)

/-- Replace only the two endpoint-sensitive components of a raw inverse jet
at slope zero by the real parts of the analytic germ derivatives.  Away from
zero this is definitionally the original recurrence jet.  This patch is
necessary because the totalized `e8Q` is zero off its positive range, so its
raw recurrence is not the right-continuous extension at the origin. -/
noncomputable def patchAnalyticQJet35AtZero (j : Jet5) : Jet5 :=
  { j with
    d3 := fun y => if y = 0 then (iteratedDeriv 3 qGerm 0).re else j.d3 y
    d5 := fun y => if y = 0 then (iteratedDeriv 5 qGerm 0).re else j.d5 y }

private theorem continuousAt_real_iteratedDeriv_qGerm (n : ℕ) :
    ContinuousAt (fun y : ℝ => (iteratedDeriv n qGerm (y : ℂ)).re) 0 := by
  have hcd : ContDiffAt ℂ (⊤ : WithTop ℕ∞) qGerm 0 := analyticAt_qGerm.contDiffAt
  have hiter : ContinuousAt (iteratedDeriv n qGerm) 0 := by
    unfold iteratedDeriv
    exact
      (ContinuousLinearMap.continuous
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ) ℂ (fun _ => 1))).continuousAt.comp
        (hcd.continuousAt_iteratedFDeriv (by simp))
  have hcast : Tendsto ((↑) : ℝ → ℂ) (nhds (0 : ℝ)) (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  exact (Complex.continuous_re.continuousAt.tendsto.comp
    (hiter.tendsto.comp hcast))

private theorem patched_component_continuousWithinAt
    (jcomp : ℝ → ℝ) (n : ℕ)
    (h : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (jcomp y : ℂ) = iteratedDeriv n qGerm (y : ℂ)) :
    ContinuousWithinAt
      (fun y => if y = 0 then (iteratedDeriv n qGerm 0).re else jcomp y)
      (Set.Ici 0) 0 := by
  let target : ℝ → ℝ := fun y => (iteratedDeriv n qGerm (y : ℂ)).re
  have heqPos :
      (fun y => if y = 0 then (iteratedDeriv n qGerm 0).re else jcomp y) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)] target := by
    filter_upwards [h, self_mem_nhdsWithin] with y hy hypos
    simp only [Set.mem_Ioi] at hypos
    rw [if_neg hypos.ne']
    exact congrArg Complex.re hy
  have heqZero :
      (fun y => if y = 0 then (iteratedDeriv n qGerm 0).re else jcomp y) =ᶠ[
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)] target := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y = 0 := by simpa using hy
    subst y
    simp [target]
  have heq :
      (fun y => if y = 0 then (iteratedDeriv n qGerm 0).re else jcomp y) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ici 0)] target := by
    rw [show Set.Ici (0 : ℝ) = Set.Ioi 0 ∪ {0} by ext y; simp [le_iff_lt_or_eq],
      nhdsWithin_union]
    exact ⟨heqPos, heqZero⟩
  exact (continuousAt_real_iteratedDeriv_qGerm n).continuousWithinAt.congr_of_eventuallyEq
    heq (by simp [target])

/-- Eventual positive-axis identification is the only analytic premise
needed after patching the two endpoint values.  Right continuity then follows
from the analytic germ itself, rather than from the false two-sided raw
derivative values of the zero-filled inverse. -/
theorem eventuallyMatchesAnalyticQJet35_patch {j : Jet5}
    (h3 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (j.d3 y : ℂ) = iteratedDeriv 3 qGerm (y : ℂ))
    (h5 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (j.d5 y : ℂ) = iteratedDeriv 5 qGerm (y : ℂ)) :
    EventuallyMatchesAnalyticQJet35 (patchAnalyticQJet35AtZero j) := by
  refine ⟨patched_component_continuousWithinAt j.d3 3 h3,
    patched_component_continuousWithinAt j.d5 5 h5, ?_, ?_⟩
  · filter_upwards [h3, self_mem_nhdsWithin] with y hy hypos
    have hypos' : 0 < y := hypos
    simpa [patchAnalyticQJet35AtZero, hypos'.ne'] using hy
  · filter_upwards [h5, self_mem_nhdsWithin] with y hy hypos
    have hypos' : 0 < y := hypos
    simpa [patchAnalyticQJet35AtZero, hypos'.ne'] using hy

/-- Eventual positive-axis agreement plus right continuity closes the actual
endpoint identification; no value of the zero-filled `e8Q` is used. -/
theorem EventuallyMatchesAnalyticQJet35.matchesAtZero {j : Jet5}
    (h : EventuallyMatchesAnalyticQJet35 j) : MatchesAnalyticQJet35AtZero j := by
  have hcast : Tendsto ((↑) : ℝ → ℂ) (nhds (0 : ℝ)) (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhdsWithin 0 (Set.Ici 0) :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self
  have hj3real : Tendsto j.d3 (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (j.d3 0)) := h.continuous3.tendsto.mono_left hsub
  have hj5real : Tendsto j.d5 (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (j.d5 0)) := h.continuous5.tendsto.mono_left hsub
  have hj3 : Tendsto (fun y : ℝ => (j.d3 y : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (j.d3 0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hj3real
  have hj5 : Tendsto (fun y : ℝ => (j.d5 y : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (j.d5 0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hj5real
  have hcd : ContDiffAt ℂ (⊤ : WithTop ℕ∞) qGerm 0 := analyticAt_qGerm.contDiffAt
  have hiter3 : ContinuousAt (iteratedDeriv 3 qGerm) 0 := by
    unfold iteratedDeriv
    exact
      (ContinuousLinearMap.continuous
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin 3 => ℂ) ℂ (fun _ => 1))).continuousAt.comp
        (hcd.continuousAt_iteratedFDeriv (by norm_num))
  have hiter5 : ContinuousAt (iteratedDeriv 5 qGerm) 0 := by
    unfold iteratedDeriv
    exact
      (ContinuousLinearMap.continuous
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin 5 => ℂ) ℂ (fun _ => 1))).continuousAt.comp
        (hcd.continuousAt_iteratedFDeriv (by norm_num))
  have hq3 : Tendsto (fun y : ℝ => iteratedDeriv 3 qGerm (y : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (iteratedDeriv 3 qGerm 0)) :=
    by
      simpa [Function.comp_def] using
        ((hiter3.tendsto.comp hcast).mono_left
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0))
  have hq5 : Tendsto (fun y : ℝ => iteratedDeriv 5 qGerm (y : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (iteratedDeriv 5 qGerm 0)) :=
    by
      simpa [Function.comp_def] using
        ((hiter5.tendsto.comp hcast).mono_left
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0))
  constructor
  · exact tendsto_nhds_unique hj3 (hq3.congr' (h.eventually3.mono fun _ hy => hy.symm))
  · exact tendsto_nhds_unique hj5 (hq5.congr' (h.eventually5.mono fun _ hy => hy.symm))

theorem coefficient_box_of_raw_derivative {n : ℕ}
    (hraw :
      ‖iteratedDeriv n qGerm 0 -
          (n.factorial : ℂ) * (sourceCenter n : ℂ)‖ ≤
        (n.factorial : ℝ) * (sourceHalfWidth n : ℝ)) :
    ‖qTaylorCoeff n - (sourceCenter n : ℂ)‖ ≤
      (sourceHalfWidth n : ℝ) := by
  have hfac : (n.factorial : ℝ) > 0 := by positivity
  have hfacC : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  unfold qTaylorCoeff
  have heq :
      iteratedDeriv n qGerm 0 / (n.factorial : ℂ) - (sourceCenter n : ℂ) =
        (iteratedDeriv n qGerm 0 -
          (n.factorial : ℂ) * (sourceCenter n : ℂ)) /
            (n.factorial : ℂ) := by
    field_simp [hfacC]
  rw [heq, norm_div]
  simp only [Complex.norm_natCast, Real.norm_natCast]
  rw [div_le_iff₀ hfac]
  simpa [mul_comm] using hraw

theorem q3_sourceBox_of_jet {j : Jet5} (hj : MatchesAnalyticQJet35AtZero j)
    (h3 :
      ‖(j.d3 0 : ℂ) - (6 : ℂ) * (sourceCenter 3 : ℂ)‖ ≤
        (6 : ℝ) * (sourceHalfWidth 3 : ℝ)) :
    ‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤
      (sourceHalfWidth 3 : ℝ) := by
  apply coefficient_box_of_raw_derivative
  norm_num only [Nat.factorial]
  rwa [← hj.d3]

theorem q5_sourceBox_of_jet {j : Jet5} (hj : MatchesAnalyticQJet35AtZero j)
    (h5 :
      ‖(j.d5 0 : ℂ) - (120 : ℂ) * (sourceCenter 5 : ℂ)‖ ≤
        (120 : ℝ) * (sourceHalfWidth 5 : ℝ)) :
    ‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤
      (sourceHalfWidth 5 : ℝ) := by
  apply coefficient_box_of_raw_derivative
  norm_num only [Nat.factorial]
  rwa [← hj.d5]

/-- Specialized directly to the inverse jet generated by
`E8InverseJet5Bridge`. -/
theorem q3_q5_sourceBoxes_of_e8QJet5 {theta : Jet5}
    (hmatch : MatchesAnalyticQJet35AtZero
      (E8InverseJet5Bridge.e8QJet5 theta))
    (h3 : ‖((E8InverseJet5Bridge.e8QJet5 theta).d3 0 : ℂ) -
        (6 : ℂ) * (sourceCenter 3 : ℂ)‖ ≤
          (6 : ℝ) * (sourceHalfWidth 3 : ℝ))
    (h5 : ‖((E8InverseJet5Bridge.e8QJet5 theta).d5 0 : ℂ) -
        (120 : ℂ) * (sourceCenter 5 : ℂ)‖ ≤
          (120 : ℝ) * (sourceHalfWidth 5 : ℝ)) :
    (‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤
        (sourceHalfWidth 3 : ℝ)) ∧
      (‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤
        (sourceHalfWidth 5 : ℝ)) :=
  ⟨q3_sourceBox_of_jet hmatch h3, q5_sourceBox_of_jet hmatch h5⟩

/-- Legacy conditional handoff for a raw inverse recurrence.  Do not use this
with the canonical zero-filled `e8Q` recurrence: its totalized endpoint values
are not right-continuous.  The valid concrete route is
`q3_q5_sourceBoxes_of_patched_e8QJet5` below. -/
theorem q3_q5_sourceBoxes_of_e8QJet5_right_limit {theta : Jet5}
    (hlimit : EventuallyMatchesAnalyticQJet35
      (E8InverseJet5Bridge.e8QJet5 theta))
    (h3 : ‖((E8InverseJet5Bridge.e8QJet5 theta).d3 0 : ℂ) -
        (6 : ℂ) * (sourceCenter 3 : ℂ)‖ ≤
          (6 : ℝ) * (sourceHalfWidth 3 : ℝ))
    (h5 : ‖((E8InverseJet5Bridge.e8QJet5 theta).d5 0 : ℂ) -
        (120 : ℂ) * (sourceCenter 5 : ℂ)‖ ≤
          (120 : ℝ) * (sourceHalfWidth 5 : ℝ)) :
    (‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤
        (sourceHalfWidth 3 : ℝ)) ∧
      (‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤
        (sourceHalfWidth 5 : ℝ)) :=
  q3_q5_sourceBoxes_of_e8QJet5 hlimit.matchesAtZero h3 h5

/-- Source-box handoff for the correct right-continuous endpoint extension.
The two displayed raw enclosures are the exact remaining numerical premises;
the analytic identification and endpoint continuity are supplied by
`eventuallyMatchesAnalyticQJet35_patch`. -/
theorem q3_q5_sourceBoxes_of_patched_e8QJet5 {theta : Jet5}
    (hmatch3 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((E8InverseJet5Bridge.e8QJet5 theta).d3 y : ℂ) =
        iteratedDeriv 3 qGerm (y : ℂ))
    (hmatch5 : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((E8InverseJet5Bridge.e8QJet5 theta).d5 y : ℂ) =
        iteratedDeriv 5 qGerm (y : ℂ))
    (h3 : ‖((patchAnalyticQJet35AtZero
          (E8InverseJet5Bridge.e8QJet5 theta)).d3 0 : ℂ) -
        (6 : ℂ) * (sourceCenter 3 : ℂ)‖ ≤
          (6 : ℝ) * (sourceHalfWidth 3 : ℝ))
    (h5 : ‖((patchAnalyticQJet35AtZero
          (E8InverseJet5Bridge.e8QJet5 theta)).d5 0 : ℂ) -
        (120 : ℂ) * (sourceCenter 5 : ℂ)‖ ≤
          (120 : ℝ) * (sourceHalfWidth 5 : ℝ)) :
    (‖qTaylorCoeff 3 - (sourceCenter 3 : ℂ)‖ ≤
        (sourceHalfWidth 3 : ℝ)) ∧
      (‖qTaylorCoeff 5 - (sourceCenter 5 : ℂ)‖ ≤
        (sourceHalfWidth 5 : ℝ)) := by
  have hm := eventuallyMatchesAnalyticQJet35_patch hmatch3 hmatch5 |>.matchesAtZero
  exact ⟨q3_sourceBox_of_jet hm h3, q5_sourceBox_of_jet hm h5⟩

end GeneralCK.Certificates.E8InverseJet5AnalyticBridge

end


