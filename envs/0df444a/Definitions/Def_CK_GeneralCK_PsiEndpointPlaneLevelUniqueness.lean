-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneLevelUniqueness
-- name    : CK_GeneralCK_PsiEndpointPlaneLevelUniqueness
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:18:06.023573+00:00
-- url     : https://prove2.me/theorems/cd539278-f96c-4b6e-aa2c-ec991b4f30e0
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneLevelUniqueness` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneLevelUniqueness` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneLevelUniqueness` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneLevelUniqueness (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneLevelUniqueness.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneDifferential
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.Compact

-- ===== source module GeneralCK.PsiEndpointPlaneLevelUniqueness =====
section

/-!
# Uniqueness of a nonnegative level along the endpoint contact curve

A continuous function cannot meet the same nonnegative level twice if its
derivative is positive at every point where the function is nonnegative.
The proof uses an interior maximum, so it does not require the manuscript's
informal component argument or any asymptotic endpoint estimates.
-/

namespace GeneralCK.PsiEndpointPlane

open Set Filter SignType

/-- Once a function reaches a nonnegative value, positive derivative on
its nonnegative locus forces every subsequent value to be strictly larger. -/
theorem lt_of_deriv_pos_on_nonnegative {f : ℝ → ℝ} {a b : ℝ}
    (hlt : a < b) (hcont : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ f x → 0 < deriv f x)
    (ha : 0 ≤ f a) : f a < f b := by
  by_contra hnot
  have hle : f b ≤ f a := le_of_not_gt hnot
  have hab := hlt.le
  have hda : 0 < deriv f a := hpos a ⟨le_rfl, hab⟩ ha
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := fun x => f x - f a)
    (by simpa using hda) (by simp)
  have hsmallN : ∀ᶠ x : ℝ in nhds a, x < b := Iio_mem_nhds hlt
  have hexists : ∃ x : ℝ, a < x ∧ x < b ∧ f a < f x := by
    have hsign' := hsign.filter_mono (nhdsWithin_le_nhds (s := Ioi a))
    have hsmall := hsmallN.filter_mono (nhdsWithin_le_nhds (s := Ioi a))
    have hright : ∀ᶠ x : ℝ in nhdsWithin a (Ioi a), a < x := self_mem_nhdsWithin
    obtain ⟨x, hx, hxs, hxb⟩ :=
      (hright.and (hsign'.and hsmall)).exists
    refine ⟨x, hx, hxb, ?_⟩
    have hxa : 0 < x - a := sub_pos.mpr hx
    rw [sign_pos hxa, sign_eq_one_iff] at hxs
    exact sub_pos.mp hxs
  obtain ⟨x, hax, hxb, hfx⟩ := hexists
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨a, le_rfl, hab⟩) hcont
  have hfc : f a < f c := hfx.trans_le (hmax ⟨hax.le, hxb.le⟩)
  have hac : a < c := lt_of_le_of_ne hc.1 (by
    intro he
    rw [← he] at hfc
    exact (lt_irrefl _ hfc))
  have hcb : c < b := lt_of_le_of_ne hc.2 (by
    intro he
    rw [he] at hfc
    exact (not_lt_of_ge hle) hfc)
  have hlocal := hmax.isLocalMax (Icc_mem_nhds hac hcb)
  have hdc := hpos c hc (ha.trans hfc.le)
  rw [hlocal.deriv_eq_zero] at hdc
  exact (lt_irrefl _ hdc)

/-- Positive derivative on the nonnegative locus rules out two equal
nonnegative levels, even if the values between them could be negative. -/
theorem eq_of_equal_nonnegative_level {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ f x → 0 < deriv f x)
    (ha : 0 ≤ f a) (heq : f a = f b) : a = b := by
  rcases hab.eq_or_lt with he | hlt
  · exact he
  · have h := lt_of_deriv_pos_on_nonnegative hlt hcont hpos ha
    rw [heq] at h
    exact False.elim (lt_irrefl _ h)

/-- The nonnegative second level is unique along any differentiable
first-level graph on an open interval. The concrete derivative and no-fold
calculations are supplied by the preceding modules. -/
theorem second_level_unique_on_graph {A B K1 K0 a b : ℝ} {D : Set ℝ}
    {curve : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hK1 : 0 ≤ K1) (hK0 : 0 ≤ K0)
    (hD : Convex ℝ D) (hDopen : IsOpen D)
    (hphysical : ∀ r ∈ D, r ∈ Ioo 0 1 ∧ curve r ∈ Ioo 0 1)
    (hcurve : ∀ r ∈ D, DifferentiableAt ℝ curve r)
    (hfirst : ∀ r ∈ D, level1 A B r (curve r) = K1)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≤ b)
    (ha0 : level0 A B a (curve a) = K0)
    (hb0 : level0 A B b (curve b) = K0) : a = b := by
  have hsub : Icc a b ⊆ D := hD.ordConnected.out ha hb
  have hsecond (r : ℝ) (hr : r ∈ D) :
      DifferentiableAt ℝ (fun z => level0 A B z (curve z)) r := by
    have h := hasDerivAt_level0_along (A := A) (B := B)
      (hphysical r hr).1 (hphysical r hr).2 (hasDerivAt_id r) (hcurve r hr).hasDerivAt
    simpa only [id_eq] using h.differentiableAt
  apply eq_of_equal_nonnegative_level hab
  · exact fun r hr => (hsecond r (hsub hr)).continuousAt.continuousWithinAt
  · intro r hr hnonnegative
    have hrD := hsub hr
    have hlevel : HasDerivAt (fun z => level1 A B z (curve z)) 0 r := by
      apply (hasDerivAt_const r K1).congr_of_eventuallyEq
      filter_upwards [hDopen.mem_nhds hrD] with z hz
      exact hfirst z hz
    exact level0_deriv_pos_along_level1 hA hB hAB
      (hphysical r hrD).1 (hphysical r hrD).2 (hcurve r hrD).hasDerivAt hlevel
      (by rw [hfirst r hrD]; exact hK1) hnonnegative
  · rw [ha0]
    exact hK0
  · exact ha0.trans hb0.symm

#print axioms eq_of_equal_nonnegative_level
#print axioms second_level_unique_on_graph

end GeneralCK.PsiEndpointPlane

end


