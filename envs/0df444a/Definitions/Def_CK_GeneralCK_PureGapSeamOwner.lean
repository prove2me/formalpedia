-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapSeamOwner
-- name    : CK_GeneralCK_PureGapSeamOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:46:40.036774+00:00
-- url     : https://prove2.me/theorems/b5bdaf51-8b51-48fb-a597-bdd8d25ce944
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapSeamOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapSeamOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapSeamOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapSeamOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapSeamOwner.lean)

import Definitions.Def_CK_GeneralCK_PureGapHalfMeanOwner

-- ===== source module GeneralCK.PureGapSeamOwner =====
section

/-!
# Strict fixed-sum seam owner

This file turns a constrained fixed-entropy minimum on the retained seam into
the exact one-variable stationarity condition used by the manuscript's seam
certificate.  Equal means, half means, and entropy caps are routed before this
interface, so every hypothesis below is strict.
-/

namespace GeneralCK
open Set Filter
open scoped Topology

/-- Restriction of the canonical pure gap to the fixed mean-sum seam. -/
noncomputable def seamPureGapCurve (S e f x : ℝ) : ℝ :=
  canonicalPureGap x (S - x) e f

theorem deriv_seamPureGapCurve {S a c e f : ℝ}
    (hsum : a + c = S) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    deriv (seamPureGapCurve S e f) a =
      -2 * deriv (fun r => F r ((e + f) / 2)) (c - a) +
        deriv (fun r => F r e) (1 - 2 * a) -
        deriv (fun r => F r f) (1 - 2 * c) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hdiffPos : 0 < c - a := sub_pos.mpr hac
  have hcenterPos : 0 < 1 - a - c := by linarith
  have hleftPos : 0 < 1 - 2 * a := by linarith
  have hrightPos : 0 < 1 - 2 * c := by linarith
  have hdiffArg := (((hasDerivAt_id a).const_mul 2).const_sub S).congr_of_eventuallyEq (by
    filter_upwards with x
    simp only [id_eq]
    ring : (fun x : ℝ => S - x - x) =ᶠ[𝓝 a] (fun x : ℝ => S - 2 * id x))
  have hcenterArg := (hasDerivAt_const a (1 - S : ℝ)).congr_of_eventuallyEq (by
    filter_upwards with x
    ring : (fun x : ℝ => 1 - x - (S - x)) =ᶠ[𝓝 a] (fun _ : ℝ => 1 - S))
  have hleftArg := (((hasDerivAt_id a).const_mul 2).const_sub 1).congr_of_eventuallyEq (by
    filter_upwards with x
    simp only [id_eq] : (fun x : ℝ => 1 - 2 * x) =ᶠ[𝓝 a]
      (fun x : ℝ => 1 - 2 * id x))
  have hrightArg := (((hasDerivAt_id a).const_mul 2).const_add
    (1 - 2 * S)).congr_of_eventuallyEq (by
    filter_upwards with x
    simp only [id_eq]
    ring : (fun x : ℝ => 1 - 2 * (S - x)) =ᶠ[𝓝 a]
      (fun x : ℝ => (1 - 2 * S) + 2 * id x))
  have hdiffPos' : 0 < S - a - a := by linarith
  have hcenterPos' : 0 < 1 - a - (S - a) := by linarith
  have hrightPos' : 0 < 1 - 2 * (S - a) := by linarith
  have hdiff := (hasDerivAt_F_radius hdiffPos' hef).differentiableAt.hasDerivAt.comp
    (h := fun x : ℝ => S - x - x) a hdiffArg
  have hcenter := (hasDerivAt_F_radius hcenterPos' hef).differentiableAt.hasDerivAt.comp
    (h := fun x : ℝ => 1 - x - (S - x)) a hcenterArg
  have hleft := (hasDerivAt_F_radius hleftPos he).differentiableAt.hasDerivAt.comp
    (h := fun x : ℝ => 1 - 2 * x) a hleftArg
  have hright := (hasDerivAt_F_radius hrightPos' hf).differentiableAt.hasDerivAt.comp
    (h := fun x : ℝ => 1 - 2 * (S - x)) a hrightArg
  have hradCenter := (hasDerivAt_const a (eta ((e + f) / 2))).sub hcenter
  have hradLeft := (hasDerivAt_const a (eta e)).sub hleft
  have hradRight := (hasDerivAt_const a (eta f)).sub hright
  have htotal :=
    ((hdiff.add (hasDerivAt_const a (entropyCorrection e f))).sub hradCenter).add
      ((hradLeft.add hradRight).div_const 2)
  have hderiv := htotal.deriv
  convert hderiv using 1
  · apply Filter.EventuallyEq.deriv_eq
    filter_upwards with x
    simp only [seamPureGapCurve, canonicalPureGap, radialPhi,
      Function.comp_apply, Pi.add_apply, Pi.sub_apply]
  · rw [show S - a = c by linarith]
    ring

/-- Strict feasibility makes the seam restriction locally feasible inside the
retained mean set. -/
theorem isLocalMin_seamPureGapCurve_of_isMinOn {S a c e f : ℝ}
    (hp : (a, c) ∈ retainedMeanSet S e f)
    (hsum : a + c = S) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hecap : e < H a) (hfcap : f < H c)
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, c)) :
    IsLocalMin (seamPureGapCurve S e f) a := by
  have ha0 : 0 < a := by
    have hne : a ≠ 0 := by
      intro ha
      rw [ha, H_zero] at hecap
      linarith
    exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)
  have hpos : ∀ᶠ x in 𝓝 a, 0 < x := Ioi_mem_nhds ha0
  have horder : ∀ᶠ x in 𝓝 a, x < S - x := by
    have hcont : ContinuousAt (fun x : ℝ => S - x - x) a := by fun_prop
    have hat : 0 < S - a - a := by rw [← hsum]; linarith
    simpa only [sub_pos] using hcont.tendsto.eventually (Ioi_mem_nhds hat)
  have hhalf : ∀ᶠ x in 𝓝 a, S - x < 1 / 2 := by
    have hcont : ContinuousAt (fun x : ℝ => S - x) a := by fun_prop
    have hat : S - a < 1 / 2 := by rw [← hsum]; linarith
    exact hcont.tendsto.eventually (Iio_mem_nhds hat)
  have hevent : ∀ᶠ x in 𝓝 a, e < H x :=
    H_continuous.continuousAt.tendsto.eventually (Ioi_mem_nhds hecap)
  have hfevent : ∀ᶠ x in 𝓝 a, f < H (S - x) := by
    have hcont : ContinuousAt (fun x : ℝ => H (S - x)) a :=
      (H_continuous.comp (continuous_const.sub continuous_id)).continuousAt
    have hat : f < H (S - a) := by simpa [show S - a = c by linarith]
    exact hcont.tendsto.eventually (Ioi_mem_nhds hat)
  filter_upwards [hpos, horder, hhalf, hevent, hfevent] with x hx ho hh heH hfH
  have hq : (x, S - x) ∈ retainedMeanSet S e f := by
    refine ⟨⟨hx.le, ho.le, hh.le, heH.le, hfH.le⟩, ?_⟩
    change S ≤ x + (S - x)
    linarith
  change seamPureGapCurve S e f a ≤ seamPureGapCurve S e f x
  rw [seamPureGapCurve, seamPureGapCurve, show S - a = c by linarith]
  exact hmin hq

/-- A strict seam minimum satisfies the exact tangent stationarity equation. -/
theorem seam_isMinOn_stationarity {S a c e f : ℝ}
    (hp : (a, c) ∈ retainedMeanSet S e f)
    (hsum : a + c = S) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) (hecap : e < H a) (hfcap : f < H c)
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, c)) :
    -2 * deriv (fun r => F r ((e + f) / 2)) (c - a) +
        deriv (fun r => F r e) (1 - 2 * a) -
        deriv (fun r => F r f) (1 - 2 * c) = 0 := by
  have hz := (isLocalMin_seamPureGapCurve_of_isMinOn hp hsum hac hc he
    hecap hfcap hmin).deriv_eq_zero
  rwa [deriv_seamPureGapCurve hsum hac hc he hf] at hz

/-- Normalized seam stationarity in the scalar `e8Theta` coordinates used by
the finite seam certificate. -/
theorem seam_isMinOn_e8Theta_stationarity {S a c e f : ℝ}
    (hp : (a, c) ∈ retainedMeanSet S e f)
    (hsum : a + c = S) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) (hecap : e < H a) (hfcap : f < H c)
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, c)) :
    -2 * e8Theta ((c - a) / (e + f)) +
        e8Theta ((1 - 2 * a) / (2 * e)) -
        e8Theta ((1 - 2 * c) / (2 * f)) = 0 := by
  have h := seam_isMinOn_stationarity hp hsum hac hc he hf hecap hfcap hmin
  rw [deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) (by linarith),
    deriv_F_radius_eq_e8Theta (by linarith) he,
    deriv_F_radius_eq_e8Theta (by linarith) hf] at h
  simpa only [show 2 * ((e + f) / 2) = e + f by ring] using h

/-- The exact certificate interface needed to exclude a negative strict seam
minimum.  It matches the fixed-entropy tangent derivative obtained above. -/
def StrictSeamMinimizerExclusion (S : ℝ) : Prop :=
  ∀ a c e f : ℝ, 0 < e → 0 < f → e < f →
    (a, c) ∈ retainedMeanSet S e f → a + c = S → a < c → c < 1 / 2 →
    e < H a → f < H c →
    (-2 * e8Theta ((c - a) / (e + f)) +
        e8Theta ((1 - 2 * a) / (2 * e)) -
        e8Theta ((1 - 2 * c) / (2 * f)) = 0) →
    canonicalPureGap a c e f < 0 → False

theorem seam_minimizer_exclusion_of_stationary
    {S : ℝ} (hseam : StrictSeamMinimizerExclusion S) :
    ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
      p.1 + p.2 = S → p.1 < p.2 → p.2 < 1 / 2 →
      e < H p.1 → f < H p.2 →
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p →
      canonicalPureGap p.1 p.2 e f < 0 → False := by
  intro e f p he hf hef hp hsum hac hc hecap hfcap hmin hneg
  rcases p with ⟨a, c⟩
  exact hseam a c e f he hf hef hp hsum hac hc hecap hfcap
    (seam_isMinOn_e8Theta_stationarity hp hsum hac hc he hf hecap hfcap hmin) hneg

end GeneralCK

end


