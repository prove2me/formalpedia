-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapHalfMeanCurve
-- name    : CK_GeneralCK_PureGapHalfMeanCurve
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:04:42.047486+00:00
-- url     : https://prove2.me/theorems/d4747d71-4993-45ac-a046-e346444781fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapHalfMeanCurve` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapHalfMeanCurve` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapHalfMeanCurve` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapHalfMeanCurve (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapHalfMeanCurve.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8HalfMean
import Definitions.Def_CK_GeneralCK_CorrectionGlobalConvexity
import Mathlib.Analysis.Calculus.DerivativeTest

-- ===== source module GeneralCK.PureGapHalfMeanCurve =====
section

/-!
# Smooth reflected curve at the half-mean face

The canonical lower-half formula is only used with its second mean at most
`1/2`.  For the transverse second-derivative argument we reflect its last
radial term evenly across `1/2`.  This file records that extension and its
exact symmetry; no numerical half-mean certificate is assumed.
-/

namespace GeneralCK
open Set Filter

/-- A negative second derivative is incompatible with a local minimum.  This
necessary-condition form complements mathlib's sufficient second-derivative
test and is convenient for computer-assisted curvature exclusions. -/
theorem not_isLocalMin_of_deriv_deriv_neg {g : ℝ → ℝ} {x : ℝ}
    (hg : ContinuousAt g x) (hneg : deriv (deriv g) x < 0) :
    ¬ IsLocalMin g x := by
  intro hmin
  have hd0 : deriv g x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax g x :=
    isLocalMax_of_deriv_deriv_neg hneg hd0 hg
  have heq : g =ᶠ[nhds x] (fun _ => g x) := by
    filter_upwards [hmin, hmax] with y hminy hmaxy
    exact le_antisymm hmaxy hminy
  have hderiv : deriv g =ᶠ[nhds x] deriv (fun _ : ℝ => g x) := heq.deriv
  have hzero : deriv (deriv g) x = 0 := by
    calc
      deriv (deriv g) x = deriv (deriv (fun _ : ℝ => g x)) x := hderiv.deriv_eq
      _ = 0 := by simp
  linarith

/-- The reflected one-variable extension used in the smooth half-mean
argument.  On the lower half it agrees exactly with `canonicalPureGap`. -/
noncomputable def halfMeanPureGapCurve (a e f c : ℝ) : ℝ :=
  F (c - a) ((e + f) / 2) + entropyCorrection e f -
    radialPhi (1 - a - c) ((e + f) / 2) +
    (radialPhi (1 - 2 * a) e + (eta f - F |1 - 2 * c| f)) / 2

theorem halfMeanPureGapCurve_eq_canonical {a e f c : ℝ} (hc : c ≤ 1 / 2) :
    halfMeanPureGapCurve a e f c = canonicalPureGap a c e f := by
  have habs : |1 - 2 * c| = 1 - 2 * c := abs_of_nonneg (by linarith)
  simp only [halfMeanPureGapCurve, canonicalPureGap, radialPhi, habs]

/-- Reflection about the half-mean point exchanges the difference and center
radii and leaves the even marginal term fixed. -/
theorem halfMeanPureGapCurve_reflect (a e f c : ℝ) :
    halfMeanPureGapCurve a e f (1 - c) = halfMeanPureGapCurve a e f c := by
  have habs : |1 - 2 * (1 - c)| = |1 - 2 * c| := by
    rw [show 1 - 2 * (1 - c) = -(1 - 2 * c) by ring, abs_neg]
  simp only [halfMeanPureGapCurve, radialPhi, habs]
  ring_nf

@[simp] theorem halfMeanPureGapCurve_half (a e f : ℝ) :
    halfMeanPureGapCurve a e f (1 / 2) =
      canonicalPureGap a (1 / 2) e f :=
  halfMeanPureGapCurve_eq_canonical le_rfl

/-- Fold an arbitrary nearby second mean back into the canonical lower half. -/
def halfMeanFold (c : ℝ) : ℝ := min c (1 - c)

@[simp] theorem halfMeanFold_half : halfMeanFold (1 / 2) = (1 / 2 : ℝ) := by
  norm_num [halfMeanFold]

theorem halfMeanFold_le_half (c : ℝ) : halfMeanFold c ≤ (1 / 2 : ℝ) := by
  by_cases hc : c ≤ 1 / 2
  · exact (min_le_left _ _).trans hc
  · exact (min_le_right _ _).trans (by linarith)

theorem halfMeanPureGapCurve_fold (a e f c : ℝ) :
    halfMeanPureGapCurve a e f (halfMeanFold c) =
      halfMeanPureGapCurve a e f c := by
  by_cases hc : c ≤ 1 / 2
  · have hcle : c ≤ 1 - c := by linarith
    rw [halfMeanFold, min_eq_left hcle]
  · have hle : 1 - c ≤ c := by linarith
    rw [halfMeanFold, min_eq_right hle]
    exact halfMeanPureGapCurve_reflect a e f c

/-- The reflected curve is differentiable, hence continuous, at the half-mean
point.  The only delicate term is `F |1-2c| f`; its zero derivative is the
proved smooth-even radial extension lemma. -/
theorem continuousAt_halfMeanPureGapCurve_half {a e f : ℝ}
    (ha : a < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    ContinuousAt (halfMeanPureGapCurve a e f) (1 / 2) := by
  have hv : 0 < 1 / 2 - a := by linarith
  have hvCenter : 0 < 1 - a - 1 / 2 := by linarith
  have hef : 0 < (e + f) / 2 := by linarith
  have hdiff := (hasDerivAt_F_radius hv hef).comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℝ)).sub_const a)
  have hcenterF := (hasDerivAt_F_radius hvCenter hef).comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℝ)).const_sub (1 - a))
  have hcenter := hcenterF.const_sub (eta ((e + f) / 2))
  have hs := ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).const_sub 1
  have habsF := Correction.hasDerivAt_F_abs_curve_zero hs
    (hasDerivAt_const (1 / 2 : ℝ) f) (by norm_num) hf
  have hright := habsF.const_sub (eta f)
  have hleft := hasDerivAt_const (1 / 2 : ℝ) (radialPhi (1 - 2 * a) e)
  have htotal :=
    (((hdiff.add (hasDerivAt_const (1 / 2 : ℝ) (entropyCorrection e f))).sub
      hcenter).add ((hleft.add hright).div_const 2))
  refine htotal.continuousAt.congr_of_eventuallyEq ?_
  filter_upwards with c
  simp only [halfMeanPureGapCurve, radialPhi, Function.comp_apply, id_eq,
    Pi.add_apply, Pi.sub_apply]

/-- A retained constrained minimum at a strict right half-mean point becomes
a genuine local minimum of the reflected smooth curve.  Strictness of the
seam and entropy caps is exactly what supplies the needed neighborhood. -/
theorem isLocalMin_halfMeanPureGapCurve_of_isMinOn {S a e f : ℝ}
    (hp : (a, 1 / 2) ∈ retainedMeanSet S e f)
    (haHalf : a < 1 / 2) (hseam : S < a + 1 / 2)
    (hecap : e < H a) (hfcap : f < H (1 / 2))
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, 1 / 2)) :
    IsLocalMin (halfMeanPureGapCurve a e f) (1 / 2) := by
  have hfoldCont : ContinuousAt halfMeanFold (1 / 2) := by
    unfold halfMeanFold
    fun_prop
  have haAtFold : a < halfMeanFold (1 / 2) := by
    rw [halfMeanFold_half]
    exact haHalf
  have haEventually : ∀ᶠ c in nhds (1 / 2 : ℝ), a < halfMeanFold c :=
    hfoldCont.tendsto.eventually (Ioi_mem_nhds haAtFold)
  have hsumEventually : ∀ᶠ c in nhds (1 / 2 : ℝ),
      S < a + halfMeanFold c := by
    have hadd : ContinuousAt (fun c : ℝ => a + halfMeanFold c) (1 / 2) :=
      continuousAt_const.add hfoldCont
    have hsumAt : S < a + halfMeanFold (1 / 2) := by
      rw [halfMeanFold_half]
      exact hseam
    exact hadd.tendsto.eventually (Ioi_mem_nhds hsumAt)
  have hfEventually : ∀ᶠ c in nhds (1 / 2 : ℝ), f < H (halfMeanFold c) := by
    have hout : ContinuousAt H (halfMeanFold (1 / 2)) := H_continuous.continuousAt
    have hH : ContinuousAt (fun c : ℝ => H (halfMeanFold c)) (1 / 2) := by
      change ContinuousAt (H ∘ halfMeanFold) (1 / 2)
      exact hout.comp hfoldCont
    have hfAt : f < H (halfMeanFold (1 / 2)) := by
      rw [halfMeanFold_half]
      exact hfcap
    exact hH.tendsto.eventually (Ioi_mem_nhds hfAt)
  filter_upwards [haEventually, hsumEventually, hfEventually] with c hac hs hfH
  rw [halfMeanPureGapCurve_half, ← halfMeanPureGapCurve_fold a e f c,
    halfMeanPureGapCurve_eq_canonical (halfMeanFold_le_half c)]
  have hq : (a, halfMeanFold c) ∈ retainedMeanSet S e f :=
    ⟨⟨hp.1.1, hac.le, halfMeanFold_le_half c, hecap.le, hfH.le⟩, hs.le⟩
  simpa using hmin hq

/-- Strict feasibility also allows an unconstrained local variation of the
other mean while the right mean stays fixed at `1/2`. -/
theorem isLocalMin_canonicalPureGap_left_of_isMinOn_rightHalf {S a e f : ℝ}
    (hp : (a, 1 / 2) ∈ retainedMeanSet S e f)
    (haHalf : a < 1 / 2) (he : 0 < e)
    (hseam : S < a + 1 / 2) (hecap : e < H a)
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, 1 / 2)) :
    IsLocalMin (fun x : ℝ => canonicalPureGap x (1 / 2) e f) a := by
  have ha0 : 0 < a := by
    have hne : a ≠ 0 := by
      intro ha
      rw [ha, H_zero] at hecap
      linarith
    exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)
  have hpos : ∀ᶠ x in nhds a, 0 < x := Ioi_mem_nhds ha0
  have hhalf : ∀ᶠ x in nhds a, x < 1 / 2 := Iio_mem_nhds haHalf
  have hsum : ∀ᶠ x in nhds a, S < x + 1 / 2 := by
    have hc : ContinuousAt (fun x : ℝ => x + 1 / 2) a :=
      continuousAt_id.add continuousAt_const
    exact hc.tendsto.eventually (Ioi_mem_nhds hseam)
  have hevent : ∀ᶠ x in nhds a, e < H x :=
    H_continuous.continuousAt.tendsto.eventually (Ioi_mem_nhds hecap)
  filter_upwards [hpos, hhalf, hsum, hevent] with x hx0 hxhalf hxsum heH
  have hq : (x, 1 / 2) ∈ retainedMeanSet S e f :=
    ⟨⟨hx0.le, hxhalf.le, le_rfl, heH.le, hp.1.2.2.2.2⟩, hxsum.le⟩
  simpa using hmin hq

/-- The ledger-shaped constrained minimum therefore supplies the exact
half-mean stationarity relation, without assuming a two-variable local
minimum across the boundary. -/
theorem rightHalf_isMinOn_stationarity {S a e f : ℝ}
    (hp : (a, 1 / 2) ∈ retainedMeanSet S e f)
    (haHalf : a < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hseam : S < a + 1 / 2) (hecap : e < H a)
    (hmin : IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, 1 / 2)) :
    e8Theta ((1 / 2 - a) / e) =
      2 * e8Theta ((1 / 2 - a) / (e + f)) := by
  apply halfMean_left_stationarity_to_e8Theta haHalf he hf
  have hlocal := isLocalMin_canonicalPureGap_left_of_isMinOn_rightHalf
    hp haHalf he hseam hecap hmin
  have hz := hlocal.deriv_eq_zero
  rw [deriv_canonicalPureGap_left haHalf (by linarith) haHalf he hf] at hz
  exact hz

/-- Exact logical endpoint of the smooth half-mean argument: a negative
transverse second derivative of the reflected curve excludes the
ledger-shaped constrained minimum. -/
theorem not_isMinOn_rightHalf_of_deriv2_neg {S a e f : ℝ}
    (hp : (a, 1 / 2) ∈ retainedMeanSet S e f)
    (haHalf : a < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hseam : S < a + 1 / 2)
    (hecap : e < H a) (hfcap : f < H (1 / 2))
    (hneg : deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) < 0) :
    ¬ IsMinOn
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) (a, 1 / 2) := by
  intro hmin
  exact (not_isLocalMin_of_deriv_deriv_neg
    (continuousAt_halfMeanPureGapCurve_half haHalf he hf) hneg)
    (isLocalMin_halfMeanPureGapCurve_of_isMinOn hp haHalf hseam
      hecap hfcap hmin)

end GeneralCK

end


