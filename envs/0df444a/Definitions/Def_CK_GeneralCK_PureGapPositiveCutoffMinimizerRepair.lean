-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapPositiveCutoffMinimizerRepair
-- name    : CK_GeneralCK_PureGapPositiveCutoffMinimizerRepair
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:23:53.106174+00:00
-- url     : https://prove2.me/theorems/9f9b8f09-639d-4219-8bd5-b55273de9a75
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapPositiveCutoffMinimizerRepair` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapPositiveCutoffMinimizerRepair` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapPositiveCutoffMinimizerRepair` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapPositiveCutoffMinimizerRepair (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapPositiveCutoffMinimizerRepair.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff

-- ===== source module GeneralCK.PureGapPositiveCutoffMinimizerRepair =====
section

/-!
# Positive-cutoff repair of the retained pure-gap route

The zero-cutoff left-cap stationary value statement is false near the origin.
The actual Bellman target below `SmallMeanPhiCutoff.retainedCutoff` is already
proved directly by SB-1, so no pure-gap sign is needed there.  This file keeps
the cutoff positive and packages only the minimizer exclusions needed on the
retained compact chamber.

Compared with `SmallMeanPhiCutoff.RetainedBoundaryOwners`, the interface below
does not ask for pointwise signs on four full boundary faces.  A negative value
would have a global minimum, so it is enough to exclude a negative minimum on
the seam, the right-half face, and the two entropy-cap faces.  The existing
strict seam, cap-fiber, half-mean, and E8 interfaces imply exactly those four
fields.
-/

namespace GeneralCK

open Set
open SmallMeanPhiCutoff

/-- Boundary data actually used by the retained compact-minimum argument.
There is deliberately no below-cutoff pure-gap field. -/
structure RetainedPureGapMinimizerExclusions (S : ℝ) : Prop where
  seam : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → p.1 < p.2 → p.2 < 1 / 2 →
    e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  rightHalf : ∀ e f p, 0 < e → 0 < f → e < f →
    p ∈ retainedMeanSet S e f → p.2 = 1 / 2 → p.1 < p.2 →
    S < p.1 + p.2 → e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  leftCap : ∀ e f p, 0 < e → 0 < f → e < f →
    p ∈ retainedMeanSet S e f → e = H p.1 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  rightCap : ∀ e f p, 0 < e → 0 < f → e < f →
    p ∈ retainedMeanSet S e f → f = H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False

/-- The existing one-dimensional analytic interfaces produce precisely the
retained minimizer exclusions.  Notice that the cap fibers use the positive
cutoff `S`; the false zero-cutoff stationary point is therefore absent. -/
theorem retainedPureGapMinimizerExclusions_of_analyticOwners {S : ℝ}
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hseam : StrictSeamMinimizerExclusion S)
    (hcaps : CanonicalPureGapCapFiberOwnersExceptEqual S)
    (hcurv : HalfMeanCurvatureNegative) :
    RetainedPureGapMinimizerExclusions S := by
  let hcapOwners := hcaps.toOwners hleft hdet
  exact {
    seam := seam_minimizer_exclusion_of_stationary hseam
    rightHalf := by
      intro e f p he hf hef hp hhalf hmean hsum hecap hfcap hmin hneg
      exact rightHalf_minimizer_exclusion_of_curvature hcurv S e f p
        he hf hef hp hhalf hmean hsum hecap hfcap hmin hneg
    leftCap := leftCap_minimizer_exclusion_of_fiberOwners hcapOwners
    rightCap := rightCap_minimizer_exclusion_of_fiberOwners hcapOwners
  }

/-- A retained negative value would have a retained global minimum.  Equal
means are owned by correction convexity; the four genuine boundary cases are
excluded by `h`; E8 rules out the smooth-interior case. -/
theorem RetainedPureGapMinimizerExclusions.nonneg {S : ℝ}
    (h : RetainedPureGapMinimizerExclusions S) (hS : S < 1 / 2)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hE8 : E8StrictOnSlopeRange) {e f : ℝ}
    (he : 0 < e) (hef : e < f) :
    ∀ p ∈ retainedMeanSet S e f,
      0 ≤ canonicalPureGap p.1 p.2 e f := by
  intro p hp
  have hf : 0 < f := he.trans hef
  by_contra hpnonneg
  have hpneg : canonicalPureGap p.1 p.2 e f < 0 := lt_of_not_ge hpnonneg
  have he1 : e ≤ 1 := hp.1.2.2.2.1.trans (H_le_one p.1)
  have hf1 : f ≤ 1 := hp.1.2.2.2.2.trans (H_le_one p.2)
  obtain ⟨q, hq, hmin, hcase⟩ :=
    exists_retained_min_boundary_or_localMin (show S ≤ 1 by linarith)
      he hf he1 hf1
  have hqneg : canonicalPureGap q.1 q.2 e f < 0 :=
    lt_of_le_of_lt (hmin hp) hpneg
  have hequal : q.1 = q.2 → 0 ≤ canonicalPureGap q.1 q.2 e f := by
    intro heq
    have hm0 : 0 < q.1 := by
      have hne : q.1 ≠ 0 := by
        intro hzero
        have he0 : e ≤ 0 := by
          calc
            e ≤ H q.1 := hq.1.2.2.2.1
            _ = 0 := by rw [hzero, H_zero]
        exact (not_lt_of_ge he0) he
      exact lt_of_le_of_ne hq.1.1 (Ne.symm hne)
    have hm1 : q.1 < 1 :=
      lt_of_le_of_lt (hq.1.2.1.trans hq.1.2.2.1) (by norm_num)
    have heMem : e ∈ Ioc 0 (H q.1) := ⟨he, hq.1.2.2.2.1⟩
    have hfMem : f ∈ Ioc 0 (H q.1) := by
      refine ⟨hf, ?_⟩
      rw [heq]
      exact hq.1.2.2.2.2
    rw [← pureGap_eq_canonicalPureGap hq.1.2.1 hq.1.2.2.1, ← heq]
    exact pureGap_equal_mean_nonneg_of_convex
      (Correction.convexOn_entropyCorrection_square hleft hdet)
      hm0 hm1 heMem hfMem
  have hrightHalf : q.2 = 1 / 2 → False := by
    intro hyHalf
    by_cases heqMean : q.1 = q.2
    · exact (not_lt_of_ge (hequal heqMean)) hqneg
    have hmeanLt : q.1 < q.2 := lt_of_le_of_ne hq.1.2.1 heqMean
    by_cases hecapEq : e = H q.1
    · exact h.leftCap e f q he hf hef hq hecapEq hmin hqneg
    by_cases hfcapEq : f = H q.2
    · exact h.rightCap e f q he hf hef hq hfcapEq hmin hqneg
    have hecapLt : e < H q.1 := lt_of_le_of_ne hq.1.2.2.2.1 hecapEq
    have hfcapLt : f < H q.2 := lt_of_le_of_ne hq.1.2.2.2.2 hfcapEq
    by_cases hsumEq : q.1 + q.2 = S
    · have : (1 / 2 : ℝ) ≤ S := by
        rw [← hsumEq, hyHalf]
        linarith [hq.1.1]
      linarith
    have hsumLt : S < q.1 + q.2 :=
      lt_of_le_of_ne hq.2 (Ne.symm hsumEq)
    exact h.rightHalf e f q he hf hef hq hyHalf hmeanLt hsumLt
      hecapLt hfcapLt hmin hqneg
  have hseam : q.1 + q.2 = S → False := by
    intro hsum
    by_cases heqMean : q.1 = q.2
    · exact (not_lt_of_ge (hequal heqMean)) hqneg
    have hmeanLt : q.1 < q.2 := lt_of_le_of_ne hq.1.2.1 heqMean
    have hrightLt : q.2 < 1 / 2 := by
      by_contra hnot
      have hhalf : q.2 = 1 / 2 :=
        le_antisymm hq.1.2.2.1 (le_of_not_gt hnot)
      have : (1 / 2 : ℝ) ≤ S := by
        rw [← hsum, hhalf]
        linarith [hq.1.1]
      linarith
    by_cases hecapEq : e = H q.1
    · exact h.leftCap e f q he hf hef hq hecapEq hmin hqneg
    by_cases hfcapEq : f = H q.2
    · exact h.rightCap e f q he hf hef hq hfcapEq hmin hqneg
    have hecapLt : e < H q.1 := lt_of_le_of_ne hq.1.2.2.2.1 hecapEq
    have hfcapLt : f < H q.2 := lt_of_le_of_ne hq.1.2.2.2.2 hfcapEq
    exact h.seam e f q he hf hef hq hsum hmeanLt hrightLt
      hecapLt hfcapLt hmin hqneg
  rcases hcase with hsum | heq | hxHalf | hyHalf | hecapEq | hfcapEq | hlocal
  · exact hseam hsum
  · exact (not_lt_of_ge (hequal heq)) hqneg
  · have heqxy : q.1 = q.2 := by
      apply le_antisymm hq.1.2.1
      rw [hxHalf]
      exact hq.1.2.2.1
    exact (not_lt_of_ge (hequal heqxy)) hqneg
  · exact hrightHalf hyHalf
  · exact h.leftCap e f q he hf hef hq hecapEq hmin hqneg
  · exact h.rightCap e f q he hf hef hq hfcapEq hmin hqneg
  · rcases retainedMeanSet_boundary_or_interior he hq with
      hsum | heq | hxHalf | hyHalf | hecapEq | hfcapEq | hinterior
    · exact hseam hsum
    · exact (not_lt_of_ge (hequal heq)) hqneg
    · have heqxy : q.1 = q.2 := by
        apply le_antisymm hq.1.2.1
        rw [hxHalf]
        exact hq.1.2.2.1
      exact (not_lt_of_ge (hequal heqxy)) hqneg
    · exact hrightHalf hyHalf
    · exact h.leftCap e f q he hf hef hq hecapEq hmin hqneg
    · exact h.rightCap e f q he hf hef hq hfcapEq hmin hqneg
    · have hsumlt : q.1 + q.2 < 1 := by
        linarith [hinterior.2.2.1, hinterior.2.2.2.1]
      exact (not_localMin_of_e8SlopeRange hE8 hinterior.2.2.1 hsumlt
        (hinterior.2.2.1.trans hinterior.2.2.2.1)
        hinterior.2.2.2.1 he hf hlocal)

/-- The weakest current analytic inputs on the positive cutoff imply the
existing retained pure-gap owner. -/
theorem retainedPureGap_of_positiveCutoffAnalyticOwners
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hseam : StrictSeamMinimizerExclusion retainedCutoff)
    (hcaps : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff)
    (hcurv : HalfMeanCurvatureNegative)
    (hE8 : E8StrictOnSlopeRange) : RetainedPureGapOwner := by
  let hmin := retainedPureGapMinimizerExclusions_of_analyticOwners
    hleft hdet hseam hcaps hcurv
  intro e f he hef p hp
  exact hmin.nonneg (by norm_num [retainedCutoff]) hleft hdet hE8 he hef p hp

#print axioms retainedPureGapMinimizerExclusions_of_analyticOwners
#print axioms RetainedPureGapMinimizerExclusions.nonneg
#print axioms retainedPureGap_of_positiveCutoffAnalyticOwners

end GeneralCK

end


