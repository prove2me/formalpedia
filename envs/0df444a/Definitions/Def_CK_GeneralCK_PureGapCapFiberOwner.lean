-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapCapFiberOwner
-- name    : CK_GeneralCK_PureGapCapFiberOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:50:44.004089+00:00
-- url     : https://prove2.me/theorems/9ee34037-f90d-4cdd-98fd-df66699d7444
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapCapFiberOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapCapFiberOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapCapFiberOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapCapFiberOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapCapFiberOwner.lean)

import Definitions.Def_CK_GeneralCK_PureGapSeamOwner

-- ===== source module GeneralCK.PureGapCapFiberOwner =====
section

/-!
# Deterministic-cap fiber minimizer bridge

On either entropy-cap face, the capped mean is fixed by `entropyInverse`.
The remaining mean ranges over one explicit closed interval.  A minimum on
that interval is owned by its two endpoints or by an interior stationary
point.  This is the analytic reduction used in manuscript Lemma 6.2.
-/

namespace GeneralCK
open Set Filter

noncomputable def capFiberLower (S h fixedMean : ℝ) : ℝ :=
  max (entropyInverse h) (S - fixedMean)

/-- The six scalar owners left after reducing both deterministic-cap faces to
their one-dimensional fibers.  These are the smallest sign premises: two
endpoint values and stationary interior values on each fiber. -/
structure CanonicalPureGapCapFiberOwners (S : ℝ) : Prop where
  leftLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e)
      (capFiberLower S f (entropyInverse e)) e f
  leftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f
  leftStationary : ∀ e f c, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f
  rightLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) ≤ entropyInverse f →
    0 ≤ canonicalPureGap (capFiberLower S e (entropyInverse f))
      (entropyInverse f) e f
  rightUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) ≤ entropyInverse f →
    0 ≤ canonicalPureGap (entropyInverse f) (entropyInverse f) e f
  rightStationary : ∀ e f a, 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) < a → a < entropyInverse f →
    deriv (fun x => canonicalPureGap x (entropyInverse f) e f) a = 0 →
    0 ≤ canonicalPureGap a (entropyInverse f) e f

theorem leftCap_minimizer_exclusion_of_fiberOwners {S : ℝ}
    (owners : CanonicalPureGapCapFiberOwners S) :
    ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
      e = H p.1 →
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p →
      canonicalPureGap p.1 p.2 e f < 0 → False := by
  intro e f p he hf hef hp hecap hmin hneg
  let a := p.1
  let c := p.2
  have ha0 : 0 ≤ a := hp.1.1
  have hac : a ≤ c := hp.1.2.1
  have hc : c ≤ 1 / 2 := hp.1.2.2.1
  have hfcap : f ≤ H c := hp.1.2.2.2.2
  have hsum : S ≤ a + c := hp.2
  have hf1 : f ≤ 1 := hfcap.trans (H_le_one c)
  have haeq : entropyInverse e = a := by
    rw [hecap]
    exact entropyInverse_H_lower ha0 (hac.trans hc)
  have hif : entropyInverse f ≤ c := by
    have hmono := entropyInverse_mono hf.le (H_le_one c) hfcap
    simpa only [entropyInverse_H_lower (show 0 ≤ c by linarith) hc] using hmono
  let L := capFiberLower S f (entropyInverse e)
  have hLc : L ≤ c := by
    dsimp [L, capFiberLower]
    rw [haeq]
    exact max_le hif (by linarith)
  have hLhalf : L ≤ 1 / 2 := hLc.trans hc
  by_cases hcL : c = L
  · have hnonneg := owners.leftLower e f he hef hf1 hLhalf
    rw [haeq] at hnonneg
    have hLdef : L = capFiberLower S f a := by simp only [L, haeq]
    have hnonneg' : 0 ≤ canonicalPureGap a c e f := by
      rw [hcL, hLdef]
      exact hnonneg
    exact (not_lt_of_ge (by simpa only [a, c] using hnonneg')) hneg
  by_cases hcHalf : c = 1 / 2
  · have hnonneg := owners.leftUpper e f he hef hf1 hLhalf
    rw [haeq, ← hcHalf] at hnonneg
    exact (not_lt_of_ge hnonneg) hneg
  have hLc' : L < c := lt_of_le_of_ne hLc (Ne.symm hcL)
  have hc' : c < 1 / 2 := lt_of_le_of_ne hc hcHalf
  have hminFiber : IsMinOn (fun y => canonicalPureGap a y e f) (Icc L (1 / 2)) c := by
    intro y hy
    change canonicalPureGap a c e f ≤ canonicalPureGap a y e f
    have hymem : (a, y) ∈ retainedMeanSet S e f := by
      refine ⟨⟨ha0, ?_, hy.2, hecap.le, ?_⟩, ?_⟩
      · have hiy : entropyInverse f ≤ y := (le_max_left _ _).trans hy.1
        have hei : entropyInverse e ≤ entropyInverse f :=
          entropyInverse_mono he.le hf1 hef.le
        rw [haeq] at hei
        exact hei.trans hiy
      · have hiy : entropyInverse f ≤ y := (le_max_left _ _).trans hy.1
        rw [← (entropyInverse_spec hf.le hf1).2.2]
        exact H_strictMonoOn.monotoneOn
          ⟨(entropyInverse_spec hf.le hf1).1, (entropyInverse_spec hf.le hf1).2.1⟩
          ⟨(entropyInverse_spec hf.le hf1).1.trans hiy, hy.2⟩ hiy
      · have hLy : capFiberLower S f a ≤ y := by
          rw [← haeq]
          exact hy.1
        have : S - a ≤ y := (le_max_right _ _).trans hLy
        change S ≤ a + y
        linarith
    have hm : canonicalPureGap p.1 p.2 e f ≤ canonicalPureGap a y e f := hmin hymem
    simpa only [a, c] using hm
  have hlocal : IsLocalMin (fun y => canonicalPureGap a y e f) c :=
    hminFiber.isLocalMin (mem_of_superset (Ioo_mem_nhds hLc' hc') Ioo_subset_Icc_self)
  have hstationary := hlocal.deriv_eq_zero
  have hnonneg := owners.leftStationary e f c he hef hf1 hLc' hc' (by
    simpa only [haeq] using hstationary)
  rw [haeq] at hnonneg
  exact (not_lt_of_ge hnonneg) hneg

theorem rightCap_minimizer_exclusion_of_fiberOwners {S : ℝ}
    (owners : CanonicalPureGapCapFiberOwners S) :
    ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
      f = H p.2 →
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p →
      canonicalPureGap p.1 p.2 e f < 0 → False := by
  intro e f p he hf hef hp hfcap hmin hneg
  let a := p.1
  let c := p.2
  have ha0 : 0 ≤ a := hp.1.1
  have hac : a ≤ c := hp.1.2.1
  have hc : c ≤ 1 / 2 := hp.1.2.2.1
  have hecap : e ≤ H a := hp.1.2.2.2.1
  have hsum : S ≤ a + c := hp.2
  have hf1 : f ≤ 1 := by rw [hfcap]; exact H_le_one c
  have hceq : entropyInverse f = c := by
    rw [hfcap]
    exact entropyInverse_H_lower (ha0.trans hac) hc
  have hie : entropyInverse e ≤ a := by
    have hmono := entropyInverse_mono he.le (H_le_one a) hecap
    simpa only [entropyInverse_H_lower ha0 (hac.trans hc)] using hmono
  let L := capFiberLower S e (entropyInverse f)
  have hLa : L ≤ a := by
    dsimp [L, capFiberLower]
    rw [hceq]
    exact max_le hie (by linarith)
  have hLc : L ≤ entropyInverse f := by rw [hceq]; exact hLa.trans hac
  by_cases haL : a = L
  · have hnonneg := owners.rightLower e f he hef hf1 hLc
    rw [hceq] at hnonneg
    have hLdef : L = capFiberLower S e c := by simp only [L, hceq]
    have hnonneg' : 0 ≤ canonicalPureGap a c e f := by
      rw [haL, hLdef]
      exact hnonneg
    exact (not_lt_of_ge (by simpa only [a, c] using hnonneg')) hneg
  by_cases hacEq : a = c
  · have hnonneg := owners.rightUpper e f he hef hf1 hLc
    rw [hceq] at hnonneg
    have hnonneg' : 0 ≤ canonicalPureGap a c e f := by
      rw [hacEq]
      exact hnonneg
    exact (not_lt_of_ge (by simpa only [a, c] using hnonneg')) hneg
  have hLa' : L < a := lt_of_le_of_ne hLa (Ne.symm haL)
  have hac' : a < c := lt_of_le_of_ne hac hacEq
  have hminFiber : IsMinOn (fun x => canonicalPureGap x c e f) (Icc L c) a := by
    intro x hx
    change canonicalPureGap a c e f ≤ canonicalPureGap x c e f
    have hxmem : (x, c) ∈ retainedMeanSet S e f := by
      refine ⟨⟨?_, hx.2, hc, ?_, hfcap.le⟩, ?_⟩
      · have hix : entropyInverse e ≤ x := (le_max_left _ _).trans hx.1
        exact (entropyInverse_spec he.le (hef.le.trans hf1)).1.trans hix
      · have hix : entropyInverse e ≤ x := (le_max_left _ _).trans hx.1
        rw [← (entropyInverse_spec he.le (hef.le.trans hf1)).2.2]
        exact H_strictMonoOn.monotoneOn
          ⟨(entropyInverse_spec he.le (hef.le.trans hf1)).1,
            (entropyInverse_spec he.le (hef.le.trans hf1)).2.1⟩
          ⟨(entropyInverse_spec he.le (hef.le.trans hf1)).1.trans hix, hx.2.trans hc⟩ hix
      · have hLx : capFiberLower S e c ≤ x := by
          rw [← hceq]
          exact hx.1
        have : S - c ≤ x := (le_max_right _ _).trans hLx
        change S ≤ x + c
        linarith
    have hm : canonicalPureGap p.1 p.2 e f ≤ canonicalPureGap x c e f := hmin hxmem
    simpa only [a, c] using hm
  have hlocal : IsLocalMin (fun x => canonicalPureGap x c e f) a :=
    hminFiber.isLocalMin (mem_of_superset (Ioo_mem_nhds hLa' hac') Ioo_subset_Icc_self)
  have hstationary := hlocal.deriv_eq_zero
  have hnonneg := owners.rightStationary e f a he hef hf1 hLa' (by
    simpa only [hceq] using hac') (by simpa only [hceq] using hstationary)
  rw [hceq] at hnonneg
  exact (not_lt_of_ge (by simpa only [a, c] using hnonneg)) hneg

/-- The already-separated small and seam owners, before the cap-fiber bridge. -/
structure CanonicalPureGapNonCapExclusions (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → p.1 < p.2 → p.2 < 1 / 2 →
    e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False

/-- Supply the strict seam owner through its stationary certificate, leaving
only the small-region value owner alongside the cap-fiber data. -/
theorem nonCapExclusions_of_small_and_strictSeam {S : ℝ}
    (hsmall : ∀ e f p, 0 < e → 0 < f → e < f →
      p ∈ canonicalMeanSet e f → p.1 + p.2 < S →
      0 ≤ canonicalPureGap p.1 p.2 e f)
    (hseam : StrictSeamMinimizerExclusion S) :
    CanonicalPureGapNonCapExclusions S where
  small := hsmall
  seam := seam_minimizer_exclusion_of_stationary hseam

/-- Exact cap-owner assembly for `CanonicalPureGapNonHalfExclusions`. -/
theorem CanonicalPureGapNonCapExclusions.withCapFiberOwners {S : ℝ}
    (h : CanonicalPureGapNonCapExclusions S)
    (owners : CanonicalPureGapCapFiberOwners S) :
    CanonicalPureGapNonHalfExclusions S where
  small := h.small
  seam := h.seam
  leftCap := leftCap_minimizer_exclusion_of_fiberOwners owners
  rightCap := rightCap_minimizer_exclusion_of_fiberOwners owners

#print axioms leftCap_minimizer_exclusion_of_fiberOwners
#print axioms rightCap_minimizer_exclusion_of_fiberOwners
#print axioms CanonicalPureGapNonCapExclusions.withCapFiberOwners
#print axioms nonCapExclusions_of_small_and_strictSeam

end GeneralCK

end


