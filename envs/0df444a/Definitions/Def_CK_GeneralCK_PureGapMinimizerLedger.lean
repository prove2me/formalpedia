-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapMinimizerLedger
-- name    : CK_GeneralCK_PureGapMinimizerLedger
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:28:42.237662+00:00
-- url     : https://prove2.me/theorems/75279af9-13be-4e5e-8d9a-f4249ac0f190
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapMinimizerLedger` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapMinimizerLedger` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapMinimizerLedger` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapMinimizerLedger (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapMinimizerLedger.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8OwnerClosure

-- ===== source module GeneralCK.PureGapMinimizerLedger =====
section

/-!
# Fixed-entropy minimizer ledger for the retained pure gap

The manuscript's half-mean and deterministic-cap arguments exclude negative
minimizers on their respective faces; they do not assert pointwise
nonnegativity on an entire face.  This file exposes that exact interface and
combines it with correction convexity at equal means and equation (8) in the
smooth interior.
-/

namespace GeneralCK

/-- The remaining manuscript obligations after equal means and the smooth
interior have been discharged.  Every boundary clause has precisely the
fixed-entropy minimizer hypothesis produced by compactness. -/
structure CanonicalPureGapMinimizerExclusions (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → p.1 < p.2 → p.2 < 1 / 2 →
    e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  rightHalf : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    p.2 = 1 / 2 → p.1 < p.2 → S < p.1 + p.2 →
    e < H p.1 → f < H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  leftCap : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    e = H p.1 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False
  rightCap : ∀ e f p, 0 < e → 0 < f → e < f → p ∈ retainedMeanSet S e f →
    f = H p.2 →
    IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
      (retainedMeanSet S e f) p →
    canonicalPureGap p.1 p.2 e f < 0 → False

/-- Pointwise outer-face owners imply the weaker, manuscript-shaped
minimizer exclusions. -/
theorem CanonicalPureGapOuterOwners.toMinimizerExclusions {S : ℝ}
    (houter : CanonicalPureGapOuterOwners S) :
    CanonicalPureGapMinimizerExclusions S where
  small := by
    intro e f p he hf hef hp hsmall
    exact houter.small e f p he hf hef.le hp hsmall
  seam := by
    intro e f p he hf hef hp hface _ _ _ _ _ hneg
    exact (not_lt_of_ge (houter.seam e f p he hf hef.le hp hface)) hneg
  rightHalf := by
    intro e f p he hf hef hp hface _ _ _ _ _ hneg
    exact (not_lt_of_ge (houter.rightHalf e f p he hf hef.le hp hface)) hneg
  leftCap := by
    intro e f p he hf hef hp hface _ hneg
    exact (not_lt_of_ge (houter.leftCap e f p he hf hef.le hp hface)) hneg
  rightCap := by
    intro e f p he hf hef hp hface _ hneg
    exact (not_lt_of_ge (houter.rightCap e f p he hf hef.le hp hface)) hneg

/-- Exact PG-1 closure: boundary minimizer exclusions, correction convexity,
and strict equation (8) imply the global positive-entropy pure gap. -/
theorem pureGap_nonneg_of_minimizerExclusions_e8 {S : ℝ} (hS : S < 1 / 2)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hexclude : CanonicalPureGapMinimizerExclusions S)
    (hE8 : E8StrictOnSlopeRange)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f := by
  apply pureGap_nonneg_of_canonicalPureGap _ ha₀ ha₁ hb₀ hb₁ he hf hecap hfcap
  intro x y g h hx hxy hy hg hgh hgcap hhcap
  let p : ℝ × ℝ := (x, y)
  have hpCanonical : p ∈ canonicalMeanSet g h :=
    ⟨hx, hxy, hy, hgcap, hhcap⟩
  by_cases heqEntropy : g = h
  · rw [← pureGap_eq_canonicalPureGap hxy hy]
    subst h
    exact pureGap_equal_entropy_nonneg hg x y
  have hghlt : g < h := lt_of_le_of_ne hgh heqEntropy
  by_cases hsmall : x + y < S
  · exact hexclude.small g h p hg (hg.trans hghlt) hghlt hpCanonical hsmall
  have hpRetained : p ∈ retainedMeanSet S g h :=
    ⟨hpCanonical, le_of_not_gt hsmall⟩
  by_contra hpnonneg
  have hpneg : canonicalPureGap p.1 p.2 g h < 0 := lt_of_not_ge hpnonneg
  have hg₁ : g ≤ 1 := hgcap.trans (H_le_one x)
  have hh₁ : h ≤ 1 := hhcap.trans (H_le_one y)
  obtain ⟨q, hq, hmin, hcase⟩ :=
    exists_retained_min_boundary_or_localMin (show S ≤ 1 by linarith)
      hg (hg.trans hghlt) hg₁ hh₁
  have hqneg : canonicalPureGap q.1 q.2 g h < 0 :=
    lt_of_le_of_lt (hmin hpRetained) hpneg
  have hequal : q.1 = q.2 → 0 ≤ canonicalPureGap q.1 q.2 g h := by
    intro heq
    have hm0 : 0 < q.1 := by
      have hne : q.1 ≠ 0 := by
        intro hzero
        have hg0 : g ≤ 0 := by
          calc
            g ≤ H q.1 := hq.1.2.2.2.1
            _ = 0 := by rw [hzero, H_zero]
        exact (not_lt_of_ge hg0) hg
      exact lt_of_le_of_ne hq.1.1 (Ne.symm hne)
    have hm1 : q.1 < 1 :=
      lt_of_le_of_lt (hq.1.2.1.trans hq.1.2.2.1) (by norm_num)
    have hgMem : g ∈ Set.Ioc 0 (H q.1) := ⟨hg, hq.1.2.2.2.1⟩
    have hhMem : h ∈ Set.Ioc 0 (H q.1) := by
      refine ⟨hg.trans hghlt, ?_⟩
      rw [heq]
      exact hq.1.2.2.2.2
    rw [← pureGap_eq_canonicalPureGap hq.1.2.1 hq.1.2.2.1, ← heq]
    exact pureGap_equal_mean_nonneg_of_convex
      (Correction.convexOn_entropyCorrection_square hleft hdet)
      hm0 hm1 hgMem hhMem
  have hrightHalf : q.2 = 1 / 2 → False := by
    intro hyHalf
    by_cases heqMean : q.1 = q.2
    · exact (not_lt_of_ge (hequal heqMean)) hqneg
    have hmeanLt : q.1 < q.2 := lt_of_le_of_ne hq.1.2.1 heqMean
    by_cases hgcapEq : g = H q.1
    · exact hexclude.leftCap g h q hg (hg.trans hghlt) hghlt hq hgcapEq hmin hqneg
    by_cases hhcapEq : h = H q.2
    · exact hexclude.rightCap g h q hg (hg.trans hghlt) hghlt hq hhcapEq hmin hqneg
    have hgcapLt : g < H q.1 := lt_of_le_of_ne hq.1.2.2.2.1 hgcapEq
    have hhcapLt : h < H q.2 := lt_of_le_of_ne hq.1.2.2.2.2 hhcapEq
    by_cases hsumEq : q.1 + q.2 = S
    · have : (1 / 2 : ℝ) ≤ S := by rw [← hsumEq, hyHalf]; linarith [hq.1.1]
      linarith
    have hsumLt : S < q.1 + q.2 :=
      lt_of_le_of_ne hq.2 (Ne.symm hsumEq)
    exact hexclude.rightHalf g h q hg (hg.trans hghlt) hghlt hq hyHalf
      hmeanLt hsumLt hgcapLt hhcapLt hmin hqneg
  have hseam : q.1 + q.2 = S → False := by
    intro hsum
    by_cases heqMean : q.1 = q.2
    · exact (not_lt_of_ge (hequal heqMean)) hqneg
    have hmeanLt : q.1 < q.2 := lt_of_le_of_ne hq.1.2.1 heqMean
    have hrightLt : q.2 < 1 / 2 := by
      by_contra hnot
      have hhalf : q.2 = 1 / 2 := le_antisymm hq.1.2.2.1 (le_of_not_gt hnot)
      have : (1 / 2 : ℝ) ≤ S := by rw [← hsum, hhalf]; linarith [hq.1.1]
      linarith
    by_cases hgcapEq : g = H q.1
    · exact hexclude.leftCap g h q hg (hg.trans hghlt) hghlt hq hgcapEq hmin hqneg
    by_cases hhcapEq : h = H q.2
    · exact hexclude.rightCap g h q hg (hg.trans hghlt) hghlt hq hhcapEq hmin hqneg
    have hgcapLt : g < H q.1 := lt_of_le_of_ne hq.1.2.2.2.1 hgcapEq
    have hhcapLt : h < H q.2 := lt_of_le_of_ne hq.1.2.2.2.2 hhcapEq
    exact hexclude.seam g h q hg (hg.trans hghlt) hghlt hq hsum
      hmeanLt hrightLt hgcapLt hhcapLt hmin hqneg
  rcases hcase with hsum | heq | hxHalf | hyHalf | hgcap' | hhcap' | hlocal
  · exact hseam hsum
  · exact (not_lt_of_ge (hequal heq)) hqneg
  · have heqxy : q.1 = q.2 := by
      apply le_antisymm hq.1.2.1
      rw [hxHalf]
      exact hq.1.2.2.1
    exact (not_lt_of_ge (hequal heqxy)) hqneg
  · exact hrightHalf hyHalf
  · exact hexclude.leftCap g h q hg (hg.trans hghlt) hghlt hq hgcap' hmin hqneg
  · exact hexclude.rightCap g h q hg (hg.trans hghlt) hghlt hq hhcap' hmin hqneg
  · rcases retainedMeanSet_boundary_or_interior hg hq with
      hsum | heq | hxHalf | hyHalf | hgcap' | hhcap' | hinterior
    · exact hseam hsum
    · exact (not_lt_of_ge (hequal heq)) hqneg
    · have heqxy : q.1 = q.2 := by
        apply le_antisymm hq.1.2.1
        rw [hxHalf]
        exact hq.1.2.2.1
      exact (not_lt_of_ge (hequal heqxy)) hqneg
    · exact hrightHalf hyHalf
    · exact hexclude.leftCap g h q hg (hg.trans hghlt) hghlt hq hgcap' hmin hqneg
    · exact hexclude.rightCap g h q hg (hg.trans hghlt) hghlt hq hhcap' hmin hqneg
    · have hsumlt : q.1 + q.2 < 1 := by
        linarith [hinterior.2.2.1, hinterior.2.2.2.1]
      exact (not_localMin_of_e8SlopeRange hE8 hinterior.2.2.1 hsumlt
        (hinterior.2.2.1.trans hinterior.2.2.2.1)
        hinterior.2.2.2.1 hg (hg.trans hghlt) hlocal)

/-- End-to-end general CK interface using the manuscript's boundary
minimizer exclusions rather than stronger pointwise boundary inequalities. -/
theorem generalCourtadeKumar_of_minimizer_ledger_and_e8 {S : ℝ}
    (hS : S < 1 / 2)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hexclude : CanonicalPureGapMinimizerExclusions S)
    (hE8 : E8StrictOnSlopeRange)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_canonical_scalar_owners href hleft hdet _ hpsi
  intro a c e f ha hac hc he hef hecap hfcap
  exact pureGap_nonneg_of_minimizerExclusions_e8 hS hleft hdet hexclude hE8
    ha (by linarith) (ha.trans hac) (by linarith) he (he.trans_le hef) hecap hfcap

end GeneralCK

end


