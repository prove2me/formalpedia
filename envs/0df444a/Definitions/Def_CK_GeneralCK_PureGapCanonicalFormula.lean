-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapCanonicalFormula
-- name    : CK_GeneralCK_PureGapCanonicalFormula
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:03:56.857797+00:00
-- url     : https://prove2.me/theorems/beba68db-8004-4c83-9b84-06a3cd047f04
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapCanonicalFormula` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapCanonicalFormula` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapCanonicalFormula` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapCanonicalFormula (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapCanonicalFormula.lean)

import Definitions.Def_CK_GeneralCK_PureGapEntropyRearrangement

/-!
# Canonical formula for the retained pure gap

This identifies the project definition of `pureGap` with the manuscript's
explicit lower-half four-variable function `G` on its canonical mean chart.
-/

namespace GeneralCK

/-- The explicit retained pure gap on sorted lower-half means. -/
noncomputable def canonicalPureGap (a c e f : ℝ) : ℝ :=
  F (c - a) ((e + f) / 2) + entropyCorrection e f -
    radialPhi (1 - a - c) ((e + f) / 2) +
    (radialPhi (1 - 2 * a) e + radialPhi (1 - 2 * c) f) / 2

/-- Exact identification of `pureGap` with the manuscript's canonical `G`. -/
theorem pureGap_eq_canonicalPureGap {a c e f : ℝ}
    (hac : a ≤ c) (hc : c ≤ 1 / 2) :
    pureGap a c e f = canonicalPureGap a c e f := by
  have hac' : a - c ≤ 0 := sub_nonpos.mpr hac
  have hcenter : 0 ≤ 1 - a - c := by linarith
  have haRad : 0 ≤ 1 - 2 * a := by linarith
  have hcRad : 0 ≤ 1 - 2 * c := by linarith
  unfold pureGap fourMomentLowerBound candidateGap canonicalPureGap phi radialPhi
  rw [abs_of_nonpos hac', abs_of_nonneg haRad, abs_of_nonneg hcRad,
    abs_of_nonneg (show 0 ≤ 1 - 2 * ((a + c) / 2) by linarith)]
  ring

/-- The global positive-entropy pure-gap theorem follows from nonnegativity
of the explicit canonical `G` on the ordered marginal-physical chamber. -/
theorem pureGap_nonneg_of_canonicalPureGap
    (hG : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ canonicalPureGap a c e f)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f := by
  apply pureGap_nonneg_of_sorted_lower_half_ordered_entropy_feasible
    (a := a) (b := b) (e := e) (f := f) _ ha₀ ha₁ hb₀ hb₁ he hf hecap hfcap
  intro x y g h hx hxy hy hg hgh hgcap hhcap
  rw [pureGap_eq_canonicalPureGap hxy hy]
  exact hG x y g h hx hxy hy hg hgh hgcap hhcap

end GeneralCK


