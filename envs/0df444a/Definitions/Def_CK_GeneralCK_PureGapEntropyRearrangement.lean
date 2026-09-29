-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapEntropyRearrangement
-- name    : CK_GeneralCK_PureGapEntropyRearrangement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:54:59.638654+00:00
-- url     : https://prove2.me/theorems/38a01abf-bc43-45d9-9f22-66a913c57544
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapEntropyRearrangement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapEntropyRearrangement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapEntropyRearrangement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapEntropyRearrangement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapEntropyRearrangement.lean)

import Definitions.Def_CK_GeneralCK_PureGapSymmetry
import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Entropy rearrangement for the retained pure gap

This proves the interior part of the manuscript's global entropy
rearrangement lemma.  The key input is the already verified nonnegative
radius--entropy mixed derivative of `radialPhi`.
-/

namespace GeneralCK
open Set

/-- At a positive radius, the radius derivative of `radialPhi` is monotone
in the positive entropy coordinate. -/
theorem deriv_radialPhi_radius_mono_entropy {z f e : ℝ}
    (hz : 0 < z) (hf : 0 < f) (hfe : f ≤ e) :
    deriv (fun r => radialPhi r f) z ≤ deriv (fun r => radialPhi r e) z := by
  have he : 0 < e := hf.trans_le hfe
  let g : ℝ → ℝ := fun h => deriv (fun r => radialPhi r h) z
  have hg : MonotoneOn g (Icc f e) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc f e)
    · intro h hh
      exact (hasDerivAt_deriv_radialPhi_radius_entropy hz
        (hf.trans_le hh.1)).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hasDerivAt_deriv_radialPhi_radius_entropy hz
        (hf.trans hh.1)).differentiableAt.differentiableWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact deriv_radialPhi_radius_entropy_nonneg hz (hf.trans hh.1)
  exact hg ⟨le_rfl, hfe⟩ ⟨hfe, le_rfl⟩ hfe

/-- Positive entropy increments of `radialPhi` increase with its positive
radius.  This is the rectangular supermodularity inequality used in PG-1. -/
theorem radialPhi_entropy_increment_mono_radius {z₀ z₁ f e : ℝ}
    (hz₀ : 0 ≤ z₀) (hz : z₀ ≤ z₁) (hf : 0 < f) (hfe : f ≤ e) :
    radialPhi z₀ e - radialPhi z₀ f ≤
      radialPhi z₁ e - radialPhi z₁ f := by
  have he : 0 < e := hf.trans_le hfe
  let q : ℝ → ℝ := fun z => radialPhi z e - radialPhi z f
  have hq : MonotoneOn q (Icc z₀ z₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc z₀ z₁)
    · have heconst : ContinuousOn (fun _ : ℝ => eta e) (Ici 0) := continuousOn_const
      have hfconst : ContinuousOn (fun _ : ℝ => eta f) (Ici 0) := continuousOn_const
      have hecont := (heconst.sub (continuousOn_F_radius he)).mono
          (show Icc z₀ z₁ ⊆ Ici 0 by
            intro z hzmem
            exact hz₀.trans hzmem.1)
      have hfcont := (hfconst.sub (continuousOn_F_radius hf)).mono
          (show Icc z₀ z₁ ⊆ Ici 0 by
            intro z hzmem
            exact hz₀.trans hzmem.1)
      have hecont' : ContinuousOn (fun z => radialPhi z e) (Icc z₀ z₁) := by
        apply hecont.congr
        intro z hzmem
        rfl
      have hfcont' : ContinuousOn (fun z => radialPhi z f) (Icc z₀ z₁) := by
        apply hfcont.congr
        intro z hzmem
        rfl
      change ContinuousOn ((fun z => radialPhi z e) - fun z => radialPhi z f) (Icc z₀ z₁)
      exact hecont'.sub hfcont'
    · intro z hzmem
      rw [interior_Icc] at hzmem
      exact ((hasDerivAt_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1)
        he).sub
        (hasDerivAt_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1) hf)).differentiableAt.differentiableWithinAt
    · intro z hzmem
      rw [interior_Icc] at hzmem
      have hm := deriv_radialPhi_radius_mono_entropy
        (lt_of_le_of_lt hz₀ hzmem.1) hf hfe
      have heq := ((hasDerivAt_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1)
          he).sub
          (hasDerivAt_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1) hf)).deriv
      change deriv q z = _ at heq
      rw [heq]
      rw [deriv_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1) he,
        deriv_radialPhi_radius (lt_of_le_of_lt hz₀ hzmem.1) hf] at hm
      linarith
  exact hq ⟨le_rfl, hz⟩ ⟨hz, le_rfl⟩ hz

/-- On the strict lower-half mean chamber, putting the smaller entropy on
the smaller mean cannot increase the retained pure gap. -/
theorem pureGap_entropy_rearrangement_lower_half {a c f e : ℝ}
    (hac : a ≤ c) (hc : c ≤ 1 / 2) (hf : 0 < f) (hfe : f ≤ e) :
    pureGap a c f e ≤ pureGap a c e f := by
  have hza : 0 ≤ 1 - 2 * c := by linarith
  have hzac : 1 - 2 * c ≤ 1 - 2 * a := by linarith
  have hrect := radialPhi_entropy_increment_mono_radius hza hzac hf hfe
  have hphi : phi c e - phi c f ≤ phi a e - phi a f := by
    simpa only [phi, radialPhi, abs_of_nonneg (show 0 ≤ 1 - 2 * c by linarith),
      abs_of_nonneg (show 0 ≤ 1 - 2 * a by linarith)] using hrect
  unfold pureGap fourMomentLowerBound candidateGap
  rw [entropyCorrection_comm f e]
  rw [add_comm f e]
  linarith

/-- Combining exact mean reflections, label exchange, and entropy
rearrangement reduces the positive-entropy physical theorem to the chamber
`0 ≤ a ≤ c ≤ 1/2` and `e ≤ f`. -/
theorem pureGap_nonneg_of_sorted_lower_half_ordered_entropy
    (howner : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
        0 ≤ pureGap a c e f)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f) :
    0 ≤ pureGap a b e f := by
  obtain ⟨x, y, g, h, hx, hxy, hy, horient, hgap⟩ :=
    exists_sorted_lower_half_pureGap ha₀ ha₁ hb₀ hb₁
  rcases horient with ⟨rfl, rfl, _hHx, _hHy⟩ | ⟨rfl, rfl, _hHx, _hHy⟩
  · rw [← hgap]
    rcases le_total e f with hef | hfe
    · exact howner x y e f hx hxy hy he hef
    · have hbase := howner x y f e hx hxy hy hf hfe
      exact hbase.trans (pureGap_entropy_rearrangement_lower_half hxy hy hf hfe)
  · rw [← hgap]
    rcases le_total f e with hfe | hef
    · exact howner x y f e hx hxy hy hf hfe
    · have hbase := howner x y e f hx hxy hy he hef
      exact hbase.trans (pureGap_entropy_rearrangement_lower_half hxy hy he hef)

/-- Feasibility-aware form of the preceding reduction.  This is the exact
canonical PG-1 interface: the remaining owner is needed only for sorted
lower-half means, ordered positive entropies, and the two marginal caps. -/
theorem pureGap_nonneg_of_sorted_lower_half_ordered_entropy_feasible
    (howner : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f := by
  obtain ⟨x, y, g, h, hx, hxy, hy, horient, hgap⟩ :=
    exists_sorted_lower_half_pureGap ha₀ ha₁ hb₀ hb₁
  have hHxy : H x ≤ H y := by
    exact H_strictMonoOn.monotoneOn
      ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  have finish (hg : 0 < g) (hh : 0 < h)
      (hgcap : g ≤ H x) (hhcap : h ≤ H y) : 0 ≤ pureGap x y g h := by
    rcases le_total g h with hgh | hhg
    · exact howner x y g h hx hxy hy hg hgh hgcap hhcap
    · have hbase := howner x y h g hx hxy hy hh hhg
          (hhg.trans hgcap) (hgcap.trans hHxy)
      exact hbase.trans (pureGap_entropy_rearrangement_lower_half hxy hy hh hhg)
  rw [← hgap]
  rcases horient with ⟨rfl, rfl, hHx, hHy⟩ | ⟨rfl, rfl, hHx, hHy⟩
  · exact finish he hf (by rwa [hHx]) (by rwa [hHy])
  · exact finish hf he (by rwa [hHx]) (by rwa [hHy])

end GeneralCK


