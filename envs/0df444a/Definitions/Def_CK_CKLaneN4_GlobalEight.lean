-- Prove2me | Definitions.Def_CK_CKLaneN4_GlobalEight
-- name    : CK_CKLaneN4_GlobalEight
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:19:59.488272+00:00
-- url     : https://prove2.me/theorems/a694e8ab-add0-4250-b245-8c0ba2024969
-- title:
--   Courtade–Kumar proof module `CKLaneN4.GlobalEight` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.GlobalEight` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.GlobalEight` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.GlobalEight (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/GlobalEight.lean)

import Definitions.Def_CK_CKLaneN4_GlobalSplit
import Definitions.Def_CK_CKLaneN4_EightTree
import Definitions.Def_CK_GeneralCK_PsiRetainedChildBridge_v2
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_GeneralCK_PsiRadialDeficit
import Definitions.Def_CK_GeneralCK_PsiLowEntropyRedesign

-- ===== source module CKLaneN4.GlobalEight =====
section

/-!
# Lane N4: the global cap-free eight-ratio theorem (psi-parent branch)

Archive: CK_GENERAL_COMPLETION `reduction/eight_global/GLOBAL_EIGHT_PROOF.md`.
For interior means and positive feasible entropies with `E = (e+f)/2`, `d = |a-b|`, `q = |1-a-b|`:

  `0 < E ≤ 11/200`, `d ≥ 8E`, `q ≤ 8E`  ⇒  `ζ ≥ R_max(phi,psi)`,

with no mean restriction and no shared entropy cap.  In the canonical orientation (`a ≤ b`,
`a + b ≤ 1`, so `q = 1 - a - b`, `d = b - a`) and in the psi-parent branch (`phi ≤ psi` at the parent)
this is `globalEightPsi` below.  (The phi-parent branch is the retained `ζ ≥ R_phi` input, i.e. the
route's `PhiBranch`; it is not used by any row of this lane, all of which are strictly psi-active.)

Proof, as archived: cap-free child decomposition §1–§2 (`retained_child_decomposition`, corpus,
`E ≤ 11/200`), parent correction (12) `≥ (7/10) q²/E` (`parent_gain_seven_tenths`: archived 77-leaf
`EIGHT_RATIO` partition + analytic tail `E ≤ 10^-4`), split loss (10) `≤ (1/5) q²/E`
(`split_term_lower`: archived 2-leaf `GLOBAL_SPLIT`), radial loss (11) `≤ (1/2) q²/E`
(`PsiRadialDeficit.radial_average_loss_le_half`; the archive states the sharper `479/1000`), endpoint
bound (5) (`PsiEndpointPlane.law_endpoint_logarithmic_lower`).  Total margin
`7/10 - 1/2 - 1/5 = 0 ≥ 0`.
-/

namespace CKLaneN4

open GeneralCK PsiChildEntropyCoupling PsiSignedSplit

/-- Parent correction (12): `E [eta(E) - eta(E + C(q))]/q² ≥ 7/10` for `0 < E ≤ 11/200`,
`0 ≤ q ≤ 8E` (archived 77-leaf partition plus the analytic tail). -/
theorem parent_gain_seven_tenths {E q : ℝ} (hE : 0 < E) (hEi : E ≤ 11 / 200) (hq : 0 ≤ q)
    (hqE : q ≤ 8 * E) :
    (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  by_cases ht : E ≤ 1 / 10000
  · exact parent_gain_tail hE ht hq hqE
  · have h := EightTree.sem_root
    simp only [SemEY, EightTree.root] at h
    exact h E q (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) hq

/-- The cap-free retained-child comparison: margin `≥ 0` for `E ≤ 11/200`. -/
theorem global_retained_child_margin {d q E t : ℝ} (hE : 0 < E) (hEi : E ≤ 11 / 200)
    (hd : 8 * E ≤ d) (hdq : d + q ≤ 1) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have hqd : q ≤ d := hqE.trans hd
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq hqd hE hEi ht
  have hg := parent_gain_seven_tenths hE hEi hq hqE
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith), abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (1 / 2) * (q ^ 2 / E) := by
    unfold radialLoss
    have e : q ^ 2 / (2 * E) = (1 / 2) * (q ^ 2 / E) := by ring
    linarith
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hs := split_term_lower (d := d) hE hEi hq (by linarith) (by linarith) hA hA' ht
  linarith

/-- Global eight-ratio theorem, psi-parent branch, canonical orientation, at law level. -/
theorem globalEightPsi_law {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have hact' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy ≤
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmean]
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := hqE.trans hd
  have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd hact'
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  have hEdef : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  rw [hca, hcb, hEdef, hce, hcf] at hb
  have hm := global_retained_child_margin hE hEi hd (by linarith [μ.a_interior.1]) hq0 hqE ht
  rw [hEdef] at hm
  have hcost := PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd
  rw [hEdef] at hcost
  have hgap : μ.gap = candidateGap B μ.a μ.b μ.e μ.f := rfl
  rw [hgap]
  linarith

/-- The global eight-ratio theorem (psi-parent branch) as a law-level proposition. -/
def GlobalEightPsi : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a + μ.b ≤ 1 → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem globalEightPsi : GlobalEightPsi :=
  fun _ μ hsum hEi hd hqE hact => globalEightPsi_law μ hsum hEi hd hqE hact

end CKLaneN4

end


