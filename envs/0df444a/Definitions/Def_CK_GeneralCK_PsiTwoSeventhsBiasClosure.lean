-- Prove2me | Definitions.Def_CK_GeneralCK_PsiTwoSeventhsBiasClosure
-- name    : CK_GeneralCK_PsiTwoSeventhsBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:45:54.353099+00:00
-- url     : https://prove2.me/theorems/557dfca2-4f1f-444d-81e8-01eeb9ce0aeb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiTwoSeventhsBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiTwoSeventhsBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiTwoSeventhsBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiTwoSeventhsBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiTwoSeventhsBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiTwoSeventhsRetainedWedge
import Definitions.Def_CK_GeneralCK_PsiTwoSeventhsParentClosure

-- ===== source module GeneralCK.PsiTwoSeventhsBiasClosure =====
section

/-! Automatic two-sevenths closure with exact remaining compact and central owners. -/

namespace GeneralCK.PsiTwoSeventhsBias

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 2 / 7)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  exact PsiTwoSeventhsRetainedWedge.law_gap_margin μ hsum hEu hd (by linarith)
    (PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hq hactive).le hactive

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 2 / 7)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  exact PsiTwoSeventhsRetainedWedge.law_gap_le_cost μ hsum hEu hd (by linarith)
    (PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hq hactive).le hactive

def compactRegion (a b E : ℝ) : Prop :=
  PsiQuarterBias.compactRegion a b E ∧
    (1 - a - b ≤ 2 / 7 → 11 / 200 < E) ∧
    (1 - a - b ≤ 2 / 7 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toQuarterCompactOwner (h : CompactOwner) : PsiQuarterBias.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 2 / 7 ∧ μ.meanEntropy ≤ 11 / 200
  · have hold := hregion.1.1.1.1
    exact PsiTwoSeventhsRetainedWedge.law_gap_le_cost μ hold.1.1.1.1.le hw.2
      (by linarith [hold.1.1.1.2.2.2.1]) hw.1
      (PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hw.1 hactive.le).le hactive.le
  · apply h k μ ⟨hregion, ?_, ?_⟩ hactive
    · intro hq
      by_contra hn
      exact hw ⟨hq, le_of_not_gt hn⟩
    · intro hq
      exact PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hq hactive.le

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hold := hregion.1.1.1.1.1
  have hab : μ.a < μ.b := by
    linarith [hold.1.1.1.2.1, hold.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 2 / 7 < 1 - a - b) ∧
    (1 - a - b ≤ 2 / 7 → 1 - a - b < 8 * E)

def centralRegion (a b E : ℝ) : Prop :=
  PsiQuarterBias.centralRegion a b E ∧ centralRemainder a b E

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toQuarterCentralOwner (h : CentralOwner) : PsiQuarterBias.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hr₁ hr₂ hr₃ hr₄ hr₅ hr₆ hr₇ hr₈ hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 2 / 7
  · exact PsiTwoSeventhsRetainedWedge.law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2
      (PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hw.2.2 hactive.le).le hactive.le
  · apply h k μ hab ⟨?_, ?_, ?_⟩ hactive
    · refine ⟨⟨⟨⟨⟨⟨⟨hsum, hb, ha, hinfo, hr₁, ?_⟩, hr₂, hr₃⟩, hr₄⟩, hr₅⟩, hr₆⟩, hr₇⟩, hr₈⟩
      intro hq
      exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact PsiTwoSeventhsParent.active_bias_lt_eight_entropy μ hq hactive.le

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hregion hactive
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

end GeneralCK.PsiTwoSeventhsBias

#print axioms GeneralCK.PsiTwoSeventhsBias.law_gap_margin
#print axioms GeneralCK.PsiTwoSeventhsBias.law_gap_le_cost
#print axioms GeneralCK.PsiTwoSeventhsBias.toQuarterCompactOwner
#print axioms GeneralCK.PsiTwoSeventhsBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiTwoSeventhsBias.toQuarterCentralOwner
#print axioms GeneralCK.PsiTwoSeventhsBias.centralOwner_of_affineCertificate

end


