-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsBiasClosure
-- name    : CK_GeneralCK_PsiThreeTenthsBiasClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:12.398453+00:00
-- url     : https://prove2.me/theorems/debd31d1-4c1a-4793-8085-294576c8e0a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsBiasClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsBiasClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsBiasClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsBiasClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsBiasClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiThreeTenthsRetainedWedge
import Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentClosure

-- ===== source module GeneralCK.PsiThreeTenthsBiasClosure =====
section

/-! Automatic three-tenths closure with exact remaining compact and central owners. -/

namespace GeneralCK.PsiThreeTenthsBias

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 3 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  exact PsiThreeTenthsRetainedWedge.law_gap_margin μ hsum hEu hd (by linarith)
    (PsiThreeTenthsParent.active_bias_lt_eight_entropy μ hq hactive).le hactive

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEu : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) (hq : 1 - μ.a - μ.b ≤ 3 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  exact PsiThreeTenthsRetainedWedge.law_gap_le_cost μ hsum hEu hd (by linarith)
    (PsiThreeTenthsParent.active_bias_lt_eight_entropy μ hq hactive).le hactive

def compactRegion (a b E : ℝ) : Prop :=
  PsiTwoSeventhsBias.compactRegion a b E ∧
    (1 - a - b ≤ 3 / 10 → 11 / 200 < E) ∧
    (1 - a - b ≤ 3 / 10 → 1 - a - b < 8 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toTwoSeventhsCompactOwner (h : CompactOwner) : PsiTwoSeventhsBias.CompactOwner := by
  intro k μ hregion hactive
  by_cases hw : 1 - μ.a - μ.b ≤ 3 / 10 ∧ μ.meanEntropy ≤ 11 / 200
  · have hold := hregion.1.1.1.1.1
    exact PsiThreeTenthsRetainedWedge.law_gap_le_cost μ hold.1.1.1.1.le hw.2
      (by linarith [hold.1.1.1.2.2.2.1]) hw.1
      (PsiThreeTenthsParent.active_bias_lt_eight_entropy μ hw.1 hactive.le).le hactive.le
  · apply h k μ ⟨hregion, ?_, ?_⟩ hactive
    · intro hq
      by_contra hn
      exact hw ⟨hq, le_of_not_gt hn⟩
    · intro hq
      exact PsiThreeTenthsParent.active_bias_lt_eight_entropy μ hq hactive.le

theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hold := hregion.1.1.1.1.1.1
  have hab : μ.a < μ.b := by
    linarith [hold.1.1.1.2.1, hold.1.1.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 3 / 10 < 1 - a - b) ∧
    (1 - a - b ≤ 3 / 10 → 1 - a - b < 8 * E)

def centralRegion (a b E : ℝ) : Prop :=
  PsiTwoSeventhsBias.centralRegion a b E ∧ centralRemainder a b E

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toTwoSeventhsCentralOwner (h : CentralOwner) : PsiTwoSeventhsBias.CentralOwner := by
  intro k μ hab hregion hactive
  by_cases hw : μ.meanEntropy ≤ 11 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 3 / 10
  · have hsum : μ.a + μ.b < 1 := hregion.1.1.1.1.1.1.1.1
    exact law_gap_le_cost μ hsum.le hw.1 hw.2.1 hw.2.2 hactive.le
  · apply h k μ hab ⟨hregion, ?_, ?_⟩ hactive
    · by_contra hn
      push Not at hn
      exact hw hn
    · intro hq
      exact PsiThreeTenthsParent.active_bias_lt_eight_entropy μ hq hactive.le

theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hregion hactive
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

end GeneralCK.PsiThreeTenthsBias

#print axioms GeneralCK.PsiThreeTenthsBias.law_gap_margin
#print axioms GeneralCK.PsiThreeTenthsBias.law_gap_le_cost
#print axioms GeneralCK.PsiThreeTenthsBias.toTwoSeventhsCompactOwner
#print axioms GeneralCK.PsiThreeTenthsBias.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiThreeTenthsBias.toTwoSeventhsCentralOwner
#print axioms GeneralCK.PsiThreeTenthsBias.centralOwner_of_affineCertificate

end


