-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameSideTail8SmallMeanRegionClosure
-- name    : CK_GeneralCK_PsiSameSideTail8SmallMeanRegionClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:56:10.014855+00:00
-- url     : https://prove2.me/theorems/bd4ac3b4-c718-4793-9ae5-ee53463a9b9c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameSideTail8SmallMeanRegionClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameSideTail8SmallMeanRegionClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameSideTail8SmallMeanRegionClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameSideTail8SmallMeanRegionClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameSideTail8SmallMeanRegionClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSameSideTail14ExtendedRegionClosure
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail8SmallMean

-- ===== source module GeneralCK.PsiSameSideTail8SmallMeanRegionClosure =====
section

/-!
# Exact complement of the checked small-mean ratio-eight strip

The ratio-eight strip is closed for every physical child entropy allocation.
The residual keeps the previous ratio-fourteen chart and adds its strict
complement, still expressed using only the means and average entropy.
-/

namespace GeneralCK

def SameSidePsiTail8SmallMeanChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    (μ.b ≤ 17 / 40 → 1 / 16384 < μ.a / μ.b) →
    (μ.a + μ.b ≤ 1 / 4 → 1 / 256 < μ.a / μ.b) →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean
    (h : SameSidePsiTail8SmallMeanChartOwner) : SameSidePsiTail14ExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hactive
  by_cases hsmall : μ.a + μ.b ≤ 1 / 4 ∧ μ.a / μ.b ≤ 1 / 256
  · exact sameSidePsiRatioTail8SmallMeanOwner μ hab.le hsmall.1 hsmall.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hside hratio hstrip ?_ hactive
    intro hsum'
    by_contra hn
    exact hsmall ⟨hsum', le_of_not_gt hn⟩

def sameSideTail8SmallMeanScalarRegion (a b E : ℝ) : Prop :=
  sameSideTail14ExtendedScalarRegion a b E ∧
    (a + b ≤ 1 / 4 → 1 / 256 < a / b)

theorem sameSidePsiTail8SmallMeanChartOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate
      sameSideTail8SmallMeanScalarRegion) :
    SameSidePsiTail8SmallMeanChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hsmall hactive
  have hregion : sameSideTail8SmallMeanScalarRegion μ.a μ.b μ.meanEntropy := by
    refine ⟨⟨hsum, hmean, ?_, hE, hside, hratio, hstrip⟩, hsmall⟩
    simpa only [InteriorLaw.information, InteriorLaw.midpoint] using hinfo
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab
    hregion hactive.le

end GeneralCK

#print axioms GeneralCK.sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean
#print axioms GeneralCK.sameSidePsiTail8SmallMeanChartOwner_of_affineCertificate

end


