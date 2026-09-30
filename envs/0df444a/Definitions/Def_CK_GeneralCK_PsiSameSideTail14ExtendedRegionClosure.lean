-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameSideTail14ExtendedRegionClosure
-- name    : CK_GeneralCK_PsiSameSideTail14ExtendedRegionClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:52:34.460759+00:00
-- url     : https://prove2.me/theorems/7c8b95bc-6a72-49d6-b4f2-69b488d437fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameSideTail14ExtendedRegionClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameSideTail14ExtendedRegionClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameSideTail14ExtendedRegionClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameSideTail14ExtendedRegionClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameSideTail14ExtendedRegionClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSameSideTail15RegionClosure
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail14Extended
import Definitions.Def_CK_GeneralCK_PsiAffineChildCertificate

-- ===== source module GeneralCK.PsiSameSideTail14ExtendedRegionClosure =====
section

/-!
# Exact same-side residual after the extended ratio-fourteen strip

The actual-law theorem covers the closed strip `b ≤ 17/40` and
`a/b ≤ 2⁻¹⁴`.  This owner records its strict complement within the
previous ratio-fifteen chart.
-/

namespace GeneralCK

def SameSidePsiTail14ExtendedChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    (μ.b ≤ 17 / 40 → 1 / 16384 < μ.a / μ.b) →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiTail15ChartOwner_of_tail14Extended
    (h : SameSidePsiTail14ExtendedChartOwner) : SameSidePsiTail15ChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hactive
  by_cases hstrip : μ.b ≤ 17 / 40 ∧ μ.a / μ.b ≤ 1 / 16384
  · exact sameSidePsiRatioTail14ExtendedOwner μ hab.le hstrip.1 hstrip.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hside hratio ?_ hactive
    intro hb
    by_contra hn
    exact hstrip ⟨hb, le_of_not_gt hn⟩

/-- The exact three-variable region remaining after the checked strips. -/
def sameSideTail14ExtendedScalarRegion (a b E : ℝ) : Prop :=
  a + b < 1 ∧ 1 / 16 < a + b ∧
  1 / 100 < H ((a + b) / 2) - E ∧ 1 / 1000000 < E ∧
  b ≤ 1 / 2 ∧ 1 / 32768 < a / b ∧
  (b ≤ 17 / 40 → 1 / 16384 < a / b)

/-- A valid two-floor child-support certificate on the residual three-variable
chart supplies the remaining actual-law owner. -/
theorem sameSidePsiTail14ExtendedChartOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate
      sameSideTail14ExtendedScalarRegion) :
    SameSidePsiTail14ExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hactive
  have hregion : sameSideTail14ExtendedScalarRegion μ.a μ.b μ.meanEntropy := by
    refine ⟨hsum, hmean, ?_, hE, hside, hratio, hstrip⟩
    simpa only [InteriorLaw.information, InteriorLaw.midpoint] using hinfo
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab
    hregion hactive.le

#print axioms sameSidePsiTail15ChartOwner_of_tail14Extended
#print axioms sameSidePsiTail14ExtendedChartOwner_of_affineCertificate

end GeneralCK

end


