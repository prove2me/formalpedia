-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameSideTail15RegionClosure
-- name    : CK_GeneralCK_PsiSameSideTail15RegionClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:37:38.092276+00:00
-- url     : https://prove2.me/theorems/e627fa9c-b5c5-43b2-a043-4b47f8b8f217
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameSideTail15RegionClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameSideTail15RegionClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameSideTail15RegionClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameSideTail15RegionClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameSideTail15RegionClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSameSideTail16RegionClosure
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail15

-- ===== source module GeneralCK.PsiSameSideTail15RegionClosure =====
section

/-!
# Exact same-side residual after the ratio-fifteen tail

Every actual law with `a/b≤2⁻¹⁵` is closed by the checked tail theorem once
the latter module passes its direct Lean audit. The remaining owner has
the strict complement ratio; every other canonical chart condition remains.
-/

namespace GeneralCK

def SameSidePsiTail15ChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiExtendedChartOwner_of_tail15
    (h : SameSidePsiTail15ChartOwner) : SameSidePsiExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 32768
  · exact sameSidePsiRatioTail15Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

theorem sameSidePsiTail16ChartOwner_of_tail15
    (h : SameSidePsiTail15ChartOwner) : SameSidePsiTail16ChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 32768
  · exact sameSidePsiRatioTail15Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

end GeneralCK

#print axioms GeneralCK.sameSidePsiExtendedChartOwner_of_tail15
#print axioms GeneralCK.sameSidePsiTail16ChartOwner_of_tail15

end


