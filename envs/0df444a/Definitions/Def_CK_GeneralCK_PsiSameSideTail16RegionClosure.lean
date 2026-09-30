-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameSideTail16RegionClosure
-- name    : CK_GeneralCK_PsiSameSideTail16RegionClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:33:42.644836+00:00
-- url     : https://prove2.me/theorems/de3e4443-fbaa-4dd5-a038-ded251b64160
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameSideTail16RegionClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameSideTail16RegionClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameSideTail16RegionClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameSideTail16RegionClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameSideTail16RegionClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiExtendedRegionClosure
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail16

-- ===== source module GeneralCK.PsiSameSideTail16RegionClosure =====
section

/-!
# Exact same-side residual after the ratio-sixteen tail

The closed region `a/b≤2⁻¹⁶` is discharged for every actual law by
`sameSidePsiRatioTail16Owner`. The only remaining same-side chart premise
begins at the strict complement `2⁻¹⁶<a/b`, with the other canonical
conditions unchanged.
-/

namespace GeneralCK

def SameSidePsiTail16ChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 65536 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiExtendedChartOwner_of_tail16
    (h : SameSidePsiTail16ChartOwner) : SameSidePsiExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 65536
  · exact sameSidePsiRatioTail16Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

end GeneralCK

#print axioms GeneralCK.sameSidePsiExtendedChartOwner_of_tail16

end


