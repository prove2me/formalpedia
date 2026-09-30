-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointBellman
-- name    : CK_GeneralCK_PsiEndpointBellman
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:54:09.428263+00:00
-- url     : https://prove2.me/theorems/40404a37-fc15-40d2-a531-42aaaeb90148
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointBellman` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointBellman` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointBellman` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointBellman (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointBellman.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_GeneralCK_PsiLargerEntropyLaw
import Definitions.Def_CK_GeneralCK_PsiOppositeCornerDomain
import Definitions.Def_CK_GeneralCK_PsiRegionLedger

-- ===== source module GeneralCK.PsiEndpointBellman =====
section

/-!
# Analytic active-psi Bellman inequality and the complete opposite corner

The supporting plane and retained child comparison now give the actual law
inequality. No endpoint-cost input or numerical certificate is required.
-/

namespace GeneralCK.PsiEndpointBellman

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost :=
  (PsiLargerEntropyLaw.law_gap_margin_of_active μ hsum hEi hd hqsmall hactive).trans
    (PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd)

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have h := law_gap_margin μ hsum hEi hd hqsmall hactive
  linarith

end GeneralCK.PsiEndpointBellman

namespace GeneralCK

/-- The full deterministic opposite-corner owner, derived analytically for
actual finite laws and every positive child entropy allocation. -/
theorem oppositePsiCornerOwner : OppositePsiCornerOwner := by
  intro k μ _hab hsum _hmean _hinfo _hside hc hactive
  obtain ⟨_hq, hqsmall, _hE, hEi, hd, _ha, _hb⟩ :=
    PsiOppositeCornerDomain.corner_domain μ hsum hc
  exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) hd hqsmall hactive.le

end GeneralCK

#print axioms GeneralCK.PsiEndpointBellman.law_gap_margin
#print axioms GeneralCK.PsiEndpointBellman.law_gap_le_cost
#print axioms GeneralCK.oppositePsiCornerOwner

end


