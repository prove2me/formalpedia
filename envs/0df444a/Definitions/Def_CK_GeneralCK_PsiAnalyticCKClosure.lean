-- Prove2me | Definitions.Def_CK_GeneralCK_PsiAnalyticCKClosure
-- name    : CK_GeneralCK_PsiAnalyticCKClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:17:56.504924+00:00
-- url     : https://prove2.me/theorems/dc2d34a1-94e1-4b95-b8b6-d2338a1d18bb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiAnalyticCKClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiAnalyticCKClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiAnalyticCKClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiAnalyticCKClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiAnalyticCKClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiAfterCornerClosure

-- ===== source module GeneralCK.PsiAnalyticCKClosure =====
section

/-!
# Direct target connection for the remaining analytic owners

This module connects the completed active-psi regions to the approved
all-dimensions CK statement. The unequal-mean phi inequality and three
remaining psi owners are explicit hypotheses. It does not assert a completed
unconditional CK proof.
-/

namespace GeneralCK

theorem finiteHybridBellman_of_phi_and_remaining_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiAnalyticRemainingOwners) : FiniteHybridBellman :=
  finiteHybridBellman_of_remaining_regions hphi (residualPsi_of_analytic_remaining_owners hpsi)

/-- The approved target follows once the phi theorem and these three
remaining active-psi owners are supplied. -/
theorem generalCourtadeKumar_of_phi_and_remaining_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiAnalyticRemainingOwners) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_remaining_regions hphi (residualPsi_of_analytic_remaining_owners hpsi)

end GeneralCK

#print axioms GeneralCK.finiteHybridBellman_of_phi_and_remaining_psi
#print axioms GeneralCK.generalCourtadeKumar_of_phi_and_remaining_psi

end


