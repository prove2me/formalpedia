-- Prove2me | Definitions.Def_CK_GeneralCK_PsiPositiveEntropyClosure
-- name    : CK_GeneralCK_PsiPositiveEntropyClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:22:47.183143+00:00
-- url     : https://prove2.me/theorems/63bfb09b-d1c9-42e9-9b55-cc69f15feea1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiPositiveEntropyClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiPositiveEntropyClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiPositiveEntropyClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiPositiveEntropyClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiPositiveEntropyClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiAnalyticCKClosure
import Definitions.Def_CK_GeneralCK_PsiGeneralLowEntropy

-- ===== source module GeneralCK.PsiPositiveEntropyClosure =====
section

/-!
# Remaining active-psi owners above the proved entropy cutoff

The canonical low-entropy theorem covers both mean orientations. Therefore
the same-side chart and opposite central owner only need new proofs above
average entropy 10^-6. The opposite compact ledger already has this strict
cutoff. This file makes that reduction explicit in the final CK dependency
interface; it does not assert any remaining owner without a proof.
-/

namespace GeneralCK

def SameSidePsiPositiveEntropyChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 4294967296 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

def OppositePsiPositiveEntropyCentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The compact ledger already explicitly requires E>10^-6. -/
abbrev OppositePsiPositiveEntropyCompactOwner : Prop := OppositePsiCompactOwner

structure ResidualPsiPositiveEntropyRemainingOwners : Prop where
  sameChart : SameSidePsiPositiveEntropyChartOwner
  oppositeCentral : OppositePsiPositiveEntropyCentralOwner
  oppositeCompact : OppositePsiPositiveEntropyCompactOwner

theorem sameSidePsiChartOwner_of_positiveEntropy
    (h : SameSidePsiPositiveEntropyChartOwner) : SameSidePsiChartOwner := by
  intro k μ hab hsum hmean hinfo hside hratio hactive
  by_cases hE : μ.meanEntropy ≤ 1 / 1000000
  · exact PsiGeneralLowEntropy.law_gap_le_cost μ hab hsum hmean hE hactive.le
  · exact h k μ hab hsum hmean hinfo (lt_of_not_ge hE) hside hratio hactive

theorem oppositePsiCentralOwner_of_positiveEntropy
    (h : OppositePsiPositiveEntropyCentralOwner) : OppositePsiCentralOwner := by
  intro k μ hab hsum hmean hinfo hside ha hactive
  by_cases hE : μ.meanEntropy ≤ 1 / 1000000
  · exact PsiGeneralLowEntropy.law_gap_le_cost μ hab hsum hmean hE hactive.le
  · exact h k μ hab hsum hmean hinfo (lt_of_not_ge hE) hside ha hactive

/-- Restore the three original owner domains by applying the checked global
low-entropy theorem wherever the strict entropy cutoff does not hold. -/
theorem ResidualPsiPositiveEntropyRemainingOwners.toAnalyticRemainingOwners
    (h : ResidualPsiPositiveEntropyRemainingOwners) : ResidualPsiAnalyticRemainingOwners where
  sameChart := sameSidePsiChartOwner_of_positiveEntropy h.sameChart
  oppositeCentral := oppositePsiCentralOwner_of_positiveEntropy h.oppositeCentral
  oppositeCompact := h.oppositeCompact

theorem residualPsi_of_positive_entropy_remaining_owners
    (h : ResidualPsiPositiveEntropyRemainingOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_analytic_remaining_owners h.toAnalyticRemainingOwners

theorem finiteHybridBellman_of_phi_and_positive_entropy_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiPositiveEntropyRemainingOwners) : FiniteHybridBellman :=
  finiteHybridBellman_of_phi_and_remaining_psi hphi hpsi.toAnalyticRemainingOwners

/-- The approved CK target now needs only the unequal-mean phi input and
three active-psi chart inputs with average entropy strictly above 10^-6. -/
theorem generalCourtadeKumar_of_phi_and_positive_entropy_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiPositiveEntropyRemainingOwners) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_phi_and_remaining_psi hphi hpsi.toAnalyticRemainingOwners

end GeneralCK

#print axioms GeneralCK.sameSidePsiChartOwner_of_positiveEntropy
#print axioms GeneralCK.oppositePsiCentralOwner_of_positiveEntropy
#print axioms GeneralCK.ResidualPsiPositiveEntropyRemainingOwners.toAnalyticRemainingOwners
#print axioms GeneralCK.residualPsi_of_positive_entropy_remaining_owners
#print axioms GeneralCK.finiteHybridBellman_of_phi_and_positive_entropy_psi
#print axioms GeneralCK.generalCourtadeKumar_of_phi_and_positive_entropy_psi

end


