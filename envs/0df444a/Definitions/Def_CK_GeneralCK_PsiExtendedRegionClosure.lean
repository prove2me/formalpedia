-- Prove2me | Definitions.Def_CK_GeneralCK_PsiExtendedRegionClosure
-- name    : CK_GeneralCK_PsiExtendedRegionClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:26:33.510102+00:00
-- url     : https://prove2.me/theorems/c7223e65-37fa-4a6c-a190-1f4069164d85
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiExtendedRegionClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiExtendedRegionClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiExtendedRegionClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiExtendedRegionClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiExtendedRegionClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiPositiveEntropyClosure
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail24
import Definitions.Def_CK_GeneralCK_PsiOuterEntropyExtension
import Definitions.Def_CK_GeneralCK_PsiBalancedMeans

-- ===== source module GeneralCK.PsiExtendedRegionClosure =====
section

/-!
# Exact residual domains after the analytic region extensions

The proved ratio tail, balanced face, and outer low-entropy region are
consumed explicitly. The three remaining owner predicates are hypotheses,
not assertions that the remaining chart inequalities have been proved.

The ratio-five endpoint cost gain by itself does not imply a hybrid chart
inequality and is not used to delete a region here.
-/

namespace GeneralCK

/-- The same-side chart above the enlarged ratio tail and global entropy
cutoff. Strict unbalance already follows from `a<b≤1/2`. -/
def SameSidePsiExtendedChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 16777216 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The central opposite chart has strict unbalance. Its `a=1/10` face
needs a new proof only above the stronger outer entropy cutoff; at `a>1/10`
the global cutoff remains `10⁻⁶`. The implication records this distinction. -/
def OppositePsiExtendedCentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The compact opposite chart retains its original open `a<1/10` face
and excludes the proved balanced face and outer entropy region. -/
def OppositePsiExtendedCompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 2 ≤ μ.b →
    1 / 268435456 < μ.a → μ.a < 1 / 10 →
    1 / 8192 < μ.a + 1 - μ.b →
    1 / 32768 < μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

structure ResidualPsiExtendedRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : OppositePsiExtendedCentralOwner
  oppositeCompact : OppositePsiExtendedCompactOwner

theorem sameSidePsiPositiveEntropyChartOwner_of_extended
    (h : SameSidePsiExtendedChartOwner) : SameSidePsiPositiveEntropyChartOwner := by
  intro k μ hab _hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 16777216
  · exact sameSidePsiRatioTail24Owner μ hab.le hside hr hactive.le
  · exact h k μ hab (by linarith) hmean hinfo hE hside (lt_of_not_ge hr) hactive

theorem oppositePsiPositiveEntropyCentralOwner_of_extended
    (h : OppositePsiExtendedCentralOwner) : OppositePsiPositiveEntropyCentralOwner := by
  intro k μ hab hsum hmean hinfo hE hside ha hactive
  rcases hsum.eq_or_lt with hbalance | hunbalanced
  · exact PsiBalancedMeans.law_gap_le_cost μ hbalance
  · by_cases houter : μ.a ≤ 1 / 10 ∧ μ.meanEntropy ≤ 1 / 32768
    · exact PsiOuterEntropyExtension.law_gap_le_cost μ hunbalanced.le houter.1 hside
        houter.2 hactive.le
    · have hface : μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy := by
        intro ha'
        by_contra hn
        exact houter ⟨ha', le_of_not_gt hn⟩
      exact h k μ hab hunbalanced hmean hinfo hE hside ha hface hactive

theorem oppositePsiPositiveEntropyCompactOwner_of_extended
    (h : OppositePsiExtendedCompactOwner) : OppositePsiPositiveEntropyCompactOwner := by
  intro k μ hab hsum hmean hinfo hside ha0 ha1 hcorner _hE hactive
  rcases hsum.eq_or_lt with hbalance | hunbalanced
  · exact PsiBalancedMeans.law_gap_le_cost μ hbalance
  · by_cases houter : μ.meanEntropy ≤ 1 / 32768
    · exact PsiOuterEntropyExtension.law_gap_le_cost μ hunbalanced.le ha1.le hside
        houter hactive.le
    · exact h k μ hab hunbalanced hmean hinfo hside ha0 ha1 hcorner
        (lt_of_not_ge houter) hactive

/-- Every region removed by the new interface is restored by a proved
actual-law theorem, including both entropy-cutoff equalities. -/
theorem ResidualPsiExtendedRemainingOwners.toPositiveEntropyRemainingOwners
    (h : ResidualPsiExtendedRemainingOwners) : ResidualPsiPositiveEntropyRemainingOwners where
  sameChart := sameSidePsiPositiveEntropyChartOwner_of_extended h.sameChart
  oppositeCentral := oppositePsiPositiveEntropyCentralOwner_of_extended h.oppositeCentral
  oppositeCompact := oppositePsiPositiveEntropyCompactOwner_of_extended h.oppositeCompact

theorem residualPsi_of_extended_remaining_owners
    (h : ResidualPsiExtendedRemainingOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_positive_entropy_remaining_owners h.toPositiveEntropyRemainingOwners

/-- The balanced mean face of the phi inequality is already proved. -/
def CanonicalUnbalancedPhiOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost

theorem CanonicalUnbalancedPhiOwner.toCanonical
    (h : CanonicalUnbalancedPhiOwner) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  intro k μ hab hsum
  rcases hsum.eq_or_lt with hbalance | hunbalanced
  · exact PsiBalancedMeans.phi_gap_le_cost μ hbalance
  · exact h k μ hab hunbalanced

theorem finiteHybridBellman_of_extended_region_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiExtendedRemainingOwners) :
    FiniteHybridBellman :=
  finiteHybridBellman_of_remaining_regions hphi.toCanonical
    (residualPsi_of_extended_remaining_owners hpsi)

/-- Direct connection to the approved CK target, with exactly the narrowed
phi domain and three remaining psi domains displayed above as hypotheses. -/
theorem generalCourtadeKumar_of_extended_region_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiExtendedRemainingOwners) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_remaining_regions hphi.toCanonical
    (residualPsi_of_extended_remaining_owners hpsi)

end GeneralCK

#print axioms GeneralCK.ResidualPsiExtendedRemainingOwners.toPositiveEntropyRemainingOwners
#print axioms GeneralCK.residualPsi_of_extended_remaining_owners
#print axioms GeneralCK.CanonicalUnbalancedPhiOwner.toCanonical
#print axioms GeneralCK.generalCourtadeKumar_of_extended_region_owners

end


