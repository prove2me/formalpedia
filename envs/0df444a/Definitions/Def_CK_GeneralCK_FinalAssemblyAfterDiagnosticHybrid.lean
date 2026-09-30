-- Prove2me | Definitions.Def_CK_GeneralCK_FinalAssemblyAfterDiagnosticHybrid
-- name    : CK_GeneralCK_FinalAssemblyAfterDiagnosticHybrid
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:22:55.71239+00:00
-- url     : https://prove2.me/theorems/b04998f1-3957-48c1-b50d-7be9fa0f92da
-- title:
--   Courtade–Kumar proof module `GeneralCK.FinalAssemblyAfterDiagnosticHybrid` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FinalAssemblyAfterDiagnosticHybrid` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FinalAssemblyAfterDiagnosticHybrid` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FinalAssemblyAfterDiagnosticHybrid (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FinalAssemblyAfterDiagnosticHybrid.lean)

import Definitions.Def_CK_GeneralCK_DiagnosticParentActivity

-- ===== source module GeneralCK.FinalAssemblyAfterDiagnosticHybrid =====
section

/-!
# Actual-law small-mean residual after the accepted diagnostic hybrid interval

This additive assembly consumes the unconditional diagnostic theorem. It
does not use the zero-cutoff pure-gap owner or convert a hybrid conclusion
into a pure-gap value. The remaining owner fields are explicit hypotheses.
-/

namespace GeneralCK.HybridAfterDiagnostic

open LeftStationaryHybridReplacement

/-- The complete accepted diagnostic region of actual laws. -/
def diagnosticLaw {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) : Prop :=
  μ.a = entropyInverse μ.e ∧
    μ.e = 1 / 10000000000000 ∧ μ.f = 1 / 1000000000000 ∧
    μ.b ∈ Set.Icc (8 / 100000000000000 : ℝ) (1 / 10000000000000)

/-- Exact open complement of the closed diagnostic interval and its three
moment identities. Both endpoints of the interval remain accepted. -/
theorem not_diagnosticLaw_iff {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    ¬diagnosticLaw μ ↔
      μ.a ≠ entropyInverse μ.e ∨
      μ.e ≠ 1 / 10000000000000 ∨ μ.f ≠ 1 / 1000000000000 ∨
      μ.b < 8 / 100000000000000 ∨ 1 / 10000000000000 < μ.b := by
  classical
  simp only [diagnosticLaw, Set.mem_Icc, not_and_or, not_le]

theorem diagnosticLaw_gap_le_cost {k : ℕ} (μ : InteriorLaw (Fin k))
    (h : diagnosticLaw μ) : μ.gap ≤ μ.cost :=
  LeftStationaryDiagnosticActivity.diagnosticHybridOwner k μ
    h.1 h.2.1 h.2.2.1 h.2.2.2

theorem diagnosticLaw_parent_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (h : diagnosticLaw μ) :
    phi μ.midpoint μ.meanEntropy + 1 / 1000000000000 ≤
      psi μ.midpoint μ.meanEntropy := by
  have ha : μ.a ≤ LeftStationaryDiagnosticActivity.leftAnchor := by
    rw [h.1, h.2.1]
    exact LeftStationaryDiagnosticActivity.inverse_left_upper
  have hm : LeftStationaryDiagnosticActivity.meanLower ≤ μ.midpoint := by
    have hb := h.2.2.2.1
    have ha0 := μ.a_interior.1
    unfold InteriorLaw.midpoint LeftStationaryDiagnosticActivity.meanLower
    linarith
  have hm' : μ.midpoint ≤ LeftStationaryDiagnosticActivity.meanUpper := by
    have hb := h.2.2.2.2
    unfold InteriorLaw.midpoint LeftStationaryDiagnosticActivity.meanUpper
    dsimp [LeftStationaryDiagnosticActivity.leftAnchor] at ha
    linarith
  have hE : μ.meanEntropy = LeftStationaryDiagnosticActivity.parentEntropy := by
    unfold InteriorLaw.meanEntropy LeftStationaryDiagnosticActivity.parentEntropy
    rw [h.2.1, h.2.2.1]
    norm_num
  rw [hE]
  exact LeftStationaryDiagnosticActivity.parent_activity_margin hm hm'

/-- The accepted interval has no weakly phi-active parent. Thus deleting it
from a phi-active owner is bookkeeping, not a new phi-region exclusion. -/
theorem not_diagnosticLaw_of_phiActive {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy) :
    ¬diagnosticLaw μ := by
  intro h
  have hm := diagnosticLaw_parent_margin μ h
  linarith

/-- Full small-mean target on the exact complement of the accepted interval.
All moment feasibility constraints are supplied by `InteriorLaw`. -/
def SmallMeanOutsideDiagnosticOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 / 16 → ¬diagnosticLaw μ →
    μ.gap ≤ μ.cost

theorem smallMeanHybrid_iff_outsideDiagnostic :
    SmallMeanHybridOwner ↔ SmallMeanOutsideDiagnosticOwner := by
  constructor
  · intro h k μ hab hsmall _hout
    exact h k μ hab hsmall
  · intro h k μ hab hsmall
    by_cases hd : diagnosticLaw μ
    · exact diagnosticLaw_gap_le_cost μ hd
    · exact h k μ hab hsmall hd

/-- After equal means and the accepted small-mean psi theorem are consumed,
the remaining small-mean domain has strictly ordered means and a weakly
phi-active parent. -/
def SmallMeanPhiOutsideDiagnosticOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 / 16 → ¬diagnosticLaw μ →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem smallMeanOutsideDiagnostic_iff_phiOutside :
    SmallMeanOutsideDiagnosticOwner ↔ SmallMeanPhiOutsideDiagnosticOwner := by
  constructor
  · intro h k μ hab hsmall hout _hactive
    exact h k μ hab.le hsmall hout
  · intro h k μ hab hsmall hout
    rcases hab.eq_or_lt with heq | hab'
    · exact μ.equal_mean_hybrid heq
    by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
    · exact h k μ hab' hsmall hout hp
    · exact small_mean_hybrid_of_active_psi μ hab hsmall (lt_of_not_ge hp).le

theorem smallMeanHybrid_iff_phiOutsideDiagnostic :
    SmallMeanHybridOwner ↔ SmallMeanPhiOutsideDiagnosticOwner :=
  smallMeanHybrid_iff_outsideDiagnostic.trans smallMeanOutsideDiagnostic_iff_phiOutside

/-- This equivalence records explicitly that the open phi branch has not
been analytically shortened by the psi-active diagnostic interval. -/
theorem phiOutsideDiagnostic_iff_phiActive :
    SmallMeanPhiOutsideDiagnosticOwner ↔ SmallMeanPhiActiveHybridOwner := by
  constructor
  · intro h k μ hab hsmall hp
    rcases hab.eq_or_lt with heq | hab'
    · exact μ.equal_mean_hybrid heq
    · exact h k μ hab' hsmall (not_diagnosticLaw_of_phiActive μ hp) hp
  · intro h k μ hab hsmall _hout hp
    exact h k μ hab.le hsmall hp

def LargeMeanPhiActiveHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 → 1 / 16 < μ.a + μ.b →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The same normalized residual psi interface consumed by the accepted
regional assemblies; their owner-to-function adapters can be supplied here. -/
def RemainingPsiHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- Production-facing target owners after consuming the diagnostic interval,
equal means, and the accepted small-mean/low-information psi regions. -/
structure RemainingOwners : Prop where
  smallMeanPhi : SmallMeanPhiOutsideDiagnosticOwner
  largeMeanPhi : LargeMeanPhiActiveHybridOwner
  psi : RemainingPsiHybridOwner

theorem RemainingOwners.smallMeanHybrid (h : RemainingOwners) : SmallMeanHybridOwner :=
  smallMeanHybrid_iff_phiOutsideDiagnostic.mpr h.smallMeanPhi

theorem RemainingOwners.canonicalPhiActive (h : RemainingOwners) :
    CanonicalPhiActiveHybridOwner := by
  intro k μ hab hsum hp
  by_cases hsmall : μ.a + μ.b ≤ 1 / 16
  · exact h.smallMeanHybrid k μ hab.le hsmall
  · exact h.largeMeanPhi k μ hab hsum (lt_of_not_ge hsmall) hp

theorem finiteHybridBellman_of_remainingOwners (h : RemainingOwners) : FiniteHybridBellman :=
  finiteHybridBellman_of_active_hybrid_owners h.canonicalPhiActive h.psi

/-- Conditional connection to the approved all-dimensions CK target. No
remaining regional owner is asserted by this theorem. -/
theorem generalCourtadeKumar_of_remainingOwners (h : RemainingOwners) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_finiteHybridBellman (finiteHybridBellman_of_remainingOwners h)

#print axioms not_diagnosticLaw_iff
#print axioms diagnosticLaw_gap_le_cost
#print axioms diagnosticLaw_parent_margin
#print axioms not_diagnosticLaw_of_phiActive
#print axioms smallMeanHybrid_iff_outsideDiagnostic
#print axioms smallMeanOutsideDiagnostic_iff_phiOutside
#print axioms smallMeanHybrid_iff_phiOutsideDiagnostic
#print axioms phiOutsideDiagnostic_iff_phiActive
#print axioms RemainingOwners.smallMeanHybrid
#print axioms RemainingOwners.canonicalPhiActive
#print axioms finiteHybridBellman_of_remainingOwners
#print axioms generalCourtadeKumar_of_remainingOwners

end GeneralCK.HybridAfterDiagnostic

end


