-- Prove2me | Definitions.Def_CK_GeneralCK_LeftStationaryHybridReplacement
-- name    : CK_GeneralCK_LeftStationaryHybridReplacement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:56.120714+00:00
-- url     : https://prove2.me/theorems/f8005610-bf1b-4524-a249-92a5dab1b175
-- title:
--   Courtade–Kumar proof module `GeneralCK.LeftStationaryHybridReplacement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LeftStationaryHybridReplacement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LeftStationaryHybridReplacement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LeftStationaryHybridReplacement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LeftStationaryHybridReplacement.lean)

import Definitions.Def_CK_GeneralCK_PureGapCanonicalFormula
import Definitions.Def_CK_GeneralCK_RemainingBellman

-- ===== source module GeneralCK.LeftStationaryHybridReplacement =====
section

/-!
# Target-level replacement for the refuted small-mean pure-gap obligation

The target is the actual finite-law cost minus the gap of `B = max phi psi`.
The small-mean psi branch is already proved. Only the correctly guarded phi
branch remains in the small-mean interface below. No pure-gap sign, scalar
numerical activity bound, or missing branch owner is asserted here.
-/

namespace GeneralCK.LeftStationaryHybridReplacement

noncomputable def childExcess (m h : ℝ) : ℝ := B m h - phi m h

theorem childExcess_nonneg (m h : ℝ) : 0 ≤ childExcess m h := by
  exact sub_nonneg.mpr (le_max_left _ _)

/-- Exact bookkeeping: a negative pure gap can be compensated by actual cost
and the changes from phi to the hybrid profile. The parent change has the
opposite sign to the child changes. -/
theorem hybrid_slack_identity (a c e f cost : ℝ) :
    cost - candidateGap B a c e f =
      (cost - fourMomentLowerBound a c e f) + pureGap a c e f +
        (childExcess a e + childExcess c f) / 2 -
          childExcess ((a + c) / 2) ((e + f) / 2) := by
  unfold pureGap candidateGap childExcess
  ring

theorem canonical_hybrid_slack_identity {a c e f cost : ℝ}
    (hac : a ≤ c) (hc : c ≤ 1 / 2) :
    cost - candidateGap B a c e f =
      (cost - fourMomentLowerBound a c e f) + canonicalPureGap a c e f +
        (childExcess a e + childExcess c f) / 2 -
          childExcess ((a + c) / 2) ((e + f) / 2) := by
  rw [← pureGap_eq_canonicalPureGap hac hc]
  exact hybrid_slack_identity a c e f cost

/-- This is a target-level owner over actual finite laws. It must not be
used as a boundary value for minimizing `canonicalPureGap`. -/
def SmallMeanHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 / 16 → μ.gap ≤ μ.cost

/-- The only missing small-mean branch after the accepted psi theorem.
The child values remain the actual maxima, and the cost remains `μ.cost`. -/
def SmallMeanPhiActiveHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 / 16 →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem smallMeanHybridOwner_iff_phiActive :
    SmallMeanHybridOwner ↔ SmallMeanPhiActiveHybridOwner := by
  constructor
  · intro h k μ hab hsmall _hactive
    exact h k μ hab hsmall
  · intro h k μ hab hsmall
    by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
    · exact h k μ hab hsmall hp
    · exact small_mean_hybrid_of_active_psi μ hab hsmall (le_of_lt (lt_of_not_ge hp))

/-- A branch-aware global interface. Unlike the older unrestricted pure-phi
interface, both branches conclude the actual hybrid inequality. -/
def CanonicalPhiActiveHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem finiteHybridBellman_of_active_hybrid_owners
    (hphi : CanonicalPhiActiveHybridOwner)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) : FiniteHybridBellman := by
  apply finiteHybridBellman_of_canonical
  intro k μ hab hsum
  rcases hab.eq_or_lt with heq | hab'
  · exact μ.equal_mean_hybrid heq
  by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact hphi k μ hab' hsum hp
  have hactive := lt_of_not_ge hp
  by_cases hsmall : μ.a + μ.b ≤ 1 / 16
  · exact small_mean_hybrid_of_active_psi μ hab hsmall hactive.le
  by_cases hlow : μ.information ≤ 1 / 100
  · exact low_information_hybrid_of_active_psi μ hlow hactive.le
  exact hpsi k μ hab' hsum (lt_of_not_ge hsmall) (lt_of_not_ge hlow) hactive

/-- The exact interval containing the negative pure-gap stationary point. -/
def DiagnosticHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a = entropyInverse μ.e →
    μ.e = 1 / 10000000000000 → μ.f = 1 / 1000000000000 →
    μ.b ∈ Set.Icc (8 / 100000000000000 : ℝ) (1 / 10000000000000) →
    μ.gap ≤ μ.cost

/-- This is the precise scalar activity certificate still needed to obtain
an unconditional diagnostic-region theorem using the already proved psi
branch. It contains neither a finite-law cost nor a pure-gap sign. -/
def DiagnosticParentActivity : Prop :=
  ∀ c ∈ Set.Icc (8 / 100000000000000 : ℝ) (1 / 10000000000000),
    phi ((entropyInverse (1 / 10000000000000) + c) / 2)
        (11 / 20000000000000) ≤
      psi ((entropyInverse (1 / 10000000000000) + c) / 2)
        (11 / 20000000000000)

theorem diagnostic_ordered_smallMean {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (ha : μ.a = entropyInverse μ.e)
    (he : μ.e = 1 / 10000000000000) (hf : μ.f = 1 / 1000000000000)
    (hb : μ.b ≤ 1 / 10000000000000) :
    μ.a ≤ μ.b ∧ μ.a + μ.b ≤ 1 / 16 := by
  have hef : μ.e ≤ μ.f := by rw [he, hf]; norm_num
  have hab := entropyInverse_mono μ.e_pos.le (H_le_one μ.b)
    (hef.trans μ.f_le_cap)
  rw [entropyInverse_H_lower μ.b_interior.1.le (by linarith)] at hab
  rw [← ha] at hab
  exact ⟨hab, by linarith⟩

/-- Every realizing law throughout the diagnostic interval is handled;
stationarity and the two pure-gap residual budgets are unnecessary here. -/
theorem diagnosticHybridOwner_of_parentActivity
    (hactive : DiagnosticParentActivity) : DiagnosticHybridOwner := by
  intro k μ ha he hf hb
  obtain ⟨hab, hsmall⟩ := diagnostic_ordered_smallMean μ ha he hf hb.2
  apply small_mean_hybrid_of_active_psi μ hab hsmall
  have hm : μ.midpoint =
      (entropyInverse (1 / 10000000000000) + μ.b) / 2 := by
    simp only [InteriorLaw.midpoint, ha, he]
  have hE : μ.meanEntropy = (11 / 20000000000000 : ℝ) := by
    simp only [InteriorLaw.meanEntropy, he, hf]
    norm_num
  rw [hm, hE]
  exact hactive μ.b hb

theorem diagnosticHybridOwner_of_smallMeanPhiActive
    (hphi : SmallMeanPhiActiveHybridOwner) : DiagnosticHybridOwner := by
  intro k μ ha he hf hb
  obtain ⟨hab, hsmall⟩ := diagnostic_ordered_smallMean μ ha he hf hb.2
  exact (smallMeanHybridOwner_iff_phiActive.mpr hphi) k μ hab hsmall

/-- The entire diagnostic interval lies below the manuscript's positive
retention cutoff, using only the physical order of means. -/
theorem diagnostic_below_retained_cutoff {a c : ℝ}
    (hac : a ≤ c) (hc : c ≤ 1 / 10000000000000) : a + c < 1 / 10000 := by
  linarith

#print axioms childExcess_nonneg
#print axioms hybrid_slack_identity
#print axioms canonical_hybrid_slack_identity
#print axioms smallMeanHybridOwner_iff_phiActive
#print axioms finiteHybridBellman_of_active_hybrid_owners
#print axioms diagnostic_ordered_smallMean
#print axioms diagnosticHybridOwner_of_parentActivity
#print axioms diagnosticHybridOwner_of_smallMeanPhiActive
#print axioms diagnostic_below_retained_cutoff

end GeneralCK.LeftStationaryHybridReplacement

end


