-- Prove2me | Definitions.Def_CK_GeneralCK_FinalProductionAssemblyPositiveCutoff
-- name    : CK_GeneralCK_FinalProductionAssemblyPositiveCutoff
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:58:25.935625+00:00
-- url     : https://prove2.me/theorems/214677f9-d4b1-4c73-a887-9d5ec25ec31b
-- title:
--   Courtade–Kumar proof module `GeneralCK.FinalProductionAssemblyPositiveCutoff` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FinalProductionAssemblyPositiveCutoff` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FinalProductionAssemblyPositiveCutoff` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FinalProductionAssemblyPositiveCutoff (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FinalProductionAssemblyPositiveCutoff.lean)

import Definitions.Def_CK_GeneralCK_PureGapPositiveCutoffMinimizerRepair
import Definitions.Def_CK_GeneralCK_FinalAssemblyAfterSmallBoundary
import Definitions.Def_CK_GeneralCK_PsiFullBiasTail8FinalBridge

-- ===== source module GeneralCK.FinalProductionAssemblyPositiveCutoff =====
section

/-!
# Final production assembly with the positive pure-gap cutoff

This is the production replacement for the refuted zero-cutoff cap premise.
The checked SB-1 theorem owns the actual Bellman target below `1/10000`.
Pure-gap minimization is used only on the retained chamber, where its cap
fibers have the positive lower endpoint

`max (entropyInverse h) (retainedCutoff - fixedMean)`.

Thus the near-origin negative stationary pure-gap value is neither assumed
nonnegative nor used.  The retained and large-mean active-phi branches share
one positive-cutoff pure-gap proof.
-/

namespace GeneralCK.FinalProductionAssemblyPositiveCutoff

open GeneralCK
open SmallMeanPhiCutoff

/-- The sole target-level region that a positive pure-gap cutoff does not
cover on the large-mean branch.  Here the first child is near zero and the
second is near one, so their individually reflected lower-half radii have sum
below the cutoff.  This is an actual hybrid owner; it does not assert the
refuted pure-gap sign. -/
def OppositeCornerBelowCutoffPhiHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b ≤ 1 → 1 / 16 < μ.a + μ.b →
    1 / 2 < μ.b → μ.a + (1 - μ.b) < retainedCutoff →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- Exact reduced production inputs after the checked small-boundary theorem.
`seam` and `capFibers` replace the inconsistent zero-cutoff residual owner.
The global reflection, half-mean, and E8 conclusions are kept explicit so this
small adapter does not depend on their very large generated object closures. -/
structure ProductionOwners : Prop where
  reflection : ∀ a b : ℝ, 0 < b → b < a → a < 1 →
    0 ≤ Reflection.curvature a b
  correctionLeft : ∀ p ∈ Correction.orderedTriangle,
    0 < Correction.Mleft p.1 p.2
  correctionDet : ∀ p ∈ Correction.orderedTriangle,
    0 ≤ Correction.Mdet p.1 p.2
  seam : StrictSeamMinimizerExclusion retainedCutoff
  capFibers : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff
  halfMeanCurvature : HalfMeanCurvatureNegative
  e8Strict : E8StrictOnSlopeRange
  oppositeCornerSmall : OppositeCornerBelowCutoffPhiHybridOwner
  psi : PsiFullBiasTail8CurrentOwners

theorem ProductionOwners.retainedPureGap (h : ProductionOwners) :
    RetainedPureGapOwner :=
  retainedPureGap_of_positiveCutoffAnalyticOwners
    h.correctionLeft h.correctionDet h.seam h.capFibers
    h.halfMeanCurvature h.e8Strict

theorem ProductionOwners.retainedSmallMeanPhi (h : ProductionOwners) :
    RetainedSmallMeanPhiHybridOwner :=
  retainedSmallMeanHybrid_of_pureGap h.retainedPureGap
    h.reflection
    h.correctionLeft h.correctionDet

/-- The same retained pure-gap theorem owns every large-mean law, since
`1/16 < a+b` is far above the positive cutoff `1/10000`. -/
theorem ProductionOwners.largeMeanPhi (h : ProductionOwners) :
    HybridAfterDiagnostic.LargeMeanPhiActiveHybridOwner := by
  intro k μ hab hsum hlarge hactive
  by_cases hb : μ.b ≤ 1 / 2
  · have hret : retainedCutoff ≤ μ.a + μ.b := by
      dsimp [retainedCutoff]
      linarith
    have hpure : 0 ≤ pureGap μ.a μ.b μ.e μ.f :=
      pureGap_nonneg_on_retained h.retainedPureGap
        μ.a_interior.1.le hab.le hb μ.e_pos μ.f_pos
        μ.e_le_cap μ.f_le_cap hret
    exact (hybrid_gap_le_phi hactive).trans
      (μ.phi_gap_le_cost_of_scalar_bounds h.reflection
        h.correctionLeft h.correctionDet hpure)
  · have hbgt : 1 / 2 < μ.b := lt_of_not_ge hb
    by_cases hopposite : μ.a + (1 - μ.b) < retainedCutoff
    · exact h.oppositeCornerSmall k μ hab hsum hlarge hbgt hopposite hactive
    · have horder : μ.a ≤ 1 - μ.b := by linarith
      have hhalf : 1 - μ.b ≤ 1 / 2 := by linarith
      have hfCap : μ.f ≤ H (1 - μ.b) := by
        simpa only [H_complement] using μ.f_le_cap
      have hpureReflected : 0 ≤ pureGap μ.a (1 - μ.b) μ.e μ.f :=
        pureGap_nonneg_on_retained h.retainedPureGap
          μ.a_interior.1.le horder hhalf μ.e_pos μ.f_pos
          μ.e_le_cap hfCap (le_of_not_gt hopposite)
      have hpure : 0 ≤ pureGap μ.a μ.b μ.e μ.f := by
        simpa only [pureGap_reflect_right] using hpureReflected
      exact (hybrid_gap_le_phi hactive).trans
        (μ.phi_gap_le_cost_of_scalar_bounds h.reflection
          h.correctionLeft h.correctionDet hpure)

theorem ProductionOwners.toRemainingOwners (h : ProductionOwners) :
    HybridAfterSmallBoundary.RemainingOwners where
  retainedSmallMeanPhi := h.retainedSmallMeanPhi
  largeMeanPhi := h.largeMeanPhi
  psi := h.psi.toRemainingPsiHybridOwner

theorem finiteHybridBellman (h : ProductionOwners) : FiniteHybridBellman :=
  HybridAfterSmallBoundary.finiteHybridBellman_of_remainingOwners
    h.toRemainingOwners

theorem generalCourtadeKumar (h : ProductionOwners) : GeneralCourtadeKumar :=
  HybridAfterSmallBoundary.generalCourtadeKumar_of_remainingOwners
    h.toRemainingOwners

#print axioms ProductionOwners.retainedPureGap
#print axioms ProductionOwners.retainedSmallMeanPhi
#print axioms ProductionOwners.largeMeanPhi
#print axioms ProductionOwners.toRemainingOwners
#print axioms finiteHybridBellman
#print axioms generalCourtadeKumar

end GeneralCK.FinalProductionAssemblyPositiveCutoff

end


