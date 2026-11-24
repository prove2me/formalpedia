-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:06.530581+00:00
-- url     : https://prove2.me/theorems/a505d126-ad2d-4440-a65d-6506b84b5302
-- title:
--   PGraded Subquot
-- statement:
--   Definitions and structural lemmas for PGraded Subquot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace GradedSubquot
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
variable (S ι) in

def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}
end GradedSubquot
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


