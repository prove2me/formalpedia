-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeZariskiDense
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeZariskiDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:12.823905+00:00
-- url     : https://prove2.me/theorems/132428f1-944f-438e-9cfa-2e966ae83633
-- title:
--   Statements Prime Zariski Dense
-- statement:
--   Definitions and structural lemmas for Statements Prime Zariski Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsPrimeZariskiDense.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def PrimeZariskiDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (j : MRing ι),
    P.IsPrime → j ∉ P →
    ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) j) ≠ 0 → eval z g = 0) →
      ∀ z ∈ mcPts P, eval z g = 0
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


