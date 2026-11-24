-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:18.308655+00:00
-- url     : https://prove2.me/theorems/91fa1fdc-6dc3-4288-ab2a-219074cb41f6
-- title:
--   Statements Chart Rank Adjoin
-- statement:
--   Definitions and structural lemmas for Statements Chart Rank Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsChartRankAdjoin.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
def ChartRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k),
    (∀ k, z ⟨k, j k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) →
      ptDeg (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩))
section Inhabitants
def genericPointProjLine : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Σ _ : Unit, Fin 2) ℚ) :=
  fun q => algebraMap (MvPolynomial (Σ _ : Unit, Fin 2) ℚ) _ (X q)
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


