-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:13.657614+00:00
-- url     : https://prove2.me/theorems/1cf44786-a14c-4d93-a65e-c9bc84dd88b5
-- title:
--   St Chart Scaling Indep
-- statement:
--   Definitions and structural lemmas for St Chart Scaling Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartScalingIndep.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
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
def ChartScalingIndep.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k),
    (∀ k, x ⟨k, i k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun q : Σ k, ι k => x q / x ⟨q.1, i q.1⟩))
        (fun k => x ⟨k, i k⟩)
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


