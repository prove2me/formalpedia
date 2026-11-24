-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StBaseRatioBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StBaseRatioBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:24.055931+00:00
-- url     : https://prove2.me/theorems/bbc7088d-2055-4344-8986-eab154319ffa
-- title:
--   St Base Ratio Basis
-- statement:
--   Definitions and structural lemmas for St Base Ratio Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StBaseRatioBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def BaseRatioBasis.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι : Type) [Fintype ι] (x : ι → Ω) (D : ℕ),
    IsArithVar (T.baseIdeal x) D →
      ∃ (i₀ : ι) (d : ℕ) (t : Fin d → Ω), x i₀ ≠ 0 ∧ D = d + 1 ∧ AlgebraicIndependent ℚ t ∧
        (∀ n, t n ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) ∧
        ∀ j, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) (x j / x i₀)
end
end GroundTheory.Heights₂.Heights.Inter


