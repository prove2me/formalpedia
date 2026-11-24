-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:58.216799+00:00
-- url     : https://prove2.me/theorems/09e0829b-7ea4-4b72-9229-f06de8654931
-- title:
--   St Chart Det Ratio
-- statement:
--   Definitions and structural lemmas for St Chart Det Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartDetRatio.lean

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
def ChartDetRatio.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι ν : Type) [Fintype ι] [Fintype ν] (E : Type) [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (δ : ν → Ω) (i₀ : ι),
    x i₀ ≠ 0 → T.IsTwistedDetGen B e δ →
      ∃ l₀, δ l₀ ≠ 0 ∧ ∀ l, δ l / δ l₀ ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
end
end GroundTheory.Heights₂.Heights.Inter


