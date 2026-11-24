-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:46.607474+00:00
-- url     : https://prove2.me/theorems/56519d4e-208d-40cd-affa-7cc912ecc8f5
-- title:
--   St Chart Dual Rational
-- statement:
--   Definitions and structural lemmas for St Chart Dual Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartDualRational.lean

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
def ChartDualRational.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι κ : Type) [Fintype ι] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (B : ChartBundle ℤ x 2 E) (φ : κ → E →ₗ[Ω] Ω) (i₀ : ι),
    x i₀ ≠ 0 → T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ →
      ∃ (b : Module.Basis (Fin 2) Ω E) (g : κ → Fin 2 → Ω), (∀ k q, φ k (b q) = x i₀ * g k q) ∧
        (∀ k q, g k q ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) ∧
        ∃ k₀ k₁, g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0
end
end GroundTheory.Heights₂.Heights.Inter


