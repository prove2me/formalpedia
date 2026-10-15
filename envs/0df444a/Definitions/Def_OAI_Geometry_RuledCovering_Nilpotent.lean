-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
-- name    : OAI_Geometry_RuledCovering_Nilpotent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:26:24.346141+00:00
-- url     : https://prove2.me/theorems/72474a41-fc82-478c-abb5-4331a45e5e95
-- title:
--   Swap-and-reflect isometry relating the two physical coordinate maps
-- statement:
--   The swap-and-reflect map is the linear isometry $\sigma$ of Euclidean space $\mathbb{R}^3$ defined by
--   $$\sigma(z_1,z_2,z_3)=(z_2,\ z_1,\ -z_3).$$
--   It is its own inverse and preserves the Euclidean norm.
--
--   The nilpotent covering statement involves, for $h,a\in\mathbb{R}$, the two coordinate maps $\Phi_1(z)=(z_1,\ z_2,\ h z_3)$ and $\Phi_2(z)=(z_2,\ z_1,\ h(a-z_3))$. They are related by
--   $$\Phi_2(z)=(0,0,ha)+\sigma\bigl(\Phi_1(z)\bigr)\qquad\text{for all } z\in\mathbb{R}^3$$
--   (shown in the same module). Hence, once a parallelogram cylinder has carrier equal to the $\Phi_1$-image of an auxiliary cylinder, rotating it by $\sigma$ and translating by $(0,0,ha)$ gives a parallelogram cylinder of the same area whose carrier is the $\Phi_2$-image of the same auxiliary cylinder. The map $\sigma$ is also used to obtain the upper tip cylinder of the tetrahedron construction from the lower one.
--
--   **Formalization Note** `swapReflect : Space ≃ₗᵢ[ℝ] Space` sends `z` to `vec3 (z 1) (z 0) (-z 2)` and has the same formula for its inverse; $\Phi_1,\Phi_2$ are `firstPhysicalMap h` and `secondPhysicalMap h a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Nilpotent.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Nilpotent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The flip and interchange relating the two physical maps. -/
def swapReflect : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 0) (-z 2)
  invFun z := vec3 (z 1) (z 0) (-z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3]; abel
  map_smul' c z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    change ‖vec3 (z 1) (z 0) (-z 2)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz,norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 0) (-z 2)
    nlinarith [norm_nonneg z,norm_nonneg (vec3 (z 1) (z 0) (-z 2))]

end RuledApproximation

end

end OAI


