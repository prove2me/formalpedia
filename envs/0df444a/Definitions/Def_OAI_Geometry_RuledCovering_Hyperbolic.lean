-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
-- name    : OAI_Geometry_RuledCovering_Hyperbolic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:23:00.275087+00:00
-- url     : https://prove2.me/theorems/1aa2245f-6b30-42be-a64f-b42deab838af
-- title:
--   Cyclic permutation of coordinates in $\mathbb{R}^3$
-- statement:
--   The cyclic coordinate permutation is the linear isometry $\kappa$ of Euclidean space $\mathbb{R}^3$ defined by
--   $$\kappa(z_1,z_2,z_3)=(z_2,\ z_3,\ z_1),\qquad \kappa^{-1}(z_1,z_2,z_3)=(z_3,\ z_1,\ z_2).$$
--   It preserves the Euclidean norm because it only permutes coordinates.
--
--   It converts the physical normalization of ruled sets into the standard one. For a set $D\subseteq\mathbb{R}^2$, a field $v:\mathbb{R}^2\to\mathbb{R}^2$ and $L\in\mathbb{R}$, the physical ruled set with vertical scale $1$ consists of the points $(s,\ p_1+s\,v_1(p),\ p_2+s\,v_2(p))$ with $p\in D$ and $|s|\le L$, and $\kappa$ maps it onto the ruled set of points $(p_1+r\,v_1(p),\ p_2+r\,v_2(p),\ r)$ with $p\in D$ and $|r|\le L$ (shown in the same module). Since the physical weight with scale $1$ is the weight $1/\sqrt{1+\|v\|^2}$, the hyperbolic covering statement for ruled sets is the special case of the isometry-invariant physical statement with scale $1$ and isometry $\kappa$.
--
--   **Formalization Note** `cycleCoordinates : Space ≃ₗᵢ[ℝ] Space` sends `z` to `vec3 (z 1) (z 2) (z 0)`; Lean's indices $0,1,2$ correspond to $z_1,z_2,z_3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Hyperbolic.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Hyperbolic.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Cyclic permutation from the transverse physical normalization to (p+rv,r). -/
def cycleCoordinates : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 2) (z 0)
  invFun z := vec3 (z 2) (z 0) (z 1)
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' c z := by ext i; fin_cases i <;> rfl
  norm_map' z := by
    change ‖vec3 (z 1) (z 2) (z 0)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz, norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 2) (z 0)
    nlinarith [norm_nonneg (vec3 (z 1) (z 2) (z 0)), norm_nonneg z]

end RuledApproximation

end

end OAI


