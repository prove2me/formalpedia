-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Frames
-- name    : OAI_Geometry_RuledCovering_Frames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:15:09.814309+00:00
-- url     : https://prove2.me/theorems/fd6b1a6a-95b7-4874-8690-02d51718747c
-- title:
--   Coordinate plane with the maximum norm and the Jacobian of a linear frame
-- statement:
--   The construction distinguishes the Euclidean plane $\mathbb{R}^2$, in which the ruled sets live, from an auxiliary coordinate plane in which lattice computations are carried out.
--
--   1. **Coordinates.** The coordinate plane $\mathbb{R}^2_\infty$ is the space of pairs $x=(x_1,x_2)$ of reals with the maximum norm $\|x\|_\infty=\max(|x_1|,|x_2|)$. Its closed balls are the axis-parallel squares $\{x:\ |x_1-b_1|\le a,\ |x_2-b_2|\le a\}$.
--   2. **Frame Jacobian.** A *frame* is a linear isomorphism $M:\mathbb{R}^2_\infty\to\mathbb{R}^2$ onto the Euclidean plane. Writing $[M]$ for its $2\times 2$ matrix with respect to the standard bases, its Jacobian is
--   $$J(M)=\bigl|\det\,[M]\bigr| .$$
--
--   Local covers are built in coordinates adapted to the derivative of the field (an eigenbasis, or an orthonormal shear frame) and then transported to the plane by a frame $M$. The Jacobian is the corresponding change-of-variables factor: $J(M)>0$, and for measurable $K\subseteq\mathbb{R}^2_\infty$ one has $\int_{M(K)}F=J(M)\int_K F\circ M$ and $|M(K)|=J(M)\,|K|$ (proved in the same module). In particular a coordinate square of side $2a$ becomes a parallelogram of area $J(M)(2a)^2$, which converts lattice sums in coordinates into integrals over the plane.
--
--   **Formalization Note** `Coordinates` is the abbreviation `Fin 2 → ℝ`, whose norm is the supremum norm, as opposed to `Plane = EuclideanSpace ℝ (Fin 2)`. A frame is a continuous linear equivalence `Coordinates ≃L[ℝ] Plane`, and `frameJacobian M` is the absolute value of the determinant of `M` composed with `EuclideanSpace.equiv (Fin 2) ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Frames.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Frames.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

abbrev Coordinates := Fin 2 → ℝ

def frameJacobian (M : Coordinates ≃L[ℝ] Plane) : ℝ :=
  |(M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toContinuousLinearMap.det|

end RuledApproximation

end

end OAI


