-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Differentiation
-- name    : OAI_Geometry_Arnold_Differentiation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:27:21.686372+00:00
-- url     : https://prove2.me/theorems/e1223a85-683e-494c-ab67-8f7cd3baae5f
-- title:
--   Continuous alternating forms on the space of real $5\times5$ matrices
-- statement:
--   For $n\in\mathbb{N}$, $\mathrm{MatForm}_n$ is the space of continuous alternating $n$-linear forms
--   $$
--   \eta:\underbrace{M_5(\mathbb{R})\times\cdots\times M_5(\mathbb{R})}_{n}\to\mathbb{R}
--   $$
--   on the real vector space $M_5(\mathbb{R})$ of $5\times5$ matrices. The topology on $M_5(\mathbb{R})$ is the one induced by the chosen operator norm.
--
--   Differential forms on the orthogonal group are handled through such forms on the ambient matrix space, which is how the topological obstruction is formulated.
--
--   **Formalization Note** The orthogonal group keeps its own product topology, which is definitionally distinct but equivalent. The type is `RM [⋀^Fin n]→L[ℝ] ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Differentiation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Differentiation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar

namespace OAI

universe uE uF uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open VectorField

/-- Matrix forms use the topology of the chosen operator norm. The orthogonal
group retains its original (definitionally distinct) product topology. -/
abbrev MatForm (n : ℕ) := by
  letI : TopologicalSpace RM :=
    (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact RM [⋀^Fin n]→L[ℝ] ℝ

end ArnoldCounterexample.CriticalBound

end

end OAI


