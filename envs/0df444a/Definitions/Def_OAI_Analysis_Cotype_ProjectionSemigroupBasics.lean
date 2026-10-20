-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
-- name    : OAI_Analysis_Cotype_ProjectionSemigroupBasics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:00.605971+00:00
-- url     : https://prove2.me/theorems/19f597fe-4e7c-4b85-81a1-ba41622a929a
-- title:
--   Endpoint values of the projection semigroup
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$.
--
--   1. **Endpoints.**
--   $$
--   T(0)=\prod_iP_i,\qquad T(1)=1 .
--   $$
--   The semigroup interpolates between the full product of the projections and the identity. Its derivative at $0$ is the linear coefficient.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionSemigroupBasics.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionSemigroupBasics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

@[simp] theorem projectionSemigroup_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    projectionSemigroup P 0 = projectionProduct P := by
  simp [projectionSemigroup]

@[simp] theorem projectionSemigroup_one {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    projectionSemigroup P 1 = 1 := by
  simp [projectionSemigroup, projectionProduct_one]

end Cotype

end

end OAI


