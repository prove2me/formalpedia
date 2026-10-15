-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
-- name    : OAI_Geometry_ProjectionVolume_SupportGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:08:14.89207+00:00
-- url     : https://prove2.me/theorems/133e4026-11de-4986-9bfb-c2db2c3a7ec4
-- title:
--   The support function $h_K(f)=\sup_{x\in K}f(x)$ of a set
-- statement:
--   Let $E$ be a real normed space, $K\subseteq E$ a set and $f:E\to\mathbb{R}$ a continuous linear functional. The file defines the support function
--
--   $$h_K(f)=\sup\{f(x):\ x\in K\}.$$
--
--   In a real Hilbert space one evaluates it at the functionals $x\mapsto\langle u,x\rangle$, which gives the usual support function $h_K(u)=\sup_{x\in K}\langle u,x\rangle$ of a direction $u$.
--
--   For nonempty compact $K$ the supremum is attained, and the module develops the standard calculus of support functions: $h_{A+B}=h_A+h_B$ for Minkowski sums, $h_{cK}=c\,h_K$ for $c\ge0$, the supremum of $f(a)+g(b)$ over a product $A\times B$ equals $h_A(f)+h_B(g)$, the value $\max(f(x),f(y))$ on a segment $[x,y]$ and $\tfrac12|f(v)|$ on a centered segment $[-\tfrac12v,\tfrac12v]$, and, via the Hahn–Banach separation theorem, the fact that a nonempty compact convex set consists exactly of the points $x$ with $f(x)\le h_K(f)$ for all $f$. This is the tool that identifies a projection body, defined by the inequalities $\langle u,y\rangle\le b(u)$ with $b$ the brightness function, with an explicit zonotope once $b$ is shown to be that zonotope's support function.
--
--   **Formalization Note** `support K f` is `sSup (f '' K)` for `f : E →L[ℝ] ℝ`. Lean's real supremum equals $0$ for the empty set and for sets that are not bounded above, so the definition agrees with the mathematical support function only when $K$ is nonempty and $f$ is bounded above on $K$ (for instance for nonempty compact $K$); the lemmas of the module carry the corresponding hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SupportGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SupportGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian

namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def support (K : Set E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' K)

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end InnerProduct

end Paper092.SupportGeometry

end OAI


