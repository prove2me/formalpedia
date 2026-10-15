-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
-- name    : OAI_Geometry_ProjectionVolume_SimplexProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:54:36.430996+00:00
-- url     : https://prove2.me/theorems/af45cef2-aa18-4ef2-8071-c5ac89ab60cd
-- title:
--   Barycentric coordinates, facets and vertices of the standard simplex $T_d$
-- statement:
--   Let $d\in\mathbb{N}$ and let $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}\subset\mathbb{R}^d$ be the standard simplex in Euclidean space. Its $d+1$ vertices and facets are indexed by the set $\{\star,1,\dots,d\}$, where the extra index $\star$ refers to the vertex $0$ and to the opposite facet lying in $\{x_1+\dots+x_d=1\}$. For $x,u\in\mathbb{R}^d$ the file defines:
--
--   1. **Barycentric coordinates.** $$\lambda_\star(x)=1-\sum_{i=1}^d x_i,\qquad \lambda_i(x)=x_i\quad(1\le i\le d).$$
--   2. **Velocities.** The rates of change of these coordinates along a direction $u$, $$\mu_\star(u)=-\sum_{i=1}^d u_i,\qquad \mu_i(u)=u_i,$$ so that $\lambda_a(x+tu)=\lambda_a(x)+t\,\mu_a(u)$ for every index $a$ and every $t\in\mathbb{R}$.
--   3. **Facets.** $F_a=\{x\in T_d:\ \lambda_a(x)=0\}$ for each index $a$.
--   4. **Coordinates as affine maps.** Each $\lambda_a$ packaged as an affine map $\mathbb{R}^d\to\mathbb{R}$: the constant $1$ minus the sum of the coordinate projections for $a=\star$, and the $i$-th coordinate projection for $a=i$.
--   5. **Vertices.** $v_\star=0$ and $v_i=e_i$, so that $\lambda_a(v_b)=1$ if $a=b$ and $\lambda_a(v_b)=0$ otherwise.
--
--   The simplex is exactly the set where all $d+1$ barycentric coordinates are nonnegative, and $F_a$ is the facet opposite the vertex $v_a$. The velocities always satisfy $\sum_a\mu_a(u)=0$. These objects organize the computation of the shadow of $T_d$ in a direction $u\neq0$: the orthogonal projection of $T_d$ onto $u^\perp$ is covered by the projections of the front facets $F_a$ with $\mu_a(u)<0$, and two such projections overlap only in a set of measure zero, so the shadow volume is a sum over front facets.
--
--   **Formalization Note** The index set is `Option (Fin d)`, with `none` playing the role of $\star$ and `some i` that of $i$ (coordinates are indexed from $0$ in Lean). The Lean names are `simplexCoordinates`, `simplexVelocity`, `simplexFacet`, `simplexCoordinateAffine` and `simplexVertex`; the identities $\lambda_a(x+tu)=\lambda_a(x)+t\mu_a(u)$ and $\lambda_a(v_b)=\delta_{ab}$ are lemmas of the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092

def simplexCoordinates {d : ℕ} (x : Euclidean d) : Option (Fin d) → ℝ
  | none => 1 - ∑ i, x i
  | some i => x i

def simplexVelocity {d : ℕ} (u : Euclidean d) : Option (Fin d) → ℝ
  | none => -∑ i, u i
  | some i => u i

def simplexFacet (d : ℕ) (a : Option (Fin d)) : Set (Euclidean d) :=
  {x | x ∈ standardSimplex d ∧ simplexCoordinates x a = 0}

def simplexCoordinateAffine {d : ℕ} : Option (Fin d) → Euclidean d →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ (Euclidean d) 1 -
      (∑ i : Fin d, (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i : Euclidean d →ₗ[ℝ] ℝ)).toAffineMap
  | some i => (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i : Euclidean d →ₗ[ℝ] ℝ).toAffineMap

def simplexVertex {d : ℕ} : Option (Fin d) → Euclidean d
  | none => 0
  | some i => EuclideanSpace.single i 1

end Paper092

end

end OAI


