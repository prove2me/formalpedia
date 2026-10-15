-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
-- name    : OAI_Geometry_ProjectionVolume_ProductProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:56:07.34448+00:00
-- url     : https://prove2.me/theorems/f1847187-90e5-4f4d-aaf3-f4a838666690
-- title:
--   Facet coordinates, facets and vertices of the product $T_{10}\times T_{10}$
-- statement:
--   Let $K=T_{10}\times T_{10}\subset\mathbb{R}^{20}$ be the set of points $x$ whose blocks $x'=(x_1,\dots,x_{10})$ and $x''=(x_{11},\dots,x_{20})$ both lie in the standard simplex $T_{10}=\operatorname{conv}\{0,e_1,\dots,e_{10}\}$. For $T_{10}$ use its barycentric coordinates $\lambda_a$, velocities $\mu_a$ and vertices $v_a$, indexed by $a\in A=\{\star,1,\dots,10\}$: $\lambda_\star(y)=1-\sum_i y_i$, $\lambda_i(y)=y_i$, $\mu_\star(w)=-\sum_i w_i$, $\mu_i(w)=w_i$, $v_\star=0$, $v_i=e_i$. The facets of $K$ are indexed by the disjoint union $A\sqcup A$ of two copies of $A$, $22$ indices in total, written $(1,a)$ and $(2,a)$. The file defines:
--
--   1. **Facet coordinates.** For $x\in\mathbb{R}^{20}$, $$\Lambda_{(1,a)}(x)=\lambda_a(x'),\qquad \Lambda_{(2,a)}(x)=\lambda_a(x'').$$
--   2. **Velocities.** For $u\in\mathbb{R}^{20}$, $M_{(1,a)}(u)=\mu_a(u')$ and $M_{(2,a)}(u)=\mu_a(u'')$, so that $\Lambda_c(x+tu)=\Lambda_c(x)+t\,M_c(u)$ for every index $c$ and every $t\in\mathbb{R}$.
--   3. **Facets.** $G_c=\{x\in K:\ \Lambda_c(x)=0\}$ for each of the $22$ indices $c$.
--   4. **Facet coordinates as affine maps.** Each $\Lambda_c$ packaged as an affine map $\mathbb{R}^{20}\to\mathbb{R}$: the affine map $\lambda_a$ composed with the linear block projection $x\mapsto x'$ (for $c=(1,a)$) or $x\mapsto x''$ (for $c=(2,a)$).
--   5. **Vertices.** For $a,b\in A$, the point $w_{a,b}\in\mathbb{R}^{20}$ with blocks $w_{a,b}'=v_a$ and $w_{a,b}''=v_b$, a product of a vertex of the first factor with a vertex of the second.
--
--   Since $K=\{x:\ \Lambda_c(x)\ge0\ \text{for all } c\}$, the facet $G_{(1,a)}$ is $F_a\times T_{10}$ and $G_{(2,a)}$ is $T_{10}\times F_a$, where $F_a$ is the facet of $T_{10}$ opposite $v_a$. Exactly as for a single simplex, these objects reduce the shadow of $K$ in a direction $u\ne0$ to a sum over the front facets $G_c$ with $M_c(u)<0$, which is how the brightness function of $K$ is computed; the vertices $w_{a,b}$ provide, for any two distinct indices $c\ne c'$, a point where $\Lambda_c=1$ and $\Lambda_{c'}=0$.
--
--   **Formalization Note** The index type is `ProductFacetIndex := Option (Fin 10) ⊕ Option (Fin 10)`, with `Sum.inl` for the first block and `Sum.inr` for the second. The Lean names are `productCoordinates`, `productVelocity`, `productFacet`, `productCoordinateAffine` and `productVertex`; blocks are extracted with `firstBlock` and `secondBlock` (with `splitBlocks` in the affine version), and `productVertex a b` is `splitBlocks.symm (simplexVertex a, simplexVertex b)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

abbrev ProductFacetIndex := Option (Fin 10) ⊕ Option (Fin 10)

def productCoordinates (x : Euclidean 20) : ProductFacetIndex → ℝ
  | .inl a => simplexCoordinates (firstBlock x) a
  | .inr a => simplexCoordinates (secondBlock x) a

def productVelocity (u : Euclidean 20) : ProductFacetIndex → ℝ
  | .inl a => simplexVelocity (firstBlock u) a
  | .inr a => simplexVelocity (secondBlock u) a

def productFacet (a : ProductFacetIndex) : Set (Euclidean 20) :=
  {x | x ∈ productWitness ∧ productCoordinates x a = 0}

def productCoordinateAffine : ProductFacetIndex → Euclidean 20 →ᵃ[ℝ] ℝ
  | .inl a => (simplexCoordinateAffine a).comp
      (((LinearMap.fst ℝ (Euclidean 10) (Euclidean 10)).comp splitBlocks.toLinearMap).toAffineMap)
  | .inr a => (simplexCoordinateAffine a).comp
      (((LinearMap.snd ℝ (Euclidean 10) (Euclidean 10)).comp splitBlocks.toLinearMap).toAffineMap)

def productVertex (a b : Option (Fin 10)) : Euclidean 20 :=
  splitBlocks.symm (simplexVertex a, simplexVertex b)

end Paper092

end

end OAI


