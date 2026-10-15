-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
-- name    : OAI_Geometry_ProjectionVolume_SimplexVolume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:59:20.600746+00:00
-- url     : https://prove2.me/theorems/17fd4b4a-ab44-4744-a711-ec19168dc03a
-- title:
--   Coordinate simplex, coordinate sign changes and signed simplices in $\mathbb{R}^n$
-- statement:
--   Work in the coordinate space $\mathbb{R}^n$ of real functions on $\{1,\dots,n\}$, with its product Lebesgue measure. The file defines:
--
--   1. **Coordinate simplex.** $$\Delta_n=\Bigl\{x\in\mathbb{R}^n:\ x_i\ge0\ \text{for all } i,\ \ \sum_{i=1}^n x_i\le1\Bigr\}.$$
--   2. **Sign change.** For a sign pattern $s\in\{\mathrm{true},\mathrm{false}\}^n$, the map $\sigma_s:\mathbb{R}^n\to\mathbb{R}^n$ with $(\sigma_s x)_i=x_i$ if $s_i=\mathrm{true}$ and $(\sigma_s x)_i=-x_i$ if $s_i=\mathrm{false}$.
--   3. **Signed simplex.** $S_s=\sigma_s^{-1}(\Delta_n)$, the reflection of $\Delta_n$ into the orthant selected by $s$: $x\in S_s$ if and only if $\sigma_s x$ has nonnegative coordinates with sum at most $1$.
--
--   Each $\sigma_s$ is a linear involution preserving Lebesgue measure, so every signed simplex has the volume of $\Delta_n$. The union of the $2^n$ signed simplices is exactly the cross-polytope $\{x:\ \sum_i|x_i|\le1\}$, and two of them overlap only inside a coordinate hyperplane. Comparing with the known volume $2^n/n!$ of this $\ell^1$ ball gives $\operatorname{vol}(\Delta_n)=1/n!$, and hence the volume of the standard simplex $\operatorname{conv}\{0,e_1,\dots,e_n\}$.
--
--   **Formalization Note** These sets live in the plain function space `Fin n → ℝ` rather than in `EuclideanSpace ℝ (Fin n)`. The Lean names are `coordinateSimplex`, `signChange` and `signedSimplex`, and a sign pattern is a function `Fin n → Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Paper092

def coordinateSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def signChange {n : ℕ} (s : Fin n → Bool) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if s i then x i else -x i

def signedSimplex {n : ℕ} (s : Fin n → Bool) : Set (Fin n → ℝ) :=
  signChange s ⁻¹' coordinateSimplex n

end Paper092

end

end OAI


