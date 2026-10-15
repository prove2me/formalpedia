-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Isometries
-- name    : OAI_Geometry_RuledCovering_Isometries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:22:13.139159+00:00
-- url     : https://prove2.me/theorems/f704fabf-a439-46d3-bd36-42a2082e3f97
-- title:
--   Rotating and translating cylinders in Euclidean space
-- statement:
--   A cylinder $C$ in $\mathbb{R}^3$ has a unit axis $u$ and a base $B$ contained in the plane $u^{\perp}$ (the orthogonal complement of the span of $u$); its carrier is $B+\mathbb{R}u$ and its area is the planar Lebesgue measure of $B$. Let $R$ be a linear isometry of $\mathbb{R}^3$ and $q\in\mathbb{R}^3$.
--
--   1. **Rotated plane.** For any $u\in\mathbb{R}^3$, the restriction of $R$ is a linear isometric isomorphism
--   $$R|_{u^{\perp}}:\ u^{\perp}\to (Ru)^{\perp},\qquad b\mapsto Rb,$$
--   with inverse $b\mapsto R^{-1}b$; it is well defined because $R$ preserves inner products.
--   2. **Rotated cylinder.** $C^{R}$ is the cylinder with axis $Ru$ (again a unit vector) and base $R(B)\subseteq (Ru)^{\perp}$.
--   3. **Transverse part.** For a cylinder $C$ with axis $u$, $\tau_C(q)=q-\langle u,q\rangle\,u\in u^{\perp}$ is the component of $q$ orthogonal to the axis.
--   4. **Translated cylinder.** $C+q$ is the cylinder with the same axis $u$ and base $\tau_C(q)+B$.
--
--   These are the operations needed to move finite cylinder covers by rigid motions. The same module shows that the carrier of $C^{R}$ is $R$ applied to the carrier of $C$, that the carrier of $C+q$ is the carrier of $C$ translated by $q$, and that both operations preserve the area and map parallelogram bases to parallelogram bases. Since every isometry of $\mathbb{R}^3$ is a linear isometry followed by a translation, a finite parallelogram cover of a set $S$ with total area at most $A$ yields one of $F(S)$ for every isometry $F$; this makes the covering statements isometry invariant, and the same operations produce the second family of cylinders in the nilpotent statement and the upper tip cylinder.
--
--   **Formalization Note** `rotatedPlane u R` is a `LinearIsometryEquiv` between the orthogonal complements of `span ℝ {u}` and `span ℝ {R u}`; `Cylinder.rotate`, `Cylinder.transversePart` and `Cylinder.translate` are as described, the unit-axis proof fields using that `R` preserves norms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Isometries.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Isometries.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def rotatedPlane (u : Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ((Submodule.span ℝ ({u} : Set Space))ᗮ) ≃ₗᵢ[ℝ]
      ((Submodule.span ℝ ({R u} : Set Space))ᗮ) where
  toFun b := ⟨R b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, R.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  invFun b := ⟨R.symm b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [← R.inner_map_map u (R.symm b), R.apply_symm_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_add' b c := by ext; simp
  map_smul' a b := by ext; simp
  norm_map' b := R.norm_map b

def Cylinder.rotate (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) : Cylinder where
  axis := R C.axis
  unit_axis := by rw [R.norm_map, C.unit_axis]
  base := rotatedPlane C.axis R '' C.base

def Cylinder.transversePart (C : Cylinder) (q : Space) :
    ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) :=
  ⟨q - (inner ℝ C.axis q) • C.axis, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, C.unit_axis]
    simp⟩

def Cylinder.translate (C : Cylinder) (q : Space) : Cylinder where
  axis := C.axis
  unit_axis := C.unit_axis
  base := (fun b => C.transversePart q + b) '' C.base

end RuledApproximation

end

end OAI


