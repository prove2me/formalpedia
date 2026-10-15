-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Determinant
-- name    : OAI_Geometry_Zonotope_Determinant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:37:35.630599+00:00
-- url     : https://prove2.me/theorems/188959c5-fb79-4352-9c86-0dd38a573905
-- title:
--   Replacing a column of the identity matrix by the all-ones vector leaves determinant one
-- statement:
--   Let $R$ be a commutative ring, $\iota$ a finite index set with decidable equality, and $i\in\iota$. Let $I$ be the $\iota\times\iota$ identity matrix over $R$, and let $I^{(i)}$ be the matrix obtained from $I$ by replacing its $i$-th column with the all-ones column. Then
--
--   $$\det I^{(i)}=1 .$$
--
--   Equivalently, the linear map $S_i$ that keeps the $i$-th coordinate and adds $s_i$ to every other coordinate, $(S_is)_j=s_j+s_i$ for $j\neq i$, has determinant one. Over $\mathbb{R}$, $S_i$ is the linear part of the affine map sending the unit cube onto the $i$-th extrusion cell of the cube-plus-diagonal zonotope $[0,1]^\iota+[0,1]\mathbf 1$, so each cell has volume exactly one; this yields the volume $|\iota|+1$ of the zonotope.
--
--   **Formalization Note** The Lean statement is `det_identity_updateCol_ones i : ((1 : Matrix ι ι R).updateCol i (fun _ => 1)).det = 1` in the namespace `DiagonalZonotope`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Determinant.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Determinant.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductZonotopeBridge

namespace OAI

noncomputable section
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- Replacing one identity column by the all-ones vector leaves determinant one. -/
theorem det_identity_updateCol_ones (i : ι) :
    ((1 : Matrix ι ι R).updateCol i (fun _ => 1)).det = 1 := by
  have h := Matrix.det_updateCol_sum (1 : Matrix ι ι R) i (fun _ => (1 : R))
  have hc : (fun k : ι => ∑ j : ι, (1 : R) • (1 : Matrix ι ι R) k j) =
      (fun _ : ι => (1 : R)) := by
    funext k
    simp [Matrix.one_apply]
  rw [hc] at h
  simpa using h

end DiagonalZonotope

end

end OAI


