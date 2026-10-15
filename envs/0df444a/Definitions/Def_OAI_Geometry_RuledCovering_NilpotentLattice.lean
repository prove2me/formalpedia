-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
-- name    : OAI_Geometry_RuledCovering_NilpotentLattice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:24:39.475285+00:00
-- url     : https://prove2.me/theorems/33e9694b-ac93-47b2-a745-951fa8cc5d38
-- title:
--   Shear template, orthonormal frames and cylinders projected from square tiles
-- statement:
--   Let $\mathbb{R}^2_\infty$ be the coordinate plane of pairs of reals with the maximum norm and $\mathbb{R}^2$ the Euclidean plane. Recall that a *square tile* is a set $T=c+a\,Q\bigl([-\tfrac12,\tfrac12]^2\bigr)$ with $c\in\mathbb{R}^2$, $a>0$ and $Q$ a linear isometry of $\mathbb{R}^2$, and that for $h\in\mathbb{R}$, $g\in\mathbb{R}^2$ and $P\subseteq\mathbb{R}^2$, $\mathcal{C}_{h,g}(P)$ denotes the cylinder whose unit axis is parallel to $d_{h,g}=(1,g_1,hg_2)$ and whose base is the orthogonal projection of $\{(0,p_1,hp_2):\ p\in P\}$ onto the plane $d_{h,g}^{\perp}$.
--
--   1. **Shear.** The linear map $N$ of $\mathbb{R}^2_\infty$ given by
--   $$N(x_1,x_2)=(x_2,\ 0),\qquad [N]=\begin{pmatrix}0&1\\0&0\end{pmatrix},$$
--   defined both as a linear and as a continuous linear map.
--   2. **Orthogonal frame.** For a linear isometry $Q$ of $\mathbb{R}^2$, the frame $M_Q:\mathbb{R}^2_\infty\to\mathbb{R}^2$, $M_Q(x)=Q(x_1,x_2)$: the coordinate pair is read as a Euclidean vector and then moved by $Q$.
--   3. **Square-projected cylinders.** For $h\in\mathbb{R}$, a cylinder $C$ is square-projected if $C=\mathcal{C}_{h,g}(T)$ for some square tile $T$ and some $g\in\mathbb{R}^2$.
--
--   These objects organize the nilpotent case. The same module shows that a planar operator $A$ with $A^2=0$ admits a linear isometry $Q$ and a real $d$ with $Q^{-1}AQ=dN$; that for every real $d$, with no smallness assumption, the sliding-row lattice model $\mathrm{LM}(dN,\,1,\,(1+|d|)/2)$ holds; and that $M_Q$ maps every coordinate square (closed max-norm ball) of positive radius onto a square tile. Consequently the covers in the nilpotent case consist of square-projected cylinders, which supplies the square tiles $T_i$ and directions $g_i$ required by the nilpotent statement.
--
--   **Formalization Note** `shearLinear` sends `p` to `![p 1, 0]` and `shearCLM` is its continuous version; `orthogonalFrame Q` is `(EuclideanSpace.equiv (Fin 2) ℝ).symm.trans Q.toContinuousLinearEquiv`; `squareProjected h C` says that `C = projectedCylinder h g T` for some `T` with `IsSquareTile T` and some `g`, equality of cylinders meaning equality of axis and base.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def shearLinear : Coordinates →ₗ[ℝ] Coordinates where
  toFun p := ![p 1, 0]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp

def shearCLM : Coordinates →L[ℝ] Coordinates := shearLinear.toContinuousLinearMap

def orthogonalFrame (R : Plane ≃ₗᵢ[ℝ] Plane) : Coordinates ≃L[ℝ] Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans R.toContinuousLinearEquiv

def squareProjected (h : ℝ) (C : Cylinder) : Prop :=
  ∃ T : Set Plane, ∃ g : Plane, IsSquareTile T ∧ C = projectedCylinder h g T

end RuledApproximation

end

end OAI


