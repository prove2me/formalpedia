-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints
-- name    : OAI_Geometry_ConjugatePoints_NoConjugatePoints
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:53:24.196345+00:00
-- url     : https://prove2.me/theorems/3684b159-bf24-44dd-bccf-d3aff5280423
-- title:
--   Gauge-corrected Jacobi fields, frame matrices and uniform cometric bounds for neck passages
-- statement:
--   This file introduces the small amount of new vocabulary used in the assembly of the no-conjugate-points theorem: a gauge correction that removes the first coordinate of a Jacobi field, the $2\times2$ frame matrices of the two ends of the neck, the inverse right-frame coordinate change, and the proposition expressing uniform bounds on the neck cometrics.
--
--   Points and vectors of $\mathbb{R}^3$ are written $x=(x_0,x_1,x_2)$; $\gamma,J:\mathbb{R}\to\mathbb{R}^3$ are arbitrary curves, $\gamma'(s)$ is the derivative of $\gamma$ at $s$ and $\gamma'_0(s)$ its first coordinate. For $q\in\mathbb{R}^2$ and a $2\times2$ real matrix $A$, $|q|^2=q_0^2+q_1^2$ and $Q_A(q)=q\cdot Aq$.
--
--   1. **Regular gauge and gauge field.**
--   $$
--   \mu_{\gamma,J}(s)=-\frac{J_0(s)}{\gamma'_0(s)},\qquad \widetilde J(s)=J(s)+\mu_{\gamma,J}(s)\,\gamma'(s).
--   $$
--   When $\gamma'_0(s)\ne0$, the corrected field $\widetilde J(s)$ has vanishing first coordinate; adding a multiple of $\gamma'$ to a Jacobi field is the usual tangential gauge freedom.
--
--   2. **Frame matrices.** For $\delta\in\mathbb{R}$, with $T_2(\delta)=\begin{pmatrix}\delta^2&1\\1&0\end{pmatrix}$ and $C_2(\delta)=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$, the flip frame is $C_2(\delta)$ for the right end and $T_2(\delta)$ for the left end.
--
--   3. **Right-frame coordinates.** $\operatorname{toRight}_\delta(x)=F_\delta^{-1}(x-(1,0,0))=(1-x_0,\ x_2,\ x_1-\delta^2x_2)$, where $F_\delta(y)=(-y_0,\delta^2y_1+y_2,y_1)$; it is the inverse of the affine right-frame map $y\mapsto F_\delta(y)+(1,0,0)$.
--
--   4. **Passage bounds.** Let $P^{\mathrm{L}}_\delta(t)=\begin{pmatrix}d_1+d_2s^2&d_2s\\d_2s&d_2\end{pmatrix}$ with $d_1=1+\delta A(t)$, $d_2=1+\delta A(1-t)$, $s=\delta^2\chi(t)$ (here $A$ is the fixed auxiliary profile and $\chi$ the smooth cut-off of the cometric construction) be the left coordinate cometric, and $P^{\mathrm{R}}_\delta(t)=C_2(\delta)P^{\mathrm{L}}_\delta(1-t)C_2(\delta)^{\mathsf T}$ the right one. For $C,\delta\in\mathbb{R}$, the proposition $\mathrm{PassageBounds}(C,\delta)$ states: for both ends $P\in\{P^{\mathrm{L}}_\delta,P^{\mathrm{R}}_\delta\}$, every $u\in[0,1]$ and every $q\in\mathbb{R}^2$,
--   $$
--   \tfrac19|q|^2\le Q_{P(u)}(q)\le18|q|^2,\qquad |P'(u)q|^2\le C^2\delta^2|q|^2,
--   $$
--   $$
--   0\le Q_{-P''(u)}(q),\qquad |P'(u)q|^2\le C\delta\,Q_{-P''(u)}(q).
--   $$
--
--   The bounds in item 4 are exactly the uniform ellipticity, first-derivative and concavity estimates on the neck cometrics that the passage analysis needs; the gauge field of item 1 reduces Jacobi fields along geodesics that are transverse to the slices $x_0=\mathrm{const}$ to fields with no $x_0$-component.
--
--   **Formalization Note** $\gamma'$, $P'$ and $P''$ are Lean's `deriv` (equal to $0$ where the function is not differentiable), and the quotient in $\mu_{\gamma,J}$ follows the convention $a/0=0$, so $\mu_{\gamma,J}(s)=0$ and $\widetilde J(s)=J(s)$ when $\gamma'_0(s)=0$. The left/right ends are indexed by a Boolean (`right = true` is the right end); the cometric is `coordinateCometric`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def regularGauge (γ J : ℝ → E3) (s : ℝ) : ℝ := -J s 0 / deriv γ s 0

def gaugeField (γ J : ℝ → E3) (s : ℝ) : E3 := J s + regularGauge γ J s • deriv γ s

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

def flipFrame (right : Bool) (δ : ℝ) : TMat := if right then C₂ δ else T₂ δ

end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def toRight (δ : ℝ) (x : E3) : E3 := (fromRightLinear δ).symm (x - ![1,0,0])
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

def PassageBounds (C δ : ℝ) : Prop :=
  ∀ right : Bool, ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
    (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
    0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

end

end OAI


