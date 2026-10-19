-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_ThreePoints
-- name    : OAI_Geometry_Arnold_ThreePoints
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:45:24.060979+00:00
-- url     : https://prove2.me/theorems/daad12c4-ef6e-4dc9-8ac2-81ecfe8977b6
-- title:
--   Lagrange equations on $S^2\times S^2$ and three explicit critical points
-- statement:
--   Let $\mathbb{R}^3$ have squared norm $|x|^2=x_0^2+x_1^2+x_2^2$, and let $S^2\times S^2=\{(x,y):|x|^2=|y|^2=1\}$. Write $p=(0,0,1)$ (pole) and $e=(1,0,0)$ (east).
--
--   1. **Multiplier criticality.** A pair $(x,y)$ is multiplier-critical if it lies on $S^2\times S^2$ and there are $\lambda,\mu\in\mathbb{R}$ with
--   $$
--   (1+y_0,\ y_1,\ y_2)=\lambda\,x,\qquad (x_0,\ x_1,\ x_2-1)=\mu\,y .
--   $$
--   These are the Lagrange equations for the critical points of $f(x,y)=\langle x,y\rangle+x_0-y_2$ on $S^2\times S^2$.
--   2. **Three explicit pairs.**
--   $$
--   q_0=(p,-e),\qquad q_+=\Bigl(\bigl(\tfrac{\sqrt3}{2},0,-\tfrac12\bigr),\bigl(\tfrac12,0,-\tfrac{\sqrt3}{2}\bigr)\Bigr),\qquad q_-=\Bigl(\bigl(-\tfrac{\sqrt3}{2},0,-\tfrac12\bigr),\bigl(\tfrac12,0,\tfrac{\sqrt3}{2}\bigr)\Bigr).
--   $$
--
--   Each of $q_0,q_\pm$ satisfies these equations, and the module shows that they are exactly the three solutions. They are the points used to count the fixed points of the counterexample map.
--
--   **Formalization Note** Pairs are `(Fin 3 → ℝ) × (Fin 3 → ℝ)`, and the equations are written coordinatewise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/ThreePoints.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/ThreePoints.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

abbrev R3 := Fin 3 → ℝ
abbrev Pair := R3 × R3

def sqNorm (x : R3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

def sphereProduct : Set Pair := {q | sqNorm q.1 = 1 ∧ sqNorm q.2 = 1}

def pole : R3 := ![0, 0, 1]
def east : R3 := ![1, 0, 0]

/-- The constrained critical equations of the polynomial. -/
def MultiplierCritical (q : Pair) : Prop :=
  q ∈ sphereProduct ∧ ∃ lam μ : ℝ,
    1 + q.2 0 = lam * q.1 0 ∧ q.2 1 = lam * q.1 1 ∧ q.2 2 = lam * q.1 2 ∧
    q.1 0 = μ * q.2 0 ∧ q.1 1 = μ * q.2 1 ∧ q.1 2 - 1 = μ * q.2 2

def qzero : Pair := (pole, -east)
def qplus : Pair := (![Real.sqrt 3 / 2, 0, -1/2], ![1/2, 0, -Real.sqrt 3 / 2])
def qminus : Pair := (![-Real.sqrt 3 / 2, 0, -1/2], ![1/2, 0, Real.sqrt 3 / 2])

open scoped Matrix

end ThreePoints
end ArnoldCounterexample

end

end OAI


