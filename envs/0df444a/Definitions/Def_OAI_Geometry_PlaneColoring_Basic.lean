-- Prove2me | Definitions.Def_OAI_Geometry_PlaneColoring_Basic
-- name    : OAI_Geometry_PlaneColoring_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:37:08.424969+00:00
-- url     : https://prove2.me/theorems/56f0c436-6f1c-4f00-910c-d69739aee425
-- title:
--   Uniform probability measure on the unit circle via the angle parametrization
-- statement:
--   Let $\mathbb{R}^2$ denote the Euclidean plane and $\lambda$ Lebesgue measure on $\mathbb{R}$. The file defines the standard parametrization of the unit circle and the uniform probability measure on it.
--
--   1. **Direction map.** For $t\in\mathbb{R}$,
--   $$u(t)=(\cos t,\ \sin t)\in\mathbb{R}^2,$$
--   the unit vector making the angle $t$ with the positive first coordinate axis.
--   2. **Normalized angle measure.** The measure $\mu$ on $\mathbb{R}$ obtained by restricting $\lambda$ to $[0,2\pi)$ and dividing by $2\pi$:
--   $$\mu(A)=\frac{\lambda\bigl(A\cap[0,2\pi)\bigr)}{2\pi}\qquad\text{for Borel sets } A\subseteq\mathbb{R}.$$
--   It is the law of an angle drawn uniformly at random from $[0,2\pi)$.
--   3. **Circle measure.** The push-forward $\sigma=u_*\mu$ of $\mu$ under the direction map,
--   $$\sigma(B)=\mu\bigl(\{t\in\mathbb{R}:\ (\cos t,\sin t)\in B\}\bigr)\qquad\text{for Borel sets } B\subseteq\mathbb{R}^2 .$$
--   This is the normalized arc-length measure on the unit circle $S^1=\{v\in\mathbb{R}^2:\ \|v\|=1\}$, i.e. the distribution of a uniformly random unit vector.
--
--   The circle measure models a uniformly random direction. Pairing a point $x$ with $x+v$, where $v$ is drawn from $\sigma$, produces a random pair of points at distance exactly $1$; this is the natural way to average a coloring of the plane over unit-distance pairs, for example when studying measurable colorings.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)` and `circleDir t` is the vector with coordinates $\cos t$ and $\sin t$. The scaling factor is the inverse of `ENNReal.ofReal (2 * π)`, an extended nonnegative real, and `circleMeasure` is `Measure.map circleDir normalizedAngleMeasure`; the companion file proves that `circleDir` is continuous, so this is a genuine push-forward, and that both measures have total mass $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PlaneColoring mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem160

def circleDir (t : ℝ) : Plane :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]

def normalizedAngleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ •
    Measure.restrict volume (Set.Ico 0 (2 * Real.pi))

def circleMeasure : Measure Plane :=
  Measure.map circleDir normalizedAngleMeasure

end Problem160

end

end OAI


