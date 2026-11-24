-- Prove2me | Definitions.Def_EkelandVP_Constraints_Supplement_parallelEnergy
-- name    : EkelandVP_Constraints_Supplement_parallelEnergy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:24:23.341935+00:00
-- url     : https://prove2.me/theorems/e6ef0768-5b22-46c5-b597-ee28b5c04797
-- title:
--   Energy, tangent velocity and Levi–Civita parallel fields along H¹ paths
-- statement:
--   For an H¹ path $c$, let $\dot c(t)$ be its tangent velocity at almost every time. Its **energy**, with the paper's normalization, is
--   $$
--   E(c)=\int_0^1\|\dot c(t)\|_{c(t)}^2\,dt.
--   $$
--   For a smooth tangent field $X$ along a smooth path, parallelism means $\nabla_{\dot c}X=0$ for the Levi–Civita connection. To define this without an arbitrary connection parameter, use a smooth chart, let $z$ be the coordinate path, $w$ the coordinate field, and $g_z$ the pulled-back Riemannian metric. For every coordinate test vector $b$, require
--   $$
--   2g_z(\dot w,b)+Dg_z[\dot z](w,b)+Dg_z[w](\dot z,b)-Dg_z[b](\dot z,w)=0.
--   $$
--   This is the coordinate Koszul formula for the unique metric-compatible torsion-free connection. It must hold in every smooth chart containing the time-point. A prescribed initial vector therefore gives the actual Levi–Civita parallel field, rather than an arbitrary comparison field.
--
--   The squared velocity error is
--   $$
--   R(c,X)=\int_0^1\|\dot c(t)-X(t)\|_{c(t)}^2\,dt.
--   $$
--   These quantities retain the squared $L^2$ error and the absence of a factor $1/2$ in the energy.
--
--   **Formalization Note** The manifold derivative within $[0,1]$ computes velocity. The field is a dependent tangent vector at each point of the same curve, smooth on the closed interval. The integral is the Bochner integral of its real squared norm. H¹ regularity gives energy integrability; smoothness on the compact interval gives error integrability. No integrability hypothesis is imposed on competitors beyond H¹ regularity, and no existence of a parallel field is part of the definition.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 338–339, Levi–Civita connection; p. 345, (6.16); p. 347, parallel translation and (6.33) (PDF 15–16,22,24); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_sobolevPaths
set_option autoImplicit false

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Bundle

namespace EkelandVP.Constraints.Supplement

universe u

variable {H M : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold 𝓘(ℝ, H) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, H) x)]

/-- Velocity computed with the manifold derivative within the closed time interval. -/
noncomputable def pathVelocity (c : SobolevPaths H M) (t : ℝ) :
    TangentSpace 𝓘(ℝ, H) (extendPath c.val t) :=
  mfderivWithin 𝓘(ℝ) 𝓘(ℝ, H) (extendPath c.val) (Icc 0 1) t 1

/-- Energy with the normalization in (6.16), p.345: no factor 1/2. -/
noncomputable def pathEnergy (c : SobolevPaths H M) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖pathVelocity c t‖ ^ 2

/-- Riemannian metric in the coordinates of a smooth chart, pulled back by its inverse. -/
noncomputable def coordinateMetric (e : OpenPartialHomeomorph M H) (z a b : H) : ℝ :=
  inner ℝ (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) e.symm z a)
    (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) e.symm z b)

/-- Coordinate expression of a vector field along a curve. -/
noncomputable def fieldCoordinates (e : OpenPartialHomeomorph M H) (c : SobolevPaths H M)
    (X : (t : ℝ) → TangentSpace 𝓘(ℝ, H) (extendPath c.val t)) (t : ℝ) : H :=
  mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) e (extendPath c.val t) (X t)

/-- Smooth tangent field along the curve, including its endpoint values. -/
def SmoothAlong (c : SobolevPaths H M)
    (X : (t : ℝ) → TangentSpace 𝓘(ℝ, H) (extendPath c.val t)) : Prop :=
  ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, H).prod 𝓘(ℝ, H)) ∞
    (fun t => Bundle.TotalSpace.mk' H (extendPath c.val t) (X t)) (Icc 0 1)

/-- Levi-Civita parallelism in coordinates. The equation is
2g(w′,b) + Dg[z′](w,b) + Dg[w](z′,b) - Dg[b](z′,w) = 0.
It is the Koszul formula for the unique torsion-free metric-compatible connection.
It neither chooses an arbitrary connection nor assumes the existence of a parallel field. -/
def IsParallel (c : SobolevPaths H M)
    (X : (t : ℝ) → TangentSpace 𝓘(ℝ, H) (extendPath c.val t)) : Prop :=
  SmoothAlong c X ∧ ∀ e : OpenPartialHomeomorph M H,
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ, H) ∞ M →
    ∀ t ∈ Icc (0 : ℝ) 1, extendPath c.val t ∈ e.source → ∀ b : H,
      let z := e (extendPath c.val t)
      let a := derivWithin (fun s => e (extendPath c.val s)) (Icc 0 1) t
      let w := fieldCoordinates e c X t
      let w' := derivWithin (fieldCoordinates e c X) (Icc 0 1) t
      2 * coordinateMetric e z w' b +
        fderiv ℝ (fun y => coordinateMetric e y w b) z a +
        fderiv ℝ (fun y => coordinateMetric e y a b) z w -
        fderiv ℝ (fun y => coordinateMetric e y a w) z b = 0

/-- Squared L² velocity error against a genuine tangent field along this same curve. -/
noncomputable def parallelError (c : SobolevPaths H M)
    (X : (t : ℝ) → TangentSpace 𝓘(ℝ, H) (extendPath c.val t)) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖pathVelocity c t - X t‖ ^ 2

end EkelandVP.Constraints.Supplement


