-- Prove2me | Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
-- name    : EkelandVP_Constraints_Supplement_riemannianManifold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:22:39.438808+00:00
-- url     : https://prove2.me/theorems/7902f07b-5640-4098-bd7c-595eff118a6a
-- title:
--   Complete strong smooth Riemannian Hilbert manifolds and the differential norm
-- statement:
--   A **complete strong Riemannian Hilbert manifold** is a smooth manifold $M$ modeled on a real Hilbert space $H$, with smoothly varying positive definite tangent inner products. Their norms induce the original tangent topology. The distance within a component is the infimum of lengths of smooth joining paths, and completeness refers to this intrinsic distance. No dimension bound, connectedness, compactness, or variational conclusion is included.
--
--   For a real differentiable function $F$, write
--   $$
--   \sigma_F(x)=\|dF_x\|_* = \|\operatorname{grad}F(x)\|_x.
--   $$
--   The equality uses the Riesz representation in the strong tangent metric. This supplies the geometry shared by the manifold applications.
--
--   **Formalization Note** Mathlib supplies the smooth manifold, strong tangent metric and intrinsic extended metric classes. Distinct components may have extended distance $+\infty$. This implements the within-component convention on p.339 and permits the disconnected counterexample recorded in DISPROOF.md. Nonemptiness is supplied by the endpoints in §6; it is not bundled into the general object. The model Hilbert space may be infinite dimensional.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 338–339, §5, tangent inner product and intrinsic distance (PDF 15–16); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
set_option autoImplicit false

open Manifold Bundle
open scoped ContDiff Bundle

namespace EkelandVP.Constraints.Supplement

universe u

/-- A complete strong smooth Riemannian Hilbert manifold. The data use Mathlib's genuine
smooth tangent metric and intrinsic extended distance. Infinite distance between different
components is allowed; no connectedness or variational conclusion is bundled. -/
structure CompleteStrongRiemannian where
  H : Type u
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℝ H]
  [completeH : CompleteSpace H]
  M : Type u
  [emetricM : EMetricSpace M]
  [chartedM : ChartedSpace H M]
  [smoothM : IsManifold 𝓘(ℝ, H) ∞ M]
  [metric : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, H) x)]
  [smoothMetric : IsContMDiffRiemannianBundle 𝓘(ℝ, H) ∞ H
    (fun x : M => TangentSpace 𝓘(ℝ, H) x)]
  [intrinsic : IsRiemannianManifold 𝓘(ℝ, H) M]
  [completeM : CompleteSpace M]

attribute [instance] CompleteStrongRiemannian.normedH CompleteStrongRiemannian.innerH
  CompleteStrongRiemannian.completeH CompleteStrongRiemannian.emetricM
  CompleteStrongRiemannian.chartedM CompleteStrongRiemannian.smoothM
  CompleteStrongRiemannian.metric CompleteStrongRiemannian.smoothMetric
  CompleteStrongRiemannian.intrinsic CompleteStrongRiemannian.completeM

/-- Differential norm in the strong tangent metric, equal to the norm of the Riesz gradient. -/
noncomputable def differentialNorm (D : CompleteStrongRiemannian) (F : D.M → ℝ) (x : D.M) : ℝ :=
  ‖mfderiv 𝓘(ℝ, D.H) 𝓘(ℝ) F x‖

end EkelandVP.Constraints.Supplement


