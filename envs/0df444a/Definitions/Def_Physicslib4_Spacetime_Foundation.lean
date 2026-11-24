-- Prove2me | Definitions.Def_Physicslib4_Spacetime_Foundation
-- name    : Physicslib4_Spacetime_Foundation
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T20:57:08.166972+00:00
-- url     : https://prove2.me/theorems/be4fd4ee-d97f-45a7-acb0-ef8086cd76e7
-- title:
--   Spacetime foundation: Lorentzian manifolds (core structure)
-- statement:
--   A **spacetime** is a real, four-dimensional, connected, smooth, Hausdorff manifold $M$ with a smooth symmetric non-degenerate Lorentzian $(0,2)$-tensor $g$ of signature $(-,+,+,+)$. The model space is $\mathbb{R}^4$ (`SpacetimeModel`); `LorentzianAt` asserts a basis with Gram matrix $\mathrm{diag}(-1,1,1,1)$. This is the core `Spacetime` structure (blueprint `def:spacetime`). **Pending:** the causal layer (`alexandrovBasis`, `chronologicalFuture`/`Past`, `IsCompletelySpacelike`, `standardMinkowskiTimeOrientation`) and `StandardMinkowskiSpacetime` itself, which the AQFT bundles reference, are part of the foundational closure to be completed via the full-project pipeline.
-- source:
--   https://github.com/physicslib/physicslib4/blob/main/Physicslib4/Spacetime/Basic.lean (def:spacetime)

import Mathlib

namespace Physicslib4

open scoped Manifold ContDiff

/-- The model space ℝ⁴ for a spacetime. -/
abbrev SpacetimeModel : Type := EuclideanSpace ℝ (Fin 4)

/-- The signature matrix diag(-1, 1, 1, 1). -/
def lorentzSignature : Fin 4 → Fin 4 → ℝ :=
  Matrix.diagonal (fun i : Fin 4 => if i = 0 then (-1 : ℝ) else 1)

/-- A symmetric bilinear form is Lorentzian if some basis has Gram matrix diag(-1,1,1,1). -/
def LorentzianAt {V : Type*} [AddCommGroup V] [Module ℝ V] (g : V → V → ℝ) : Prop :=
  ∃ b : Module.Basis (Fin 4) ℝ V, ∀ i j : Fin 4, g (b i) (b j) = lorentzSignature i j

/-- A spacetime: a connected four-dimensional smooth Hausdorff manifold with a Lorentzian metric. -/
structure Spacetime where
  Carrier : Type*
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [connected : ConnectedSpace Carrier]
  [chartedSpace : ChartedSpace SpacetimeModel Carrier]
  model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel
  [isManifold : IsManifold model ∞ Carrier]
  [boundaryless : model.Boundaryless]
  tangent_findim : ∀ x : Carrier, FiniteDimensional ℝ (TangentSpace model x)
  val : ∀ x : Carrier, TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ
  symm : ∀ (x : Carrier) (v w : TangentSpace model x), val x v w = val x w v
  nondegenerate : ∀ (x : Carrier) (v : TangentSpace model x),
    (∀ w : TangentSpace model x, val x v w = 0) → v = 0
  lorentzian : ∀ x : Carrier, LorentzianAt (fun v w : TangentSpace model x => val x v w)
  contMDiff : ContMDiff model
      (model.prod 𝓘(ℝ, SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)) ∞
      (fun x ↦ Bundle.TotalSpace.mk'
        (SpacetimeModel →L[ℝ] SpacetimeModel →L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace model x →L[ℝ] TangentSpace model x →L[ℝ] ℝ)
        x (val x))

end Physicslib4


