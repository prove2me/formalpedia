-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_ContinuousOnChartProjM
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_ContinuousOnChartProjM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:39.440805+00:00
-- url     : https://prove2.me/theorems/a735be8c-134a-4173-be25-9a8298b891b1
-- title:
--   Continuous On Chart Proj M
-- statement:
--   Definitions and structural lemmas for Continuous On Chart Proj M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/ContinuousOnChartProjM.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Theta
namespace FibreMeasure
open MeasureTheory Topology Filter Set
section Chart
variable {G T : Type*}
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
  [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
structure IsTransChart (dX : Measure G) (Γ : G → T) (Ω : Set G) (σ : T → G → G) : Prop where
  isOpen : IsOpen Ω
  continuousOn : ContinuousOn (fun q : T × G ↦ σ q.1 q.2) (univ ×ˢ Ω)
  mapsTo : ∀ s X, X ∈ Ω → σ s X ∈ Ω
  zero : ∀ X ∈ Ω, σ 0 X = X
  add : ∀ s t X, X ∈ Ω → σ s (σ t X) = σ (s + t) X
  shift : ∀ s X, X ∈ Ω → Γ (σ s X) = Γ X + s
  pres : ∀ s, MeasurePreserving (σ s) (dX.restrict Ω) (dX.restrict Ω)
variable {dX : Measure G} {Γ : G → T} {Ω : Set G} {σ : T → G → G}
variable (Γ σ) in

def chartProj (X : G) : G := σ (-Γ X) X
variable (Γ Ω σ) in

noncomputable def chartProjM : G → G := by
  classical exact Ω.piecewise (chartProj Γ σ) id
namespace IsTransChart
variable (h : IsTransChart dX Γ Ω σ)
include h
end IsTransChart
end Chart
end FibreMeasure
end GroundTheory.Heights₂.Theta


