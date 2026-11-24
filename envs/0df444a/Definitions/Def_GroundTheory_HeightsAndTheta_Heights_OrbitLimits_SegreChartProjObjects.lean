-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:33.606165+00:00
-- url     : https://prove2.me/theorems/6ef49688-1daf-42ee-bcdf-03ce8a4085cf
-- title:
--   Segre Chart Proj Objects
-- statement:
--   Definitions and structural lemmas for Segre Chart Proj Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
section Proj
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical in

def chartProjMatrix {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) : Matrix (Fin d) (Fin m) ℂ :=
  fun r a => Ψ (fun i' => if σ a = i' then 1 else 0) r.succ
end Proj
section Chart
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0}
open Classical in

def chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin m → ℂ) → ℝ :=
  (chartLiftDom σ i).piecewise (g ∘ chartLift σ i) 0
def chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (L : Fin e → HermLine ι) :
    Fin e → (Fin m → ℂ) → ℝ :=
  fun j => pot L j ∘ chartLift σ i
end Chart
end GroundTheory.Heights₂.Heights


