-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:06.015378+00:00
-- url     : https://prove2.me/theorems/9daaeb98-593d-4eda-a909-d963f46f4925
-- title:
--   Segre Chart Objects
-- statement:
--   Definitions and structural lemmas for Segre Chart Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)
section Chart
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def segreChartSet (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, segre z i = 1 ∧ x = fun a => segre z (σ a)}
def segreChartIdeal (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (segreChartSet P σ i)
def segreChartComponents (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (segreChartIdeal P σ i)).toFinset
end Chart
section Lift
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ) :
    (Σ k, ι k) → ℂ :=
  fun p => x (σ.symm (Function.update i p.1 p.2))
end Lift
end GroundTheory.Heights₂.Heights


