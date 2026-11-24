-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:13.683562+00:00
-- url     : https://prove2.me/theorems/e8e9404f-8c66-420b-a08f-89d61ee7919c
-- title:
--   St Chart Cone Component
-- statement:
--   Definitions and structural lemmas for St Chart Cone Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartConeComponent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
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
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
def chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  bind₁ (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ))
theorem chartSubst_X {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (p : Σ k, ι k) :
    chartSubst σ i (X p) = X (σ.symm (Function.update i p.1 p.2)) := by
  simp [chartSubst]
example : chartSubst (Fintype.equivFin ((k : Unit) → PBlk 3 k)).symm (fun _ => 0) (X ⟨(), 0⟩) =
    X ((Fintype.equivFin ((k : Unit) → PBlk 3 k)).symm.symm (fun _ => 0)) := by
  rw [chartSubst_X]
  congr 2
def ChartConeComponent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiProjPrime W → ∀ W' ∈ segreChartComponents W σ i,
      ∃ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W'
end GroundTheory.Heights₂.Heights.Targets


