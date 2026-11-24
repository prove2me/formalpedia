-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:31.292459+00:00
-- url     : https://prove2.me/theorems/475f580d-7f73-4f73-827a-e88045fb3e0e
-- title:
--   Curve Count Objects
-- statement:
--   Definitions and structural lemmas for Curve Count Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k
def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)
def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))
def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k
end Objects
section Lemmas
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
end Lemmas
section Examples
example (a : Unit → ℤ) (τ : ℕ) :
    chartUnit (fun _ : (Σ _ : Unit, Fin 1) => (1 : ℚ)) (fun _ => 0) a τ = 1 := by
  simp [chartUnit]
example : chartRadius (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (ι := fun _ : Unit => Fin 1) (-1)) (fun _ => 0)
    (fun _ => 1) = Real.exp 1 := by
  simp [chartRadius, ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight]
example : curveChartMono (ι := fun _ : Unit => Fin 1) (fun _ => 0) (fun _ => 2) ≠ 0 := by
  simp [curveChartMono, X_ne_zero]
end Examples
end
end GroundTheory.Heights₂.Heights.Targets


