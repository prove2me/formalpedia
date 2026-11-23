-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:21.382176+00:00
-- url     : https://prove2.me/theorems/d339b4e7-a318-4004-8686-8e28ac92eb30
-- title:
--   Differentiable Rising S
-- statement:
--   Definitions and structural lemmas for Differentiable Rising S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
namespace GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
def risingS (σ : ℂ) (m : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j))
def eTerm (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (2 + m i) * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))
def dz (j : I) : (I → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℂ) j
def dzbar (j : I) : (I → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dz j)
def homFac (z : I → ℂ) : ℂ := ∏ i, ((1 + z i) / (2 * (Real.pi : ℂ) * Complex.I))
def logFac (z : I → ℂ) : ℂ := ((Real.log (Complex.normSq (homFac z)) : ℝ) : ℂ)
def modPt {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (z : I → ℂ) : Φ → ℂ :=
  fun τ => defCoord φ z θ (e.symm τ) / (1 + z (e.symm τ))
example (φ : E →+* ℂ) (x : E) :
    eTerm (fun _ : Unit => φ) (fun _ => 1) 0 0 x = -2 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 3 := by
  simp [eTerm, defCoord]
end GlobalTheory.WeightTwoSum


