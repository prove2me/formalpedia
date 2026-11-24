-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:40.173804+00:00
-- url     : https://prove2.me/theorems/4d9b5f5e-6183-4847-ad43-0f8981178372
-- title:
--   St Reg Radial Weight
-- statement:
--   Definitions and structural lemmas for St Reg Radial Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegRadialWeight.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def radialTransform (d : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * t ^ d - ∫ τ in (0 : ℝ)..t, a τ * ((d : ℝ) * τ ^ (d - 1))
def RegRadialWeight.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * ((d : ℝ) * τ ^ (d - 1))) = 0 →
      ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => radialTransform d a (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y
def RegRadialWeight.bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
def RegRadialWeight.weight (t : ℝ) : ℝ := RegRadialWeight.bump (t / 4) - 4 * RegRadialWeight.bump t
end
end GroundTheory.Heights₂.Heights


