-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:05.754573+00:00
-- url     : https://prove2.me/theorems/b82a8569-7553-4e3f-890f-9100ba056a72
-- title:
--   PMixed Number Polynomial
-- statement:
--   Definitions and structural lemmas for PMixed Number Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace MixedNumberPolynomial
section Differences
variable {K : Type*}
def gStep {G : Type*} [AddCommGroup G] (b : K → ℤ) (h : (K → ℤ) → G) : (K → ℤ) → G :=
  fun m => h m - h (m - b)
theorem gStep_comm {G : Type*} [AddCommGroup G] (a b : K → ℤ) (h : (K → ℤ) → G) :
    gStep a (gStep b h) = gStep b (gStep a h) := by
  funext m
  simp only [gStep]
  rw [sub_right_comm m a b]
  abel
instance {G : Type*} [AddCommGroup G] : LeftCommutative (gStep (K := K) (G := G)) :=
  ⟨gStep_comm⟩
variable [DecidableEq K]
end Differences
section Polynomials
variable {K : Type*}
def dPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - bind₁ (fun k => X k - C (b k : ℚ)) p
def Low (A : MvPolynomial K ℚ) (N : ℕ) : Prop := A = 0 ∨ A.totalDegree < N
end Polynomials
end MixedNumberPolynomial
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


