-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:49.118646+00:00
-- url     : https://prove2.me/theorems/3c6ca168-470f-41ee-a6a8-fcaad8f2304e
-- title:
--   PDivision
-- statement:
--   Definitions and structural lemmas for PDivision, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
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
namespace EffectiveHS
open Finset
structure MulTower (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where

  W : Submodule R A

  V : ℕ → Submodule R A

  mul_mem : ∀ j, ∀ w ∈ W, ∀ f ∈ V j, w * f ∈ V (j + 1)
def mono {A : Type*} [CommRing A] {D : ℕ} (s : Fin D → A) (α : Fin D → ℕ) : A :=
  ∏ i, s i ^ α i
namespace MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
def Raises (k : ℕ) (x : A) : Prop := ∀ j, ∀ f ∈ τ.V j, x * f ∈ τ.V (j + k)
theorem Raises.mul {τ : MulTower R A} {k l : ℕ} {x y : A} (hx : τ.Raises k x)
    (hy : τ.Raises l y) : τ.Raises (k + l) (x * y) := by
  intro j f hf
  have e : j + (k + l) = j + l + k := by omega
  rw [e, mul_assoc]
  exact hx _ _ (hy j f hf)
def P (D T : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ α : Fin D → ℕ, ∃ h ∈ τ.V D, ∑ i, α i = T - D ∧ F = mono s α * h}
def Vpp (D T a₀ : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ (α : Fin D → ℕ) (k : ℕ) (w : Fin k → A) (m : A),
      (∀ i, w i ∈ τ.W) ∧ m ∈ τ.V 0 ∧ ∑ i, α i + k = T ∧ ∑ i, α i ≤ a₀ ∧
        F = mono s α * (∏ i, w i) * m} ⊔ τ.P D T s
variable {D : ℕ} {s : Fin D → A}
end MulTower
noncomputable def polyTower : MulTower ℚ (MvPolynomial (Fin 2) ℚ) where
  W := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1
  V j := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ j
  mul_mem j w hw f hf := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hw hf ⊢
    have h := hw.mul hf
    rwa [add_comm] at h
section Lift
open MeasureTheory
noncomputable def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial
end Lift
end EffectiveHS
end GroundTheory.Heights₂.Heights


