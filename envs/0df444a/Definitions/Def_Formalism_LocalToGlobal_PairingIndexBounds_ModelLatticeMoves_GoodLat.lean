-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GoodLat
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GoodLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:08.04815+00:00
-- url     : https://prove2.me/theorems/5731c9b1-ea2b-473c-8c06-dc96749b82ae
-- title:
--   Good Lat
-- statement:
--   Definitions and structural lemmas for Good Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/GoodLat.lean

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_IsBichar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def wU (H : Sesq V) (α : V → ℂ) (x : V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun F z := α x * opU H x F z
  map_add' F G := by funext z; simp [opU, mul_add, add_mul]
  map_smul' r F := by funext z; simp [opU, smul_eq_mul]; ring
def cU (H : Sesq V) (A B : AddSubgroup V) (b : B) (a : A) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (a : V) (b : V) : ℂ))
def wA (H : Sesq V) (α : V → ℂ) (A : AddSubgroup V) (a : A) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (a : V)
def wB (H : Sesq V) (α : V → ℂ) (B : AddSubgroup V) (b : B) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (b : V)
def GoodLat (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) : Prop :=
  IsSemiChar H Λ α ∧ Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) ∧
    (∀ a ∈ A, ∀ b ∈ B, a + b ∈ Λ → a ∈ Λ) ∧
    (∀ a ∈ A, (∀ b ∈ B, b ∈ Λ → ∃ m : ℤ, altE H a b = m) → a ∈ Λ) ∧
    (∀ b ∈ B, (∀ a ∈ A, a ∈ Λ → ∃ m : ℤ, altE H a b = m) → b ∈ Λ)
def volA (A Λ₀ Λ : AddSubgroup V) : ℝ :=
  (((Λ₀ ⊓ A).relIndex (Λ ⊓ A) : ℕ) : ℝ) / (((Λ ⊓ A).relIndex (Λ₀ ⊓ A) : ℕ) : ℝ)
end Formalism.L2.PairingIndexBounds.Mv


