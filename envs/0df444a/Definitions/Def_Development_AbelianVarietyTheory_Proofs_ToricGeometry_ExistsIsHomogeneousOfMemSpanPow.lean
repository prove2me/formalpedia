-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:32.0101+00:00
-- url     : https://prove2.me/theorems/a82bc446-aa33-4b6c-b5f7-abcd95ab66ef
-- title:
--   Exists Is Homogeneous Of Mem Span Pow
-- statement:
--   Definitions and structural lemmas for Exists Is Homogeneous Of Mem Span Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace ThetaGen
section Abstract
variable {X : Type}
def homog (d : ℕ) (f : X → ℂ) : ℂ × X → ℂ := fun p => p.1 ^ d * f p.2
def homogL (d : ℕ) : (X → ℂ) →ₗ[ℂ] (ℂ × X → ℂ) where
  toFun := homog d
  map_add' f h := by funext p; simp only [homog, Pi.add_apply]; ring
  map_smul' c f := by funext p; simp only [homog, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
variable (R : ℕ → Submodule ℂ (X → ℂ))
def gradedRing : Subalgebra ℂ (ℂ × X → ℂ) :=
  Algebra.adjoin ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f}
end Abstract
section Entire
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Entire
def level {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) : Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z,
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun n n' z => by
    simp only [Pi.add_apply, ha.2, hb.2, mul_add]⟩
  zero_mem' := ⟨differentiable_const _, fun n n' z => by simp⟩
  smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun n n' z => by
    simp only [Pi.smul_apply, ha.2, smul_eq_mul]; ring⟩
end ThetaGen
end GlobalTheory


