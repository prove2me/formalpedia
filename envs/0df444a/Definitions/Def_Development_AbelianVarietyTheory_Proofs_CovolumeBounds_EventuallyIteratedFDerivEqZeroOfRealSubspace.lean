-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:37.009628+00:00
-- url     : https://prove2.me/theorems/c2df3310-9f81-4818-a365-b60cbb7ab17b
-- title:
--   Eventually Iterated FDeriv Eq Zero Of Real Subspace
-- statement:
--   Definitions and structural lemmas for Eventually Iterated FDeriv Eq Zero Of Real Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
namespace GlobalTheory.SCV
section General
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable [FiniteDimensional ℂ E] [CompleteSpace V]
end General
section Coordinates
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
noncomputable def scaledRealPoints (ι : Type*) (a : ℂ) : Submodule ℝ (ι → ℂ) where
  carrier := {z | ∃ x : ι → ℝ, z = fun i => a * x i}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by ext i; simp [mul_add]⟩
  zero_mem' := ⟨0, by ext i; simp⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by ext i; simp [mul_left_comm]⟩
variable [CompleteSpace V]
end Coordinates
end GlobalTheory.SCV


