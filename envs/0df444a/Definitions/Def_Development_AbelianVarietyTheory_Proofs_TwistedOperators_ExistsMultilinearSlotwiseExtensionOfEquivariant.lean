-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:48.369605+00:00
-- url     : https://prove2.me/theorems/9a5752d9-6944-43e7-9b8a-ec70a5d6061b
-- title:
--   Exists Multilinear Slotwise Extension Of Equivariant
-- statement:
--   Definitions and structural lemmas for Exists Multilinear Slotwise Extension Of Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
namespace GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]
def piecewiseSubmodule (A B : ∀ τ, Submodule ℂ (H τ)) (s : Finset ι) (τ : ι) : Submodule ℂ (H τ) :=
  if τ ∈ s then B τ else A τ
def Invariant (A B : ∀ τ, Submodule ℂ (H τ)) (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E)))
    (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)) (T₀ : MultilinearMap ℂ H E) (s : Finset ι)
    (T : MultilinearMap ℂ H E) : Prop :=
  (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
  (∀ τ, τ ∉ s → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ piecewiseSubmodule A B s τ') →
      ∀ r ∈ Rk τ, ∀ x ∈ A τ, T (update u τ (r.1 x)) = r.2 (T (update u τ x))) ∧
  (∀ τ, τ ∈ s → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ piecewiseSubmodule A B s τ') →
      T.toLinearMap u τ ∈ C τ ∧
      ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (update u τ (r.1 x)) = r.2 (T (update u τ x)))
end GlobalTheory.FactorwiseExtension
namespace GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]
end GlobalTheory.FactorwiseExtension


