-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:48.821477+00:00
-- url     : https://prove2.me/theorems/f4c59259-0a90-4de8-bcad-699a51dfb471
-- title:
--   Operators
-- statement:
--   Definitions and structural lemmas for Operators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def IsStable (T : Set (End ℂ M)) (p : Submodule ℂ M) : Prop :=
  ∀ t ∈ T, ∀ x ∈ p, t x ∈ p
def IsSimpleUnder (T : Set (End ℂ M)) : Prop :=
  Nontrivial M ∧ ∀ p : Submodule ℂ M, IsStable T p → p = ⊥ ∨ p = ⊤
theorem IsStable.adjoin {T : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T p) :
    ∀ a ∈ Algebra.adjoin ℂ T, ∀ x ∈ p, a x ∈ p := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem t ht => exact h t ht
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact p.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact p.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
variable [FiniteDimensional ℂ M]
def restrictSet (T : Set (End ℂ M)) (N : Submodule ℂ M) (hN : IsStable T N) : Set (End ℂ N) :=
  Set.range fun t : T => (t : End ℂ M).restrict (hN t t.2)
end RestrictedTensor
end GroundTheory.Automorphic


