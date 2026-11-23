-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
-- name    : ReciprocityTheory_GroupCohomology_SectionA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:35.432879+00:00
-- url     : https://prove2.me/theorems/836e6738-d3e2-4c15-a3d5-76e4e3d25e89
-- title:
--   Section A
-- statement:
--   Definitions and structural lemmas for Section A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/SectionA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise Set
namespace ReciprocityTheory.Coh.ContinuousSections
variable {G : Type*} [Group G]
def rel (K N : Subgroup G) [hN : N.Normal] : Setoid G where
  r x y := ∃ k ∈ K, ∃ n ∈ N, y = k * n * x
  iseqv := {
    refl := fun x => ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
    symm := by
      rintro x y ⟨k, hk, n, hn, rfl⟩
      refine ⟨k⁻¹, K.inv_mem hk, k * n⁻¹ * k⁻¹, hN.conj_mem _ (N.inv_mem hn) k, by group⟩
    trans := by
      rintro x y z ⟨k, hk, n, hn, rfl⟩ ⟨k', hk', n', hn', rfl⟩
      refine ⟨k' * k, K.mul_mem hk' hk, k⁻¹ * n' * k * n, N.mul_mem ?_ hn, by group⟩
      simpa using hN.conj_mem n' hn' k⁻¹ }
noncomputable def rep (K N : Subgroup G) [N.Normal] (x : G) : G :=
  (Quotient.mk (rel K N) x).out
def tr (K N : Subgroup G) [N.Normal] : Set G := {y | y * (rep K N y)⁻¹ ∈ N}
variable [TopologicalSpace G] [IsTopologicalGroup G]
def admitted (U : Subgroup G) (p : Subgroup G × Set G) : Prop :=
  p.1 ≤ U ∧ IsClosed p.2 ∧ (∀ k ∈ p.1, ∀ s ∈ p.2, k * s ∈ p.2) ∧
  (∀ a ∈ p.2, ∀ b ∈ p.2, a * b⁻¹ ∈ U → a * b⁻¹ ∈ p.1) ∧ ∀ g, ∃ a ∈ p.2, a * g⁻¹ ∈ U
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end ReciprocityTheory.Coh.ContinuousSections


