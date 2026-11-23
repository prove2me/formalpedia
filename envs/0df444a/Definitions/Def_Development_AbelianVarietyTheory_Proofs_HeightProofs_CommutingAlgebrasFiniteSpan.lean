-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpan
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:55.140705+00:00
-- url     : https://prove2.me/theorems/f8456b90-59e4-45e2-a65e-b312f7e7cca2
-- title:
--   Commuting Algebras Finite Span
-- statement:
--   Definitions and structural lemmas for Commuting Algebras Finite Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommutingAlgebrasFiniteSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
namespace GlobalTheory.FiniteOrbit
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y : M | ∃ a ∈ A, y = a x}
theorem apply_mem_orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) {a : Module.End ℂ M}
    (ha : a ∈ A) : a x ∈ orb A x :=
  Submodule.subset_span ⟨a, ha, rfl⟩
theorem orb_le {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {N : Submodule ℂ M}
    (h : ∀ a ∈ A, a x ∈ N) : orb A x ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, ha, rfl⟩
  exact h a ha
def finVec (A : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | FiniteDimensional ℂ (orb A x)}
  add_mem' := by
    intro x y hx hy
    have hx' : FiniteDimensional ℂ (orb A x) := hx
    have hy' : FiniteDimensional ℂ (orb A y) := hy
    have : orb A (x + y) ≤ orb A x ⊔ orb A y := orb_le fun a ha => by
      rw [map_add]
      exact Submodule.add_mem_sup (apply_mem_orb A x ha) (apply_mem_orb A y ha)
    exact Submodule.finiteDimensional_of_le this
  zero_mem' := by
    have : orb A (0 : M) ≤ ⊥ := orb_le fun a _ => by simp
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    intro c x hx
    have hx' : FiniteDimensional ℂ (orb A x) := hx
    have : orb A (c • x) ≤ orb A x := orb_le fun a ha => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (apply_mem_orb A x ha)
    exact Submodule.finiteDimensional_of_le this
def orbSub (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {y : M | ∃ a ∈ A, ∃ x ∈ W, y = a x}
end GlobalTheory.FiniteOrbit


