-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:14.054194+00:00
-- url     : https://prove2.me/theorems/dc7522d1-8baa-4dd3-90f1-0c79d9de2709
-- title:
--   Mul Apply
-- statement:
--   Definitions and structural lemmas for Mul Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, y = (a : M → M) x}
lemma orb_le {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {U : Submodule ℂ M} :
    orb A x ≤ U ↔ ∀ a ∈ A, (a : M → M) x ∈ U := by
  unfold orb
  rw [Submodule.span_le]
  constructor
  · intro h a ha; exact h ⟨a, ha, rfl⟩
  · rintro h y ⟨a, ha, rfl⟩; exact h a ha
lemma mem_orb {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {a : Module.End ℂ M} (ha : a ∈ A) :
    (a : M → M) x ∈ orb A x := Submodule.subset_span ⟨a, ha, rfl⟩
def good (A : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | FiniteDimensional ℂ (orb A x)}
  zero_mem' := by
    show FiniteDimensional ℂ (orb A 0)
    have : orb A 0 ≤ ⊥ := orb_le.mpr (fun a _ => by simp)
    exact Submodule.finiteDimensional_of_le this
  add_mem' := by
    intro x y hx hy
    haveI : FiniteDimensional ℂ (orb A x) := hx
    haveI : FiniteDimensional ℂ (orb A y) := hy
    show FiniteDimensional ℂ (orb A (x + y))
    have : orb A (x + y) ≤ orb A x ⊔ orb A y := orb_le.mpr (fun a ha => by
      rw [map_add]
      exact Submodule.add_mem_sup (mem_orb ha) (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    intro c x hx
    haveI : FiniteDimensional ℂ (orb A x) := hx
    show FiniteDimensional ℂ (orb A (c • x))
    have : orb A (c • x) ≤ orb A x := orb_le.mpr (fun a ha => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this
def grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, ∃ x ∈ W, y = (a : M → M) x}
end GlobalTheory.OrbitGrowth


