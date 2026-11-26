-- Prove2me | Definitions.Def_Spectral_Stone_Generator
-- name    : Spectral_Stone_Generator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:53:35.467218+00:00
-- url     : https://prove2.me/theorems/91bcaa3a-e4b5-5c9f-9708-16ab72ea722f
-- title:
--   Generator
-- statement:
--   Definitions and structural lemmas for Generator, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Generator.lean

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
structure StrongContUnitary (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  toFun : ℝ → (E →L[ℂ] E)
  isUnitary : ∀ t, toFun t ∈ unitary (E →L[ℂ] E)
  zero : toFun 0 = 1
  add : ∀ s t, toFun (s + t) = toFun s * toFun t
  stronglyContinuous : ∀ x, Continuous (fun t => toFun t x)
namespace StrongContUnitary
noncomputable def differenceQuotient (U : StrongContUnitary E) (x : E) (t : ℝ) : E :=
  (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x)
theorem differenceQuotient_zero (U : StrongContUnitary E) :
    differenceQuotient U (0 : E) = 0 := by
  funext t
  simp only [differenceQuotient, map_zero, sub_self, smul_zero, Pi.zero_apply]
theorem differenceQuotient_add (U : StrongContUnitary E) (x y : E) :
    differenceQuotient U (x + y) =
      differenceQuotient U x + differenceQuotient U y := by
  funext t
  simp only [differenceQuotient, map_add, add_sub_add_comm, smul_add, Pi.add_apply]
theorem differenceQuotient_smul (U : StrongContUnitary E) (c : ℂ) (x : E) :
    differenceQuotient U (c • x) = c • differenceQuotient U x := by
  funext t
  simp only [differenceQuotient, map_smul, ← smul_sub, smul_smul, Pi.smul_apply, mul_comm]
def generatorDomain (U : StrongContUnitary E) : Submodule ℂ E where
  carrier := {x | ∃ y, Filter.Tendsto (differenceQuotient U x)
    (nhdsWithin 0 {0}ᶜ) (nhds y)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [differenceQuotient_zero]
    exact tendsto_const_nhds
  add_mem' {x y} hx hy := by
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    refine ⟨x' + y', ?_⟩
    rw [differenceQuotient_add]
    exact hx.add hy
  smul_mem' c x hx := by
    obtain ⟨x', hx⟩ := hx
    refine ⟨c • x', ?_⟩
    rw [differenceQuotient_smul]
    exact hx.const_smul c
theorem mem_generatorDomain_iff (U : StrongContUnitary E) (x : E) :
    x ∈ generatorDomain U ↔
      ∃ y, Filter.Tendsto (differenceQuotient U x)
        (nhdsWithin 0 {0}ᶜ) (nhds y) :=
  Iff.rfl
noncomputable def generatorLimit (U : StrongContUnitary E)
    (x : generatorDomain U) : E :=
  Classical.choose ((mem_generatorDomain_iff U x).mp x.property)
theorem generatorLimit_spec (U : StrongContUnitary E)
    (x : generatorDomain U) :
    Filter.Tendsto (differenceQuotient U x)
      (nhdsWithin 0 {0}ᶜ) (nhds (generatorLimit U x)) :=
  Classical.choose_spec ((mem_generatorDomain_iff U x).mp x.property)
noncomputable def generator
    (U : StrongContUnitary E) : E →ₗ.[ℂ] E :=
  { domain := generatorDomain U
    toFun :=
      { toFun := generatorLimit U
        map_add' := fun x y ↦ by
          apply tendsto_nhds_unique (generatorLimit_spec U (x + y))
          change Filter.Tendsto
            (differenceQuotient U ((x : E) + (y : E)))
            (nhdsWithin 0 {0}ᶜ)
            (nhds (generatorLimit U x + generatorLimit U y))
          rw [differenceQuotient_add]
          exact (generatorLimit_spec U x).add (generatorLimit_spec U y)
        map_smul' := fun c x ↦ by
          apply tendsto_nhds_unique (generatorLimit_spec U (c • x))
          change Filter.Tendsto
            (differenceQuotient U (c • (x : E)))
            (nhdsWithin 0 {0}ᶜ)
            (nhds (c • generatorLimit U x))
          rw [differenceQuotient_smul]
          exact (generatorLimit_spec U x).const_smul c } }
end StrongContUnitary


