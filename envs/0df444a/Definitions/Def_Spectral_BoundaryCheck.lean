-- Prove2me | Definitions.Def_Spectral_BoundaryCheck
-- name    : Spectral_BoundaryCheck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:14:22.511811+00:00
-- url     : https://prove2.me/theorems/c6d8d6df-3be2-53e2-9484-416be0ae0358
-- title:
--   Boundary Check
-- statement:
--   Definitions and structural lemmas for Boundary Check, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/BoundaryCheck.lean

import Definitions.Def_Spectral_Cayley_Inverse
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_FuncCalc
import Definitions.Def_Spectral_Stone_Theorem
import Theorems.Thm_cayleyTransform_unitary
import Theorems.Thm_dense_range_one_sub_cayleyTransform
import Theorems.Thm_inverseCayley_cayleyTransform
import Theorems.Thm_one_not_mem_eigenvalues_cayleyTransform
import Theorems.Thm_spectral_theorem_existence
import Theorems.Thm_spectral_theorem_uniqueness

set_option autoImplicit false
namespace SpectralStoneBoundary
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    cayleyTransform A hA ∈ unitary (E →L[ℂ] E) :=
  cayleyTransform_unitary A hA
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∀ x, cayleyTransform A hA x = x → x = 0 :=
  one_not_mem_eigenvalues_cayleyTransform A hA
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    DenseRange (fun x => x - cayleyTransform A hA x) :=
  dense_range_one_sub_cayleyTransform A hA
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    inverseCayley (cayleyTransform A hA) (cayleyTransform_unitary A hA)
      (one_not_mem_eigenvalues_cayleyTransform A hA)
      (dense_range_one_sub_cayleyTransform A hA) = A :=
  inverseCayley_cayleyTransform A hA
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A :=
  spectral_theorem_existence A hA
example (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S :=
  spectral_theorem_uniqueness A hA E₁ E₂ h₁ h₂ S hS
end SpectralStoneBoundary


