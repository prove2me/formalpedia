-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:51.769959+00:00
-- url     : https://prove2.me/theorems/f9c70093-f9be-49fb-bf67-db8e893de119
-- title:
--   Capelli Polynomial Coefficients Ideal
-- statement:
--   Definitions and structural lemmas for Capelli Polynomial Coefficients Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def preserving (I : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {f | ∀ F ∈ I, f F ∈ I}
  mul_mem' {f g} hf hg F hF := hf _ (hg F hF)
  add_mem' {f g} hf hg F hF := I.add_mem (hf F hF) (hg F hF)
  algebraMap_mem' r F hF := by
    simp only [Set.mem_setOf_eq, Module.algebraMap_end_apply]
    exact I.smul_mem r hF
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
noncomputable def sumPoly {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) : A[X] :=
  ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks


