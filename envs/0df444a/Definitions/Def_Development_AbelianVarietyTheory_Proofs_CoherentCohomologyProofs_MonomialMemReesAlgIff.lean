-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:24.482993+00:00
-- url     : https://prove2.me/theorems/bd4f0d3d-43e6-42bb-9c67-da7adc216aa6
-- title:
--   Monomial Mem Rees Alg Iff
-- statement:
--   Definitions and structural lemmas for Monomial Mem Rees Alg Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialMemReesAlgIff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.ReesAlgebraMembership
variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
def reesAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] where
  carrier := {f | ∀ n, f.coeff n ∈ M n}
  add_mem' := fun {f g} hf hg n => by
    rw [coeff_add]
    exact (M n).add_mem (hf n) (hg n)
  mul_mem' := fun {f g} hf hg n => by
    rw [coeff_mul]
    refine (M n).sum_mem fun c hc => ?_
    have hn : c.1 + c.2 = n := by simpa using hc
    rw [← hn]
    exact SetLike.mul_mem_graded (hf c.1) (hg c.2)
  algebraMap_mem' := fun r n => by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact (M 0).smul_mem r (SetLike.one_mem_graded M)
    · exact (M n).zero_mem
variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]
end GlobalTheory.ReesAlgebraMembership


