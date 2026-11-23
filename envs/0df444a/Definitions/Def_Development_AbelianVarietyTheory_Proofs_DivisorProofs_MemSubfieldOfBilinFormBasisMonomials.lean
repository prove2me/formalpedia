-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:55.898584+00:00
-- url     : https://prove2.me/theorems/0867d598-6a45-4f44-8893-755ce4c7544b
-- title:
--   Mem Subfield Of Bilin Form Basis Monomials
-- statement:
--   Definitions and structural lemmas for Mem Subfield Of Bilin Form Basis Monomials, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
def monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) : Submodule ℤ (I → ℤ) :=
  AddSubgroup.toIntSubmodule
  { carrier := {v | ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀}
    zero_mem' := by simp [k₀.one_mem]
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq, Pi.add_apply, zpow_add, Finset.prod_mul_distrib,
        Units.val_mul] at *
      exact k₀.mul_mem ha hb
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib,
        Units.val_inv_eq_inv_val] at *
      exact k₀.inv_mem ha }
end GlobalTheory


