-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_HasColengthEqPowMulPow
-- name    : ReciprocityTheory_DualLattices_HasColengthEqPowMulPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:43.490396+00:00
-- url     : https://prove2.me/theorems/128f7a60-4558-44d0-917d-1be7b1a04b2c
-- title:
--   Has Colength Eq Pow Mul Pow
-- statement:
--   Definitions and structural lemmas for Has Colength Eq Pow Mul Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasColengthEqPowMulPow.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
theorem quotient_out_add_coe (K : AddSubgroup N) (q : N ⧸ K) (k : K) :
    ((q.out + k : N) : N ⧸ K) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]
def quotientProdSubgroupEquiv (K : AddSubgroup N) : (N ⧸ K) × K ≃ N where
  toFun p := p.1.out + p.2
  invFun x := ((x : N ⧸ K),
    ⟨-((x : N ⧸ K).out) + x, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)⟩)
  left_inv := by
    rintro ⟨q, k⟩
    refine Prod.ext (quotient_out_add_coe K q k) (Subtype.ext ?_)
    show -((((q.out + k : N)) : N ⧸ K).out) + (q.out + k) = k
    rw [quotient_out_add_coe K q k]
    abel
  right_inv := by
    intro x
    show (x : N ⧸ K).out + (-((x : N ⧸ K).out) + x) = x
    abel
end ReciprocityTheory.PGsh.L2


