-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
-- name    : QEC_Coding_BalancedProduct_LPSFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:31:50.657086+00:00
-- url     : https://prove2.me/theorems/33ab3f3f-aa19-44f4-b115-71d60a128b69
-- title:
--   LPSFamily
-- statement:
--   Definitions and structural lemmas for LPSFamily, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSFamily.lean

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner
structure AdmissiblePrime401 where
  q : Nat
  prime : q.Prime
  gt40 : 40 < q
  legendre : @legendreSym q ⟨prime⟩ 401 = -1
instance (a : AdmissiblePrime401) : Fact a.q.Prime := ⟨a.prime⟩
def LPS401FamilyRayleighBound : Prop :=
  ∀ (q : Nat) (hqPrime : q.Prime) (hq40 : 40 < q)
    (hq : @legendreSym q ⟨hqPrime⟩ 401 = -1),
    @LPS401RayleighBound q ⟨hqPrime⟩ hq
theorem exists_admissiblePrime401_gt (B : Nat) :
    ∃ a : AdmissiblePrime401, B < a.q := by
  obtain ⟨q, hqB, hqPrime, hqMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B 401)
      (q := 401) (a := 3) (by norm_num) (by norm_num)
  haveI : Fact q.Prime := ⟨hqPrime⟩
  haveI : Fact (401 : Nat).Prime := ⟨by decide +kernel⟩
  have hq40 : 40 < q := by omega
  have hLegendre : @legendreSym q ⟨hqPrime⟩ 401 = -1 := by
    change legendreSym q (401 : ℤ) = -1
    have hqr : legendreSym q (401 : ℤ) = legendreSym 401 (q : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four
        (p := 401) (q := q) (by norm_num) (by omega)
    rw [hqr, legendreSym.mod]
    have hmod : q % 401 = 3 := hqMod
    rw [← Int.natCast_mod, hmod]
    exact (by decide +kernel :
      @legendreSym 401 ⟨by decide +kernel⟩ 3 = -1)
  exact ⟨⟨q, hqPrime, hq40, hLegendre⟩,
    lt_of_le_of_lt (Nat.le_max_left B 401) hqB⟩
noncomputable def admissiblePrime401At (B : Nat) : AdmissiblePrime401 :=
  Classical.choose (exists_admissiblePrime401_gt B)
end QEC.Coding.BalancedProduct.LPSFamily


