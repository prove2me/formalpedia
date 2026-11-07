-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
-- name    : QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:53:31.916379+00:00
-- url     : https://prove2.me/theorems/c4a5d7c1-6ca2-4fef-8889-14356e4e27ec
-- title:
--   Rat Func Coefficient Equiv
-- statement:
--   Definitions and structural lemmas for Rat Func Coefficient Equiv, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean

import Mathlib.FieldTheory.RatFunc.AsPolynomial
set_option autoImplicit false
namespace RatFunc
noncomputable def coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    RatFunc K ≃+* RatFunc L := by
  let ep : Polynomial K ≃+* Polynomial L := Polynomial.mapEquiv e
  let hnonzero : nonZeroDivisors (Polynomial K) ≤
      (nonZeroDivisors (Polynomial L)).comap ep :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ep ep.injective
  let f : RatFunc K →+* RatFunc L := RatFunc.mapRingHom ep hnonzero
  apply RingEquiv.ofBijective f
  constructor
  · exact RatFunc.map_injective ep hnonzero ep.injective
  · intro x
    let p : Polynomial K := ep.symm x.num
    let q : Polynomial K := ep.symm x.denom
    refine ⟨algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q, ?_⟩
    change RatFunc.map ep hnonzero
        (algebraMap (Polynomial K) (RatFunc K) p /
          algebraMap (Polynomial K) (RatFunc K) q) = x
    rw [RatFunc.map_apply_div]
    change algebraMap (Polynomial L) (RatFunc L) (ep p) /
        algebraMap (Polynomial L) (RatFunc L) (ep q) = x
    rw [show ep p = x.num by simp [p], show ep q = x.denom by simp [q]]
    exact x.num_div_denom
end RatFunc


