-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:50:13.440431+00:00
-- url     : https://prove2.me/theorems/fd1bec94-8eac-41ee-b09a-4996d9d2f225
-- title:
--   Skew Ring
-- statement:
--   Definitions and structural lemmas for Skew Ring, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRing.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def constantFrobeniusZRingAction
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →* RingAut (ConstantExtension P r) :=
  zpowersHom _ (constantFrobenius P r).toRingEquiv
noncomputable instance constantFrobeniusZSMul
    (P : BasePrime) (r : Rank) :
    SMul (Multiplicative ℤ) (ConstantExtension P r) :=
  ⟨fun n c => constantFrobeniusZRingAction P r n c⟩
noncomputable instance constantFrobeniusZMulSemiringAction
    (P : BasePrime) (r : Rank) :
    MulSemiringAction (Multiplicative ℤ) (ConstantExtension P r) where
  one_smul c := by
    change constantFrobeniusZRingAction P r 1 c = c
    rw [map_one]
    rfl
  mul_smul n m c := by
    change constantFrobeniusZRingAction P r (n * m) c =
      constantFrobeniusZRingAction P r n
        (constantFrobeniusZRingAction P r m c)
    rw [map_mul]
    rfl
  smul_zero n := map_zero (constantFrobeniusZRingAction P r n)
  smul_add n := map_add (constantFrobeniusZRingAction P r n)
  smul_one n := map_one (constantFrobeniusZRingAction P r n)
  smul_mul n := map_mul (constantFrobeniusZRingAction P r n)
abbrev CartwrightStegerSkewLaurentRing
    (P : BasePrime) (r : Rank) :=
  SkewMonoidAlgebra (ConstantExtension P r) (Multiplicative ℤ)
noncomputable def skewLaurentMonomialUnit
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    (CartwrightStegerSkewLaurentRing P r)ˣ where
  val := SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
    (c : ConstantExtension P r)
  inv := SkewMonoidAlgebra.single (Multiplicative.ofAdd (-n))
    (Multiplicative.ofAdd (-n) •
      (c⁻¹ : ConstantExtension P r))
  val_inv := by
    rw [SkewMonoidAlgebra.single_mul_single]
    simp
  inv_val := by
    rw [SkewMonoidAlgebra.single_mul_single]
    rw [← smul_mul']
    simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


