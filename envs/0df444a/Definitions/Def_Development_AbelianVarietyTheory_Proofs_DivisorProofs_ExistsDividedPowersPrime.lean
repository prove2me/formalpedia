-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:13.932087+00:00
-- url     : https://prove2.me/theorems/8ade86d7-64bc-4196-a297-ba2cef1ccd61
-- title:
--   Exists Divided Powers Prime
-- statement:
--   Definitions and structural lemmas for Exists Divided Powers Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
namespace GlobalTheory.TorsionFreeDividedPowers
open DividedPowers
def natPosSubmonoid (R : Type) [CommRing R] : Submonoid R where
  carrier := {r | ∃ k : ℕ, k ≠ 0 ∧ (k : R) = r}
  one_mem' := ⟨1, one_ne_zero, Nat.cast_one⟩
  mul_mem' := by
    rintro a b ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨j * k, Nat.mul_ne_zero hj hk, by push_cast; ring⟩
noncomputable def ofFactorialUnits {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) : DividedPowers J where
  dpow           := OfInvertibleFactorial.dpow J
  dpow_null hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt (h _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt (h _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt (h _) hk (lt_add_one _) hx
end GlobalTheory.TorsionFreeDividedPowers


