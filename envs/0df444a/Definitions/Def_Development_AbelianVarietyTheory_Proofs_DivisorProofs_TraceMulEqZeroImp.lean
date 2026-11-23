-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMulEqZeroImp
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMulEqZeroImp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:33.63948+00:00
-- url     : https://prove2.me/theorems/4efd3ed5-896c-47f1-ae9f-64f822a83b2c
-- title:
--   Trace Mul Eq Zero Imp
-- statement:
--   Definitions and structural lemmas for Trace Mul Eq Zero Imp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceMulEqZeroImp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TraceMulVanishing
theorem trace_mul_eq_zero_imp {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [IsReduced A] (x : A)
    (h : ∀ z : A, (Algebra.trace F A : A → F) (x * z) = (0 : F)) : x = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one] at hy

  have h1 : x ^ (n + 1) = x ^ (n + 1) * (x * y) := by
    calc x ^ (n + 1) = x * x ^ n := by rw [pow_succ']
      _ = x * (x ^ (n + 1) * y) := by rw [hy]
      _ = x ^ (n + 1) * (x * y) := by ring
  have h2 : ∀ j : ℕ, x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ (x * y) j, ← mul_assoc, ← ih]; exact h1
  have h3 : x ^ (n + 1) = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by
    calc x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ (n + 1) := h2 (n + 1)
      _ = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by rw [mul_pow]; ring
  have he : IsIdempotentElem (x ^ (n + 1) * y ^ (n + 1)) := by
    unfold IsIdempotentElem
    calc x ^ (n + 1) * y ^ (n + 1) * (x ^ (n + 1) * y ^ (n + 1))
        = (x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1)) * y ^ (n + 1) := by ring
      _ = x ^ (n + 1) * y ^ (n + 1) := by rw [← h3]
  have htr : Algebra.trace F A (x ^ (n + 1) * y ^ (n + 1)) = 0 := by
    have := h (x ^ n * y ^ (n + 1))
    rwa [show x * (x ^ n * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) by ring] at this
  have hl : IsIdempotentElem (Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1))) := he.map _
  have hz : Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1)) = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hl).1 (by rw [← Algebra.trace_apply]; exact htr)
  have he0 : x ^ (n + 1) * y ^ (n + 1) = 0 := by
    have := congrArg (fun f : Module.End F A => f 1) hz
    simpa using this
  have hxn : x ^ (n + 1) = 0 := by
    rw [h3, mul_assoc, he0, mul_zero]
  exact IsReduced.eq_zero x ⟨n + 1, hxn⟩
example : ∀ {F A : Type} [inst : Field F] [CharZero F] [inst_2 : CommRing A] [inst_3 : Algebra F A] [Module.Finite F A] [IsReduced A] (x : A), (∀ (z : A), (Algebra.trace F A : A → F) (x * z) = (0 : F)) → x = (0 : A) :=
  @trace_mul_eq_zero_imp
end GlobalTheory.TraceMulVanishing


