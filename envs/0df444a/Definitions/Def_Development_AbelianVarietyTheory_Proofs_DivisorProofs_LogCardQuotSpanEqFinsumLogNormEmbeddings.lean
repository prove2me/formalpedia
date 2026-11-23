-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:39.822969+00:00
-- url     : https://prove2.me/theorems/c54fb60e-bf05-40d9-a94f-ad2c4c80b8e6
-- title:
--   Log Card Quot Span Eq Finsum Log Norm Embeddings
-- statement:
--   Definitions and structural lemmas for Log Card Quot Span Eq Finsum Log Norm Embeddings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardQuotSpanEqFinsumLogNormEmbeddings.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
namespace GlobalTheory
namespace IndexNormEmb
theorem injective_of_ringHom (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (τ : B →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥ := by
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have := Ideal.eq_bot_of_comap_eq_bot h
  have hx' : x ∈ RingHom.ker τ := hx
  rw [this] at hx'
  simpa using hx'
noncomputable def embEquiv (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] :
    (FractionRing B →ₐ[ℚ] ℂ) ≃ (B →+* ℂ) where
  toFun σ := (σ : FractionRing B →+* ℂ).comp (algebraMap B (FractionRing B))
  invFun τ := (IsFractionRing.lift (K := FractionRing B) (injective_of_ringHom B τ)).toRatAlgHom
  left_inv σ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext B⁰
    ext x
    simp
  right_inv τ := by
    ext x
    simp
end IndexNormEmb
end GlobalTheory


