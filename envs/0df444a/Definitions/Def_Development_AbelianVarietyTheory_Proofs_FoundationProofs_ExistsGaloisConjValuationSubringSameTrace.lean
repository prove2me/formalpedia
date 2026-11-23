-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:35.484808+00:00
-- url     : https://prove2.me/theorems/be9d83aa-7003-4c0f-a80d-65838cbd716a
-- title:
--   Exists Galois Conj Valuation Subring Same Trace
-- statement:
--   Definitions and structural lemmas for Exists Galois Conj Valuation Subring Same Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsGaloisConjValuationSubringSameTrace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DiagMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
noncomputable section
namespace GlobalTheory.ValConj
open Finset
open scoped Pointwise
section tails
variable {L : Type} [Field L]
end tails
variable {F L : Type} [Field F] [Field L] [Algebra F L]
def core (F : Type) [Field F] [Algebra F L] (W₁ W₂ : ValuationSubring L) : Subring L where
  carrier := {x | ∀ σ : L ≃ₐ[F] L, σ x ∈ W₁ ∧ σ x ∈ W₂}
  mul_mem' ha hb σ := by
    rw [map_mul]; exact ⟨mul_mem (ha σ).1 (hb σ).1, mul_mem (ha σ).2 (hb σ).2⟩
  one_mem' σ := by rw [map_one]; exact ⟨one_mem _, one_mem _⟩
  add_mem' ha hb σ := by
    rw [map_add]; exact ⟨add_mem (ha σ).1 (hb σ).1, add_mem (ha σ).2 (hb σ).2⟩
  zero_mem' σ := by rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
  neg_mem' ha σ := by rw [map_neg]; exact ⟨neg_mem (ha σ).1, neg_mem (ha σ).2⟩
instance (W₁ W₂ : ValuationSubring L) : IsInvariantSubring (L ≃ₐ[F] L) (core F W₁ W₂) where
  smul_mem τ _ hx σ := hx (σ * τ)
def centre (S : Subring L) (W : ValuationSubring L) (h : S ≤ W.toSubring) : Ideal S :=
  (IsLocalRing.maximalIdeal W).comap (Subring.inclusion h)
instance (S : Subring L) (W : ValuationSubring L) (h : S ≤ W.toSubring) : (centre S W h).IsPrime :=
  Ideal.comap_isPrime _ _
end GlobalTheory.ValConj


