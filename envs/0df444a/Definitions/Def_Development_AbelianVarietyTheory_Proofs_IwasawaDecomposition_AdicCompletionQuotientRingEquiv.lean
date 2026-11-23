-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:03.103884+00:00
-- url     : https://prove2.me/theorems/186367e3-0c16-4c63-b8dd-c4a166f3db12
-- title:
--   Adic Completion Quotient Ring Equiv
-- statement:
--   Definitions and structural lemmas for Adic Completion Quotient Ring Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)
theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (Ideal.Quotient.mk q)) ^ n).comap (Ideal.Quotient.mk q) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map
noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* (A ⧸ q) ⧸ (J.map (Ideal.Quotient.mk q)) ^ n :=
  (Ideal.quotientMap _ (Ideal.Quotient.mk q) (pow_le_comap J q n)).comp (evalₐ J n).toRingHom
theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (Ideal.Quotient.mk q (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]
theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev J q n) = lev J q m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap J q m h3)
noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
  AdicCompletion.liftRingHom _ (lev J q) (fun hle ↦ lev_compat J q hle)
end GlobalTheory.AdicQuot


