-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AssociatedOfHeightOneAgree
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AssociatedOfHeightOneAgree
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:12.178972+00:00
-- url     : https://prove2.me/theorems/4db57526-423e-4c19-8dee-88e1e2f15c1c
-- title:
--   Associated Of Height One Agree
-- statement:
--   Definitions and structural lemmas for Associated Of Height One Agree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AssociatedOfHeightOneAgree.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_dvd_of_forall_height_eq_one
import Theorems.Thm_GlobalTheory_mem_minimalPrimes_span_singleton_of_height_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
theorem exists_unit_eq_mul_of_height_one_avoiding (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (hdiv : ∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) :
    ∃ u : Rˣ, a = u * b := by

  have avoid : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∀ x : R, x ≠ 0 → x ∈ Q →
      (∀ j ∈ J, Prime (π j) → ¬ π j ∣ x) → ∀ j ∈ J, π j ∉ Q := by
    intro Q hQ h1 x hx hxQ hnd j hj hjQ
    rcases hπ j hj with hu | hp
    · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hjQ hu)
    · have hmin := mem_minimalPrimes_span_singleton_of_height_eq_one h1 hp.ne_zero hjQ
      have hsp : (Ideal.span {π j}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hle : Q ≤ Ideal.span {π j} :=
        hmin.2 ⟨hsp, le_refl _⟩ ((Ideal.span_singleton_le_iff_mem Q).mpr hjQ)
      exact hnd j hj hp (Ideal.mem_span_singleton.mp (hle hxQ))
  have hba : b ∣ a := dvd_of_forall_height_eq_one hb fun Q _ h1 hbQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 b hb hbQ fun j hj hp => (hdiv j hj hp).2)
    exact ⟨d, hd, c, by rw [mul_comm d a, e]⟩
  have hab : a ∣ b := dvd_of_forall_height_eq_one ha fun Q _ h1 haQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 a ha haQ fun j hj hp => (hdiv j hj hp).1)
    exact ⟨c, hc, d, by rw [mul_comm c b, ← e]⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hba hab
  exact ⟨u, by rw [← hu, mul_comm]⟩
example : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 →
    (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) →
    (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b :=
  @exists_unit_eq_mul_of_height_one_avoiding
end GlobalTheory


