-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProjectiveCharts
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProjectiveCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:31.868989+00:00
-- url     : https://prove2.me/theorems/3575223a-3a72-48eb-a130-d1ce8448f996
-- title:
--   Projective Charts
-- statement:
--   Definitions and structural lemmas for Projective Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ProjectiveCharts.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal :
    {B : Type} → [inst : CommRing B] → {n : ℕ} → Ideal (MvPolynomial (Fin n) B) → Prop :=
    fun {B : Type} [CommRing B] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) B)) ↦
      ∀ (d : ℕ), ∀ f ∈ P, (MvPolynomial.homogeneousComponent d : MvPolynomial (Fin n) B → MvPolynomial (Fin n) B) f ∈ P
noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.V0 :
    {B : Type} →
      [inst : CommRing B] →
        {M : ℕ} → Finset (Fin M) → Ideal (MvPolynomial (Fin M) B) → Ideal (MvPolynomial (Fin M) B) → ℕ → Prop :=
    fun {B : Type} [CommRing B] {M : ℕ} (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) ↦
      ∀ (n : ℕ), n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ (m : ℕ), MvPolynomial.X i ^ m * f ∈ Q) → f ∈ Q
noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.V1 :
    {B : Type} →
      [inst : CommRing B] →
        {M : ℕ} → Finset (Fin M) → Ideal (MvPolynomial (Fin M) B) → Ideal (MvPolynomial (Fin M) B) → ℕ → Prop :=
    fun {B : Type} [CommRing B] {M : ℕ} (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) ↦
      ∀ (n : ℕ),
        n₀ ≤ n →
          ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
            (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
              (∀ i ∈ W,
                  ∀ j ∈ W,
                    ∃ (m : ℕ),
                      (MvPolynomial.X i * MvPolynomial.X j) ^ m *
                          (MvPolynomial.X j ^ k * f i - MvPolynomial.X i ^ k * f j) ∈
                        Q) →
                ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ (m : ℕ), MvPolynomial.X i ^ m * (MvPolynomial.X i ^ k * g - f i) ∈ Q
section Helpers
open MvPolynomial
variable {B : Type} [CommRing B] {M : ℕ}
theorem pow_mul_mem {R : Type} [CommRing R] {Q : Ideal R} {r f : R} {m k : ℕ}
    (hmk : m ≤ k) (h : r ^ m * f ∈ Q) : r ^ k * f ∈ Q := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hmk
  have : r ^ (m + c) * f = r ^ c * (r ^ m * f) := by ring
  rw [this]
  exact Q.mul_mem_left _ h
def sat {R : Type} [CommRing R] (P Q : Ideal R) (x : R) : Ideal R where
  carrier := {f | f ∈ P ∧ ∃ m : ℕ, x ^ m * f ∈ Q}
  zero_mem' := ⟨P.zero_mem, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, l, hl⟩
    refine ⟨P.add_mem ha hb, m + l, ?_⟩
    rw [mul_add]
    exact Q.add_mem (pow_mul_mem (by omega) hm) (pow_mul_mem (by omega) hl)
  smul_mem' := by
    rintro c a ⟨ha, m, hm⟩
    refine ⟨P.mul_mem_left _ ha, m, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Q.mul_mem_left _ hm
def plus {R : Type} [CommRing R] (P Q : Ideal R) (x : R) : Ideal R where
  carrier := {g | ∃ q ∈ Q, ∃ h ∈ P, g = q + x * h}
  zero_mem' := ⟨0, Q.zero_mem, 0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨q, hq, h, hh, rfl⟩ ⟨q', hq', h', hh', rfl⟩
    exact ⟨q + q', Q.add_mem hq hq', h + h', P.add_mem hh hh', by ring⟩
  smul_mem' := by
    rintro c _ ⟨q, hq, h, hh, rfl⟩
    exact ⟨c * q, Q.mul_mem_left _ hq, c * h, P.mul_mem_left _ hh, by rw [smul_eq_mul]; ring⟩
end Helpers


