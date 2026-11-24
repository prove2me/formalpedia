-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:23.992802+00:00
-- url     : https://prove2.me/theorems/fc4d5894-6322-4b3d-87d9-73a686d666fd
-- title:
--   Exists Unit Factorization Bounded
-- statement:
--   Definitions and structural lemmas for Exists Unit Factorization Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/ExistsUnitFactorizationBounded.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Theorems.Thm_UpperTheory_Reformulated_B_Qi27_norm_ringA_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
namespace UnramifiedCompletion
variable (l : ℕ) [hl : Fact l.Prime]
lemma normL_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicComplex.norm_extends' l _
  have h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one
lemma castL_ne_zero : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
variable {l}
lemma norm_ringA_le {x : ℂ_[l]} (hx : x ∈ ringA l) : ‖x‖ ≤ 1 := by
  first | exact UpperTheory.Reformulated.B.Qi27.norm_ringA_le .. | (apply UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi27.norm_ringA_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl x hx | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl x | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l hl | exact @UpperTheory.Reformulated.B.Qi27.norm_ringA_le l
end UnramifiedCompletion
open UnramifiedCompletion
namespace UnramifiedCompletion
variable {l : ℕ} [hl : Fact l.Prime]
lemma norm_ringB_le {x : ℂ_[l]} (hx : x ∈ ringB l) : ‖x‖ ≤ 1 := by
  have h : closure (ringA l : Set ℂ_[l]) ⊆ {x | ‖x‖ ≤ 1} :=
    closure_minimal (fun x hx => norm_ringA_le hx) (isClosed_le continuous_norm continuous_const)
  exact h hx
lemma castL_mem_ringB : (l : ℂ_[l]) ∈ ringB l := natCast_mem _ l
def PerA (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y
def DivB (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y
lemma exists_unit_factorization_bounded (hdiv : DivB l) : ∀ n : ℕ, ∀ x ∈ ringB l, ‖(l : ℂ_[l])‖ ^ n < ‖x‖ →
    ∃ k : ℕ, ∃ u ∈ ringB l, ‖u‖ = 1 ∧ x = (l : ℂ_[l]) ^ k * u := by
  intro n
  induction n with
  | zero =>
    intro x hx h
    rw [pow_zero] at h
    exact absurd (norm_ringB_le hx) (not_le.2 h)
  | succ n ih =>
    intro x hx h
    rcases (norm_ringB_le hx).lt_or_eq with h1 | h1
    · obtain ⟨y, hy, e⟩ := hdiv x hx h1
      have h2 : ‖(l : ℂ_[l])‖ ^ n < ‖y‖ := by
        rw [e, norm_mul, pow_succ, mul_comm] at h
        exact lt_of_mul_lt_mul_left h (norm_nonneg _)
      obtain ⟨k, u, hu, hu1, e2⟩ := ih y hy h2
      exact ⟨k + 1, u, hu, hu1, by rw [e, e2, pow_succ]; ring⟩
    · exact ⟨0, x, hx, h1, by simp⟩
lemma exists_unit (hdiv : DivB l) {x : ℂ_[l]} (hx : x ∈ ringB l) (h0 : x ≠ 0) :
    ∃ k : ℕ, ∃ u ∈ ringB l, ‖u‖ = 1 ∧ x = (l : ℂ_[l]) ^ k * u := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (normL_lt_one l)
  exact exists_unit_factorization_bounded hdiv n x hx hn
def fracS (hdiv : DivB l) (hinv : ∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l) : Subfield ℂ_[l] where
  carrier := {x | ∃ k : ℕ, (l : ℂ_[l]) ^ k * x ∈ ringB l}
  mul_mem' := by
    rintro a b ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have h := mul_mem hj hk
    convert h using 1
    ring
  one_mem' := ⟨0, by simp [one_mem]⟩
  add_mem' := by
    rintro a b ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have h := add_mem (mul_mem (pow_mem castL_mem_ringB k) hj) (mul_mem (pow_mem castL_mem_ringB j) hk)
    convert h using 1
    ring
  zero_mem' := ⟨0, by simp [zero_mem]⟩
  neg_mem' := by
    rintro a ⟨j, hj⟩
    exact ⟨j, by rw [mul_neg]; exact neg_mem hj⟩
  inv_mem' := by
    rintro a ⟨j, hj⟩
    by_cases h0 : a = 0
    · exact ⟨0, by simp [h0, zero_mem]⟩
    obtain ⟨k, u, hu, hu1, e⟩ :=
      exists_unit hdiv hj (mul_ne_zero (pow_ne_zero _ (castL_ne_zero l)) h0)
    have hu0 : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    refine ⟨k, ?_⟩
    have e2 : (l : ℂ_[l]) ^ k * a⁻¹ = (l : ℂ_[l]) ^ j * u⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul₀ h0, mul_assoc, mul_comm u⁻¹ a, ← mul_assoc, e, mul_assoc,
        mul_inv_cancel₀ hu0, mul_one]
    rw [e2]
    exact mul_mem (pow_mem castL_mem_ringB j) (hinv u hu hu1)
end UnramifiedCompletion
end Formalism.L2.Th1.D


