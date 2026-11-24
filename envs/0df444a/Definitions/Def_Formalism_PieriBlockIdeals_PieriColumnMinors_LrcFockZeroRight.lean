-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:53.507009+00:00
-- url     : https://prove2.me/theorems/996328ef-3aae-4b10-9ebf-07ae8592539e
-- title:
--   Lrc Fock Zero Right
-- statement:
--   Definitions and structural lemmas for Lrc Fock Zero Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
def Zl (l : ℕ) : Subring ℚ where
  carrier := {x | x.den.Coprime l}
  mul_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha
theorem mem_Zl (l : ℕ) (x : ℚ) : x ∈ Zl l ↔ x.den.Coprime l := Iff.rfl
theorem lrc_int_mem (l : ℕ) (z : ℤ) : (z : ℚ) ∈ Zl l := by
  rw [mem_Zl]; simp
theorem lrc_coprime_iff {l : ℕ} (hl : l.Prime) (m : ℕ) : m.Coprime l ↔ ¬ (l : ℤ) ∣ (m : ℤ) := by
  rw [Int.natCast_dvd_natCast, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
theorem lrc_inv_mem {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : ((m : ℚ)⁻¹) ∈ Zl l := by
  rw [mem_Zl]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero _)
  have h : ((m : ℚ)⁻¹).den = m.natAbs := by
    rw [Rat.inv_intCast_den, if_neg hm0]
  rw [h, lrc_coprime_iff hl, Int.dvd_natAbs]
  exact hm
theorem zl_mem_iff {l : ℕ} (hl : l.Prime) (x : ℚ) :
    x ∈ Zl l ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ z : ℤ, (m : ℚ) * x = z := by
  constructor
  · intro hx
    refine ⟨(x.den : ℤ), (lrc_coprime_iff hl _).1 hx, x.num, ?_⟩
    have := Rat.den_mul_eq_num x
    exact_mod_cast this
  · rintro ⟨m, hm, z, hz⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      intro h
      have : m = 0 := by exact_mod_cast h
      subst this
      exact hm (dvd_zero _)
    have : x = (m : ℚ)⁻¹ * (z : ℚ) := by
      rw [← hz, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    rw [this]
    exact (Zl l).mul_mem (lrc_inv_mem hl m hm) (lrc_int_mem l z)
example (l : ℕ) (V : Type) [AddCommGroup V] [Module ℚ V] : IsScalarTower (Zl l) ℚ V := inferInstance
example (l : ℕ) : Algebra (Zl l) ℚ := inferInstance
theorem lrc_smul_def (l : ℕ) {V : Type*} [AddCommGroup V] [Module ℚ V] (c : Zl l) (v : V) :
    c • v = (c : ℚ) • v := rfl
def locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) :
    Submodule (Zl l) V where
  carrier := {v | ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M}
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨m', hm', hb⟩
    refine ⟨m * m', fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm h
      · exact hm' h
    · rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact M.zsmul_mem ha _
      · rw [mul_smul]
        exact M.zsmul_mem hb _
  zero_mem' := ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simp⟩
  smul_mem' := by
    rintro c v ⟨m, hm, hv⟩
    obtain ⟨m', hm', z, hz⟩ := (zl_mem_iff hl (c : ℚ)).1 c.2
    refine ⟨m' * m, fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm' h
      · exact hm h
    · have : (m' * m) • (c • v) = z • (m • v) := by
        rw [lrc_smul_def, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ z, ← Int.cast_smul_eq_zsmul ℚ m,
          smul_smul, smul_smul, ← hz]
        congr 1
        push_cast
        ring
      rw [this]
      exact M.zsmul_mem hv _
end Formalism.CohomologicalDescent.LR


