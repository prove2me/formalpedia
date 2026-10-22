-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:27:06.588546+00:00
-- url     : https://prove2.me/theorems/90fe3a64-951c-4a61-8090-78df6ea7d758
-- title:
--   Two-step incidence cancellation on convex families
-- statement:
--   This bundle supplies two-step incidence cancellation on convex families. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/inc_inc_sum.lean, selected declarations in lines 24–91; source SHA-256 cccda3855f8699ef45c55eb519bf2d90ac2c83c03dfe6a0a847e9f8cb94884c8; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem inc_inc_sum [Fintype V] {𝓕 : Finset V → Prop} [DecidablePred 𝓕] (hconv : IsConvex 𝓕)
    {J J'' : Finset V} (hJ : 𝓕 J) (hJ'' : 𝓕 J'') :
    ∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕, inc k J J' * inc k J' J'' = 0
-- SWARM:STATEMENT-END
:= by
  by_cases hcase : ∃ a b : V, a ≠ b ∧ a ∉ J ∧ b ∉ J ∧ J'' = insert a (insert b J)
  · obtain ⟨a, b, hab, haJ, hbJ, rfl⟩ := hcase
    have hanb : a ∉ insert b J := fun h => by
      rcases Finset.mem_insert.mp h with h1 | h1
      · exact hab h1
      · exact haJ h1
    have hbna : b ∉ insert a J := fun h => by
      rcases Finset.mem_insert.mp h with h1 | h1
      · exact hab h1.symm
      · exact hbJ h1
    have hmemA : insert a J ∈ (Finset.univ : Finset (Finset V)).filter 𝓕 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hconv hJ hJ'' (Finset.subset_insert a J)
        (Finset.insert_subset_insert a (Finset.subset_insert b J))
    have hmemB : insert b J ∈ (Finset.univ : Finset (Finset V)).filter 𝓕 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hconv hJ hJ'' (Finset.subset_insert b J) (Finset.subset_insert a _)
    have hne : insert a J ≠ insert b J := fun h => by
      have hm : a ∈ insert b J := h ▸ Finset.mem_insert_self a J
      rcases Finset.mem_insert.mp hm with h1 | h1
      · exact hab h1
      · exact haJ h1
    have hrest : ∀ c ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
        c ≠ insert a J ∧ c ≠ insert b J →
        inc k J c * inc k c (insert a (insert b J)) = 0 := by
      intro c _ hc
      by_cases h1 : inc k J c = 0
      · rw [h1, zero_mul]
      by_cases h2 : inc k c (insert a (insert b J)) = 0
      · rw [h2, mul_zero]
      obtain ⟨j, hjJ, rfl⟩ := exists_insert_of_inc_ne_zero h1
      obtain ⟨i, hi, heq⟩ := exists_insert_of_inc_ne_zero h2
      have hjmem : j ∈ insert a (insert b J) := by
        rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self j J)
      rcases Finset.mem_insert.mp hjmem with hja | hj2
      · exact absurd (by rw [hja] : insert j J = insert a J) hc.1
      · rcases Finset.mem_insert.mp hj2 with hjb | hj3
        · exact absurd (by rw [hjb] : insert j J = insert b J) hc.2
        · exact absurd hj3 hjJ
    rw [Finset.sum_eq_add_of_mem (f := fun J' => inc k J J' * inc k J' (insert a (insert b J)))
      (insert a J) (insert b J) hmemA hmemB hne hrest]
    have e1 : inc k J (insert a J) = (-1 : k) ^ nu J a := inc_insert haJ
    have e2 : inc k (insert a J) (insert a (insert b J)) = (-1 : k) ^ nu (insert a J) b := by
      rw [Finset.insert_comm]; exact inc_insert hbna
    have e3 : inc k J (insert b J) = (-1 : k) ^ nu J b := inc_insert hbJ
    have e4 : inc k (insert b J) (insert a (insert b J)) = (-1 : k) ^ nu (insert b J) a :=
      inc_insert hanb
    rw [e1, e2, e3, e4]
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [nu_insert_of_lt haJ hlt, nu_insert_of_gt hlt, pow_succ]; ring
    · exact absurd heq hab
    · rw [nu_insert_of_gt hgt, nu_insert_of_lt hbJ hgt, pow_succ]; ring
  · apply Finset.sum_eq_zero
    intro c _
    by_cases h1 : inc k J c = 0
    · rw [h1, zero_mul]
    by_cases h2 : inc k c J'' = 0
    · rw [h2, mul_zero]
    obtain ⟨j, hjJ, rfl⟩ := exists_insert_of_inc_ne_zero h1
    obtain ⟨i, hi, heq⟩ := exists_insert_of_inc_ne_zero h2
    have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self j J)
    have hiJ : i ∉ J := fun h => hi (Finset.mem_insert_of_mem h)
    exact absurd ⟨i, j, hij, hiJ, hjJ, heq⟩ hcase
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


