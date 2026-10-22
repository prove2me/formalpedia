-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:25:11.869294+00:00
-- url     : https://prove2.me/theorems/97ea5cf2-019e-404e-b77d-77694dae223e
-- title:
--   Contraction identity for insertion-invariant subset families
-- statement:
--   This bundle supplies contraction identity for insertion-invariant subset families. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
--
--   The included constructions and necessary compatibility results are:
--
--   - A nonzero homotopy coefficient forces the erase pattern.
--   - Value of the homotopy coefficient on the erase pattern.
--   - `hc` vanishes when `j ∉ A`.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/hc_inc_sum.lean, selected declarations in lines 20–187; source SHA-256 567a17b5d9273b4adfa25ffc94a99bd5ce72c5d9df4cf10c57641bc2ef8d214d; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
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
/-- A nonzero homotopy coefficient forces the erase pattern. -/
theorem hc_ne_zero_cases {j : V} {A B : Finset V} (h : hc k j A B ≠ 0) :
    j ∈ A ∧ B = A.erase j := by
  by_contra hcon
  rw [hc, if_neg hcon] at h
  exact h rfl

/-- Value of the homotopy coefficient on the erase pattern. -/
theorem hc_erase {j : V} {A : Finset V} (hj : j ∈ A) :
    hc k j A (A.erase j) = (-1 : k) ^ nu (A.erase j) j := by
  rw [hc, if_pos ⟨hj, rfl⟩]

/-- `hc` vanishes when `j ∉ A`. -/
theorem hc_of_notMem {j : V} {A B : Finset V} (hj : j ∉ A) : hc k j A B = 0 := by
  rw [hc, if_neg (fun h => hj h.1)]

theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : k) ^ n) * ((-1 : k) ^ n) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨n, rfl⟩
-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem hc_inc_sum [Fintype V] {𝓕 : Finset V → Prop} [DecidablePred 𝓕] {j : V}
    (hcyl : ∀ J, 𝓕 J ↔ 𝓕 (insert j J)) {J J'' : Finset V} (hJ : 𝓕 J) (hJ'' : 𝓕 J'') :
    ∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
      (hc k j J J' * inc k J' J'' + inc k J J' * hc k j J' J'') = if J = J'' then 1 else 0
-- SWARM:STATEMENT-END
:= by
  rw [Finset.sum_add_distrib]
  by_cases hjJ : j ∈ J
  · -- `j ∈ J`: the first sum survives only at `J' = J.erase j`.
    have hmemE : J.erase j ∈ (Finset.univ : Finset (Finset V)).filter 𝓕 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcyl (J.erase j)).mpr (by rwa [Finset.insert_erase hjJ])
    have hzero1 : ∀ b ∈ (Finset.univ : Finset (Finset V)).filter 𝓕, b ≠ J.erase j →
        hc k j J b * inc k b J'' = 0 := by
      intro b _ hb
      rw [hc, if_neg (by rintro ⟨-, rfl⟩; exact hb rfl), zero_mul]
    have hS1 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
        hc k j J J' * inc k J' J'') = (-1 : k) ^ nu J j * inc k (J.erase j) J'' := by
      rw [Finset.sum_eq_single_of_mem (J.erase j) hmemE hzero1, hc_erase hjJ, nu_erase_self]
    rw [hS1]
    by_cases hex : ∃ a, a ∉ J.erase j ∧ J'' = insert a (J.erase j)
    · obtain ⟨a, ha, hJ''eq⟩ := hex
      rcases eq_or_ne a j with haj | haj
      · -- `J'' = J`: the first sum gives `1`, the second vanishes.
        rw [haj, Finset.insert_erase hjJ] at hJ''eq
        rw [hJ''eq]
        have hinc : inc k (J.erase j) J = (-1 : k) ^ nu J j := by
          have h := inc_insert (k := k) (Finset.notMem_erase j J)
          rwa [Finset.insert_erase hjJ, nu_erase_self] at h
        have hS2 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
            inc k J J' * hc k j J' J) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          by_cases h2 : hc k j b J = 0
          · rw [h2, mul_zero]
          · obtain ⟨-, hbe⟩ := hc_ne_zero_cases h2
            rw [hbe] at hjJ
            exact absurd hjJ (Finset.notMem_erase j b)
        rw [hinc, hS2, add_zero, if_pos rfl, neg_one_pow_mul_self]
      · -- `J'' = insert a (J.erase j)` with `a ∉ J`, `a ≠ j`: the two halves cancel.
        have haJ : a ∉ J := fun hmem => ha (Finset.mem_erase.mpr ⟨haj, hmem⟩)
        subst hJ''eq
        have hincE : inc k (J.erase j) (insert a (J.erase j)) = (-1 : k) ^ nu (J.erase j) a :=
          inc_insert ha
        have haerase : (insert a J).erase j = insert a (J.erase j) :=
          Finset.erase_insert_of_ne haj
        have hjaJ : j ∈ insert a J := Finset.mem_insert_of_mem hjJ
        have hmemA : insert a J ∈ (Finset.univ : Finset (Finset V)).filter 𝓕 := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have h := (hcyl (insert a (J.erase j))).mp hJ''
          rwa [Finset.insert_comm, Finset.insert_erase hjJ] at h
        have hzero2 : ∀ b ∈ (Finset.univ : Finset (Finset V)).filter 𝓕, b ≠ insert a J →
            inc k J b * hc k j b (insert a (J.erase j)) = 0 := by
          intro b _ hb
          by_cases h1 : inc k J b = 0
          · rw [h1, zero_mul]
          by_cases h2 : hc k j b (insert a (J.erase j)) = 0
          · rw [h2, mul_zero]
          obtain ⟨c, hcJ, rfl⟩ := exists_insert_of_inc_ne_zero h1
          obtain ⟨-, hbe⟩ := hc_ne_zero_cases h2
          have hcj : c ≠ j := by rintro rfl; exact hcJ hjJ
          rw [Finset.erase_insert_of_ne hcj] at hbe
          have hac : a = c := by
            have h3 : a ∈ insert c (J.erase j) := by
              rw [← hbe]; exact Finset.mem_insert_self a (J.erase j)
            rcases Finset.mem_insert.mp h3 with h4 | h4
            · exact h4
            · exact absurd h4 ha
          exact absurd (show insert c J = insert a J by rw [hac]) hb
        have hS2 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
            inc k J J' * hc k j J' (insert a (J.erase j)))
            = (-1 : k) ^ nu J a * (-1 : k) ^ nu (insert a (J.erase j)) j := by
          rw [Finset.sum_eq_single_of_mem (insert a J) hmemA hzero2, inc_insert haJ,
            ← haerase, hc_erase hjaJ]
        have hne : J ≠ insert a (J.erase j) := by
          intro h
          apply haJ
          rw [h]
          exact Finset.mem_insert_self a (J.erase j)
        rw [hincE, hS2, if_neg hne]
        rcases lt_or_gt_of_ne haj with hlt | hgt
        · have e1 : nu J a = nu (J.erase j) a := by
            conv_lhs => rw [← Finset.insert_erase hjJ]
            exact nu_insert_of_gt hlt
          have e2 : nu (insert a (J.erase j)) j = nu J j + 1 := by
            rw [nu_insert_of_lt ha hlt, nu_erase_self]
          rw [e1, e2, pow_succ]
          ring
        · have e1 : nu J a = nu (J.erase j) a + 1 := by
            conv_lhs => rw [← Finset.insert_erase hjJ]
            exact nu_insert_of_lt (Finset.notMem_erase j J) hgt
          have e2 : nu (insert a (J.erase j)) j = nu J j := by
            rw [nu_insert_of_gt hgt, nu_erase_self]
          rw [e1, e2, pow_succ]
          ring
    · -- no such `a`: both halves vanish and `J ≠ J''`.
      have h1 : inc k (J.erase j) J'' = 0 := inc_eq_zero hex
      have hne : J ≠ J'' := by
        intro h
        exact hex ⟨j, Finset.notMem_erase j J, by rw [← h, Finset.insert_erase hjJ]⟩
      have hS2 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
          inc k J J' * hc k j J' J'') = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases h2 : inc k J b = 0
        · rw [h2, zero_mul]
        by_cases h3 : hc k j b J'' = 0
        · rw [h3, mul_zero]
        obtain ⟨c, hcJ, rfl⟩ := exists_insert_of_inc_ne_zero h2
        obtain ⟨-, hbe⟩ := hc_ne_zero_cases h3
        have hcj : c ≠ j := by rintro rfl; exact hcJ hjJ
        rw [Finset.erase_insert_of_ne hcj] at hbe
        exact absurd ⟨c, fun hm => hcJ (Finset.mem_of_mem_erase hm), hbe⟩ hex
      rw [h1, hS2, mul_zero, add_zero, if_neg hne]
  · -- `j ∉ J`: the first sum vanishes, the second survives only at `J' = insert j J`.
    have hS1 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
        hc k j J J' * inc k J' J'') = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [hc_of_notMem hjJ, zero_mul]
    have hmemI : insert j J ∈ (Finset.univ : Finset (Finset V)).filter 𝓕 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcyl J).mp hJ
    have hzero2 : ∀ b ∈ (Finset.univ : Finset (Finset V)).filter 𝓕, b ≠ insert j J →
        inc k J b * hc k j b J'' = 0 := by
      intro b _ hb
      by_cases h1 : inc k J b = 0
      · rw [h1, zero_mul]
      by_cases h2 : hc k j b J'' = 0
      · rw [h2, mul_zero]
      obtain ⟨c, hcJ, rfl⟩ := exists_insert_of_inc_ne_zero h1
      obtain ⟨hjb, -⟩ := hc_ne_zero_cases h2
      rcases Finset.mem_insert.mp hjb with h4 | h4
      · exact absurd (show insert c J = insert j J by rw [h4]) hb
      · exact absurd h4 hjJ
    have hS2 : (∑ J' ∈ (Finset.univ : Finset (Finset V)).filter 𝓕,
        inc k J J' * hc k j J' J'') = (-1 : k) ^ nu J j * hc k j (insert j J) J'' := by
      rw [Finset.sum_eq_single_of_mem (insert j J) hmemI hzero2, inc_insert hjJ]
    rw [hS1, hS2, zero_add]
    by_cases hJJ : J = J''
    · subst hJJ
      have hval : hc k j (insert j J) J = (-1 : k) ^ nu J j := by
        have h := hc_erase (k := k) (Finset.mem_insert_self j J)
        rwa [Finset.erase_insert hjJ] at h
      rw [hval, if_pos rfl, neg_one_pow_mul_self]
    · have hnegc : ¬ (j ∈ insert j J ∧ J'' = (insert j J).erase j) := by
        rintro ⟨-, h⟩
        rw [Finset.erase_insert hjJ] at h
        exact hJJ h.symm
      have h0 : hc k j (insert j J) J'' = 0 := by rw [hc, if_neg hnegc]
      rw [h0, mul_zero, if_neg hJJ]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


