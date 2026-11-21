-- Prove2me | solution 1 for AcycTesting.NearLinear.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:54:11.314676+00:00
-- url     : https://prove2.me/submissions/35b3c426-2bb5-4097-913c-67c39855d764

import Mathlib

/-!
# Maclaurin's inequality for nonnegative reals

For nonnegative reals `z i` and `s ≤ N`:
`e_s(z) / C(N,s) ≤ ((∑ z)/N)^s`
where `e_s(z) = ∑_{|I| = s} ∏_{i ∈ I} z i`.

The proof is the classical induction on the number of variables: split the elementary
symmetric sum according to whether the last variable is used, apply the induction
hypothesis to the remaining variables, and finish with Bernoulli's inequality.
-/

namespace MaclaurinProof

open Finset

/-- Splitting the elementary symmetric sum of order `s+1` along a new variable. -/
private lemma esymm_insert_succ {α : Type*} [DecidableEq α] (a : α) (t : Finset α) (ha : a ∉ t)
    (z : α → ℝ) (s : ℕ) :
    (∑ I ∈ (insert a t).powersetCard (s + 1), ∏ i ∈ I, z i)
      = (∑ I ∈ t.powersetCard (s + 1), ∏ i ∈ I, z i)
        + z a * (∑ I ∈ t.powersetCard s, ∏ i ∈ I, z i) := by
  classical
  have hmem : ∀ k, ∀ I ∈ t.powersetCard k, a ∉ I := by
    intro k I hI h
    exact ha ((Finset.mem_powersetCard.mp hI).1 h)
  have hdisj : Disjoint (t.powersetCard (s + 1)) ((t.powersetCard s).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro I hI1 hI2
    obtain ⟨J, -, rfl⟩ := Finset.mem_image.mp hI2
    exact hmem _ _ hI1 (Finset.mem_insert_self a J)
  have hinj : Set.InjOn (insert a) (↑(t.powersetCard s) : Set (Finset α)) := by
    intro I hI J hJ hIJ
    have hI' : a ∉ I := hmem _ _ hI
    have hJ' : a ∉ J := hmem _ _ hJ
    rw [← Finset.erase_insert hI', hIJ, Finset.erase_insert hJ']
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [Finset.prod_insert (hmem _ _ hI)]

/-- The one-variable inequality at the heart of the induction step. -/
private lemma core (n s : ℕ) (hs : 1 ≤ s) (u x : ℝ) (hu : 0 ≤ u)
    (hx : 0 ≤ x) :
    (((n : ℝ) + 1 - (s : ℝ)) / ((n : ℝ) + 1)) * u ^ s
        + ((s : ℝ) / ((n : ℝ) + 1)) * x * u ^ (s - 1)
      ≤ (((n : ℝ) * u + x) / ((n : ℝ) + 1)) ^ s := by
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlow : -2 * u ≤ (x - u) / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hH : 0 ≤ 2 * u + (x - u) / ((n : ℝ) + 1) := by linarith
  have hbern := pow_add_mul_le_add_pow (a := u) (b := (x - u) / ((n : ℝ) + 1)) hu hH s
  have hbase : u + (x - u) / ((n : ℝ) + 1) = ((n : ℝ) * u + x) / ((n : ℝ) + 1) := by
    field_simp
    ring
  have hpow : u ^ s = u ^ (s - 1) * u := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ]
  have hLHS : u ^ s + (s : ℝ) * u ^ (s - 1) * ((x - u) / ((n : ℝ) + 1))
      = (((n : ℝ) + 1 - (s : ℝ)) / ((n : ℝ) + 1)) * u ^ s
        + ((s : ℝ) / ((n : ℝ) + 1)) * x * u ^ (s - 1) := by
    rw [hpow]
    field_simp
    ring
  rw [← hbase, ← hLHS]
  exact hbern

/-- The induction step, with the binomial coefficients handled via Pascal-type identities. -/
private lemma step_key (n s : ℕ) (u' x u : ℝ) (hs : 1 ≤ s) (hu' : 0 ≤ u') (hx : 0 ≤ x)
    (hux : x + (n : ℝ) * u' = ((n : ℝ) + 1) * u) :
    (n.choose s : ℝ) * u' ^ s + x * ((n.choose (s - 1) : ℝ) * u' ^ (s - 1))
      ≤ ((n + 1).choose s : ℝ) * u ^ s := by
  have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
  by_cases hsn : s ≤ n + 1
  · have hC : (0 : ℝ) < ((n + 1).choose s : ℝ) := by
      exact_mod_cast Nat.choose_pos hsn
    have hsub : ((n + 1 - s : ℕ) : ℝ) = ((n : ℝ) + 1) - (s : ℝ) := by
      rw [Nat.cast_sub hsn]
      push_cast
      ring
    have h1 : (n.choose s : ℝ)
        = ((n + 1).choose s : ℝ) * (((n : ℝ) + 1) - (s : ℝ)) / ((n : ℝ) + 1) := by
      rw [eq_div_iff hden]
      have hnat := Nat.choose_mul_succ_eq n s
      have h := congrArg (fun m : ℕ => (m : ℝ)) hnat
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
      rw [hsub] at h
      linarith
    have h2 : (n.choose (s - 1) : ℝ)
        = ((n + 1).choose s : ℝ) * (s : ℝ) / ((n : ℝ) + 1) := by
      rw [eq_div_iff hden]
      have hnat := Nat.add_one_mul_choose_eq n (s - 1)
      rw [Nat.sub_add_cancel hs] at hnat
      have h := congrArg (fun m : ℕ => (m : ℝ)) hnat
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
      linarith
    have hu_eq : u = ((n : ℝ) * u' + x) / ((n : ℝ) + 1) := by
      field_simp
      linarith
    have hcore := core n s hs u' x hu' hx
    rw [hu_eq, h1, h2]
    calc ((n + 1).choose s : ℝ) * (((n : ℝ) + 1) - (s : ℝ)) / ((n : ℝ) + 1) * u' ^ s
          + x * (((n + 1).choose s : ℝ) * (s : ℝ) / ((n : ℝ) + 1) * u' ^ (s - 1))
        = ((n + 1).choose s : ℝ) * ((((n : ℝ) + 1 - (s : ℝ)) / ((n : ℝ) + 1) * u' ^ s
            + ((s : ℝ) / ((n : ℝ) + 1)) * x * u' ^ (s - 1))) := by ring
      _ ≤ ((n + 1).choose s : ℝ) * ((((n : ℝ) * u' + x) / ((n : ℝ) + 1)) ^ s) :=
          mul_le_mul_of_nonneg_left hcore hC.le
  · have hns : n < s := by omega
    have hns1 : n < s - 1 := by omega
    have hC0 : ((n + 1).choose s : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < s), Nat.cast_zero]
    rw [Nat.choose_eq_zero_of_lt hns, Nat.choose_eq_zero_of_lt hns1, hC0]
    simp

/-- Maclaurin's inequality in "unnormalized" form, by induction on the finite set of
variables. The parameter `u` is the average of `z` over `t`. -/
private lemma esymm_bound {α : Type*} [DecidableEq α] :
    ∀ (t : Finset α) (z : α → ℝ), (∀ i ∈ t, 0 ≤ z i) → ∀ (u : ℝ),
      ∑ i ∈ t, z i = (t.card : ℝ) * u →
      ∀ s : ℕ,
        (∑ I ∈ t.powersetCard s, ∏ i ∈ I, z i) ≤ (t.card.choose s : ℝ) * u ^ s := by
  intro t
  induction t using Finset.induction with
  | empty =>
      intro z hz u hS s
      rcases s with _ | s
      · simp
      · have h0 : (∅ : Finset α).powersetCard (s + 1) = ∅ := by
          rw [Finset.powersetCard_eq_empty]
          simp
        rw [h0]
        simp
  | insert a t ha ih =>
      intro z hz u hS s
      have hz' : ∀ i ∈ t, 0 ≤ z i := fun i hi => hz i (Finset.mem_insert_of_mem hi)
      have hxa : 0 ≤ z a := hz a (Finset.mem_insert_self a t)
      have hS' : z a + ∑ i ∈ t, z i = ((t.card : ℝ) + 1) * u := by
        rw [← Finset.sum_insert ha, hS, Finset.card_insert_of_notMem ha]
        push_cast
        ring
      by_cases hs0 : s = 0
      · subst hs0
        simp
      · have hs1 : 1 ≤ s := by omega
        set u' : ℝ := (∑ i ∈ t, z i) / (t.card : ℝ) with hu'_def
        have hu'_nonneg : 0 ≤ u' :=
          div_nonneg (Finset.sum_nonneg hz') (Nat.cast_nonneg _)
        have hSu' : ∑ i ∈ t, z i = (t.card : ℝ) * u' := by
          rw [hu'_def]
          rcases Nat.eq_zero_or_pos t.card with h0 | h0
          · have ht : t = ∅ := Finset.card_eq_zero.mp h0
            subst ht
            simp
          · have h0' : (t.card : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp h0
            field_simp
        have ih1 := ih z hz' u' hSu' s
        have ih2 := ih z hz' u' hSu' (s - 1)
        have hx2 : z a * (∑ I ∈ t.powersetCard (s - 1), ∏ i ∈ I, z i)
            ≤ z a * ((t.card.choose (s - 1) : ℝ) * u' ^ (s - 1)) :=
          mul_le_mul_of_nonneg_left ih2 hxa
        have hkey : (t.card.choose s : ℝ) * u' ^ s
            + z a * ((t.card.choose (s - 1) : ℝ) * u' ^ (s - 1))
            ≤ ((t.card + 1).choose s : ℝ) * u ^ s := by
          have h := step_key t.card s u' (z a) u hs1 hu'_nonneg hxa (by rw [← hSu']; exact hS')
          simpa using h
        have hrec := esymm_insert_succ a t ha z (s - 1)
        rw [Nat.sub_add_cancel hs1] at hrec
        rw [hrec, Finset.card_insert_of_notMem ha]
        linarith

/-- **Maclaurin's inequality** for nonnegative reals. -/
theorem maclaurin (N s : ℕ) (hs : s ≤ N) (z : Fin N → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s, ∏ i ∈ I, z i) / (N.choose s : ℝ) ≤
      ((1 / (N : ℝ)) * ∑ i, z i) ^ s := by
  classical
  have hz' : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤ z i := fun i _ => hz i
  have hES : ∑ i ∈ (Finset.univ : Finset (Fin N)), z i
      = ((Finset.univ : Finset (Fin N)).card : ℝ) * ((∑ i, z i) / (N : ℝ)) := by
    rw [Finset.card_univ, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp
    · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
      field_simp
  have hbound := esymm_bound (Finset.univ : Finset (Fin N)) z hz'
    ((∑ i, z i) / (N : ℝ)) hES s
  simp only [Finset.card_univ, Fintype.card_fin] at hbound
  have hC : (0 : ℝ) < (N.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hs
  have hmain : (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s, ∏ i ∈ I, z i)
      / (N.choose s : ℝ) ≤ ((∑ i, z i) / (N : ℝ)) ^ s := by
    rw [div_le_iff₀ hC]
    calc (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s, ∏ i ∈ I, z i)
        ≤ (N.choose s : ℝ) * ((∑ i, z i) / (N : ℝ)) ^ s := hbound
      _ = ((∑ i, z i) / (N : ℝ)) ^ s * (N.choose s : ℝ) := by ring
  have hrhs : (1 / (N : ℝ)) * ∑ i, z i = (∑ i, z i) / (N : ℝ) := by ring
  rw [hrhs]
  exact hmain

end MaclaurinProof

/-- **Maclaurin's inequality** for nonnegative reals: for nonnegative `z` and `s ≤ N`,
`e_s(z) / C(N,s) ≤ ((∑ z)/N)^s`. -/
theorem solution (N s : ℕ) (hs : s ≤ N) (z : Fin N → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s, ∏ i ∈ I, z i) / (N.choose s : ℝ) ≤
      ((1 / (N : ℝ)) * ∑ i, z i) ^ s :=
  MaclaurinProof.maclaurin N s hs z hz
