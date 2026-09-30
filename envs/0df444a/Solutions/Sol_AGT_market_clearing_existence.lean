-- Prove2me | solution 1 for AGT.market_clearing_existence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:48:08.721981+00:00
-- url     : https://prove2.me/submissions/d4d22e2b-6b05-44ef-8402-d61877f69dab

import Mathlib

set_option autoImplicit false

open Finset Set

namespace MarketClearingProof

variable {A B : Type*} [Fintype A] [Fintype B]

attribute [local instance] Classical.propDecidable

def Feasible (money : B → ℝ) (interest : B → Finset A) (x : B → A → ℝ) : Prop :=
  (∀ j a, 0 ≤ x j a) ∧ (∀ j a, a ∉ interest j → x j a = 0) ∧
    ∀ j, ∑ a, x j a = money j

def total (x : B → A → ℝ) (a : A) : ℝ := ∑ j, x j a

-- Its gradient with respect to each buyer's spending is twice the good's price.
noncomputable def energy (supply : A → ℕ) (x : B → A → ℝ) : ℝ :=
  ∑ a, total x a ^ 2 / (supply a : ℝ)

lemma feasible_compact (money : B → ℝ) (interest : B → Finset A) :
    IsCompact {x : B → A → ℝ | Feasible money interest x} := by
  have hclosed : IsClosed {x : B → A → ℝ | Feasible money interest x} := by
    simp only [Feasible, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_iInter fun j => isClosed_iInter fun a =>
      isClosed_le continuous_const (by fun_prop : Continuous fun x : B → A → ℝ => x j a)).inter ?_
    refine (isClosed_iInter fun j => isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop : Continuous fun x : B → A → ℝ => x j a) continuous_const).inter ?_
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro x hx
  change (fun _ _ => (0 : ℝ)) ≤ x ∧ x ≤ (fun j _ => money j)
  refine ⟨hx.1, ?_⟩
  intro j a
  calc x j a ≤ ∑ a, x j a := single_le_sum (fun a _ => hx.1 j a) (mem_univ a)
    _ = money j := hx.2.2 j

lemma feasible_nonempty (money : B → ℝ) (hmoney : ∀ j, 0 < money j)
    (interest : B → Finset A) (hbuyer : ∀ j, (interest j).Nonempty) :
    {x : B → A → ℝ | Feasible money interest x}.Nonempty := by
  classical
  let chosen (j : B) : A := (hbuyer j).choose
  have hchosen (j : B) : chosen j ∈ interest j := (hbuyer j).choose_spec
  let x : B → A → ℝ := fun j a => if a = chosen j then money j else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro j a
    dsimp [x]
    split
    · exact (hmoney j).le
    · exact le_rfl
  · intro j a ha
    have hne : a ≠ chosen j := fun h => ha (h ▸ hchosen j)
    simp [x, hne]
  · intro j
    simp [x]

lemma exists_minimizer (supply : A → ℕ) (money : B → ℝ)
    (hmoney : ∀ j, 0 < money j) (interest : B → Finset A)
    (hbuyer : ∀ j, (interest j).Nonempty) :
    ∃ x, Feasible money interest x ∧
      ∀ y, Feasible money interest y → energy supply x ≤ energy supply y := by
  have hc : Continuous (energy supply : (B → A → ℝ) → ℝ) := by
    unfold energy total
    fun_prop
  obtain ⟨x, hx, hmin⟩ := (feasible_compact money interest).exists_isMinOn
    (feasible_nonempty money hmoney interest hbuyer) hc.continuousOn
  exact ⟨x, hx, fun y hy => hmin hy⟩

noncomputable def transfer (x : B → A → ℝ) (j : B) (a b : A) (epsilon : ℝ) :
    B → A → ℝ := fun k c =>
  x k c + if k = j then (if c = b then epsilon else 0) -
    (if c = a then epsilon else 0) else 0

lemma transfer_row (x : B → A → ℝ) (j k : B) (a b : A) (epsilon : ℝ) :
    ∑ c, transfer x j a b epsilon k c = ∑ c, x k c := by
  classical
  by_cases h : k = j
  · simp [transfer, h, sum_add_distrib, sum_sub_distrib]
  · simp [transfer, h]

lemma total_transfer (x : B → A → ℝ) (j : B) (a b c : A) (epsilon : ℝ) :
    total (transfer x j a b epsilon) c =
      total x c + (if c = b then epsilon else 0) - (if c = a then epsilon else 0) := by
  classical
  simp [total, transfer, sum_add_distrib, add_sub_assoc]

lemma transfer_feasible (money : B → ℝ) (interest : B → Finset A)
    (x : B → A → ℝ) (hx : Feasible money interest x)
    (j : B) (a b : A) (ha : a ∈ interest j) (hb : b ∈ interest j)
    (hab : a ≠ b) (epsilon : ℝ) (he : 0 ≤ epsilon) (hea : epsilon ≤ x j a) :
    Feasible money interest (transfer x j a b epsilon) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k c
    by_cases hkj : k = j
    · subst k
      by_cases hca : c = a
      · subst c
        simp only [transfer, if_neg hab, eq_self, if_true, zero_sub]
        linarith
      · by_cases hcb : c = b
        · subst c
          simp only [transfer, if_neg hca, eq_self, if_true, sub_zero]
          exact add_nonneg (hx.1 j b) he
        · simpa [transfer, hca, hcb] using hx.1 j c
    · simpa [transfer, hkj] using hx.1 k c
  · intro k c hc
    by_cases hkj : k = j
    · subst k
      have hca : c ≠ a := fun h => hc (h ▸ ha)
      have hcb : c ≠ b := fun h => hc (h ▸ hb)
      simpa [transfer, hca, hcb] using hx.2.1 j c hc
    · simpa [transfer, hkj] using hx.2.1 k c hc
  · intro k
    rw [transfer_row]
    exact hx.2.2 k

lemma energy_transfer (supply : A → ℕ) (x : B → A → ℝ) (j : B)
    (a b : A) (hab : a ≠ b) (epsilon : ℝ) :
    energy supply (transfer x j a b epsilon) = energy supply x +
      2 * epsilon * (total x b / (supply b : ℝ) - total x a / (supply a : ℝ)) +
      epsilon ^ 2 * (1 / (supply a : ℝ) + 1 / (supply b : ℝ)) := by
  classical
  have hterm (c : A) :
      total (transfer x j a b epsilon) c ^ 2 / (supply c : ℝ) =
        total x c ^ 2 / (supply c : ℝ) +
          (if c = a then (-2 * epsilon * total x a + epsilon ^ 2) /
            (supply a : ℝ) else 0) +
          (if c = b then (2 * epsilon * total x b + epsilon ^ 2) /
            (supply b : ℝ) else 0) := by
    rw [total_transfer]
    by_cases hca : c = a
    · subst c
      simp only [if_neg hab, eq_self, if_true, add_zero]
      ring
    · by_cases hcb : c = b
      · subst c
        simp only [if_neg hca, eq_self, if_true, sub_zero, add_zero]
        ring
      · simp [hca, hcb]
  unfold energy
  simp_rw [hterm]
  simp only [sum_add_distrib, sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma minimizer_cheapest (supply : A → ℕ) (hsupply : ∀ a, 0 < supply a)
    (money : B → ℝ) (interest : B → Finset A) (x : B → A → ℝ)
    (hx : Feasible money interest x)
    (hmin : ∀ y, Feasible money interest y → energy supply x ≤ energy supply y)
    (j : B) (a b : A) (hxa : 0 < x j a) (hb : b ∈ interest j) :
    total x a / (supply a : ℝ) ≤ total x b / (supply b : ℝ) := by
  classical
  have hs (c : A) : 0 < (supply c : ℝ) := by exact_mod_cast hsupply c
  have ha : a ∈ interest j := by
    by_contra h
    exact (ne_of_gt hxa) (hx.2.1 j a h)
  by_contra h
  have hgap : 0 < total x a / (supply a : ℝ) - total x b / (supply b : ℝ) :=
    sub_pos.mpr (lt_of_not_ge h)
  have hab : a ≠ b := by
    intro h'
    subst b
    simp at hgap
  let q : ℝ := 1 / (supply a : ℝ) + 1 / (supply b : ℝ)
  have hq : 0 < q := add_pos (one_div_pos.mpr (hs a)) (one_div_pos.mpr (hs b))
  -- This transfer is feasible and makes the quadratic term smaller than the linear gain.
  let epsilon : ℝ := min (x j a)
    ((total x a / (supply a : ℝ) - total x b / (supply b : ℝ)) / q)
  have he : 0 < epsilon := lt_min hxa (div_pos hgap hq)
  have hea : epsilon ≤ x j a := min_le_left _ _
  have heq : epsilon * q ≤ total x a / (supply a : ℝ) - total x b / (supply b : ℝ) :=
    (le_div_iff₀ hq).mp (min_le_right _ _)
  have hbound := mul_le_mul_of_nonneg_left heq he.le
  have hstrict := mul_pos he hgap
  have henergy := hmin (transfer x j a b epsilon)
    (transfer_feasible money interest x hx j a b ha hb hab epsilon he.le hea)
  rw [energy_transfer supply x j a b hab epsilon] at henergy
  change energy supply x ≤ energy supply x +
    2 * epsilon * (total x b / (supply b : ℝ) - total x a / (supply a : ℝ)) +
    epsilon ^ 2 * q at henergy
  nlinarith

end MarketClearingProof

theorem solution {A B : Type*} [Fintype A] [Fintype B]
    (supply : A → ℕ) (hsupply : ∀ a, 0 < supply a)
    (money : B → ℝ) (hmoney : ∀ j, 0 < money j)
    (interest : B → Finset A) (hbuyer : ∀ j, (interest j).Nonempty)
    (hgood : ∀ a : A, ∃ j : B, a ∈ interest j) :
    ∃ (price : A → ℝ) (spend : B → A → ℝ),
      (∀ a, 0 < price a) ∧
      (∀ j a, 0 ≤ spend j a) ∧
      (∀ j a, spend j a ≠ 0 →
        a ∈ interest j ∧ ∀ b ∈ interest j, price a ≤ price b) ∧
      (∀ j, ∑ a, spend j a = money j) ∧
      (∀ a, ∑ j, spend j a = price a * (supply a : ℝ)) := by
  classical
  obtain ⟨x, hx, hmin⟩ := MarketClearingProof.exists_minimizer supply money hmoney
    interest hbuyer
  let price : A → ℝ := fun a => MarketClearingProof.total x a / (supply a : ℝ)
  have hs (a : A) : 0 < (supply a : ℝ) := by exact_mod_cast hsupply a
  have hcheapest (j : B) (a b : A) (hxa : 0 < x j a) (hb : b ∈ interest j) :
      price a ≤ price b :=
    MarketClearingProof.minimizer_cheapest supply hsupply money interest x hx hmin
      j a b hxa hb
  have hpositive (a : A) : 0 < price a := by
    obtain ⟨j, hja⟩ := hgood a
    have hex : ∃ b, 0 < x j b := by
      by_contra h
      have hn (b : A) : x j b ≤ 0 := le_of_not_gt (fun hb => h ⟨b, hb⟩)
      have hsum : ∑ b, x j b ≤ 0 := sum_nonpos (fun b _ => hn b)
      rw [hx.2.2 j] at hsum
      exact (not_le_of_gt (hmoney j)) hsum
    obtain ⟨b, hxb⟩ := hex
    have htotal : 0 < MarketClearingProof.total x b :=
      hxb.trans_le (single_le_sum (fun k _ => hx.1 k b) (Finset.mem_univ j))
    exact (div_pos htotal (hs b)).trans_le (hcheapest j b a hxb hja)
  refine ⟨price, x, hpositive, hx.1, ?_, hx.2.2, ?_⟩
  · intro j a hne
    have ha : a ∈ interest j := by
      by_contra h
      exact hne (hx.2.1 j a h)
    refine ⟨ha, fun b hb => hcheapest j a b ?_ hb⟩
    exact lt_of_le_of_ne (hx.1 j a) (Ne.symm hne)
  · intro a
    exact (div_mul_cancel₀ (MarketClearingProof.total x a) (ne_of_gt (hs a))).symm

#print axioms solution
