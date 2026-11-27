-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:22:19.018871+00:00
-- url     : https://prove2.me/submissions/4a7447ee-f384-40e7-bd64-fe515e7867cc

import Mathlib
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_normAdj
import Definitions.Def_AbelianCayleyHDX_character
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.L21

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma vec_add_self {n : ℕ} (x : Vec n) : x + x = 0 := by
  ext i; simp [zmod2_add_self]

lemma neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℝ) ^ (a + b).val = (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

lemma character_add_right {n : ℕ} (ξ x y : Vec n) :
    character ξ (x + y) = character ξ x * character ξ y := by
  unfold character
  rw [← neg_one_pow_val_add]
  congr 2
  rw [← Finset.sum_add_distrib]
  congr 1; ext i; simp [mul_add]

lemma character_add_left {n : ℕ} (ξ η x : Vec n) :
    character (ξ + η) x = character ξ x * character η x := by
  unfold character
  rw [← neg_one_pow_val_add]
  congr 2
  rw [← Finset.sum_add_distrib]
  congr 1; ext i; simp [add_mul]

lemma character_sq {n : ℕ} (ξ x : Vec n) : character ξ x * character ξ x = 1 := by
  rw [← character_add_left, vec_add_self]
  simp [character]

lemma zmod2_eq_one (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma sum_character_eq_zero {n : ℕ} (ξ : Vec n) (hξ : ξ ≠ 0) :
    ∑ x : Vec n, character ξ x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push Not at h; exact hξ (funext h)
  have hval : character ξ (Pi.single i 1) = -1 := by
    unfold character
    have : (∑ j, ξ j * (Pi.single i (1 : ZMod 2) : Vec n) j) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp only [Pi.single_eq_same, mul_one]
        exact zmod2_eq_one _ hi
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [this, ZMod.val_one]; norm_num
  have h : ∑ x : Vec n, character ξ (x + Pi.single i 1) = ∑ x : Vec n, character ξ x :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod 2) : Vec n)) _ _ (fun x => rfl)
  have h2 : ∑ x : Vec n, character ξ (x + Pi.single i 1) = - ∑ x : Vec n, character ξ x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [character_add_right, hval]; ring
  linarith

theorem orth {n : ℕ} (ξ η : Vec n) (h : ξ ≠ η) :
    ∑ x : Vec n, character ξ x * character η x = 0 := by
  simp_rw [← character_add_left]
  apply sum_character_eq_zero
  intro h'
  apply h
  have : ξ + η + η = η := by rw [h', zero_add]
  rwa [add_assoc, vec_add_self, add_zero] at this

theorem lin_indep {n : ℕ} : LinearIndependent ℝ (fun ξ : Vec n => character ξ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc η
  have h1 : ∑ x : Vec n, (∑ ξ, c ξ • character ξ) x * character η x = 0 := by
    rw [hc]; simp
  have h2 : ∑ x : Vec n, (∑ ξ, c ξ • character ξ) x * character η x =
      ∑ ξ, c ξ * ∑ x : Vec n, character ξ x * character η x := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [h2, Finset.sum_eq_single η] at h1
  · simp only [character_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    have : (0 : ℝ) < (Fintype.card (Vec n) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · linarith
  · intro ξ _ hξ
    rw [orth ξ η hξ, mul_zero]
  · simp

theorem span_top {n : ℕ} :
    Submodule.span ℝ (Set.range fun ξ : Vec n => character ξ) = ⊤ := by
  apply lin_indep.span_eq_top_of_card_eq_finrank'
  rw [Module.finrank_fintype_fun_eq_card]

theorem normAdj_char {n : ℕ} (S : Finset (Vec n)) (ξ : Vec n) :
    normAdj S (character ξ) = ((1 / (S.card : ℝ)) * ∑ s ∈ S, character ξ s) • character ξ := by
  ext x
  simp only [normAdj, Pi.smul_apply, smul_eq_mul, character_add_right]
  rw [← Finset.mul_sum]
  ring

lemma adj_translate {n : ℕ} (S : Finset (Vec n)) (x a b : Vec n) :
    (cayleyGraph S).Adj a b → (cayleyGraph S).Adj (x + a) (x + b) := by
  rintro ⟨h1, h2⟩
  refine ⟨fun h => h1 (add_left_cancel h), ?_⟩
  have : x + a + (x + b) = a + b := by
    rw [add_add_add_comm, vec_add_self, zero_add]
  rw [this]; exact h2

lemma reach_translate {n : ℕ} (S : Finset (Vec n)) (x a b : Vec n)
    (h : (cayleyGraph S).Reachable a b) : (cayleyGraph S).Reachable (x + a) (x + b) := by
  let f : cayleyGraph S →g cayleyGraph S := ⟨fun z => x + z, fun h => adj_translate S x _ _ h⟩
  exact h.map f

theorem connected_iff {n : ℕ} (S : Finset (Vec n)) (h0 : (0 : Vec n) ∉ S) :
    (cayleyGraph S).Connected ↔ Submodule.span (ZMod 2) (S : Set (Vec n)) = ⊤ := by
  constructor
  · intro hc
    rw [eq_top_iff]
    intro x _
    obtain ⟨w⟩ := hc.preconnected 0 x
    -- induction on the walk: every vertex of a walk from 0 lies in span S
    suffices ∀ (u v : Vec n) (p : (cayleyGraph S).Walk u v),
        u ∈ Submodule.span (ZMod 2) (S : Set (Vec n)) →
        v ∈ Submodule.span (ZMod 2) (S : Set (Vec n)) by
      exact this 0 x w (Submodule.zero_mem _)
    intro u v p
    induction p with
    | nil => exact id
    | @cons a b c hadj p ih =>
      intro hu
      apply ih
      obtain ⟨_, hs⟩ := hadj
      have : b = a + (a + b) := by
        rw [← add_assoc, vec_add_self, zero_add]
      rw [this]
      exact Submodule.add_mem _ hu (Submodule.subset_span hs)
  · intro hspan
    have key : ∀ x : Vec n, (cayleyGraph S).Reachable 0 x := by
      intro x
      have hx : x ∈ Submodule.span (ZMod 2) (S : Set (Vec n)) := by rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem s hs =>
        apply SimpleGraph.Adj.reachable
        refine ⟨fun h => h0 (h ▸ hs), ?_⟩
        simpa using hs
      | zero => exact SimpleGraph.Reachable.refl _
      | add a b _ _ ha hb =>
        have := reach_translate S a 0 b hb
        rw [add_zero] at this
        exact ha.trans this
      | smul c a _ ha =>
        rcases (show c = 0 ∨ c = 1 by fin_cases c; exacts [Or.inl rfl, Or.inr rfl]) with rfl | rfl
        · rw [zero_smul]
        · rw [one_smul]; exact ha
    have : Nonempty (Vec n) := ⟨0⟩
    exact ⟨fun u v => (key u).symm.trans (key v)⟩

end AbelianCayleyHDX.L21

open AbelianCayleyHDX AbelianCayleyHDX.L21 in
theorem solution {n : ℕ} (S : Finset (Vec n)) (_hS : S.Nonempty) (h0 : (0 : Vec n) ∉ S) :
    (∀ ξ η : Vec n, ξ ≠ η → ∑ x : Vec n, character ξ x * character η x = 0) ∧
    LinearIndependent ℝ (fun ξ : Vec n => character ξ) ∧
    Submodule.span ℝ (Set.range fun ξ : Vec n => character ξ) = ⊤ ∧
    (∀ ξ : Vec n, normAdj S (character ξ) =
      ((1 / (S.card : ℝ)) * ∑ s ∈ S, character ξ s) • character ξ) ∧
    ((cayleyGraph S).Connected ↔ Submodule.span (ZMod 2) (S : Set (Vec n)) = ⊤) :=
  ⟨orth, lin_indep, span_top, normAdj_char S, connected_iff S h0⟩
