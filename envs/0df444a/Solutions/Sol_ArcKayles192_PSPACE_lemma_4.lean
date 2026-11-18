-- Prove2me | solution 1 for ArcKayles192.PSPACE.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:10:18.626504+00:00
-- url     : https://prove2.me/submissions/b64eb126-2dd8-47aa-adca-b1041adc6f2d

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

open ArcKayles192.PSPACE

namespace AK4

variable {V : Type*} [DecidableEq V]

lemma sg_eq (G : SimpleGraph V) (S : Finset V) :
    sg G S = mex {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x} := by
  rw [sg]

lemma opt_finite (G : SimpleGraph V) (S : Finset V) :
    {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}.Finite := by
  apply Set.Finite.subset ((S ×ˢ S).finite_toSet.image (fun p : V × V => sg G (S \ {p.1, p.2})))
  rintro x ⟨u, v, ⟨hu, hv, _⟩, rfl⟩
  exact ⟨(u, v), by simp [hu, hv], rfl⟩

/-- mex characterisation of sg -/
lemma sg_char (G : SimpleGraph V) (S : Finset V) :
    (∀ i < sg G S, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i) ∧
    (∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ sg G S) := by
  have hne : ({x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ).Nonempty :=
    (opt_finite G S).infinite_compl.nonempty
  have hmex : sg G S = sInf {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
    rw [sg_eq]; rfl
  constructor
  · intro i hi
    rw [hmex] at hi
    by_contra hcon
    have hmem : i ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      intro ⟨u, v, ⟨hu, hv, ha⟩, h⟩
      exact hcon ⟨u, v, hu, hv, ha, h⟩
    exact absurd (Nat.sInf_le hmem) (by omega)
  · intro u v hu hv ha h
    have hmem : sg G S ∈ {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}ᶜ := by
      rw [hmex]; exact Nat.sInf_mem hne
    exact hmem ⟨u, v, ⟨hu, hv, ha⟩, h⟩

/-- value characterisation: if x is not an option value and every smaller value is, then sg = x -/
lemma sg_eq_of (G : SimpleGraph V) (S : Finset V) (x : ℕ)
    (h1 : ∀ i < x, ∃ u v, u ∈ S ∧ v ∈ S ∧ G.Adj u v ∧ sg G (S \ {u, v}) = i)
    (h2 : ∀ u v, u ∈ S → v ∈ S → G.Adj u v → sg G (S \ {u, v}) ≠ x) : sg G S = x := by
  obtain ⟨c1, c2⟩ := sg_char G S
  rcases lt_trichotomy (sg G S) x with h | h | h
  · obtain ⟨u, v, hu, hv, ha, he⟩ := h1 _ h
    exact absurd he (c2 u v hu hv ha)
  · exact h
  · obtain ⟨u, v, hu, hv, ha, he⟩ := c1 _ h
    exact absurd he (h2 u v hu hv ha)

def XF {h : ℕ} (xs : Fin h → ℕ) : ℕ := (List.ofFn xs).foldr (· ^^^ ·) 0

lemma XF_zero (xs : Fin 0 → ℕ) : XF xs = 0 := by simp [XF]

lemma XF_succ {h : ℕ} (xs : Fin (h + 1) → ℕ) : XF xs = xs 0 ^^^ XF (fun j : Fin h => xs j.succ) := by
  simp [XF, List.ofFn_succ]

lemma XF_update {h : ℕ} (xs : Fin h → ℕ) (i : Fin h) (b : ℕ) :
    XF (Function.update xs i b) = XF xs ^^^ xs i ^^^ b := by
  induction h with
  | zero => exact i.elim0
  | succ h ih =>
    rw [XF_succ, XF_succ]
    cases i using Fin.cases with
    | zero =>
      simp only [Function.update_self]
      have : (fun j : Fin h => Function.update xs 0 b j.succ) = fun j => xs j.succ := by
        funext j; simp [Function.update_of_ne (Fin.succ_ne_zero j)]
      rw [this]
      generalize XF (fun j : Fin h => xs j.succ) = R
      generalize xs 0 = a
      rw [Nat.xor_comm a R, Nat.xor_assoc R a a, Nat.xor_self, Nat.xor_zero, Nat.xor_comm]
    | succ j =>
      have h0 : Function.update xs j.succ b 0 = xs 0 := Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
      have h1 : (fun k : Fin h => Function.update xs j.succ b k.succ) =
          Function.update (fun k : Fin h => xs k.succ) j b := by
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · rw [Function.update_of_ne (fun e => hk (Fin.succ_injective _ e)), Function.update_of_ne hk]
      rw [h0, h1, ih]
      simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

lemma nim_exists {h : ℕ} (xs : Fin h → ℕ) (y : ℕ) (hy : y < XF xs) :
    ∃ i, (y ^^^ XF xs ^^^ xs i) < xs i := by
  induction h generalizing y with
  | zero => simp [XF_zero] at hy
  | succ h ih =>
    rw [XF_succ] at hy
    rcases Nat.lt_xor_cases hy with h1 | h1
    · refine ⟨0, ?_⟩
      rw [XF_succ]
      have : y ^^^ (xs 0 ^^^ XF fun j : Fin h => xs j.succ) ^^^ xs 0 = y ^^^ XF fun j : Fin h => xs j.succ := by
        simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
      rw [this]; exact h1
    · obtain ⟨j, hj⟩ := ih (fun j => xs j.succ) (y ^^^ xs 0) h1
      refine ⟨j.succ, ?_⟩
      rw [XF_succ]
      have : y ^^^ (xs 0 ^^^ XF fun j : Fin h => xs j.succ) ^^^ xs j.succ =
          (y ^^^ xs 0) ^^^ XF (fun j : Fin h => xs j.succ) ^^^ xs j.succ := by
        simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
      rw [this]; exact hj


lemma xor_aux (a b c : ℕ) : a ^^^ b ^^^ (c ^^^ a ^^^ b) = c := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> cases c.testBit k <;> rfl

lemma xor_ne (X a t : ℕ) (hne : t ≠ a) : X ^^^ a ^^^ t ≠ X := by
  intro h
  apply hne
  apply Nat.eq_of_testBit_eq; intro k
  have := congrArg (fun z => Nat.testBit z k) h
  simp only [Nat.testBit_xor] at this
  cases hX : X.testBit k <;> cases ha : a.testBit k <;> cases ht : t.testBit k <;>
    simp_all

lemma sigma_erase {h : ℕ} {W : Fin h → Type*} [∀ i, DecidableEq (W i)]
    (S : ∀ i, Finset (W i)) (i : Fin h) (x y : W i) :
    (Finset.univ.sigma S \ {⟨i, x⟩, ⟨i, y⟩} : Finset (Σ k, W k)) =
      Finset.univ.sigma (Function.update S i (S i \ {x, y})) := by
  ext ⟨k, z⟩
  simp only [Finset.mem_sdiff, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Sigma.mk.inj_iff]
  by_cases hk : k = i
  · subst hk
    simp [Function.update_self]
  · simp [Function.update_of_ne hk, hk]

theorem sum_theorem (h : ℕ) {W : Fin h → Type*} [∀ i, DecidableEq (W i)]
    (G : ∀ i, SimpleGraph (W i)) (S : ∀ i, Finset (W i)) :
    sg (sigmaGraph G) (Finset.univ.sigma S) = XF (fun i => sg (G i) (S i)) := by
  induction' hN : (Finset.univ.sigma S).card using Nat.strong_induction_on with N ih generalizing S
  have mv : ∀ (i : Fin h) (x y : W i), x ∈ S i → y ∈ S i →
      sg (sigmaGraph G) (Finset.univ.sigma S \ {⟨i, x⟩, ⟨i, y⟩}) =
        XF (fun k => sg (G k) (S k)) ^^^ sg (G i) (S i) ^^^ sg (G i) (S i \ {x, y}) := by
    intro i x y hx hy
    rw [sigma_erase S i x y]
    have hlt : (Finset.univ.sigma (Function.update S i (S i \ {x, y}))).card < N := by
      rw [← sigma_erase S i x y, ← hN]
      exact card_sdiff_pair_lt _ (Finset.mem_sigma.2 ⟨Finset.mem_univ _, hx⟩)
    rw [ih _ hlt (Function.update S i (S i \ {x, y})) rfl]
    have : (fun k => sg (G k) (Function.update S i (S i \ {x, y}) k)) =
        Function.update (fun k => sg (G k) (S k)) i (sg (G i) (S i \ {x, y})) := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    rw [this, XF_update]
  apply sg_eq_of
  · intro y hy
    obtain ⟨i, hi⟩ := nim_exists (fun k => sg (G k) (S k)) y hy
    obtain ⟨x, v, hx, hv, hadj, hval⟩ := (sg_char (G i) (S i)).1 _ hi
    refine ⟨⟨i, x⟩, ⟨i, v⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hx⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_univ _, hv⟩, ?_, ?_⟩
    · refine ⟨?_, Or.inl ⟨i, x, v, rfl, rfl, hadj⟩⟩
      intro heq
      have := Sigma.mk.inj_iff.1 heq
      exact (G i).ne_of_adj hadj (eq_of_heq this.2)
    · rw [mv i x v hx hv, hval]
      exact xor_aux _ _ _
  · intro u v hu hv ha
    obtain ⟨hne, ⟨i, x, y, rfl, rfl, hadj⟩ | ⟨i, x, y, rfl, rfl, hadj⟩⟩ := ha
    · rw [mv i x y (Finset.mem_sigma.1 hu).2 (Finset.mem_sigma.1 hv).2]
      exact xor_ne _ _ _ ((sg_char (G i) (S i)).2 x y (Finset.mem_sigma.1 hu).2
        (Finset.mem_sigma.1 hv).2 hadj)
    · rw [Finset.pair_comm, mv i x y (Finset.mem_sigma.1 hv).2 (Finset.mem_sigma.1 hu).2]
      exact xor_ne _ _ _ ((sg_char (G i) (S i)).2 x y (Finset.mem_sigma.1 hv).2
        (Finset.mem_sigma.1 hu).2 hadj)

end AK4

theorem solution (h : ℕ) {W : Fin h → Type*} [∀ i, DecidableEq (W i)]
    (G : ∀ i, SimpleGraph (W i)) (S : ∀ i, Finset (W i)) :
    sg (sigmaGraph G) (Finset.univ.sigma S) =
      (List.ofFn fun i => sg (G i) (S i)).foldr (· ^^^ ·) 0 :=
  AK4.sum_theorem h G S
