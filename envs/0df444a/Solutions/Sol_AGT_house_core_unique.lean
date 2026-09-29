-- Prove2me | solution 1 for AGT.house_core_unique
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T10:17:30.916775+00:00
-- url     : https://prove2.me/submissions/1e183dd9-6c91-4646-b4e0-58f44c908409

import Definitions.Def_agt_matching
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Common

/-!
# The core of a housing market is the single Top Trading Cycle allocation

Theorem 10.6 of *Algorithmic Game Theory* (Shapley–Scarf, Roth–Postlewaite): with strict
preferences exactly one allocation of the housing market is unblocked, namely the outcome
of Gale's Top Trading Cycle algorithm.
-/



namespace GaleShapley

open Finset

/-! ## Ranks -/

/-- The number of alternatives strictly better than `a` in the strict total order `r`. -/
noncomputable def rk {α : Type*} (r : α → α → Prop) (a : α) : ℕ := {b | r b a}.ncard

section Rank

variable {α : Type*} [Fintype α] {r : α → α → Prop}

theorem rk_lt_rk (h : IsStrictTotalOrder α r) {a b : α} (hab : r a b) : rk r a < rk r b := by
  have := h
  apply Set.ncard_lt_ncard
  · constructor
    · intro x hx; exact trans_of r hx hab
    · intro hsub
      have : a ∈ {x : α | r x a} := hsub hab
      exact absurd this (by simpa using irrefl_of r a)
  · exact Set.toFinite _

theorem rk_lt_card (h : IsStrictTotalOrder α r) (a : α) : rk r a < Fintype.card α := by
  have := h
  have h2 : ({b : α | r b a}).ncard < (Set.univ : Set α).ncard := by
    apply Set.ncard_lt_ncard _ Set.finite_univ
    constructor
    · exact Set.subset_univ _
    · intro hsub
      have : a ∈ {x : α | r x a} := hsub (Set.mem_univ a)
      exact absurd this (by simpa using irrefl_of r a)
  simpa [rk, Set.ncard_univ, Nat.card_eq_fintype_card] using h2

theorem rk_lt_iff (h : IsStrictTotalOrder α r) (a b : α) : rk r a < rk r b ↔ r a b := by
  have := h
  constructor
  · intro hlt
    rcases trichotomous_of r a b with h1 | h1 | h1
    · exact h1
    · subst h1; omega
    · have := rk_lt_rk h h1; omega
  · exact rk_lt_rk h

theorem rk_inj (h : IsStrictTotalOrder α r) : Function.Injective (rk r) := by
  have := h
  intro a b hab
  rcases trichotomous_of r a b with h1 | h1 | h1
  · have := rk_lt_rk h h1; omega
  · exact h1
  · have := rk_lt_rk h h1; omega

end Rank


end GaleShapley

namespace TTC

open Finset GaleShapley

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Top choices inside a set -/

/-- The best element of `R` for agent `i` (junk value `i` if `R` is empty). -/
noncomputable def topIn (P : N → N → N → Prop) (R : Finset N) (i : N) : N :=
  if h : R.Nonempty then (R.exists_min_image (rk (P i)) h).choose else i

omit [Fintype N] [DecidableEq N] in
theorem topIn_mem {P : N → N → N → Prop} {R : Finset N} (h : R.Nonempty) (i : N) :
    topIn P R i ∈ R := by
  rw [topIn, dif_pos h]
  exact (R.exists_min_image (rk (P i)) h).choose_spec.1

omit [Fintype N] [DecidableEq N] in
theorem topIn_le {P : N → N → N → Prop} {R : Finset N} (h : R.Nonempty) (i : N) {j : N}
    (hj : j ∈ R) : rk (P i) (topIn P R i) ≤ rk (P i) j := by
  rw [topIn, dif_pos h]
  exact (R.exists_min_image (rk (P i)) h).choose_spec.2 j hj

/-- The best element of `R` is weakly preferred to every element of `R`. -/
theorem topIn_pref {P : N → N → N → Prop} (hP : AGT.IsPrefProfile P) {R : Finset N}
    (h : R.Nonempty) (i : N) {j : N} (hj : j ∈ R) :
    topIn P R i = j ∨ P i (topIn P R i) j := by
  by_cases he : topIn P R i = j
  · exact Or.inl he
  · refine Or.inr ((rk_lt_iff (hP i) _ _).1 ?_)
    have h1 := topIn_le (P := P) h i hj
    have h2 : rk (P i) (topIn P R i) ≠ rk (P i) j := fun hc => he (rk_inj (hP i) hc)
    omega

/-! ## Cycles of the top-choice map -/

open scoped Classical in
/-- The agents of `R` lying on a cycle of the top-choice map of `R`. -/
noncomputable def cyc (P : N → N → N → Prop) (R : Finset N) : Finset N :=
  R.filter fun i => ∃ p, 0 < p ∧ (topIn P R)^[p] i = i

omit [Fintype N] [DecidableEq N] in
theorem mem_cyc {P : N → N → N → Prop} {R : Finset N} {i : N} :
    i ∈ cyc P R ↔ i ∈ R ∧ ∃ p, 0 < p ∧ (topIn P R)^[p] i = i := by
  classical
  simp [cyc]

omit [Fintype N] [DecidableEq N] in
/-- Pigeonhole: a self-map of a nonempty finite set has a periodic point. -/
theorem exists_periodic {R : Finset N} (h : R.Nonempty) (f : N → N)
    (hf : ∀ i ∈ R, f i ∈ R) : ∃ i ∈ R, ∃ p, 0 < p ∧ f^[p] i = i := by
  obtain ⟨i₀, hi₀⟩ := h
  have hiter : ∀ k, f^[k] i₀ ∈ R := by
    intro k
    induction k with
    | zero => simpa using hi₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hf _ ih
  have hcard : R.card < (Finset.range (R.card + 1)).card := by simp
  obtain ⟨x, _, y, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun k _ => hiter k)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨f^[x] i₀, hiter x, y - x, by omega, ?_⟩
    rw [← Function.iterate_add_apply, show y - x + x = y by omega]
    exact heq.symm
  · refine ⟨f^[y] i₀, hiter y, x - y, by omega, ?_⟩
    rw [← Function.iterate_add_apply, show x - y + y = x by omega]
    exact heq

omit [Fintype N] [DecidableEq N] in
theorem cyc_nonempty {P : N → N → N → Prop} {R : Finset N} (h : R.Nonempty) :
    (cyc P R).Nonempty := by
  obtain ⟨i, hi, p, hp, hper⟩ := exists_periodic h (topIn P R) (fun j _ => topIn_mem h j)
  exact ⟨i, mem_cyc.2 ⟨hi, p, hp, hper⟩⟩

omit [Fintype N] [DecidableEq N] in
theorem cyc_subset {P : N → N → N → Prop} {R : Finset N} : cyc P R ⊆ R :=
  fun _ hi => (mem_cyc.1 hi).1

omit [Fintype N] [DecidableEq N] in
/-- Iterating a periodic point along a multiple of its period returns to it. -/
theorem iterate_mul_fixed {f : N → N} {i : N} {p : ℕ} (h : f^[p] i = i) :
    ∀ k, f^[k * p] i = i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, h, ih]

omit [Fintype N] [DecidableEq N] in
theorem topIn_mem_cyc {P : N → N → N → Prop} {R : Finset N} (h : R.Nonempty) {i : N}
    (hi : i ∈ cyc P R) : topIn P R i ∈ cyc P R := by
  obtain ⟨hiR, p, hp, hper⟩ := mem_cyc.1 hi
  refine mem_cyc.2 ⟨topIn_mem h i, p, hp, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hper]

omit [Fintype N] [DecidableEq N] in
/-- The top-choice map is injective on the cycle agents. -/
theorem topIn_injOn_cyc {P : N → N → N → Prop} {R : Finset N} :
    ∀ i ∈ cyc P R, ∀ j ∈ cyc P R, topIn P R i = topIn P R j → i = j := by
  intro i hi j hj hij
  obtain ⟨_, p, hp, hperi⟩ := mem_cyc.1 hi
  obtain ⟨_, q, hq, hperj⟩ := mem_cyc.1 hj
  set f := topIn P R
  have hi' : f^[q * p] i = i := iterate_mul_fixed hperi q
  have hj' : f^[p * q] j = j := iterate_mul_fixed hperj p
  have hpq : q * p = p * q := Nat.mul_comm _ _
  have hn : 0 < p * q := Nat.mul_pos hp hq
  have e1 : f^[p * q - 1] (f i) = i := by
    have h' : f^[p * q - 1 + 1] i = i := by
      rw [show p * q - 1 + 1 = p * q by omega, ← hpq]; exact hi'
    rwa [Function.iterate_succ_apply] at h'
  have e2 : f^[p * q - 1] (f j) = j := by
    have h' : f^[p * q - 1 + 1] j = j := by
      rw [show p * q - 1 + 1 = p * q by omega]; exact hj'
    rwa [Function.iterate_succ_apply] at h'
  rw [← e1, ← e2, hij]

/-! ## The rounds of the algorithm -/

/-- The agents still unassigned after `k` rounds. -/
noncomputable def rem (P : N → N → N → Prop) : ℕ → Finset N
  | 0 => Finset.univ
  | k + 1 => rem P k \ cyc P (rem P k)

theorem rem_succ (P : N → N → N → Prop) (k : ℕ) :
    rem P (k + 1) = rem P k \ cyc P (rem P k) := rfl

theorem rem_card_lt {P : N → N → N → Prop} {k : ℕ} (h : (rem P k).Nonempty) :
    (rem P (k + 1)).card < (rem P k).card := by
  obtain ⟨x, hx⟩ := cyc_nonempty (P := P) h
  apply Finset.card_lt_card
  rw [rem_succ]
  refine ⟨Finset.sdiff_subset, fun hsub => ?_⟩
  have hmem := hsub (cyc_subset hx)
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 hx

theorem rem_card_le (P : N → N → N → Prop) {k : ℕ} (hk : k ≤ Fintype.card N) :
    (rem P k).card + k ≤ Fintype.card N := by
  induction k with
  | zero => simp [rem]
  | succ k ih =>
    have ih' := ih (by omega)
    rcases Finset.eq_empty_or_nonempty (rem P k) with he | hne
    · have : rem P (k + 1) = ∅ := by rw [rem_succ, he]; simp
      rw [this]
      simp
      omega
    · have := rem_card_lt (P := P) (k := k) hne
      omega

theorem rem_empty (P : N → N → N → Prop) : rem P (Fintype.card N) = ∅ := by
  have := rem_card_le P (le_refl (Fintype.card N))
  exact Finset.card_eq_zero.1 (by omega)

theorem exists_level (P : N → N → N → Prop) (i : N) : ∃ k, i ∈ cyc P (rem P k) := by
  by_contra hc
  simp only [not_exists] at hc
  have hall : ∀ k, i ∈ rem P k := by
    intro k
    induction k with
    | zero => simp [rem]
    | succ k ih =>
      rw [rem_succ, Finset.mem_sdiff]
      exact ⟨ih, hc k⟩
  have := hall (Fintype.card N)
  rw [rem_empty] at this
  simp at this

open scoped Classical in
/-- The round at which agent `i` is assigned. -/
noncomputable def lev (P : N → N → N → Prop) (i : N) : ℕ := Nat.find (exists_level P i)

open scoped Classical in
theorem mem_cyc_lev (P : N → N → N → Prop) (i : N) : i ∈ cyc P (rem P (lev P i)) :=
  Nat.find_spec (exists_level P i)

open scoped Classical in
theorem lev_min (P : N → N → N → Prop) {i : N} {k : ℕ} (h : i ∈ cyc P (rem P k)) :
    lev P i ≤ k :=
  Nat.find_min' (exists_level P i) h

/-- The agents remaining after `k` rounds are exactly those assigned at round `k` or later. -/
theorem mem_rem_iff (P : N → N → N → Prop) (k : ℕ) (i : N) :
    i ∈ rem P k ↔ k ≤ lev P i := by
  induction k with
  | zero => simp [rem]
  | succ k ih =>
    rw [rem_succ, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      have hk : k ≤ lev P i := ih.1 h1
      rcases Nat.lt_or_ge (lev P i) (k + 1) with hlt | hge
      · exact absurd (show lev P i = k by omega ▸ mem_cyc_lev P i) h2
      · exact hge
    · intro h
      refine ⟨ih.2 (by omega), fun hc => ?_⟩
      have := lev_min P hc
      omega

theorem mem_cyc_iff (P : N → N → N → Prop) (k : ℕ) (i : N) :
    i ∈ cyc P (rem P k) ↔ lev P i = k := by
  constructor
  · intro h
    have h1 := lev_min P h
    have h2 := (mem_rem_iff P k i).1 (cyc_subset h)
    omega
  · intro h
    rw [← h]
    exact mem_cyc_lev P i

theorem rem_lev_nonempty (P : N → N → N → Prop) (i : N) : (rem P (lev P i)).Nonempty :=
  ⟨i, (mem_rem_iff P _ i).2 le_rfl⟩

/-! ## The Top Trading Cycle allocation -/

/-- The allocation produced by the Top Trading Cycle algorithm. -/
noncomputable def ttc (P : N → N → N → Prop) (i : N) : N :=
  topIn P (rem P (lev P i)) i

theorem lev_ttc (P : N → N → N → Prop) (i : N) : lev P (ttc P i) = lev P i :=
  (mem_cyc_iff P _ _).1 (topIn_mem_cyc (rem_lev_nonempty P i) (mem_cyc_lev P i))

theorem ttc_injective (P : N → N → N → Prop) : Function.Injective (ttc P) := by
  intro i j hij
  have hlev : lev P i = lev P j := by rw [← lev_ttc P i, ← lev_ttc P j, hij]
  refine topIn_injOn_cyc i (mem_cyc_lev P i) j ((mem_cyc_iff P _ j).2 hlev.symm) ?_
  show ttc P i = topIn P (rem P (lev P i)) j
  rw [hij, hlev]
  rfl

/-- The Top Trading Cycle allocation as a permutation. -/
noncomputable def ttcEquiv (P : N → N → N → Prop) : N ≃ N :=
  Equiv.ofBijective (ttc P)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨ttc_injective P, rfl⟩)

/-- Each agent gets his favourite house among those of the agents assigned no earlier. -/
theorem ttc_pref (P : N → N → N → Prop) (hP : AGT.IsPrefProfile P) (i : N) {j : N}
    (hj : lev P i ≤ lev P j) : ttc P i = j ∨ P i (ttc P i) j :=
  topIn_pref hP (rem_lev_nonempty P i) i ((mem_rem_iff P _ j).2 hj)

omit [Fintype N] in
/-- A finite set mapped into itself by an injection is mapped onto itself. -/
theorem mem_of_image_mem {A : Finset N} {f : N → N} (hinj : Function.Injective f)
    (hmaps : ∀ j ∈ A, f j ∈ A) {i : N} (h : f i ∈ A) : i ∈ A := by
  have hsub : A.image f ⊆ A := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hmaps j hj
  have hcard : (A.image f).card = A.card := Finset.card_image_of_injective _ hinj
  have heq : A.image f = A := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [← heq] at h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 h
  rwa [hinj hji] at hj

/-- The permutation that trades along the cycles formed at round `k`. -/
noncomputable def cycPerm (P : N → N → N → Prop) (k : ℕ) : N ≃ N :=
  Equiv.ofBijective (fun x => if lev P x = k then ttc P x else x)
    ((Fintype.bijective_iff_injective_and_card _).2 (by
      refine ⟨fun x y hxy => ?_, rfl⟩
      by_cases hx : lev P x = k <;> by_cases hy : lev P y = k <;>
        simp only [hx, hy, if_false, if_pos] at hxy
      · exact ttc_injective P hxy
      · exact absurd (by rw [← hxy, lev_ttc]; exact hx) hy
      · exact absurd (by rw [hxy, lev_ttc]; exact hy) hx
      · exact hxy))

theorem cycPerm_apply (P : N → N → N → Prop) {k : ℕ} {x : N} (h : lev P x = k) :
    cycPerm P k x = ttc P x := by
  show (if lev P x = k then ttc P x else x) = ttc P x
  rw [if_pos h]

/-! ## The allocation is in the core, and is the only core point -/

theorem ttc_not_blocked (P : N → N → N → Prop) (hP : AGT.IsPrefProfile P) :
    ¬ AGT.HouseBlocked P (ttcEquiv P) := by
  classical
  rintro ⟨S, t, hne, hclosed, hweak, i₀, hi₀S, hi₀⟩
  have hcoin : ∀ k, ∀ i ∈ S, lev P i = k → t i = ttc P i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hiS hlev
      have hIH : ∀ j, j ∈ S → lev P j < k → t j = ttc P j := fun j hjS hj =>
        ih (lev P j) hj j hjS rfl
      have hgk : k ≤ lev P (t i) := by
        by_contra hc
        rw [not_le] at hc
        set A : Finset N := Finset.univ.filter (fun j => j ∈ S ∧ lev P j < k) with hA
        have hmaps : ∀ j ∈ A, t j ∈ A := by
          intro j hj
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          refine ⟨hclosed j hj.1, ?_⟩
          rw [hIH j hj.1 hj.2, lev_ttc]
          exact hj.2
        have hti : t i ∈ A := by
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hclosed i hiS, hc⟩
        have : i ∈ A := mem_of_image_mem t.injective hmaps hti
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at this
        omega
      have hbest := ttc_pref P hP i (j := t i) (by rw [hlev]; exact hgk)
      rcases hweak i hiS with h1 | h1
      · exact h1
      · exfalso
        have h1' : P i (t i) (ttc P i) := h1
        have := hP i
        rcases hbest with h2 | h2
        · rw [h2] at h1'
          exact irrefl_of (P i) _ h1'
        · exact irrefl_of (P i) (t i) (trans_of (P i) h1' h2)
  have heq := hcoin (lev P i₀) i₀ hi₀S rfl
  have := hP i₀
  have hbad : P i₀ (ttc P i₀) (ttc P i₀) := by rw [heq] at hi₀; exact hi₀
  exact irrefl_of (P i₀) _ hbad

theorem eq_ttc_of_not_blocked (P : N → N → N → Prop) (hP : AGT.IsPrefProfile P)
    (s : N ≃ N) (hs : ¬ AGT.HouseBlocked P s) : s = ttcEquiv P := by
  classical
  have key : ∀ k, ∀ i, lev P i = k → s i = ttc P i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hIH : ∀ j, lev P j < k → s j = ttc P j := fun j hj => ih (lev P j) hj j rfl
      have hge : ∀ j, k ≤ lev P j → k ≤ lev P (s j) := by
        intro j hj
        by_contra hc
        rw [not_le] at hc
        set A : Finset N := Finset.univ.filter (fun x => lev P x < k) with hA
        have hmaps : ∀ x ∈ A, s x ∈ A := by
          intro x hx
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rw [hIH x hx, lev_ttc]
          exact hx
        have hsj : s j ∈ A := by
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hc
        have : j ∈ A := mem_of_image_mem s.injective hmaps hsj
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at this
        omega
      have hpref : ∀ j, lev P j = k → (ttc P j = s j ∨ P j (ttc P j) (s j)) := by
        intro j hj
        exact ttc_pref P hP j (by rw [hj]; exact hge j (le_of_eq hj.symm))
      intro i hi
      by_contra hne
      apply hs
      refine ⟨{j | lev P j = k}, cycPerm P k, ⟨i, hi⟩, ?_, ?_, ?_⟩
      · intro j hj
        show lev P (cycPerm P k j) = k
        rw [cycPerm_apply P hj, lev_ttc]
        exact hj
      · intro j hj
        rw [cycPerm_apply P hj]
        rcases hpref j hj with h | h
        · exact Or.inl h
        · exact Or.inr h
      · refine ⟨i, hi, ?_⟩
        rw [cycPerm_apply P hi]
        rcases hpref i hi with h | h
        · exact absurd h.symm hne
        · exact h
  exact Equiv.ext fun i => key (lev P i) i rfl

end TTC

/-! ## The theorem -/

theorem solution {N : Type*} [Fintype N] [DecidableEq N]
    (P : N → N → N → Prop) (hP : AGT.IsPrefProfile P) :
    ∃! σ : N ≃ N, ¬ AGT.HouseBlocked P σ :=
  ⟨TTC.ttcEquiv P, TTC.ttc_not_blocked P hP, fun s hs => TTC.eq_ttc_of_not_blocked P hP s hs⟩
