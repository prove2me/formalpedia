-- Prove2me | solution 1 for ActiveLanguageGeneration.Hierarchy.finite_active_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:30.196999+00:00
-- url     : https://prove2.me/submissions/016c5f55-a579-44ec-81b3-38a1c6751beb

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Mathlib
import Theorems.Thm_ActiveLanguageGeneration_Hierarchy_finite_functions_free_subset

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

namespace Dev.Transport

variable {U V : Type}

/-- Image of a language along an equivalence. -/
def mapLang (e : U ≃ V) (L : Language U) : Language V :=
  ⟨e '' L.val, L.property.image e.injective.injOn⟩

def mapColl (e : U ≃ V) (C : LanguageCollection U) : LanguageCollection V :=
  mapLang e '' C

def mapGen (e : U ≃ V) (G : Generator U) : Generator V :=
  fun l => e (G (l.map e.symm))

lemma mapLang_symm (e : U ≃ V) (L : Language U) : mapLang e.symm (mapLang e L) = L := by
  apply Subtype.ext
  simp [mapLang, Set.image_image]

lemma mapColl_symm (e : U ≃ V) (C : LanguageCollection U) :
    mapColl e.symm (mapColl e C) = C := by
  simp [mapColl, Set.image_image, mapLang_symm]

lemma inputHistory_comp (e : U ≃ V) (x : ℕ → U) (n : ℕ) :
    inputHistory (fun j => e (x j)) n = (inputHistory x n).map e := by
  simp [inputHistory, List.map_map, Function.comp_def]

lemma outputAt_mapGen (e : U ≃ V) (G : Generator U) (x : ℕ → U) (n : ℕ) :
    outputAt (mapGen e G) (fun j => e (x j)) n = e (outputAt G x n) := by
  simp [outputAt, mapGen, inputHistory_comp, List.map_map, Function.comp_def]

lemma seen_comp (e : U ≃ V) (x : ℕ → U) (n : ℕ) :
    seenInputs (fun j => e (x j)) n = e '' seenInputs x n := by
  ext z
  simp only [seenInputs, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma prior_comp (e : U ≃ V) (G : Generator U) (x : ℕ → U) (n : ℕ) :
    priorOutputs (mapGen e G) (fun j => e (x j)) n = e '' priorOutputs G x n := by
  ext z
  simp only [priorOutputs, Set.mem_setOf_eq, Set.mem_image, outputAt_mapGen]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨outputAt G x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma correctAt_map (e : U ≃ V) (mode : Repetition) (G : Generator U) (L : Language U)
    (x : ℕ → U) (n : ℕ) :
    CorrectAt mode (mapGen e G) (mapLang e L) (fun j => e (x j)) n ↔ CorrectAt mode G L x n := by
  cases mode <;>
  simp [CorrectAt, outputAt_mapGen, seen_comp, prior_comp, mapLang, e.injective.mem_set_image]

lemma isEnum_map (e : U ≃ V) (L : Language U) (x : ℕ → U) (h : IsEnumeration L x) :
    IsEnumeration (mapLang e L) (fun j => e (x j)) := by
  refine ⟨e.injective.comp h.1, ?_⟩
  simp only [mapLang, ← h.2]
  exact (Set.range_comp e x)

theorem kgen_map (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U) (k : ℕ)
    (h : ActiveKGeneratable mode C k) : ActiveKGeneratable mode (mapColl e C) k := by
  obtain ⟨hk, G, hG⟩ := h
  refine ⟨hk, mapGen e G, ?_⟩
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨x, hx, hc⟩ := hG L hL
  exact ⟨fun j => e (x j), isEnum_map e L x hx, fun n hn => (correctAt_map e mode G L x n).2 (hc n hn)⟩

theorem kgen_iff (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U) (k : ℕ) :
    ActiveKGeneratable mode (mapColl e C) k ↔ ActiveKGeneratable mode C k := by
  refine ⟨fun h => ?_, kgen_map e mode C k⟩
  have := kgen_map e.symm mode _ k h
  rwa [mapColl_symm] at this

end Dev.Transport
end ActiveLanguageGeneration.Hierarchy
end

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Dev.Concrete

/-- Fresh label of the cell `(n, i, j)` of block `n`. -/
def F (k n i j : ℕ) : ℕ := (n * k + i) * k + j

/-- The label of entry `j` of row `i` of block `n`.  Row `0` of a block `n ≥ 1` is the column
number `n - 1` (block `(n-1)/k`, column `(n-1)%k`); every other row is fresh. -/
def E (k : ℕ) (n i j : ℕ) : ℕ :=
  if h : i = 0 ∧ 1 ≤ n then E k ((n - 1) / k) j ((n - 1) % k) else F k n i j
termination_by n
decreasing_by
  have := Nat.div_le_self (n - 1) k
  omega

lemma E_old (k n j : ℕ) (h : 1 ≤ n) :
    E k n 0 j = E k ((n - 1) / k) j ((n - 1) % k) := by
  rw [E]; simp [h]

lemma E_fresh (k n i j : ℕ) (h : i ≠ 0 ∨ n = 0) : E k n i j = F k n i j := by
  rw [E]
  have : ¬ (i = 0 ∧ 1 ≤ n) := by omega
  simp [this]

lemma F_div_mod (k n i j : ℕ) (hk : 0 < k) (hj : j < k) (hi : i < k) :
    F k n i j % k = j ∧ F k n i j / k % k = i ∧ F k n i j / k / k = n := by
  have h1 : F k n i j = j + (n * k + i) * k := by unfold F; ring
  have h2 : F k n i j / k = n * k + i := by
    rw [h1, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj]; simp
  have h3 : n * k + i = i + n * k := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · rw [h2, h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · rw [h2, h3, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hi]; simp

lemma F_inj (k n i j n' i' j' : ℕ) (hk : 0 < k) (hj : j < k) (hi : i < k) (hj' : j' < k)
    (hi' : i' < k) (h : F k n i j = F k n' i' j') : n = n' ∧ i = i' ∧ j = j' := by
  obtain ⟨a1, a2, a3⟩ := F_div_mod k n i j hk hj hi
  obtain ⟨b1, b2, b3⟩ := F_div_mod k n' i' j' hk hj' hi'
  rw [h] at a1 a2 a3
  exact ⟨a3.symm.trans b3, a2.symm.trans b2, a1.symm.trans b1⟩

lemma F_birth (k n i j : ℕ) (hk : 0 < k) (hj : j < k) (hi : i < k) :
    F k n i j / (k * k) = n := by
  obtain ⟨_, _, h3⟩ := F_div_mod k n i j hk hj hi
  rw [← Nat.div_div_eq_div_mul]; exact h3

/-- Every label of block `n` was born at a block `≤ n`. -/
lemma E_birth_le (k : ℕ) (hk : 0 < k) :
    ∀ n i j : ℕ, i < k → j < k → E k n i j / (k * k) ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hi hj
    by_cases h : i = 0 ∧ 1 ≤ n
    · obtain ⟨rfl, hn⟩ := h
      rw [E_old k n j hn]
      have hm : (n - 1) / k < n := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      exact le_trans (ih _ hm j _ hj (Nat.mod_lt _ hk)) hm.le
    · rw [E_fresh k n i j (by omega), F_birth k n i j hk hj hi]

lemma E_birth_old (k : ℕ) (hk : 0 < k) (n j : ℕ) (hn : 1 ≤ n) (hj : j < k) :
    E k n 0 j / (k * k) < n := by
  rw [E_old k n j hn]
  have hm : (n - 1) / k < n := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact lt_of_le_of_lt (E_birth_le k hk _ j _ hj (Nat.mod_lt _ hk)) hm

lemma E_birth_fresh (k : ℕ) (hk : 0 < k) (n i j : ℕ) (h : i ≠ 0 ∨ n = 0) (hi : i < k)
    (hj : j < k) : E k n i j / (k * k) = n := by
  rw [E_fresh k n i j h, F_birth k n i j hk hj hi]

/-- A fresh row against a column-row. -/
lemma AB_pairs (k : ℕ) (hk : 0 < k) (n i m' j0' a b : ℕ) (hA : i ≠ 0 ∨ n = 0) (hi : i < k)
    (ha : a < k) (hb : b < k) (hj0' : j0' < k)
    (h : E k n i a = E k m' b j0') :
    ((b ≠ 0 ∨ m' = 0) → n = m' ∧ i = b ∧ a = j0') ∧ ((b = 0 ∧ 1 ≤ m') → n < m') := by
  constructor
  · intro hb'
    rw [E_fresh k n i a hA, E_fresh k m' b j0' (by omega)] at h
    exact F_inj k n i a m' b j0' hk ha hi hj0' hb h
  · rintro ⟨rfl, hm⟩
    have h1 := E_birth_fresh k hk n i a hA hi ha
    have h2 := E_birth_old k hk m' j0' hm hj0'
    rw [h] at h1
    omega

/-- Two column-rows. -/
lemma BB_pairs (k : ℕ) (hk : 0 < k) (m j0 m' j0' a b : ℕ) (ha : a < k) (hb : b < k)
    (hj0 : j0 < k) (hj0' : j0' < k) (hne : ¬ (m = m' ∧ j0 = j0'))
    (h : E k m a j0 = E k m' b j0') :
    (a ≠ 0 ∨ m = 0) → b = 0 ∧ 1 ≤ m' ∧ m < m' := by
  intro hfa
  have hl := E_birth_fresh k hk m a j0 hfa ha hj0
  by_cases hfb : b ≠ 0 ∨ m' = 0
  · exfalso
    rw [E_fresh k m a j0 hfa, E_fresh k m' b j0' hfb] at h
    obtain ⟨h1, _, h3⟩ := F_inj k m a j0 m' b j0' hk hj0 ha hj0' hb h
    exact hne ⟨h1, h3⟩
  · have hb0 : b = 0 := by omega
    have hm' : 1 ≤ m' := by omega
    subst hb0
    have h2 := E_birth_old k hk m' j0' hm' hj0'
    rw [← h] at h2
    omega

lemma E_row_inj (k : ℕ) (hk : 0 < k) (n i a a' : ℕ) (hi : i < k) (ha : a < k) (ha' : a' < k)
    (h : E k n i a = E k n i a') : a = a' := by
  by_cases hA : i ≠ 0 ∨ n = 0
  · rw [E_fresh k n i a hA, E_fresh k n i a' hA] at h
    exact (F_inj k n i a n i a' hk ha hi ha' hi h).2.2
  · have hn : 1 ≤ n := by omega
    have hi0 : i = 0 := by omega
    subst hi0
    rw [E_old k n a hn, E_old k n a' hn] at h
    have hj0 : (n - 1) % k < k := Nat.mod_lt _ hk
    generalize (n - 1) % k = j0 at h hj0
    generalize (n - 1) / k = m at h
    by_cases hf : a ≠ 0 ∨ m = 0
    · by_cases hf' : a' ≠ 0 ∨ m = 0
      · rw [E_fresh k m a j0 hf, E_fresh k m a' j0 hf'] at h
        exact (F_inj k m a j0 m a' j0 hk hj0 ha hj0 ha' h).1 |> fun _ =>
          (F_inj k m a j0 m a' j0 hk hj0 ha hj0 ha' h).2.1
      · exfalso
        have ha'0 : a' = 0 := by omega
        have hm : 1 ≤ m := by omega
        subst ha'0
        have h1 := E_birth_fresh k hk m a j0 hf ha hj0
        have h2 := E_birth_old k hk m j0 hm hj0
        rw [h] at h1
        omega
    · by_cases hf' : a' ≠ 0 ∨ m = 0
      · exfalso
        have ha0 : a = 0 := by omega
        have hm : 1 ≤ m := by omega
        subst ha0
        have h1 := E_birth_fresh k hk m a' j0 hf' ha' hj0
        have h2 := E_birth_old k hk m j0 hm hj0
        rw [← h] at h1
        omega
      · omega

/-- Two distinct rows of the construction share at most one label. -/
theorem notwo (k : ℕ) (hk : 0 < k) (n i n' i' a a' b b' : ℕ) (hi : i < k) (hi' : i' < k)
    (ha : a < k) (ha' : a' < k) (hb : b < k) (hb' : b' < k)
    (hne : ¬ (n = n' ∧ i = i'))
    (h1 : E k n i a = E k n' i' b) (h2 : E k n i a' = E k n' i' b') : a = a' ∨ b = b' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hca, hcb⟩ := hcon
  by_cases hA : i ≠ 0 ∨ n = 0
  · by_cases hA' : i' ≠ 0 ∨ n' = 0
    · rw [E_fresh k n i a hA, E_fresh k n' i' b hA'] at h1
      exact hne ⟨(F_inj k n i a n' i' b hk ha hi hb hi' h1).1,
        (F_inj k n i a n' i' b hk ha hi hb hi' h1).2.1⟩
    · -- A against B
      have hn' : 1 ≤ n' := by omega
      have hi'0 : i' = 0 := by omega
      subst hi'0
      rw [E_old k n' b hn'] at h1
      rw [E_old k n' b' hn'] at h2
      have hj0 : (n' - 1) % k < k := Nat.mod_lt _ hk
      have p1 := AB_pairs k hk n i ((n' - 1) / k) ((n' - 1) % k) a b hA hi ha hb hj0 h1
      have p2 := AB_pairs k hk n i ((n' - 1) / k) ((n' - 1) % k) a' b' hA hi ha' hb' hj0 h2
      omega
  · have hn : 1 ≤ n := by omega
    have hi0 : i = 0 := by omega
    subst hi0
    by_cases hA' : i' ≠ 0 ∨ n' = 0
    · -- B against A
      rw [E_old k n a hn] at h1
      rw [E_old k n a' hn] at h2
      have hj0 : (n - 1) % k < k := Nat.mod_lt _ hk
      have p1 := AB_pairs k hk n' i' ((n - 1) / k) ((n - 1) % k) b a hA' hi' hb ha hj0 h1.symm
      have p2 := AB_pairs k hk n' i' ((n - 1) / k) ((n - 1) % k) b' a' hA' hi' hb' ha' hj0 h2.symm
      omega
    · have hn' : 1 ≤ n' := by omega
      have hi'0 : i' = 0 := by omega
      subst hi'0
      rw [E_old k n a hn] at h1
      rw [E_old k n a' hn] at h2
      rw [E_old k n' b hn'] at h1
      rw [E_old k n' b' hn'] at h2
      have hj0 : (n - 1) % k < k := Nat.mod_lt _ hk
      have hj0' : (n' - 1) % k < k := Nat.mod_lt _ hk
      have hne' : ¬ ((n - 1) / k = (n' - 1) / k ∧ (n - 1) % k = (n' - 1) % k) := by
        rintro ⟨e1, e2⟩
        have x1 := Nat.div_add_mod (n - 1) k
        have x2 := Nat.div_add_mod (n' - 1) k
        rw [e1, e2] at x1
        apply hne
        refine ⟨?_, rfl⟩
        omega
      have hne'' : ¬ ((n' - 1) / k = (n - 1) / k ∧ (n' - 1) % k = (n - 1) % k) := by
        rintro ⟨e1, e2⟩; exact hne' ⟨e1.symm, e2.symm⟩
      have q1 := BB_pairs k hk _ _ _ _ a b ha hb hj0 hj0' hne' h1
      have q2 := BB_pairs k hk _ _ _ _ a' b' ha' hb' hj0 hj0' hne' h2
      have r1 := BB_pairs k hk _ _ _ _ b a hb ha hj0' hj0 hne'' h1.symm
      have r2 := BB_pairs k hk _ _ _ _ b' a' hb' ha' hj0' hj0 hne'' h2.symm
      omega

end ActiveLanguageGeneration.Hierarchy.Dev.Concrete
end

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

namespace Dev.Concrete

/-- Strings: `k`-tuples of positive integers (a string is read as the set of its entries). -/
abbrev Str (k : ℕ) := Fin k → ℕ+

/-- The `p`-th string of the enumeration built from the label injection `e`. -/
def Y (k : ℕ) (e : ℕ → ℕ+) (p : ℕ) : Str k := fun a => e (E k (p / k) (p % k) a)

lemma Y_entry_inj (k : ℕ) (hk : 0 < k) (e : ℕ → ℕ+) (he : Function.Injective e) (p : ℕ) :
    Function.Injective (Y k e p) := by
  intro a a' h
  apply Fin.ext
  exact E_row_inj k hk (p / k) (p % k) a a' (Nat.mod_lt _ hk) a.2 a'.2 (he h)

lemma Y_overlap (k : ℕ) (hk : 0 < k) (e : ℕ → ℕ+) (he : Function.Injective e) (p q : ℕ)
    (hpq : p ≠ q) (a a' b b' : Fin k) (h1 : Y k e p a = Y k e q b)
    (h2 : Y k e p a' = Y k e q b') : a = a' ∨ b = b' := by
  have hne : ¬ (p / k = q / k ∧ p % k = q % k) := by
    rintro ⟨e1, e2⟩
    apply hpq
    have x1 := Nat.div_add_mod p k
    have x2 := Nat.div_add_mod q k
    rw [e1, e2] at x1
    omega
  have := notwo k hk (p / k) (p % k) (q / k) (q % k) a a' b b' (Nat.mod_lt _ hk)
    (Nat.mod_lt _ hk) a.2 a'.2 b.2 b'.2 hne (he h1) (he h2)
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

lemma Y_inj (k : ℕ) (hk : 2 ≤ k) (e : ℕ → ℕ+) (he : Function.Injective e) :
    Function.Injective (Y k e) := by
  intro p q h
  by_contra hpq
  have := Y_overlap k (by omega) e he p q hpq ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩
    ⟨1, by omega⟩ (by rw [h]) (by rw [h])
  rcases this with h | h <;> simp [Fin.ext_iff] at h

/-- The collection: all languages enumerated by some `Y k e`. -/
def Coll (k : ℕ) : LanguageCollection (Str k) :=
  {L | ∃ e : ℕ → ℕ+, Function.Injective e ∧ L.val = Set.range (Y k e)}

def idx (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

lemma Y_rec (k : ℕ) (hk : 0 < k) (e : ℕ → ℕ+) (n : ℕ) :
    Y k e ((n + 1) * k) = fun i : Fin k => Y k e ((n / k) * k + i) (idx k hk n) := by
  funext a
  have h1 : ((n + 1) * k) / k = n + 1 := Nat.mul_div_cancel _ hk
  have h2 : ((n + 1) * k) % k = 0 := Nat.mul_mod_left _ _
  have h3 : (n / k * k + a) / k = n / k := by
    rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt a.2]; simp
  have h4 : (n / k * k + a) % k = a := by
    rw [Nat.mul_comm, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt a.2]
  simp only [Y, h1, h2, h3, h4, idx]
  congr 1
  have := E_old k (n + 1) a (by omega)
  simpa using this

def dv (k : ℕ) : Str k := fun _ => 1

def colList (k : ℕ) (hk : 0 < k) (h : List (Str k)) (c : ℕ) : Str k :=
  fun i => (h.getD ((c / k) * k + i) (dv k)) (idx k hk c)

def gen (k : ℕ) (hk : 0 < k) (h : List (Str k)) : Str k :=
  if k ≤ h.length then colList k hk h (h.length - k) else h.getD (h.length - 1) (dv k)

lemma hist_getD (k : ℕ) (x : ℕ → Str k) (n i : ℕ) (hi : i < n + 1) :
    (inputHistory x n).getD i (dv k) = x i := by
  simp [inputHistory, List.getD_eq_getElem?_getD, hi]

lemma out_late (k : ℕ) (hk : 0 < k) (x : ℕ → Str k) (hx : ∀ n, x ((n + 1) * k) =
    fun i : Fin k => x ((n / k) * k + i) (idx k hk n)) (n : ℕ) (hn : k ≤ n + 1) :
    outputAt (gen k hk) x n = x ((n + 1 - k + 1) * k) := by
  have hlen : (inputHistory x n).length = n + 1 := by simp [inputHistory]
  unfold outputAt
  unfold gen
  rw [hlen, if_pos hn, hx (n + 1 - k)]
  funext i
  unfold colList
  have : (n + 1 - k) / k * k + i < n + 1 := by
    have := Nat.div_mul_le_self (n + 1 - k) k
    have := i.2
    omega
  rw [hist_getD k x n _ this]

lemma out_early (k : ℕ) (hk : 0 < k) (x : ℕ → Str k) (n : ℕ) (hn : n + 1 < k) :
    outputAt (gen k hk) x n = x n := by
  have hlen : (inputHistory x n).length = n + 1 := by simp [inputHistory]
  unfold outputAt gen
  rw [hlen, if_neg (by omega)]
  have := hist_getD k x n n (by omega)
  simpa using this

theorem upper (k : ℕ) (hk : 2 ≤ k) : ActiveKGeneratable .NR (Coll k) k := by
  have hk0 : 0 < k := by omega
  refine ⟨hk0, gen k hk0, ?_⟩
  rintro L ⟨e, he, hL⟩
  have hinj := Y_inj k hk e he
  refine ⟨Y k e, ⟨hinj, hL.symm⟩, ?_⟩
  intro n hn
  have hrec := Y_rec k hk0 e
  have hT : ∀ n, k ≤ n + 1 → n < (n + 1 - k + 1) * k := by
    intro n hn
    obtain ⟨c, hc⟩ : ∃ c, n + 1 = c + k := ⟨n + 1 - k, by omega⟩
    have : n + 1 - k = c := by omega
    rw [this]
    have : c ≤ c * k := Nat.le_mul_of_pos_right c hk0
    nlinarith
  simp only [CorrectAt]
  rw [out_late k hk0 (Y k e) hrec n hn, hL]
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro (⟨j, hj, hjx⟩ | ⟨j, hj, hjx⟩)
  · have := hinj hjx
    have := hT n hn
    omega
  · by_cases hjk : k ≤ j + 1
    · rw [out_late k hk0 (Y k e) hrec j hjk] at hjx
      have := hinj hjx
      have := Nat.eq_of_mul_eq_mul_right hk0 this
      omega
    · rw [out_early k hk0 (Y k e) j (by omega)] at hjx
      have := hinj hjx
      have h2 : k ≤ (n + 1 - k + 1) * k := Nat.le_mul_of_pos_left k (by omega)
      omega

/-! Lower bound. -/

lemma free_M (k r : ℕ) (hk : 0 < k) (hr : 0 < r) (H : List (Str k) → Str k) :
    ∃ M : Set ℕ+, M.Infinite ∧ ∀ A : Fin r → Str k, (∀ i c, A i c ∈ M) →
      ∀ ℓ : Fin k, H (List.ofFn A) ℓ ∈ M → ∃ i c, A i c = H (List.ofFn A) ℓ := by
  classical
  let ι := (m : Fin (r * k)) × ((Fin r × Fin k → Fin (m.val + 1)) × Fin k)
  let g : (x : ι) → DistinctTuple (Set.univ : Set ℕ+) ((Nat.succPNat x.1.val : ℕ+) : ℕ) → ℕ+ :=
    fun x a => H (List.ofFn (fun i : Fin r => fun c : Fin k =>
      ((a (x.2.1 (i, c)) : (Set.univ : Set ℕ+)) : ℕ+))) x.2.2
  obtain ⟨M, -, hMinf, hM⟩ := finite_functions_free_subset (Set.univ : Set ℕ+)
    Set.infinite_univ (ι := ι) (fun x => Nat.succPNat x.1.val) g
  refine ⟨M, hMinf, ?_⟩
  intro A hA ℓ hℓ
  by_contra hcon
  push Not at hcon
  let S : Finset ℕ+ := Finset.univ.image (fun p : Fin r × Fin k => A p.1 p.2)
  have hne : S.Nonempty := ⟨A ⟨0, hr⟩ ⟨0, hk⟩, Finset.mem_image.2 ⟨(⟨0, hr⟩, ⟨0, hk⟩), Finset.mem_univ _, rfl⟩⟩
  have hle : S.card ≤ r * k := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin r × Fin k)))
      (f := fun p : Fin r × Fin k => A p.1 p.2)
    simpa [Fintype.card_prod] using this
  obtain ⟨s, hs⟩ : ∃ s, S.card = s + 1 := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.2 hne).ne'
  let m : Fin (r * k) := ⟨s, by omega⟩
  let eqv : S ≃ Fin (s + 1) := S.equivFinOfCardEq hs
  let σ : Fin r × Fin k → Fin (m.val + 1) := fun p =>
    eqv ⟨A p.1 p.2, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩
  let a : DistinctTuple (Set.univ : Set ℕ+) ((Nat.succPNat m.val : ℕ+) : ℕ) :=
    ⟨fun j => ⟨(eqv.symm j : ℕ+), trivial⟩, fun j j' h => by
      have h' : ((eqv.symm j : S) : ℕ+) = ((eqv.symm j' : S) : ℕ+) :=
        congrArg (fun z : (Set.univ : Set ℕ+) => (z : ℕ+)) h
      exact eqv.symm.injective (Subtype.ext h')⟩
  have hvals : tupleValues a ⊆ M := by
    rintro z ⟨j, rfl⟩
    have hmem := (eqv.symm j).2
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hmem
    show ((eqv.symm j : S) : ℕ+) ∈ M
    rw [← hp]
    exact hA _ _
  have key := hM ⟨m, σ, ℓ⟩ a hvals
  have hAeq : (fun i : Fin r => fun c : Fin k => ((a (σ (i, c))) : ℕ+)) = A := by
    funext i c
    show ((eqv.symm (eqv ⟨A i c, _⟩) : S) : ℕ+) = A i c
    simp
  apply key
  have hg : g ⟨m, σ, ℓ⟩ a = H (List.ofFn A) ℓ := by
    show H (List.ofFn (fun i : Fin r => fun c : Fin k => ((a (σ (i, c))) : ℕ+))) ℓ = _
    rw [hAeq]
  rw [hg]
  refine ⟨hℓ, ?_⟩
  rintro ⟨j, hj⟩
  have hmem := (eqv.symm j).2
  obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hmem
  apply hcon p.1 p.2
  rw [hp]
  exact hj.symm ▸ rfl

lemma hist_ofFn (k r : ℕ) (x : ℕ → Str k) :
    inputHistory x r = List.ofFn (fun i : Fin (r + 1) => x i) := by
  apply List.ext_getElem
  · simp [inputHistory]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simp [inputHistory]

theorem lower (r : ℕ) : ¬ ActiveKGeneratable .R (Coll (r + 2)) (r + 1) := by
  rintro ⟨-, G, hG⟩
  have hk0 : 0 < r + 2 := by omega
  have hk2 : 2 ≤ r + 2 := by omega
  obtain ⟨M, hMinf, h9⟩ := free_M (r + 2) (r + 1) hk0 (by omega) G
  let ne := hMinf.natEmbedding M
  let e : ℕ → ℕ+ := fun n => (ne n).val
  have he : Function.Injective e := fun a b h => ne.injective (Subtype.ext h)
  have heM : ∀ n, e n ∈ M := fun n => (ne n).2
  have hYM : ∀ p a, Y (r + 2) e p a ∈ M := fun p a => heM _
  let L : Language (Str (r + 2)) :=
    ⟨Set.range (Y (r + 2) e), Set.infinite_range_of_injective (Y_inj _ hk2 e he)⟩
  obtain ⟨x, ⟨hxinj, hxrange⟩, hcorr⟩ := hG L ⟨e, he, rfl⟩
  have hc := hcorr r (by omega)
  simp only [CorrectAt, outputAt, seenInputs] at hc
  have hmemx : ∀ j, ∃ p, x j = Y (r + 2) e p := fun j => by
    have : x j ∈ L.val := hxrange ▸ ⟨j, rfl⟩
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp.symm⟩
  rw [hist_ofFn] at hc
  set A : Fin (r + 1) → Str (r + 2) := fun i => x i with hA
  obtain ⟨hBL, hBseen⟩ := hc
  obtain ⟨q, hq⟩ := hBL
  have hAM : ∀ i c, A i c ∈ M := by
    intro i c
    obtain ⟨p, hp⟩ := hmemx i
    show x i c ∈ M
    rw [hp]; exact hYM _ _
  have hBM : ∀ ℓ, (G (List.ofFn A)) ℓ ∈ M := by
    intro ℓ
    rw [← hq]; exact hYM _ _
  have h9' := fun ℓ => h9 A hAM ℓ (hBM ℓ)
  choose f g hfg using h9'
  obtain ⟨ℓ, ℓ', hne', hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  obtain ⟨p, hp⟩ := hmemx (f ℓ)
  have hBne : q ≠ p := by
    rintro rfl
    apply hBseen
    exact ⟨(f ℓ : ℕ), by have := (f ℓ).2; omega, by rw [hp, hq]⟩
  have e1 : Y (r + 2) e q ℓ = Y (r + 2) e p (g ℓ) := by
    rw [hq, ← hp]; exact (hfg ℓ).symm
  have e2 : Y (r + 2) e q ℓ' = Y (r + 2) e p (g ℓ') := by
    rw [hq, ← hp, hfeq]; exact (hfg ℓ').symm
  have := Y_overlap (r + 2) hk0 e he q p hBne ℓ ℓ' (g ℓ) (g ℓ') e1 e2
  rcases this with h | h
  · exact hne' h
  · apply hne'
    apply Y_entry_inj (r + 2) hk0 e he q
    rw [e1, e2, h]

end Dev.Concrete

theorem chk_exists_concrete (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Countable V) (_ : Infinite V) (C : LanguageCollection V),
      ActiveKGeneratable .NR C k ∧ ¬ ActiveKGeneratable .R C (k - 1) := by
  refine ⟨Dev.Concrete.Str k, inferInstance, ?_, Dev.Concrete.Coll k, Dev.Concrete.upper k hk, ?_⟩
  · exact Infinite.of_injective (fun n : ℕ+ => (fun _ : Fin k => n))
      (fun a b h => congr_fun h ⟨0, by omega⟩)
  · obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
    exact Dev.Concrete.lower r

end ActiveLanguageGeneration.Hierarchy
end

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Theorem 4.1, printed p.18 (PDF p.19), on an arbitrary countably infinite string universe. Both the NR upper bound and the R lower bound are retained. -/
theorem chk_finite_active_hierarchy (U : Type) [Countable U] [Infinite U] :
    ∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      ActiveKGeneratable .NR C k ∧ ¬ ActiveKGeneratable .R C (k - 1) := by
  intro k hk
  obtain ⟨V, hc, hi, C, h1, h2⟩ := chk_exists_concrete k hk
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := V) (β := U)
  refine ⟨Dev.Transport.mapColl e C, ?_, ?_⟩
  · exact (Dev.Transport.kgen_iff e _ C k).2 h1
  · exact fun h => h2 ((Dev.Transport.kgen_iff e _ C (k - 1)).1 h)

end ActiveLanguageGeneration.Hierarchy
end

theorem solution : type_of% @ActiveLanguageGeneration.Hierarchy.chk_finite_active_hierarchy := @ActiveLanguageGeneration.Hierarchy.chk_finite_active_hierarchy
