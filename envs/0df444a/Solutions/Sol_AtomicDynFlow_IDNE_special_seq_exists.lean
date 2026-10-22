-- Prove2me | solution 1 for AtomicDynFlow.IDNE.special_seq_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T08:17:34.404738+00:00
-- url     : https://prove2.me/submissions/d9e01bd0-4c7e-4807-b027-ac92cf5fe053

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Selection

open AtomicDynFlow.IDNE

namespace ADFF

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

section basic
variable (G : Instance V E A)

/-- the filterMap step function of the queue recursion -/
def fwd (π : A → Option (List E)) (s : ℕ) (e : E) (e' : E) : Option A :=
  match G.queue π s e' with
  | a :: _ => if Instance.nextAfter e' ((π a).getD []) = some e then some a else none
  | [] => none

lemma queue_zero (π : A → Option (List E)) (e : E) :
    G.queue π 0 e = (G.Q0 e).filter (fun a => (π a).isSome) := rfl

lemma queue_succ (π : A → Option (List E)) (s : ℕ) (e : E) :
    G.queue π (s + 1) e =
      (G.queue π s e).tail ++
      (G.inflow (s + 1) (G.tail e)).filter
        (fun a => match π a with
          | some P => decide (P.head? = some e)
          | none => false) ++
      (G.inc (G.tail e)).filterMap (fwd G π s e) := rfl

lemma fwd_eq_some (π : A → Option (List E)) (s : ℕ) (e e' : E) (b : A) :
    fwd G π s e e' = some b ↔
      (G.queue π s e').head? = some b ∧ Instance.nextAfter e' ((π b).getD []) = some e := by
  unfold fwd
  cases h : G.queue π s e' with
  | nil => simp
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq]
    split_ifs with h1
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, h1⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [reduceCtorEq, false_iff, not_and]
      rintro rfl; exact h1

lemma inflow_filter_mem (π : A → Option (List E)) (s : ℕ) (e : E) (a : A) :
    a ∈ (G.inflow (s + 1) (G.tail e)).filter
        (fun a => match π a with
          | some P => decide (P.head? = some e)
          | none => false) ↔
      a ∈ G.inflow (s + 1) (G.tail e) ∧ ∃ P, π a = some P ∧ P.head? = some e := by
  rw [List.mem_filter]
  cases h : π a with
  | none => simp
  | some P => simp

lemma mem_queue_succ (π : A → Option (List E)) (s : ℕ) (e : E) (a : A) :
    a ∈ G.queue π (s + 1) e ↔
      a ∈ (G.queue π s e).tail ∨
      (a ∈ G.inflow (s + 1) (G.tail e) ∧ ∃ P, π a = some P ∧ P.head? = some e) ∨
      (∃ e', G.head e' = G.tail e ∧ (G.queue π s e').head? = some a ∧
        Instance.nextAfter e' ((π a).getD []) = some e) := by
  rw [queue_succ, List.mem_append, List.mem_append, inflow_filter_mem, List.mem_filterMap]
  simp only [fwd_eq_some, G.inc_mem]
  constructor
  · rintro ((h | h) | ⟨e', h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨e', h1, h2⟩)
  · rintro (h | h | ⟨e', h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e', h1, h2⟩

/-- `a` has started by time `s`. -/
def Started (a : A) (s : ℕ) : Prop := ∃ v t, G.StartsAt a v t ∧ t ≤ s

lemma mem_queue_present (π : A → Option (List E)) :
    ∀ (s : ℕ) (e : E) (a : A), a ∈ G.queue π s e → (π a).isSome ∧ Started G a s := by
  intro s
  induction s with
  | zero =>
    intro e a h
    rw [queue_zero, List.mem_filter] at h
    exact ⟨by simpa using h.2, G.tail e, 0, Or.inl ⟨e, h.1, rfl, rfl⟩, le_rfl⟩
  | succ s ih =>
    intro e a h
    rw [mem_queue_succ] at h
    rcases h with h | ⟨h1, P, hP, _⟩ | ⟨e', _, h2, _⟩
    · obtain ⟨h1, v, t, ht, hts⟩ := ih e a (List.mem_of_mem_tail h)
      exact ⟨h1, v, t, ht, by omega⟩
    · exact ⟨by simp [hP], G.tail e, s + 1, Or.inr h1, le_rfl⟩
    · obtain ⟨h1, v, t, ht, hts⟩ := ih e' a (List.mem_of_mem_head? h2)
      exact ⟨h1, v, t, ht, by omega⟩

/-- start-time uniqueness -/
lemma startsAt_unique (a : A) (v v' : V) (t t' : ℕ) (h : G.StartsAt a v t)
    (h' : G.StartsAt a v' t') : v = v' ∧ t = t' := by
  obtain ⟨s0, -, huniq⟩ := G.partition a
  rcases h with ⟨e, he, hv, ht⟩ | h <;> rcases h' with ⟨e', he', hv', ht'⟩ | h'
  · have h1 : (Sum.inl e : E ⊕ (ℕ × V)) = Sum.inl e' := by
      rw [huniq (Sum.inl e) he, huniq (Sum.inl e') he']
    cases h1; exact ⟨hv ▸ hv', by omega⟩
  · have h1 : (Sum.inl e : E ⊕ (ℕ × V)) = Sum.inr (t', v') := by
      rw [huniq (Sum.inl e) he, huniq (Sum.inr (t', v')) h']
    cases h1
  · have h1 : (Sum.inl e' : E ⊕ (ℕ × V)) = Sum.inr (t, v) := by
      rw [huniq (Sum.inl e') he', huniq (Sum.inr (t, v)) h]
    cases h1
  · have h1 : (Sum.inr (t, v) : E ⊕ (ℕ × V)) = Sum.inr (t', v') := by
      rw [huniq (Sum.inr (t, v)) h, huniq (Sum.inr (t', v')) h']
    cases h1; exact ⟨rfl, rfl⟩

lemma not_started_of_inflow (a : A) (s : ℕ) (v : V) (h : a ∈ G.inflow (s + 1) v) :
    ¬ Started G a s := by
  rintro ⟨w, t, ht, hts⟩
  have := (startsAt_unique G a _ _ _ _ ht (Or.inr h)).2
  omega

lemma nextAfter_mem (e : E) : ∀ (P : List E) (e2 : E), Instance.nextAfter e P = some e2 →
    e ∈ P ∧ e2 ∈ P := by
  intro P
  induction P with
  | nil => intro e2 h; simp [Instance.nextAfter] at h
  | cons x rest ih =>
    intro e2 h
    simp only [Instance.nextAfter] at h
    split_ifs at h with hx
    · subst hx
      refine ⟨by simp, ?_⟩
      cases rest with
      | nil => simp at h
      | cons y r => simp at h; subst h; simp
    · obtain ⟨h1, h2⟩ := ih e2 h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- In a nodup list, `nextAfter e P = some e` is impossible. -/
lemma nextAfter_ne_self (e : E) : ∀ (P : List E), P.Nodup → Instance.nextAfter e P ≠ some e := by
  intro P
  induction P with
  | nil => simp [Instance.nextAfter]
  | cons x rest ih =>
    intro hnd h
    rw [List.nodup_cons] at hnd
    simp only [Instance.nextAfter] at h
    split_ifs at h with hx
    · subst hx
      cases rest with
      | nil => simp at h
      | cons y r =>
        simp at h; subst h; exact hnd.1 (by simp)
    · exact ih hnd.2 h

/-- Invariant: every queue is duplicate-free and every agent is in at most one queue. -/
lemma queue_inv (π : A → Option (List E)) (hnd : ∀ a P, π a = some P → P.Nodup) :
    ∀ s : ℕ, (∀ e, (G.queue π s e).Nodup) ∧
      (∀ e e' a, a ∈ G.queue π s e → a ∈ G.queue π s e' → e = e') := by
  intro s
  induction s with
  | zero =>
    refine ⟨fun e => ?_, fun e e' a h h' => ?_⟩
    · rw [queue_zero]; exact (G.nodup (Sum.inl e)).filter _
    · rw [queue_zero, List.mem_filter] at h h'
      obtain ⟨s0, -, huniq⟩ := G.partition a
      have h1 : (Sum.inl e : E ⊕ (ℕ × V)) = Sum.inl e' := by
        rw [huniq (Sum.inl e) h.1, huniq (Sum.inl e') h'.1]
      cases h1; rfl
  | succ s ih =>
    obtain ⟨ihnd, ihu⟩ := ih
    -- heads are distinct across edges
    have hhead : ∀ e1 e2 a, (G.queue π s e1).head? = some a → (G.queue π s e2).head? = some a →
        e1 = e2 := fun e1 e2 a h1 h2 =>
      ihu e1 e2 a (List.mem_of_mem_head? h1) (List.mem_of_mem_head? h2)
    have hnotail : ∀ e e' a, (G.queue π s e').head? = some a → a ∉ (G.queue π s e).tail := by
      intro e e' a h1 h2
      have := ihu e e' a (List.mem_of_mem_tail h2) (List.mem_of_mem_head? h1)
      subst this
      have hnd' := ihnd e
      cases hq : G.queue π s e with
      | nil => simp [hq] at h1
      | cons x l =>
        rw [hq] at h1 h2 hnd'
        simp at h1; subst h1
        exact (List.nodup_cons.1 hnd').1 h2
    refine ⟨fun e => ?_, fun e e' a h h' => ?_⟩
    · rw [queue_succ]
      refine List.Nodup.append (List.Nodup.append ((ihnd e).sublist (List.tail_sublist _))
        ((G.nodup (Sum.inr (s + 1, G.tail e))).filter _) ?_) ?_ ?_
      · intro a h1 h2
        rw [inflow_filter_mem] at h2
        exact not_started_of_inflow G a s _ h2.1
          (mem_queue_present G π s e a (List.mem_of_mem_tail h1)).2
      · refine List.Nodup.filterMap ?_ (G.inc_nodup _)
        intro e1 e2 b h1 h2
        rw [Option.mem_def, fwd_eq_some] at h1 h2
        exact hhead e1 e2 b h1.1 h2.1
      · intro a h1 h2
        rw [List.mem_filterMap] at h2
        obtain ⟨e', -, h2⟩ := h2
        rw [fwd_eq_some] at h2
        rcases List.mem_append.1 h1 with h1 | h1
        · exact hnotail e e' a h2.1 h1
        · rw [inflow_filter_mem] at h1
          exact not_started_of_inflow G a s _ h1.1
            (mem_queue_present G π s e' a (List.mem_of_mem_head? h2.1)).2
    · rw [mem_queue_succ] at h h'
      rcases h with h | ⟨hi, P, hP, hPe⟩ | ⟨f, _, hf1, hf2⟩ <;>
        rcases h' with h' | ⟨hi', P', hP', hPe'⟩ | ⟨f', _, hf1', hf2'⟩
      · exact ihu e e' a (List.mem_of_mem_tail h) (List.mem_of_mem_tail h')
      · exact absurd (mem_queue_present G π s e a (List.mem_of_mem_tail h)).2
          (not_started_of_inflow G a s _ hi')
      · have := ihu e f' a (List.mem_of_mem_tail h) (List.mem_of_mem_head? hf1')
        subst this; exact absurd h (hnotail e e a hf1')
      · exact absurd (mem_queue_present G π s e' a (List.mem_of_mem_tail h')).2
          (not_started_of_inflow G a s _ hi)
      · rw [hP] at hP'; cases hP'; rw [hPe] at hPe'; cases hPe'; rfl
      · exact absurd (mem_queue_present G π s f' a (List.mem_of_mem_head? hf1')).2
          (not_started_of_inflow G a s _ hi)
      · have := ihu e' f a (List.mem_of_mem_tail h') (List.mem_of_mem_head? hf1)
        subst this; exact absurd h' (hnotail e' e' a hf1)
      · exact absurd (mem_queue_present G π s f a (List.mem_of_mem_head? hf1)).2
          (not_started_of_inflow G a s _ hi')
      · have := hhead f f' a hf1 hf1'
        subst this
        rw [hf2] at hf2'; cases hf2'; rfl

end basic

section paths
set_option linter.unusedSectionVars false
variable {tail head : E → V} {d : V} (h : V → ℕ) (hh : ∀ e, h (tail e) < h (head e))
include hh

lemma pt_mem : ∀ (P : List E) (u : V), PathTo tail head d u P → ∀ e ∈ P, h u ≤ h (tail e) := by
  intro P
  induction P with
  | nil => intro u _ e he; simp at he
  | cons x P ih =>
    intro u hp e he
    obtain ⟨hx, hp⟩ := hp
    rcases List.mem_cons.1 he with rfl | he
    · rw [hx]
    · have := ih _ hp e he
      have := hh x
      rw [hx] at this; omega

lemma pt_nodup : ∀ (P : List E) (u : V), PathTo tail head d u P → P.Nodup := by
  intro P
  induction P with
  | nil => intro _ _; exact List.nodup_nil
  | cons x P ih =>
    intro u hp
    obtain ⟨hx, hp'⟩ := hp
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih _ hp'⟩
    have h1 := pt_mem h hh P _ hp' x hmem
    have h2 := hh x
    omega

lemma pt_head_inj : ∀ (P : List E) (u : V), PathTo tail head d u P → ∀ e1 ∈ P, ∀ e2 ∈ P,
    head e1 = head e2 → e1 = e2 := by
  intro P
  induction P with
  | nil => intro _ _ e1 he1; simp at he1
  | cons x P ih =>
    intro u hp e1 he1 e2 he2 heq
    obtain ⟨hx, hp'⟩ := hp
    have key : ∀ f ∈ P, head f ≠ head x := by
      intro f hf hfx
      have := pt_mem h hh P _ hp' f hf
      have := hh f
      rw [hfx] at *; omega
    rcases List.mem_cons.1 he1 with h1 | h1 <;> rcases List.mem_cons.1 he2 with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd heq.symm (key e2 h2)
    · subst h2; exact absurd heq (key e1 h1)
    · exact ih _ hp' e1 h1 e2 h2 heq

lemma pt_start_not_head : ∀ (P : List E) (u : V), PathTo tail head d u P → ∀ e ∈ P,
    head e ≠ u := by
  intro P u hp e he heq
  have := pt_mem h hh P u hp e he
  have := hh e
  rw [heq] at *; omega

lemma pt_next_head : ∀ (P : List E) (u : V), PathTo tail head d u P → ∀ e e2,
    Instance.nextAfter e P = some e2 → head e = tail e2 := by
  intro P
  induction P with
  | nil => intro _ _ e e2 h; simp [Instance.nextAfter] at h
  | cons x P ih =>
    intro u hp e e2 hn
    obtain ⟨hx, hp'⟩ := hp
    simp only [Instance.nextAfter] at hn
    split_ifs at hn with hxe
    · subst hxe
      cases P with
      | nil => simp at hn
      | cons y P => simp at hn; subst hn; exact hp'.1.symm
    · exact ih _ hp' e e2 hn

lemma pt_next_or_last : ∀ (P : List E) (u : V), PathTo tail head d u P → ∀ e ∈ P,
    (∃ e2, Instance.nextAfter e P = some e2) ∨ (Instance.nextAfter e P = none ∧ head e = d) := by
  intro P
  induction P with
  | nil => intro _ _ e he; simp at he
  | cons x P ih =>
    intro u hp e he
    obtain ⟨hx, hp'⟩ := hp
    simp only [Instance.nextAfter]
    by_cases hxe : x = e
    · subst hxe
      rw [if_pos rfl]
      cases P with
      | nil => right; exact ⟨rfl, hp'⟩
      | cons y P => left; exact ⟨y, rfl⟩
    · rw [if_neg hxe]
      rcases List.mem_cons.1 he with rfl | he
      · exact absurd rfl hxe
      · exact ih _ hp' e he

lemma pt_last : ∀ (P : List E) (u : V), PathTo tail head d u P → P ≠ [] → ∃ e ∈ P, head e = d := by
  intro P
  induction P with
  | nil => intro _ _ h; exact absurd rfl h
  | cons e P ih =>
    intro v hp _
    rcases hp with ⟨_, hP⟩
    cases P with
    | nil => exact ⟨e, by simp, hP⟩
    | cons e' P' =>
      obtain ⟨f, hf, hfd⟩ := ih (head e) hP (by simp)
      exact ⟨f, List.mem_cons_of_mem _ hf, hfd⟩

end paths

lemma nextAfter_getElem {E : Type} [DecidableEq E] : ∀ (P : List E), P.Nodup → ∀ (n : ℕ)
    (hn : n + 1 < P.length),
    Instance.nextAfter (P[n]'(by omega)) P = some (P[n + 1]'hn) := by
  intro P
  induction P with
  | nil => intro _ n hn; simp at hn
  | cons x P ih =>
    intro hnd n hn
    rw [List.nodup_cons] at hnd
    cases n with
    | zero =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Instance.nextAfter, if_pos rfl]
      cases P with
      | nil => simp at hn
      | cons y P => simp
    | succ n =>
      simp only [List.getElem_cons_succ, Instance.nextAfter]
      have hne : x ≠ P[n]'(by simp at hn; omega) := by
        intro hx; exact hnd.1 (hx ▸ List.getElem_mem _)
      rw [if_neg hne]
      exact ih hnd.2 n (by simp at hn; omega)

section dyn
variable (G : Instance V E A)

/-- a height function -/
noncomputable def ht : V → ℕ := Classical.choose G.acyclic

lemma ht_lt (e : E) : ht G (G.tail e) < ht G (G.head e) := Classical.choose_spec G.acyclic e

/-- Valid partial profile: each present agent follows one of his strategies. -/
def Valid (π : A → Option (List E)) : Prop := ∀ a P, π a = some P → G.IsStrategy a P

lemma strategy_path (a : A) (P : List E) (h : G.IsStrategy a P) :
    ∃ u n, G.StartsAt a u n ∧ G.IsPathTo u P ∧
      (∀ e, a ∈ G.Q0 e → P.head? = some e) := by
  rcases h with ⟨e, he, hP, hpath⟩ | ⟨r, v, hin, hpath⟩
  · refine ⟨G.tail e, 0, Or.inl ⟨e, he, rfl, rfl⟩, hpath, fun e' he' => ?_⟩
    obtain ⟨s0, -, huniq⟩ := G.partition a
    have h1 : (Sum.inl e : E ⊕ (ℕ × V)) = Sum.inl e' := by
      rw [huniq (Sum.inl e) he, huniq (Sum.inl e') he']
    cases h1; exact hP
  · refine ⟨v, r, Or.inr hin, hpath, fun e' he' => ?_⟩
    obtain ⟨s0, -, huniq⟩ := G.partition a
    have h1 : (Sum.inl e' : E ⊕ (ℕ × V)) = Sum.inr (r, v) := by
      rw [huniq (Sum.inl e') he', huniq (Sum.inr (r, v)) hin]
    cases h1

lemma valid_nodup (π : A → Option (List E)) (hv : Valid G π) : ∀ a P, π a = some P → P.Nodup := by
  intro a P hP
  obtain ⟨u, n, -, hp, -⟩ := strategy_path G a P (hv a P hP)
  exact pt_nodup (ht G) (ht_lt G) P u hp

/-- `Heads π a e s`: agent `a` heads the queue of `e` at time `s`. -/
def Heads (π : A → Option (List E)) (a : A) (e : E) (s : ℕ) : Prop :=
  (G.queue π s e).head? = some a

lemma heads_of_idx (π : A → Option (List E)) :
    ∀ (i s : ℕ) (e : E) (a : A), (G.queue π s e)[i]? = some a → Heads G π a e (s + i) := by
  intro i
  induction i with
  | zero =>
    intro s e a h
    simpa [Heads, List.head?_eq_getElem?] using h
  | succ i ih =>
    intro s e a h
    have h2 : (G.queue π (s + 1) e)[i]? = some a := by
      rw [queue_succ, List.append_assoc, List.getElem?_append_left]
      · rw [List.getElem?_tail]; exact h
      · have := (List.getElem?_eq_some_iff.1 h).1
        simp; omega
    have := ih (s + 1) e a h2
    rwa [show s + 1 + i = s + (i + 1) by omega] at this

lemma heads_of_mem (π : A → Option (List E)) (s : ℕ) (e : E) (a : A)
    (h : a ∈ G.queue π s e) : ∃ i, i < (G.queue π s e).length ∧ Heads G π a e (s + i) := by
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem h
  exact ⟨i, hi, heads_of_idx G π i s e a (by rw [List.getElem?_eq_getElem hi, hia])⟩

lemma heads_mem (π : A → Option (List E)) (a : A) (e : E) (s : ℕ) (h : Heads G π a e s) :
    a ∈ G.queue π s e := List.mem_of_mem_head? h

/-- After heading `e`, an agent only appears on edges of larger tail height. -/
lemma after_heads (π : A → Option (List E)) (hv : Valid G π) (a : A) (e : E) (s : ℕ)
    (hs : Heads G π a e s) :
    ∀ k (e' : E), a ∈ G.queue π (s + 1 + k) e' → ht G (G.head e) ≤ ht G (G.tail e') := by
  have hinv := queue_inv G π (valid_nodup G π hv)
  have hpath : ∀ (f f' : E) (t : ℕ), Heads G π a f t →
      Instance.nextAfter f ((π a).getD []) = some f' → G.head f = G.tail f' := by
    intro f f' t hf hn
    obtain ⟨hsome, -⟩ := mem_queue_present G π t f a (heads_mem G π a f t hf)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hsome
    rw [hP] at hn
    obtain ⟨u, n, -, hp, -⟩ := strategy_path G a P (hv a P hP)
    exact pt_next_head (ht G) (ht_lt G) P u hp f f' hn
  intro k
  induction k with
  | zero =>
    intro e' h'
    rw [Nat.add_zero, mem_queue_succ] at h'
    rcases h' with h' | ⟨hi, -⟩ | ⟨f, _, hf1, hf2⟩
    · have := (hinv s).2 e' e a (List.mem_of_mem_tail h') (heads_mem G π a e s hs)
      subst this
      exfalso
      have hnd := (hinv s).1 e'
      unfold Heads at hs
      cases hq : G.queue π s e' with
      | nil => simp [hq] at hs
      | cons x l =>
        rw [hq] at hs h' hnd
        simp at hs; subst hs
        exact (List.nodup_cons.1 hnd).1 h'
    · exact absurd (mem_queue_present G π s e a (heads_mem G π a e s hs)).2
        (not_started_of_inflow G a s _ hi)
    · have := (hinv s).2 f e a (List.mem_of_mem_head? hf1) (heads_mem G π a e s hs)
      subst this
      rw [hpath f e' s hs hf2]
  | succ k ih =>
    intro e' h'
    rw [show s + 1 + (k + 1) = (s + 1 + k) + 1 by omega, mem_queue_succ] at h'
    rcases h' with h' | ⟨hi, -⟩ | ⟨f, _, hf1, hf2⟩
    · exact ih e' (List.mem_of_mem_tail h')
    · have := (mem_queue_present G π s e a (heads_mem G π a e s hs)).2
      obtain ⟨w, t, ht', hts⟩ := this
      exact absurd ⟨w, t, ht', by omega⟩ (not_started_of_inflow G a _ _ hi)
    · have h1 := ih f (List.mem_of_mem_head? hf1)
      have h2 := hpath f e' _ hf1 hf2
      have h3 := ht_lt G f
      rw [h2] at h3; omega

lemma heads_unique (π : A → Option (List E)) (hv : Valid G π) (a : A) (e : E) (s s' : ℕ)
    (hs : Heads G π a e s) (hs' : Heads G π a e s') : s = s' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := after_heads G π hv a e s hs (s' - s - 1) e
      (by rw [show s + 1 + (s' - s - 1) = s' by omega]; exact heads_mem G π a e s' hs')
    have := ht_lt G e; omega
  · have := after_heads G π hv a e s' hs' (s - s' - 1) e
      (by rw [show s' + 1 + (s - s' - 1) = s by omega]; exact heads_mem G π a e s hs)
    have := ht_lt G e; omega

/-- An agent heading `e` with next edge `e2` is in the queue of `e2` one step later. -/
lemma heads_next (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (e e2 : E) (s : ℕ) (hs : Heads G π a e s)
    (hn : Instance.nextAfter e P = some e2) : a ∈ G.queue π (s + 1) e2 := by
  rw [mem_queue_succ]
  right; right
  obtain ⟨u, n, -, hp, -⟩ := strategy_path G a P (hv a P hP)
  refine ⟨e, pt_next_head (ht G) (ht_lt G) P u hp e e2 hn, hs, by rw [hP]; exact hn⟩

/-- The present agent `a` is in the queue of its first edge at its start time. -/
lemma first_edge (π : A → Option (List E)) (hv : Valid G π) (a : A) (e : E) (P : List E)
    (hP : π a = some (e :: P)) : ∃ u n, G.StartsAt a u n ∧ a ∈ G.queue π n e := by
  have hs := hv a _ hP
  rcases hs with ⟨e0, he0, hh, hpath⟩ | ⟨r, v, hin, hpath⟩
  · simp at hh; subst hh
    refine ⟨G.tail e, 0, Or.inl ⟨e, he0, rfl, rfl⟩, ?_⟩
    rw [queue_zero, List.mem_filter]; exact ⟨he0, by simp [hP]⟩
  · cases r with
    | zero => rw [G.inflow_zero] at hin; simp at hin
    | succ r =>
      refine ⟨v, r + 1, Or.inr hin, ?_⟩
      rw [mem_queue_succ]; right; left
      have : G.tail e = v := hpath.1
      rw [this]; exact ⟨hin, _, hP, rfl⟩

/-- Every edge of a present agent's path is headed by him at some time. -/
lemma heads_exists (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) : ∀ (n : ℕ) (hn : n < P.length), ∃ s, Heads G π a (P[n]'hn) s := by
  intro n
  induction n with
  | zero =>
    intro hn
    cases P with
    | nil => simp at hn
    | cons e P =>
      obtain ⟨u, t, -, hmem⟩ := first_edge G π hv a e P hP
      obtain ⟨i, -, hi⟩ := heads_of_mem G π t e a hmem
      exact ⟨t + i, hi⟩
  | succ n ih =>
    intro hn
    obtain ⟨s, hs⟩ := ih (by omega)
    have hnext := nextAfter_getElem P (valid_nodup G π hv a P hP) n hn
    have hmem := heads_next G π hv a P hP _ _ s hs hnext
    obtain ⟨i, -, hi⟩ := heads_of_mem G π (s + 1) _ a hmem
    exact ⟨s + 1 + i, hi⟩

lemma heads_exists' (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (e : E) (he : e ∈ P) : ∃ s, Heads G π a e s := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
  exact heads_exists G π hv a P hP n hn

/-- Heading an edge implies it is on the agent's path. -/
lemma heads_on_path (π : A → Option (List E)) (hv : Valid G π) :
    ∀ (s : ℕ) (e : E) (a : A), a ∈ G.queue π s e → e ∈ (π a).getD [] := by
  intro s
  induction s with
  | zero =>
    intro e a h
    rw [queue_zero, List.mem_filter] at h
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 (by simpa using h.2)
    obtain ⟨u, n, -, -, hq⟩ := strategy_path G a P (hv a P hP)
    have := hq e h.1
    rw [hP]; simp only [Option.getD_some]
    exact List.mem_of_mem_head? this
  | succ s ih =>
    intro e a h
    rw [mem_queue_succ] at h
    rcases h with h | ⟨-, P, hP, hPe⟩ | ⟨f, -, -, hf⟩
    · exact ih e a (List.mem_of_mem_tail h)
    · rw [hP]; exact List.mem_of_mem_head? hPe
    · exact (nextAfter_mem f _ e hf).2

end dyn


section arrival
variable (G : Instance V E A)

lemma arrival_le_of (π : A → Option (List E)) (a : A) (v : V) (t : ℕ∞)
    (h : (π a).isSome = true ∧ ((∃ n : ℕ, G.StartsAt a v n ∧ t = (n : ℕ∞)) ∨
     ∃ (e : E) (s : ℕ), e ∈ (π a).getD [] ∧ G.head e = v ∧
       (G.queue π s e).head? = some a ∧ t = ((s + 1 : ℕ) : ℕ∞))) :
    G.arrival π a v ≤ t := sInf_le h

lemma le_arrival_of (π : A → Option (List E)) (a : A) (v : V) (t : ℕ∞)
    (h : ∀ x, ((π a).isSome = true ∧ ((∃ n : ℕ, G.StartsAt a v n ∧ x = (n : ℕ∞)) ∨
     ∃ (e : E) (s : ℕ), e ∈ (π a).getD [] ∧ G.head e = v ∧
       (G.queue π s e).head? = some a ∧ x = ((s + 1 : ℕ) : ℕ∞))) → t ≤ x) :
    t ≤ G.arrival π a v := le_sInf h

/-- arrival at the starting vertex is the start time -/
lemma arrival_start (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (u : V) (n : ℕ) (hu : G.StartsAt a u n) : G.arrival π a u = n := by
  obtain ⟨u', n', hu', hp, -⟩ := strategy_path G a P (hv a P hP)
  obtain ⟨rfl, rfl⟩ := startsAt_unique G a _ _ _ _ hu hu'
  apply le_antisymm
  · exact arrival_le_of G π a u _ ⟨by simp [hP], Or.inl ⟨n, hu, rfl⟩⟩
  · apply le_arrival_of
    rintro x ⟨-, ⟨m, hm, rfl⟩ | ⟨e, s, he, hhe, -, -⟩⟩
    · rw [(startsAt_unique G a _ _ _ _ hu hm).2]
    · rw [hP] at he
      exact absurd hhe (pt_start_not_head (ht G) (ht_lt G) P u hp e he)

/-- arrival at the head of an edge of the path -/
lemma arrival_head (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (e : E) (he : e ∈ P) (s : ℕ) (hs : Heads G π a e s) :
    G.arrival π a (G.head e) = ((s + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u', n', hu', hp, -⟩ := strategy_path G a P (hv a P hP)
  apply le_antisymm
  · exact arrival_le_of G π a _ _ ⟨by simp [hP], Or.inr ⟨e, s, by rw [hP]; exact he, rfl, hs, rfl⟩⟩
  · apply le_arrival_of
    rintro x ⟨-, ⟨m, hm, rfl⟩ | ⟨e', s', he', hhe, hs', rfl⟩⟩
    · obtain ⟨h1, -⟩ := startsAt_unique G a _ _ _ _ hm hu'
      exact absurd h1 (pt_start_not_head (ht G) (ht_lt G) P u' hp e he)
    · rw [hP] at he'
      have := pt_head_inj (ht G) (ht_lt G) P u' hp e' he' e he hhe
      subst this
      rw [heads_unique G π hv a e' s s' hs hs']

lemma arrival_absent (π : A → Option (List E)) (a : A) (h : π a = none) (v : V) :
    G.arrival π a v = ⊤ := by
  apply le_antisymm le_top
  apply le_arrival_of
  rintro x ⟨hx, -⟩
  simp [h] at hx

lemma arrival_off (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (v : V) (hv' : ¬ G.OnPath a P v) : G.arrival π a v = ⊤ := by
  apply le_antisymm le_top
  apply le_arrival_of
  rintro x ⟨-, ⟨m, hm, rfl⟩ | ⟨e', s', he', hhe, hs', rfl⟩⟩
  · exact absurd (Or.inl ⟨m, hm⟩) hv'
  · rw [hP] at he'
    exact absurd (Or.inr ⟨e', he', hhe⟩) hv'

lemma onPath_d (a : A) (P : List E) (h : G.IsStrategy a P) : G.OnPath a P G.d := by
  obtain ⟨u, n, hu, hp, -⟩ := strategy_path G a P h
  by_cases hP : P = []
  · subst hP
    have : u = G.d := hp
    subst this
    exact Or.inl ⟨n, hu⟩
  · exact Or.inr (pt_last (ht G) (ht_lt G) P u hp hP)

/-- The arrival time at a vertex of the path is finite, and at least the start time. -/
lemma arrival_onPath (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (v : V) (hv' : G.OnPath a P v) :
    ∃ t : ℕ, G.arrival π a v = t ∧ ∀ u n, G.StartsAt a u n → n ≤ t := by
  rcases hv' with ⟨n, hn⟩ | ⟨e, he, rfl⟩
  · refine ⟨n, arrival_start G π hv a P hP v n hn, fun u m hm => ?_⟩
    rw [(startsAt_unique G a _ _ _ _ hm hn).2]
  · obtain ⟨s, hs⟩ := heads_exists' G π hv a P hP e he
    refine ⟨s + 1, arrival_head G π hv a P hP e he s hs, fun u m hm => ?_⟩
    obtain ⟨-, w, t, hw, hts⟩ := mem_queue_present G π s e a (heads_mem G π a e s hs)
    rw [(startsAt_unique G a _ _ _ _ hm hw).2]; omega

variable [DecidableEq A]

/-- agents started by time `t` -/
def AgentsBy (t : ℕ) : Finset A :=
  (Finset.univ : Finset E).biUnion (fun e => (G.Q0 e).toFinset) ∪
  ((Finset.range (t + 1)) ×ˢ (Finset.univ : Finset V)).biUnion
    (fun rv => (G.inflow rv.1 rv.2).toFinset)

lemma mem_agentsBy (a : A) (t : ℕ) (h : Started G a t) : a ∈ AgentsBy G t := by
  obtain ⟨v, n, hn, hnt⟩ := h
  unfold AgentsBy
  rw [Finset.mem_union]
  rcases hn with ⟨e, he, -, -⟩ | hn
  · left; rw [Finset.mem_biUnion]; exact ⟨e, Finset.mem_univ _, List.mem_toFinset.2 he⟩
  · right; rw [Finset.mem_biUnion]
    exact ⟨(n, v), Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_univ _⟩,
      List.mem_toFinset.2 hn⟩

lemma agentsBy_mono {t t' : ℕ} (h : t ≤ t') : AgentsBy G t ⊆ AgentsBy G t' := by
  intro a ha
  unfold AgentsBy at *
  rw [Finset.mem_union] at *
  rcases ha with ha | ha
  · exact Or.inl ha
  · right
    rw [Finset.mem_biUnion] at *
    obtain ⟨rv, hrv, h2⟩ := ha
    rw [Finset.mem_product, Finset.mem_range] at hrv
    exact ⟨rv, Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), hrv.2⟩, h2⟩

lemma queue_length_le (π : A → Option (List E)) (hv : Valid G π) (s : ℕ) (e : E) :
    (G.queue π s e).length ≤ (AgentsBy G s).card := by
  have hnd := (queue_inv G π (valid_nodup G π hv) s).1 e
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro a ha
  exact mem_agentsBy G a s (mem_queue_present G π s e a (List.mem_toFinset.1 ha)).2

/-- one-step bound -/
def bstep (t : ℕ) : ℕ := t + (AgentsBy G t).card

lemma bstep_mono : Monotone (bstep G) := by
  intro t t' h
  unfold bstep
  have := Finset.card_le_card (agentsBy_mono G h)
  omega

lemma bstep_ge (t : ℕ) : t ≤ bstep G t := by unfold bstep; omega

lemma iter_mono_n (t : ℕ) : ∀ m n, m ≤ n → (bstep G)^[m] t ≤ (bstep G)^[n] t := by
  intro m n hmn
  induction n with
  | zero => rw [Nat.le_zero.1 hmn]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hmn with h | h
    · rw [Function.iterate_succ_apply']
      exact le_trans (ih (by omega)) (bstep_ge G _)
    · rw [h]

lemma iter_mono_t (n : ℕ) : Monotone ((bstep G)^[n]) := (bstep_mono G).iterate n

/-- The heading time of the `n`-th edge is bounded by the `n+1`-th iterate of `bstep`. -/
lemma heads_bound (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (u : V) (t0 : ℕ) (hu : G.StartsAt a u t0) :
    ∀ (n : ℕ) (hn : n < P.length), ∃ s, Heads G π a (P[n]'hn) s ∧ s + 1 ≤ (bstep G)^[n+1] t0 := by
  intro n
  induction n with
  | zero =>
    intro hn
    cases P with
    | nil => simp at hn
    | cons e P =>
      obtain ⟨u', t, ht', hmem⟩ := first_edge G π hv a e P hP
      obtain ⟨-, rfl⟩ := startsAt_unique G a _ _ _ _ hu ht'
      obtain ⟨i, hi, hh⟩ := heads_of_mem G π t0 e a hmem
      have hl := queue_length_le G π hv t0 e
      refine ⟨t0 + i, hh, ?_⟩
      simp only [zero_add, Function.iterate_one, bstep]
      omega
  | succ n ih =>
    intro hn
    obtain ⟨s, hs, hsb⟩ := ih (by omega)
    have hnext := nextAfter_getElem P (valid_nodup G π hv a P hP) n hn
    have hmem := heads_next G π hv a P hP _ _ s hs hnext
    obtain ⟨i, hi, hh⟩ := heads_of_mem G π (s + 1) _ a hmem
    have hl := queue_length_le G π hv (s + 1) (P[n + 1])
    refine ⟨s + 1 + i, hh, ?_⟩
    rw [Function.iterate_succ_apply']
    have := bstep_mono G hsb
    simp only [bstep] at this ⊢
    omega

/-- Uniform bound on the arrival time at `d`. -/
lemma arrival_d_le (π : A → Option (List E)) (hv : Valid G π) (a : A) (P : List E)
    (hP : π a = some P) (u : V) (t0 : ℕ) (hu : G.StartsAt a u t0) :
    G.arrival π a G.d ≤ (((bstep G)^[Fintype.card E] t0 : ℕ) : ℕ∞) := by
  obtain ⟨u', n', hu', hp, -⟩ := strategy_path G a P (hv a P hP)
  obtain ⟨rfl, rfl⟩ := startsAt_unique G a _ _ _ _ hu hu'
  by_cases hP0 : P = []
  · subst hP0
    have : u = G.d := hp
    subst this
    rw [arrival_start G π hv a [] hP _ _ hu]
    exact_mod_cast iter_mono_n G t0 0 _ (Nat.zero_le _)
  · obtain ⟨e, he, hed⟩ := pt_last (ht G) (ht_lt G) P u hp hP0
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    obtain ⟨s, hs, hsb⟩ := heads_bound G π hv a P hP u t0 hu n hn
    rw [← hed, arrival_head G π hv a P hP _ he s hs]
    have hlen : P.length ≤ Fintype.card E := (valid_nodup G π hv a P hP).length_le_card
    have := iter_mono_n G t0 (n + 1) (Fintype.card E) (by omega)
    exact_mod_cast le_trans hsb this

end arrival

end ADFF


open AtomicDynFlow.IDNE

namespace ADFF

section pairs
variable {α : Type}

lemma pair_sub_cons (a b x : α) (l : List α) :
    [a, b].Sublist (x :: l) ↔ [a, b].Sublist l ∨ (a = x ∧ b ∈ l) := by
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, hr2⟩)
    · exact Or.inl h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inr ⟨rfl, List.singleton_sublist.1 hr2⟩
  · rintro (h | ⟨rfl, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.2 hb⟩

lemma pair_sub_mem {a b : α} {l : List α} (h : [a, b].Sublist l) : a ∈ l ∧ b ∈ l :=
  ⟨h.subset (by simp), h.subset (by simp)⟩

lemma pair_sub_asymm (a b : α) : ∀ (l : List α), l.Nodup → [a, b].Sublist l →
    [b, a].Sublist l → False := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons x l ih =>
    intro hnd h1 h2
    rw [List.nodup_cons] at hnd
    rw [pair_sub_cons] at h1 h2
    rcases h1 with h1 | ⟨rfl, hb⟩ <;> rcases h2 with h2 | ⟨hbx, ha⟩
    · exact ih hnd.2 h1 h2
    · subst hbx; exact hnd.1 (pair_sub_mem h1).2
    · exact hnd.1 (pair_sub_mem h2).2
    · exact hnd.1 ha

lemma pair_sub_trans (a b c : α) : ∀ (l : List α), l.Nodup → [a, b].Sublist l →
    [b, c].Sublist l → [a, c].Sublist l := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons x l ih =>
    intro hnd h1 h2
    rw [List.nodup_cons] at hnd
    rw [pair_sub_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, hb⟩ <;> rcases h2 with h2 | ⟨hbx, hc⟩
    · exact Or.inl (ih hnd.2 h1 h2)
    · subst hbx; exact absurd (pair_sub_mem h1).2 hnd.1
    · exact Or.inr ⟨rfl, (pair_sub_mem h2).2⟩
    · subst hbx; exact absurd hb hnd.1

lemma pair_sub_total (a b : α) (hab : a ≠ b) : ∀ (l : List α), a ∈ l → b ∈ l →
    [a, b].Sublist l ∨ [b, a].Sublist l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x l ih =>
    intro ha hb
    rw [pair_sub_cons, pair_sub_cons]
    rcases List.mem_cons.1 ha with h1 | ha <;> rcases List.mem_cons.1 hb with h2 | hb
    · exact absurd (h1.trans h2.symm) hab
    · exact Or.inl (Or.inr ⟨h1, hb⟩)
    · exact Or.inr (Or.inr ⟨h2, ha⟩)
    · rcases ih ha hb with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)

end pairs

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq A]

section before
variable (G : Instance V E A)

lemma src_unique (a : A) (s1 s2 : E ⊕ (ℕ × V)) (h1 : a ∈ srcList G.Q0 G.inflow s1)
    (h2 : a ∈ srcList G.Q0 G.inflow s2) : s1 = s2 := by
  obtain ⟨s0, -, huniq⟩ := G.partition a
  rw [huniq s1 h1, huniq s2 h2]

variable (φ : A → Option (List E)) (j : A) (P : List E) (i : A) (Q : List E)

lemma before_nil_nil (u : V) : G.Before φ j P i Q u [] [] ↔
    (G.arrival (Function.update φ j (some P)) j u < G.arrival (Function.update φ i (some Q)) i u ∨
    (G.arrival (Function.update φ j (some P)) j u = G.arrival (Function.update φ i (some Q)) i u ∧
      ∃ s, List.Sublist [j, i] (srcList G.Q0 G.inflow s))) := by
  rw [Instance.Before]

lemma before_nil_cons (u : V) (e : E) (r : List E) : G.Before φ j P i Q u [] (e :: r) ↔
    (G.arrival (Function.update φ j (some P)) j u ≤
      G.arrival (Function.update φ i (some Q)) i u) := by
  rw [Instance.Before]
  simp only [and_true]
  exact le_iff_lt_or_eq.symm

lemma before_cons_nil (u : V) (e : E) (r : List E) : G.Before φ j P i Q u (e :: r) [] ↔
    (G.arrival (Function.update φ j (some P)) j u <
      G.arrival (Function.update φ i (some Q)) i u) := by
  rw [Instance.Before]
  simp

lemma before_cons_cons (u : V) (e e' : E) (r r' : List E) :
    G.Before φ j P i Q u (e :: r) (e' :: r') ↔
    (G.arrival (Function.update φ j (some P)) j u < G.arrival (Function.update φ i (some Q)) i u ∨
    (G.arrival (Function.update φ j (some P)) j u = G.arrival (Function.update φ i (some Q)) i u ∧
      (G.incRank e < G.incRank e' ∨ (e = e' ∧ G.Before φ j P i Q (G.tail e) r r')))) := by
  rw [Instance.Before]

lemma before_le (u : V) (rp rq : List E) (h : G.Before φ j P i Q u rp rq) :
    G.arrival (Function.update φ j (some P)) j u ≤
      G.arrival (Function.update φ i (some Q)) i u := by
  cases rp with
  | nil =>
    cases rq with
    | nil =>
      rw [before_nil_nil] at h
      rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    | cons e r => rwa [before_nil_cons] at h
  | cons e r =>
    cases rq with
    | nil => rw [before_cons_nil] at h; exact h.le
    | cons e' r' =>
      rw [before_cons_cons] at h
      rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.le

end before

section order
variable (G : Instance V E A) (φ : A → Option (List E))

lemma before_asymm (j : A) (P : List E) (i : A) (Q : List E) :
    ∀ (rp rq : List E) (u : V), G.Before φ j P i Q u rp rq → G.Before φ i Q j P u rq rp → False := by
  intro rp
  induction rp with
  | nil =>
    intro rq u h1 h2
    cases rq with
    | nil =>
      rw [before_nil_nil] at h1 h2
      rcases h1 with h1 | ⟨h1, s1, hs1⟩ <;> rcases h2 with h2 | ⟨h2, s2, hs2⟩
      · exact lt_asymm h1 h2
      · exact absurd h2 (ne_of_gt h1)
      · exact absurd h1 (ne_of_gt h2)
      · have := src_unique G j s1 s2 (pair_sub_mem hs1).1 (pair_sub_mem hs2).2
        subst this
        exact pair_sub_asymm j i _ (G.nodup s1) hs1 hs2
    | cons e r =>
      rw [before_nil_cons] at h1
      rw [before_cons_nil] at h2
      exact absurd h1 (not_le.2 h2)
  | cons e r ih =>
    intro rq u h1 h2
    cases rq with
    | nil =>
      rw [before_cons_nil] at h1
      rw [before_nil_cons] at h2
      exact absurd h2 (not_le.2 h1)
    | cons e' r' =>
      rw [before_cons_cons] at h1 h2
      rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
      · exact lt_asymm h1 h2
      · exact absurd h2 (ne_of_gt h1)
      · exact absurd h1 (ne_of_gt h2)
      · rcases h1' with h1' | ⟨rfl, h1'⟩ <;> rcases h2' with h2' | ⟨h3, h2'⟩
        · omega
        · subst h3; omega
        · omega
        · exact ih r' _ h1' h2'

lemma before_trans (j : A) (P : List E) (i : A) (Q : List E) (k : A) (R : List E) :
    ∀ (rp rq rr : List E) (u : V), G.Before φ j P i Q u rp rq → G.Before φ i Q k R u rq rr →
      G.Before φ j P k R u rp rr := by
  intro rp
  induction rp with
  | nil =>
    intro rq rr u h1 h2
    cases rq with
    | nil =>
      cases rr with
      | nil =>
        rw [before_nil_nil] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, s1, hs1⟩ <;> rcases h2 with h2 | ⟨h2, s2, hs2⟩
        · exact Or.inl (lt_trans h1 h2)
        · exact Or.inl (h2 ▸ h1)
        · exact Or.inl (h1 ▸ h2)
        · refine Or.inr ⟨h1.trans h2, s1, ?_⟩
          have := src_unique G i s1 s2 (pair_sub_mem hs1).2 (pair_sub_mem hs2).1
          subst this
          exact pair_sub_trans j i k _ (G.nodup s1) hs1 hs2
      | cons e r =>
        rw [before_nil_cons]
        exact le_trans (before_le G φ _ _ _ _ _ _ _ h1) (before_le G φ _ _ _ _ _ _ _ h2)
    | cons e r =>
      cases rr with
      | nil =>
        rw [before_cons_nil] at h2
        rw [before_nil_cons] at h1
        rw [before_nil_nil]
        exact Or.inl (lt_of_le_of_lt h1 h2)
      | cons e' r' =>
        rw [before_nil_cons]
        exact le_trans (before_le G φ _ _ _ _ _ _ _ h1) (before_le G φ _ _ _ _ _ _ _ h2)
  | cons e r ih =>
    intro rq rr u h1 h2
    cases rq with
    | nil =>
      rw [before_cons_nil] at h1
      cases rr with
      | nil =>
        rw [before_cons_nil]
        exact lt_of_lt_of_le h1 (before_le G φ _ _ _ _ _ _ _ h2)
      | cons e' r' =>
        rw [before_nil_cons] at h2
        rw [before_cons_cons]
        exact Or.inl (lt_of_lt_of_le h1 h2)
    | cons e1 r1 =>
      cases rr with
      | nil =>
        rw [before_cons_nil] at h2 ⊢
        exact lt_of_le_of_lt (before_le G φ _ _ _ _ _ _ _ h1) h2
      | cons e2 r2 =>
        rw [before_cons_cons] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
        · exact Or.inl (lt_trans h1 h2)
        · exact Or.inl (h2 ▸ h1)
        · exact Or.inl (h1 ▸ h2)
        · refine Or.inr ⟨h1.trans h2, ?_⟩
          rcases h1' with h1' | ⟨rfl, h1'⟩ <;> rcases h2' with h2' | ⟨h3, h2'⟩
          · exact Or.inl (lt_trans h1' h2')
          · subst h3; exact Or.inl h1'
          · exact Or.inl h2'
          · subst h3; exact Or.inr ⟨rfl, ih r1 r2 _ h1' h2'⟩

end order

section total
variable (G : Instance V E A)

lemma pt_start_unique : ∀ (P : List E) (u u' : V), PathTo G.tail G.head G.d u P →
    PathTo G.tail G.head G.d u' P → u = u' := by
  intro P u u' h1 h2
  cases P with
  | nil => exact (show u = G.d from h1).trans (show u' = G.d from h2).symm
  | cons e P => exact h1.1.symm.trans h2.1

lemma pt_split : ∀ (L : List E) (w : V) (e : E) (S : List E),
    PathTo G.tail G.head G.d w (L ++ e :: S) → PathTo G.tail G.head G.d (G.head e) S := by
  intro L
  induction L with
  | nil => intro w e S h; exact h.2
  | cons x L ih => intro w e S h; exact ih _ e S h.2

lemma valid_update (φ : A → Option (List E)) (hφ : Valid G φ) (j : A) (P : List E)
    (hP : G.IsStrategy j P) : Valid G (Function.update φ j (some P)) := by
  intro a R hR
  by_cases haj : a = j
  · subst haj; simp at hR; subst hR; exact hP
  · rw [Function.update_of_ne haj] at hR; exact hφ a R hR

lemma before_total (φ : A → Option (List E)) (hφ : Valid G φ) (j : A) (P : List E) (i : A)
    (Q : List E) (hjP : G.IsStrategy j P) (hiQ : G.IsStrategy i Q) (hne : (i, Q) ≠ (j, P)) :
    ∀ (rp rq S : List E) (u : V), P = rp.reverse ++ S → Q = rq.reverse ++ S →
      PathTo G.tail G.head G.d u S →
      G.Before φ j P i Q u rp rq ∨ G.Before φ i Q j P u rq rp := by
  have hvj := valid_update G φ hφ j P hjP
  have hvi := valid_update G φ hφ i Q hiQ
  intro rp
  induction rp with
  | nil =>
    intro rq S u hP hQ hS
    cases rq with
    | nil =>
      simp only [List.reverse_nil, List.nil_append] at hP hQ
      rw [← hP] at hS
      have hQP : Q = P := hQ.trans hP.symm
      subst hQP
      have hji : j ≠ i := by rintro rfl; exact hne rfl
      obtain ⟨uj, nj, hsj, hpj, hq0j⟩ := strategy_path G j Q hjP
      obtain ⟨ui, ni, hsi, hpi, hq0i⟩ := strategy_path G i Q hiQ
      have e1 := pt_start_unique G Q u uj hS hpj
      have e2 := pt_start_unique G Q u ui hS hpi
      subst e1; subst e2
      have tj := arrival_start G _ hvj j Q (by simp) u nj hsj
      have ti := arrival_start G _ hvi i Q (by simp) u ni hsi
      rw [before_nil_nil, before_nil_nil, tj, ti]
      rcases lt_trichotomy nj ni with h | h | h
      · exact Or.inl (Or.inl (by exact_mod_cast h))
      · subst h
        -- same source
        have hsrc : ∃ s, j ∈ srcList G.Q0 G.inflow s ∧ i ∈ srcList G.Q0 G.inflow s := by
          rcases hsj with ⟨ej, hej, -, hn0⟩ | hinj <;> rcases hsi with ⟨ei, hei, -, hn1⟩ | hini
          · have h1 := hq0j ej hej
            have h2 := hq0i ei hei
            rw [h1] at h2; cases h2
            exact ⟨Sum.inl ej, hej, hei⟩
          · rw [hn0, G.inflow_zero] at hini; simp at hini
          · rw [hn1, G.inflow_zero] at hinj; simp at hinj
          · exact ⟨Sum.inr (nj, u), hinj, hini⟩
        obtain ⟨s, hjs, his⟩ := hsrc
        rcases pair_sub_total j i hji _ hjs his with h | h
        · exact Or.inl (Or.inr ⟨rfl, s, h⟩)
        · exact Or.inr (Or.inr ⟨rfl, s, h⟩)
      · exact Or.inr (Or.inl (by exact_mod_cast h))
    | cons e r =>
      rw [before_nil_cons, before_cons_nil]
      exact le_or_gt _ _
  | cons e r ih =>
    intro rq S u hP hQ hS
    cases rq with
    | nil =>
      rw [before_nil_cons, before_cons_nil]
      exact (le_or_gt _ _).symm.imp id id |>.elim (fun h => Or.inl h) (fun h => Or.inr h)
    | cons e' r' =>
      rw [before_cons_cons, before_cons_cons]
      rcases lt_trichotomy (G.arrival (Function.update φ j (some P)) j u)
        (G.arrival (Function.update φ i (some Q)) i u) with h | h | h
      · exact Or.inl (Or.inl h)
      · have hP' : P = r.reverse ++ e :: S := by simp [hP]
        have hQ' : Q = r'.reverse ++ e' :: S := by simp [hQ]
        obtain ⟨uj, nj, -, hpj, -⟩ := strategy_path G j P hjP
        obtain ⟨ui, ni, -, hpi, -⟩ := strategy_path G i Q hiQ
        have hpe := pt_split G r.reverse uj e S (hP' ▸ hpj)
        have hpe' := pt_split G r'.reverse ui e' S (hQ' ▸ hpi)
        have he := pt_start_unique G S _ _ hpe hS
        have he' := pt_start_unique G S _ _ hpe' hS
        rcases lt_trichotomy (G.incRank e) (G.incRank e') with h2 | h2 | h2
        · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
        · have hee : e = e' := by
            unfold Instance.incRank at h2
            rw [he, he'] at h2
            exact (List.idxOf_inj ((G.inc_mem u e).2 he)).1 h2
          subst hee
          have hS' : PathTo G.tail G.head G.d (G.tail e) (e :: S) := ⟨rfl, he ▸ hS⟩
          rcases ih r' (e :: S) (G.tail e) hP' hQ' hS' with h3 | h3
          · exact Or.inl (Or.inr ⟨h, Or.inr ⟨rfl, h3⟩⟩)
          · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨rfl, h3⟩⟩)
        · exact Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩)
      · exact Or.inr (Or.inl h)

end total

section exists_sel
variable (G : Instance V E A)

lemma strategy_exists (a : A) : ∃ P, G.IsStrategy a P := by
  obtain ⟨s, hs, -⟩ := G.partition a
  rcases s with e | ⟨r, v⟩
  · obtain ⟨P', hP'⟩ := G.reach (G.head e)
    exact ⟨e :: P', Or.inl ⟨e, hs, rfl, rfl, hP'⟩⟩
  · obtain ⟨P', hP'⟩ := G.reach v
    exact ⟨P', Or.inr ⟨r, v, hs, hP'⟩⟩

lemma before_of_lt (φ : A → Option (List E)) (j : A) (P : List E) (i : A) (Q : List E) (u : V)
    (rp rq : List E)
    (h : G.arrival (Function.update φ j (some P)) j u <
      G.arrival (Function.update φ i (some Q)) i u) : G.Before φ j P i Q u rp rq := by
  cases rp with
  | nil =>
    cases rq with
    | nil => rw [before_nil_nil]; exact Or.inl h
    | cons e r => rw [before_nil_cons]; exact h.le
  | cons e r =>
    cases rq with
    | nil => rw [before_cons_nil]; exact h
    | cons e' r' => rw [before_cons_cons]; exact Or.inl h

theorem select_exists_unique (φ : A → Option (List E)) (hφ : Valid G φ)
    (hrem : ∃ j, φ j = none) : ∃! jP : A × List E, G.IsSelected φ jP.1 jP.2 := by
  classical
  let R : A × List E → A × List E → Prop := fun x y =>
    G.Before φ x.1 x.2 y.1 y.2 G.d x.2.reverse y.2.reverse
  let Cand : A × List E → Prop := fun x => φ x.1 = none ∧ G.IsStrategy x.1 x.2
  have hasymm : ∀ x y, R x y → R y x → False := fun x y h1 h2 =>
    before_asymm G φ x.1 x.2 y.1 y.2 _ _ _ h1 h2
  have htrans : ∀ x y z, R x y → R y z → R x z := fun x y z h1 h2 =>
    before_trans G φ x.1 x.2 y.1 y.2 z.1 z.2 _ _ _ _ h1 h2
  have htotal : ∀ x y, Cand x → Cand y → x ≠ y → R x y ∨ R y x := by
    intro x y hx hy hxy
    exact before_total G φ hφ x.1 x.2 y.1 y.2 hx.2 hy.2 (fun h => hxy h.symm) _ _ [] G.d
      (by simp) (by simp) (show G.d = G.d from rfl)
  obtain ⟨j0, hj0⟩ := hrem
  obtain ⟨P0, hP0⟩ := strategy_exists G j0
  have hv0 := valid_update G φ hφ j0 P0 hP0
  obtain ⟨T0, hT0, -⟩ := arrival_onPath G _ hv0 j0 P0 (by simp) G.d (onPath_d G j0 P0 hP0)
  let F : Set (A × List E) := {x | Cand x ∧ x.1 ∈ AgentsBy G T0 ∧ x.2.length ≤ Fintype.card E}
  have hFfin : F.Finite := by
    apply Set.Finite.subset (((AgentsBy G T0 : Finset A) : Set A).toFinite.prod
      (List.finite_length_le E (Fintype.card E)))
    rintro x ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  have hlen : ∀ a P, G.IsStrategy a P → P.length ≤ Fintype.card E := by
    intro a P h
    obtain ⟨u, n, -, hp, -⟩ := strategy_path G a P h
    exact (pt_nodup (ht G) (ht_lt G) P u hp).length_le_card
  have hc0 : (j0, P0) ∈ F := by
    refine ⟨⟨hj0, hP0⟩, ?_, hlen _ _ hP0⟩
    obtain ⟨u, n, hu, -, -⟩ := strategy_path G j0 P0 hP0
    obtain ⟨t, ht', hst⟩ := arrival_onPath G _ hv0 j0 P0 (by simp) G.d (onPath_d G j0 P0 hP0)
    rw [hT0] at ht'
    have : t = T0 := by exact_mod_cast ht'.symm
    exact mem_agentsBy G j0 T0 ⟨u, n, hu, this ▸ hst u n hu⟩
  -- outside `F`, candidates lose to `(j0, P0)`
  have hout : ∀ x, Cand x → x ∉ F → R (j0, P0) x := by
    intro x hx hxF
    have hnot : x.1 ∉ AgentsBy G T0 := fun h => hxF ⟨hx, h, hlen _ _ hx.2⟩
    obtain ⟨u, n, hu, -, -⟩ := strategy_path G x.1 x.2 hx.2
    have hvx := valid_update G φ hφ x.1 x.2 hx.2
    obtain ⟨t, ht', hst⟩ := arrival_onPath G _ hvx x.1 x.2 (by simp) G.d (onPath_d G _ _ hx.2)
    have hnT : T0 < n := by
      by_contra hc
      exact hnot (mem_agentsBy G _ T0 ⟨u, n, hu, by omega⟩)
    apply before_of_lt
    show G.arrival (Function.update φ j0 (some P0)) j0 G.d <
      G.arrival (Function.update φ x.1 (some x.2)) x.1 G.d
    rw [hT0, ht']
    have := hst u n hu
    exact_mod_cast (by omega : T0 < t)
  haveI : Finite F := hFfin.to_subtype
  let R' : F → F → Prop := fun a b => R a.1 b.1
  haveI : IsTrans F R' := ⟨fun a b c h1 h2 => htrans _ _ _ h1 h2⟩
  haveI : Std.Irrefl R' := ⟨fun a h => hasymm _ _ h h⟩
  have hwf : WellFounded R' := Finite.wellFounded_of_trans_of_irrefl R'
  obtain ⟨m, -, hm⟩ := hwf.has_min Set.univ ⟨⟨_, hc0⟩, Set.mem_univ _⟩
  have hmin : ∀ x, Cand x → x ≠ m.1 → R m.1 x := by
    intro x hx hxm
    by_cases hxF : x ∈ F
    · rcases htotal m.1 x m.2.1 hx (Ne.symm hxm) with h | h
      · exact h
      · exact absurd h (hm ⟨x, hxF⟩ (Set.mem_univ _))
    · have h0 := hout x hx hxF
      by_cases hm0 : m.1 = (j0, P0)
      · rw [hm0]; exact h0
      · rcases htotal m.1 (j0, P0) m.2.1 ⟨hj0, hP0⟩ hm0 with h | h
        · exact htrans _ _ _ h h0
        · exact absurd h (hm ⟨_, hc0⟩ (Set.mem_univ _))
  refine ⟨m.1, ⟨m.2.1.1, m.2.1.2, fun i Q hi hQ hne => hmin (i, Q) ⟨hi, hQ⟩ hne⟩, ?_⟩
  rintro y ⟨hy1, hy2, hy3⟩
  by_contra hym
  have h1 := hmin y ⟨hy1, hy2⟩ hym
  have h2 := hy3 m.1.1 m.1.2 m.2.1.1 m.2.1.2 (fun h => hym h.symm)
  exact hasymm _ _ h1 h2

end exists_sel

section pfx
variable (G : Instance V E A)

lemma pp_some : ∀ (L : List (A × List E)) (a : A) (P : List E), prefixProfile L a = some P →
    (a, P) ∈ L := by
  intro L
  induction L with
  | nil => intro a P h; simp [prefixProfile] at h
  | cons x L ih =>
    intro a P h
    obtain ⟨b, R⟩ := x
    simp only [prefixProfile] at h
    split_ifs at h with hab
    · cases h; subst hab; simp
    · exact List.mem_cons_of_mem _ (ih a P h)

lemma pp_none_iff : ∀ (L : List (A × List E)) (a : A),
    prefixProfile L a = none ↔ a ∉ L.map Prod.fst := by
  intro L
  induction L with
  | nil => intro a; simp [prefixProfile]
  | cons x L ih =>
    intro a
    obtain ⟨b, R⟩ := x
    simp only [prefixProfile, List.map_cons, List.mem_cons, not_or]
    split_ifs with hab
    · simp [hab]
    · rw [ih a]; simp [hab]

lemma valid_pp (L : List (A × List E)) (hL : G.IsSpecialPrefix L) :
    Valid G (prefixProfile L) := by
  intro a P h
  obtain ⟨n, hn, hx⟩ := List.getElem_of_mem (pp_some L a P h)
  have := (hL n hn).2.1
  rw [hx] at this
  exact this

end pfx

end ADFF


open AtomicDynFlow.IDNE

namespace ADFF

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq A]

section seq
variable (G : Instance V E A)

lemma ppe (p : A → List E) :
    ∀ (L : List (A × List E)), (∀ y ∈ L, y.2 = p y.1) → ∀ x,
      prefixProfile L x = if x ∈ L.map Prod.fst then some (p x) else none := by
  intro L
  induction L with
  | nil => intro _ x; simp [prefixProfile]
  | cons y L ih =>
    intro hL x
    obtain ⟨b, P⟩ := y
    have hb : P = p b := hL (b, P) (by simp)
    have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)) x
    by_cases hxb : x = b
    · subst hxb; simp [prefixProfile, hb]
    · have e1 : prefixProfile ((b, P) :: L) x = prefixProfile L x := by
        simp [prefixProfile, hxb]
      have e2 : (x ∈ ((b, P) :: L).map Prod.fst) ↔ x ∈ L.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons, hxb, false_or]
      rw [e1, ih']
      exact if_congr e2.symm rfl rfl

lemma sp_append (L : List (A × List E)) (hL : G.IsSpecialPrefix L) (x : A × List E)
    (hx : G.IsSelected (prefixProfile L) x.1 x.2) : G.IsSpecialPrefix (L ++ [x]) := by
  intro n hn
  rw [List.length_append, List.length_singleton] at hn
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hn) with h | h
  · rw [List.take_append_of_le_length h.le, List.getElem_append_left h]
    exact hL n h
  · subst h
    rw [List.take_left' rfl, List.getElem_append_right (le_refl _)]
    simpa using hx

/-- the condition for one more iteration -/
def Cond (L : List (A × List E)) : Prop := G.IsSpecialPrefix L ∧ ∃ j, j ∉ L.map Prod.fst

lemma cond_sel (L : List (A × List E)) (h : Cond G L) :
    ∃ jP : A × List E, G.IsSelected (prefixProfile L) jP.1 jP.2 := by
  obtain ⟨j, hj⟩ := h.2
  exact (select_exists_unique G (prefixProfile L) (valid_pp G L h.1)
    ⟨j, (pp_none_iff L j).2 hj⟩).exists

noncomputable def step (L : List (A × List E)) : List (A × List E) := by
  classical
  exact if h : Cond G L then L ++ [Classical.choose (cond_sel G L h)] else L

noncomputable def seqL : ℕ → List (A × List E)
  | 0 => []
  | n + 1 => step G (seqL n)

lemma step_prefix (L : List (A × List E)) : L <+: step G L := by
  unfold step
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

lemma seq_prefix (n : ℕ) : ∀ k, seqL G n <+: seqL G (n + k) := by
  intro k
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (step_prefix G _)

lemma seq_prefix_le {n m : ℕ} (h : n ≤ m) : seqL G n <+: seqL G m := by
  have := seq_prefix G n (m - n)
  rwa [Nat.add_sub_cancel' h] at this

lemma seq_coh (n m i : ℕ) (hn : i < (seqL G n).length) (hm : i < (seqL G m).length) :
    (seqL G n)[i] = (seqL G m)[i] := by
  rcases le_total n m with h | h
  · exact (seq_prefix_le G h).getElem hn
  · exact ((seq_prefix_le G h).getElem hm).symm

lemma seq_special : ∀ n, G.IsSpecialPrefix (seqL G n) := by
  intro n
  induction n with
  | zero => intro m hm; simp [seqL] at hm
  | succ n ih =>
    show G.IsSpecialPrefix (step G (seqL G n))
    unfold step
    split_ifs with h
    · exact sp_append G _ ih _ (Classical.choose_spec (cond_sel G _ h))
    · exact ih

lemma seq_nodup : ∀ n, ((seqL G n).map Prod.fst).Nodup := by
  intro n
  induction n with
  | zero => simp [seqL]
  | succ n ih =>
    show ((step G (seqL G n)).map Prod.fst).Nodup
    unfold step
    split_ifs with h
    · rw [List.map_append, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      have hs := Classical.choose_spec (cond_sel G _ h)
      have hnone := hs.1
      rw [pp_none_iff] at hnone
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      rintro rfl
      exact hnone (hb ▸ ha)
    · exact ih

lemma seq_len_of_absent (a : A) (ha : ∀ n, a ∉ (seqL G n).map Prod.fst) :
    ∀ n, (seqL G n).length = n := by
  intro n
  induction n with
  | zero => simp [seqL]
  | succ n ih =>
    show (step G (seqL G n)).length = n + 1
    unfold step
    rw [dif_pos ⟨seq_special G n, a, ha n⟩]
    simp [ih]

/-- Every agent is eventually selected. -/
lemma seq_exhaust (a : A) : ∃ n, a ∈ (seqL G n).map Prod.fst := by
  by_contra hcon
  push_neg at hcon
  have hlen := seq_len_of_absent G a hcon
  obtain ⟨R, hR⟩ := strategy_exists G a
  obtain ⟨ua, ta, hsa, -, -⟩ := strategy_path G a R hR
  let B : ℕ := (bstep G)^[Fintype.card E] ta
  -- every selected agent starts by time `B`
  have hsub : ∀ n, ∀ b ∈ (seqL G n).map Prod.fst, b ∈ AgentsBy G B := by
    intro n b hb
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    rw [List.length_map] at hi
    rw [List.getElem_map] at hbi
    have hsel := seq_special G n i hi
    set L' := (seqL G n).take i with hL'
    set x := (seqL G n)[i] with hx
    have hL'sp : G.IsSpecialPrefix L' := by
      have := seq_special G i
      have hpre : seqL G i = L' := by
        have hln := hlen n
        have h1 := seq_prefix_le G (show i ≤ n by omega)
        have h2 : (seqL G i).length = i := hlen i
        rw [hL']
        obtain ⟨t, ht⟩ := h1
        rw [← ht, List.take_left' h2]
      rw [← hpre]; exact this
    have hφ := valid_pp G L' hL'sp
    have haL' : prefixProfile L' a = none := by
      rw [pp_none_iff]
      intro hmem
      exact hcon n (((List.take_prefix i _).map Prod.fst).subset hmem)
    have hxa : (a, R) ≠ (x.1, x.2) := by
      intro h
      have : a = x.1 := congrArg Prod.fst h
      apply hcon n
      rw [this]
      exact List.mem_map.2 ⟨(seqL G n)[i], List.getElem_mem _, rfl⟩
    have hbef := hsel.2.2 a R haL' hR hxa
    have hle := before_le G _ _ _ _ _ _ _ _ hbef
    -- bound on `a`
    have hva := valid_update G _ hφ a R hR
    have hB := arrival_d_le G _ hva a R (by simp) ua ta hsa
    -- lower bound on `x.1`
    have hvx := valid_update G _ hφ x.1 x.2 hsel.2.1
    obtain ⟨t, ht, hst⟩ := arrival_onPath G _ hvx x.1 x.2 (by simp) G.d
      (onPath_d G _ _ hsel.2.1)
    obtain ⟨ux, nx, hux, -, -⟩ := strategy_path G x.1 x.2 hsel.2.1
    have h1 := hst ux nx hux
    have h2 : (t : ℕ∞) ≤ (B : ℕ∞) := by rw [← ht]; exact le_trans hle hB
    have h3 : t ≤ B := by exact_mod_cast h2
    rw [← hbi]
    exact mem_agentsBy G _ B ⟨ux, nx, hux, by omega⟩
  let n := (AgentsBy G B).card + 1
  have hnd := seq_nodup G n
  have hcard := List.toFinset_card_of_nodup hnd
  have hle : ((seqL G n).map Prod.fst).toFinset.card ≤ (AgentsBy G B).card :=
    Finset.card_le_card (fun b hb => hsub n b (List.mem_toFinset.1 hb))
  rw [hcard, List.length_map, hlen n] at hle
  omega

/-- the stage at which `a` is selected -/
noncomputable def stage (a : A) : ℕ := by
  classical
  exact Nat.find (seq_exhaust G a)

noncomputable def sig (a : A) : ℕ := ((seqL G (stage G a)).map Prod.fst).idxOf a

noncomputable def pth (a : A) : List E :=
  (((seqL G (stage G a))[sig G a]?).map Prod.snd).getD []

lemma stage_mem (a : A) : a ∈ (seqL G (stage G a)).map Prod.fst := by
  classical
  unfold stage
  exact Nat.find_spec (seq_exhaust G a)

lemma stage_le (a : A) (n : ℕ) (h : a ∈ (seqL G n).map Prod.fst) : stage G a ≤ n := by
  classical
  unfold stage
  exact Nat.find_min' (seq_exhaust G a) h

lemma sig_lt (a : A) : sig G a < (seqL G (stage G a)).length := by
  have := List.idxOf_lt_length_of_mem (stage_mem G a)
  rw [List.length_map] at this
  exact this

lemma sig_self (a : A) :
    (seqL G (stage G a))[sig G a]'(sig_lt G a) = (a, pth G a) := by
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (stage_mem G a))
  rw [List.getElem_map] at h1
  have h2 : pth G a = ((seqL G (stage G a))[sig G a]'(sig_lt G a)).2 := by
    unfold pth
    rw [List.getElem?_eq_getElem (sig_lt G a)]
    rfl
  rw [h2]
  ext
  · exact h1
  · rfl

lemma seq_agree (n i : ℕ) (hi : i < (seqL G n).length) :
    sig G ((seqL G n)[i]).1 = i ∧ pth G ((seqL G n)[i]).1 = ((seqL G n)[i]).2 := by
  set b := ((seqL G n)[i]).1 with hb
  have hbmem : b ∈ (seqL G n).map Prod.fst :=
    List.mem_map.2 ⟨(seqL G n)[i], List.getElem_mem _, rfl⟩
  have hle := stage_le G b n hbmem
  have hpre := (seq_prefix_le G hle).map Prod.fst
  have hidx : sig G b = i := by
    unfold sig
    obtain ⟨t, ht⟩ := hpre
    have := List.idxOf_append_of_mem (l₂ := t) (stage_mem G b)
    rw [ht] at this
    rw [← this]
    have h3 := List.Nodup.idxOf_getElem (seq_nodup G n) i (by rw [List.length_map]; exact hi)
    rw [List.getElem_map] at h3
    exact h3
  refine ⟨hidx, ?_⟩
  have h4 := sig_self G b
  have h5 := seq_coh G (stage G b) n (sig G b) (sig_lt G b) (hidx ▸ hi)
  rw [h4] at h5
  have : (seqL G n)[sig G b]'(hidx ▸ hi) = (seqL G n)[i] := by simp [hidx]
  rw [this] at h5
  rw [← h5]

theorem special_seq : ∃ (σ : A → ℕ) (p : A → List E), G.IsSpecialSeq σ p := by
  refine ⟨sig G, pth G, ?_, ?_, ?_⟩
  · intro a b hab
    have ha := sig_self G a
    have hb := sig_self G b
    have := seq_coh G (stage G a) (stage G b) (sig G a) (sig_lt G a) (hab ▸ sig_lt G b)
    rw [ha] at this
    have h2 : (seqL G (stage G b))[sig G a]'(hab ▸ sig_lt G b) =
        (seqL G (stage G b))[sig G b]'(sig_lt G b) := by simp [hab]
    rw [h2, hb] at this
    exact congrArg Prod.fst this
  · intro a m hm
    have hlt : m < (seqL G (stage G a)).length := lt_trans hm (sig_lt G a)
    exact ⟨_, (seq_agree G (stage G a) m hlt).1⟩
  · intro a
    set n := stage G a
    set l := seqL G n
    have hk := sig_lt G a
    have hsel := seq_special G n (sig G a) hk
    rw [sig_self G a] at hsel
    have hval : ∀ y ∈ l.take (sig G a), y.2 = pth G y.1 := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take hy |> fun h => h)
      exact (seq_agree G n i hi).2.symm
    have hpp : prefixProfile (l.take (sig G a)) =
        fun b => if sig G b < sig G a then some (pth G b) else none := by
      funext b
      rw [ppe (pth G) _ hval b]
      apply if_congr _ rfl rfl
      constructor
      · intro hb
        obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
        rw [List.length_map, List.length_take] at hi
        rw [List.getElem_map, List.getElem_take] at hbi
        have := (seq_agree G n i (lt_of_lt_of_le hi (min_le_right _ _))).1
        rw [hbi] at this
        rw [this]; exact lt_of_lt_of_le hi (min_le_left _ _)
      · intro hb
        have h1 := sig_self G b
        have hlt : sig G b < l.length := lt_trans hb hk
        have h2 := seq_coh G (stage G b) n (sig G b) (sig_lt G b) hlt
        rw [h1] at h2
        apply List.mem_map.2
        refine ⟨(b, pth G b), ?_, rfl⟩
        rw [h2]
        apply List.mem_iff_getElem.2
        refine ⟨sig G b, by rw [List.length_take]; omega, ?_⟩
        rw [List.getElem_take]
    rw [hpp] at hsel
    exact hsel

end seq

end ADFF


open AtomicDynFlow.IDNE

theorem solution {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) :
    ∃ (σ : A → ℕ) (p : A → List E), G.IsSpecialSeq σ p := ADFF.special_seq G
