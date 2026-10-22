-- Prove2me | solution 2 for AtomicDynFlow.IDNE.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T08:24:57.055077+00:00
-- url     : https://prove2.me/submissions/1696ded2-06da-4090-8291-4dade647b11f

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium

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

namespace ADFCE

/-! Counterexample. Vertices `x = 0`, `u = 1`, `d = 2`; edges `h = 0 : x → u`,
`e = 1 : u → d`, `f = 2 : u → d`. Agents `b₁ = 0`, `b₂ = 1`, `j = 2` in the initial queue of `e`
(in this order), `k = 3` in the initial queue of `h`. -/

def tl : Fin 3 → Fin 3 := ![0, 1, 1]
def hd : Fin 3 → Fin 3 := ![1, 2, 2]

def G0 : Instance (Fin 3) (Fin 3) (Fin 4) where
  tail := tl
  head := hd
  d := 2
  acyclic := ⟨fun v => v.val, by decide⟩
  reach := by
    intro v
    fin_cases v
    · exact ⟨[0, 1], rfl, rfl, rfl⟩
    · exact ⟨[1], rfl, rfl⟩
    · exact ⟨[], rfl⟩
  inc := ![[], [0], [1, 2]]
  inc_mem := by decide
  inc_nodup := by decide
  Q0 := ![[3], [0, 1, 2], []]
  inflow := fun _ _ => []
  inflow_zero := fun _ => rfl
  nodup := by
    intro s
    rcases s with e | rv
    · fin_cases e <;> decide
    · exact List.nodup_nil
  partition := by
    intro a
    have key : ∀ s : Fin 3 ⊕ (ℕ × Fin 3), a ∈ srcList (![[3], [0, 1, 2], []] : Fin 3 → List (Fin 4))
        (fun _ _ => ([] : List (Fin 4))) s ↔ s = Sum.inl (if a = 3 then 0 else 1) := by
      intro s
      rcases s with e | rv
      · simp only [srcList, Sum.inl.injEq]
        fin_cases a <;> fin_cases e <;> decide
      · simp [srcList]
    refine ⟨Sum.inl (if a = 3 then 0 else 1), (key _).2 rfl, fun s hs => (key s).1 hs⟩

lemma strat_e (b : Fin 4) (hb : b ≠ 3) (P : List (Fin 3)) (h : G0.IsStrategy b P) : P = [1] := by
  rcases h with ⟨e, he, hP, hpath⟩ | ⟨r, v, hin, -⟩
  · have he1 : e = 1 := by
      revert he; fin_cases b <;> fin_cases e <;> simp_all [G0] <;> decide
    subst he1
    cases P with
    | nil => simp at hP
    | cons e' P =>
      simp at hP; subst hP
      cases P with
      | nil => rfl
      | cons e'' P =>
        exfalso
        obtain ⟨-, h2, -⟩ := hpath
        revert h2; fin_cases e'' <;> decide
  · simp [G0] at hin

lemma strat_k (P : List (Fin 3)) (h : G0.IsStrategy 3 P) : P = [0, 1] ∨ P = [0, 2] := by
  rcases h with ⟨e, he, hP, hpath⟩ | ⟨r, v, hin, -⟩
  · have he0 : e = 0 := by
      revert he; fin_cases e <;> decide
    subst he0
    cases P with
    | nil => simp at hP
    | cons e' P =>
      simp at hP; subst hP
      obtain ⟨-, hpath⟩ := hpath
      cases P with
      | nil =>
        have h0 : G0.head 0 = G0.d := hpath
        exact absurd h0 (by decide)
      | cons e'' P =>
        obtain ⟨h2, hpath⟩ := hpath
        cases P with
        | nil =>
          have : e'' = 1 ∨ e'' = 2 := by revert h2; fin_cases e'' <;> decide
          rcases this with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        | cons e3 P =>
          exfalso
          obtain ⟨h3, -⟩ := hpath
          have : e'' = 1 ∨ e'' = 2 := by revert h2; fin_cases e'' <;> decide
          rcases this with rfl | rfl <;> (revert h3; fin_cases e3 <;> decide)
  · simp [G0] at hin

/-- the concrete profile in which `k` takes `R` -/
def prof (R : List (Fin 3)) : Fin 4 → Option (List (Fin 3)) :=
  fun b => if b = 3 then some R else some [1]

lemma prof_eq (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) :
    (fun b => some (r b)) = prof (r 3) := by
  funext b
  unfold prof
  by_cases hb : b = 3
  · subst hb; simp
  · rw [if_neg hb, strat_e b hb (r b) (hr b)]

lemma valid_of (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) :
    ADFF.Valid G0 (fun b => some (r b)) := by
  intro a P h
  simp at h; subst h; exact hr a

/-- `j` is at `u` at time `0` -/
lemma arr_j_u (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) :
    G0.arrival (fun b => some (r b)) 2 1 = 0 := by
  have := ADFF.arrival_start G0 _ (valid_of r hr) 2 (r 2) rfl 1 0
    (Or.inl ⟨1, by decide, rfl, rfl⟩)
  simpa using this

/-- `k` reaches `u` at time `1` -/
lemma arr_k_u (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) :
    G0.arrival (fun b => some (r b)) 3 1 = 1 := by
  have hs : ADFF.Heads G0 (fun b => some (r b)) 3 0 0 := by
    unfold ADFF.Heads
    rw [prof_eq r hr]
    rcases strat_k (r 3) (hr 3) with h | h <;> rw [h] <;> decide
  have hmem : (0 : Fin 3) ∈ r 3 := by
    rcases strat_k (r 3) (hr 3) with h | h <;> rw [h] <;> decide
  have := ADFF.arrival_head G0 _ (valid_of r hr) 3 (r 3) rfl 0 hmem 0 hs
  have e : G0.head 0 = 1 := rfl
  rw [e] at this
  simpa using this

/-- `j` reaches `d` at time `3` -/
lemma arr_j_d (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) :
    G0.arrival (fun b => some (r b)) 2 2 = 3 := by
  have hs : ADFF.Heads G0 (fun b => some (r b)) 2 1 2 := by
    unfold ADFF.Heads
    rw [prof_eq r hr]
    rcases strat_k (r 3) (hr 3) with h | h <;> rw [h] <;> decide
  have hmem : (1 : Fin 3) ∈ r 2 := by
    rw [strat_e 2 (by decide) (r 2) (hr 2)]; decide
  have := ADFF.arrival_head G0 _ (valid_of r hr) 2 (r 2) rfl 1 hmem 2 hs
  have e : G0.head 1 = 2 := rfl
  rw [e] at this
  simpa using this

/-- `k` on `[h, f]` reaches `d` at time `2` -/
lemma arr_k_d (r : Fin 4 → List (Fin 3)) (hr : ∀ b, G0.IsStrategy b (r b)) (hk : r 3 = [0, 2]) :
    G0.arrival (fun b => some (r b)) 3 2 = 2 := by
  have hs : ADFF.Heads G0 (fun b => some (r b)) 3 2 1 := by
    unfold ADFF.Heads
    rw [prof_eq r hr, hk]
    decide
  have hmem : (2 : Fin 3) ∈ r 3 := by rw [hk]; decide
  have := ADFF.arrival_head G0 _ (valid_of r hr) 3 (r 3) rfl 2 hmem 1 hs
  have e : G0.head 2 = 2 := rfl
  rw [e] at this
  simpa using this

lemma strat_kf : G0.IsStrategy 3 [0, 2] := Or.inl ⟨0, by decide, rfl, rfl, rfl, rfl⟩

/-- `G0` has no path profile satisfying the sequential optimality of Definition 2. -/
theorem no_idne (σ : Fin 4 → ℕ) (p : Fin 4 → List (Fin 3)) (h : G0.IsIDNEWith σ p) : False := by
  obtain ⟨hp, hinj, -, hopt⟩ := h
  rcases lt_or_gt_of_ne (show σ 3 ≠ σ 2 from fun h' => absurd (hinj h') (by decide)) with h1 | h1
  · -- `k` before `j`: at `u`, `j` (present at time 0) beats `k` (time 1)
    have hon : G0.OnPath 3 (p 3) 1 := by
      right
      refine ⟨0, ?_, rfl⟩
      rcases strat_k (p 3) (hp 3) with h | h <;> rw [h] <;> decide
    have key := hopt 3 1 hon p hp (fun _ _ => rfl)
    have hle : G0.arrival (fun b => some (p b)) 3 1 ≤ G0.arrival (fun b => some (p b)) 2 1 := by
      rw [key]
      exact iInf₂_le_of_le 2 h1.le (iInf₂_le_of_le p ⟨hp, fun _ _ => rfl⟩ le_rfl)
    rw [arr_k_u p hp, arr_j_u p hp] at hle
    exact absurd hle (by decide)
  · -- `j` before `k`: at `d`, `k` on `[h, f]` (time 2) beats `j` (time 3)
    have hon : G0.OnPath 2 (p 2) 2 := by
      right
      refine ⟨1, ?_, rfl⟩
      rw [strat_e 2 (by decide) (p 2) (hp 2)]; decide
    have key := hopt 2 2 hon p hp (fun _ _ => rfl)
    let r : Fin 4 → List (Fin 3) := Function.update p 3 [0, 2]
    have hr : ∀ b, G0.IsStrategy b (r b) := by
      intro b
      by_cases hb : b = 3
      · subst hb; simp only [r, Function.update_self]; exact strat_kf
      · simp only [r, Function.update_of_ne hb]; exact hp b
    have hagree : ∀ b, σ b < σ 2 → r b = p b := by
      intro b hb
      have : b ≠ 3 := by rintro rfl; omega
      simp only [r, Function.update_of_ne this]
    have hle : G0.arrival (fun b => some (p b)) 2 2 ≤ G0.arrival (fun b => some (r b)) 3 2 := by
      rw [key]
      exact iInf₂_le_of_le 3 h1.le (iInf₂_le_of_le r ⟨hr, hagree⟩ le_rfl)
    rw [arr_j_d p hp, arr_k_d r hr (by simp [r])] at hle
    exact absurd hle (by decide)

end ADFCE


open AtomicDynFlow.IDNE

theorem solution : ¬ (∀ {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A),
    ∃ p : A → List E, (∀ a, G.IsStrategy a (p a)) ∧ G.IsIDNE p ∧ G.IsNE p) := by
  intro h
  obtain ⟨p, -, ⟨σ, hσ⟩, -⟩ := h ADFCE.G0
  exact ADFCE.no_idne σ p hσ
