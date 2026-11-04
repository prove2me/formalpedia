-- Prove2me | solution 1 for AtomicDynRouting.ResidenceTime.p3_new_token_only_waiting
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:06:08.188665+00:00
-- url     : https://prove2.me/submissions/1d220004-293d-4960-8338-4afc8dfe365a

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

open AtomicDynRouting.ResidenceTime

namespace ADRT1Aux

section Graph

variable {V E : Type} (N : Network V E)

def Reach (u v : V) : Prop := ∃ P : List E, N.IsPathFrom u v P

theorem path_nil (u w : V) : N.IsPathFrom u w [] ↔ u = w := by
  simp [Network.IsPathFrom]

theorem path_cons (u w : V) (e : E) (P : List E) :
    N.IsPathFrom u w (e :: P) ↔ N.tail e = u ∧ N.IsPathFrom (N.head e) w P := by
  simp [Network.IsPathFrom]

theorem path_append : ∀ (P Q : List E) (u m w : V),
    N.IsPathFrom u m P → N.IsPathFrom m w Q → N.IsPathFrom u w (P ++ Q)
  | [], Q, u, m, w, hP, hQ => by
      rw [path_nil] at hP; subst hP; simpa using hQ
  | e :: P, Q, u, m, w, hP, hQ => by
      rw [path_cons] at hP
      rw [List.cons_append, path_cons]
      exact ⟨hP.1, path_append P Q _ _ _ hP.2 hQ⟩

theorem reach_refl (u : V) : Reach N u u := ⟨[], (path_nil N u u).2 rfl⟩

theorem reach_trans {u v w : V} (h1 : Reach N u v) (h2 : Reach N v w) : Reach N u w := by
  obtain ⟨P, hP⟩ := h1; obtain ⟨Q, hQ⟩ := h2
  exact ⟨P ++ Q, path_append N P Q _ _ _ hP hQ⟩

theorem reach_edge (e : E) : Reach N (N.tail e) (N.head e) :=
  ⟨[e], (path_cons N _ _ e []).2 ⟨rfl, (path_nil N _ _).2 rfl⟩⟩

theorem path_take_drop : ∀ (P : List E) (u w : V) (i : ℕ) (x : E),
    N.IsPathFrom u w P → P[i]? = some x →
    N.IsPathFrom u (N.tail x) (P.take i) ∧ N.IsPathFrom (N.head x) w (P.drop (i+1))
  | [], u, w, i, x, _, hx => by simp at hx
  | e :: P, u, w, 0, x, hP, hx => by
      rw [path_cons] at hP
      simp at hx; subst hx
      refine ⟨(path_nil N _ _).2 hP.1.symm, ?_⟩
      simpa using hP.2
  | e :: P, u, w, i+1, x, hP, hx => by
      rw [path_cons] at hP
      simp at hx
      obtain ⟨h1, h2⟩ := path_take_drop P _ w i x hP.2 hx
      refine ⟨?_, by simpa using h2⟩
      simp only [List.take_succ_cons]
      exact (path_cons N _ _ e _).2 ⟨hP.1, h1⟩

theorem path_first {u w : V} {P : List E} {x : E} (hP : N.IsPathFrom u w P)
    (hx : P[0]? = some x) : N.tail x = u := by
  have := (path_take_drop N P u w 0 x hP hx).1
  simpa [path_nil] using this.symm

theorem path_consec {u w : V} {P : List E} {i : ℕ} {x y : E} (hP : N.IsPathFrom u w P)
    (hx : P[i]? = some x) (hy : P[i+1]? = some y) : N.head x = N.tail y := by
  have h := (path_take_drop N P u w i x hP hx).2
  have : (P.drop (i+1))[0]? = some y := by simpa [List.getElem?_drop] using hy
  exact (path_first N h this).symm

theorem path_last {u w : V} {P : List E} {x : E} (hP : N.IsPathFrom u w P)
    (hx : P[P.length - 1]? = some x) : N.head x = w := by
  have h := (path_take_drop N P u w _ x hP hx).2
  have hlen : P.length - 1 + 1 = P.length := by
    have : P.length - 1 < P.length := (List.getElem?_eq_some_iff.1 hx).1
    omega
  rw [hlen, List.drop_length, path_nil] at h
  exact h

theorem reach_of_get {u w : V} {P : List E} {i : ℕ} {x : E} (hP : N.IsPathFrom u w P)
    (hx : P[i]? = some x) : Reach N u (N.tail x) ∧ Reach N (N.head x) w :=
  ⟨⟨_, (path_take_drop N P u w i x hP hx).1⟩, ⟨_, (path_take_drop N P u w i x hP hx).2⟩⟩

theorem reach_between {u w : V} {P : List E} {i i' : ℕ} {x y : E} (hP : N.IsPathFrom u w P)
    (hx : P[i]? = some x) (hy : P[i']? = some y) (hii : i < i') :
    Reach N (N.head x) (N.tail y) := by
  have h := (path_take_drop N P u w i x hP hx).2
  have : (P.drop (i+1))[i' - (i+1)]? = some y := by
    rw [List.getElem?_drop]; rw [show i + 1 + (i' - (i+1)) = i' by omega]; exact hy
  exact (reach_of_get N h this).1

theorem reach_of_mem {u w : V} {P : List E} {f : E} (hP : N.IsPathFrom u w P) (hf : f ∈ P) :
    Reach N u (N.tail f) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
  exact (reach_of_get N hP hi).1

theorem path_nodup (hN : N.Acyclic) : ∀ (P : List E) (u w : V),
    N.IsPathFrom u w P → (P.map N.tail).Nodup
  | [], _, _, _ => by simp
  | e :: P, u, w, hP => by
      rw [path_cons] at hP
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, path_nodup hN P _ _ hP.2⟩
      intro hmem
      obtain ⟨f, hf, htf⟩ := List.mem_map.1 hmem
      obtain ⟨Q, hQ⟩ := reach_of_mem N hP.2 hf
      have hc : N.IsPathFrom (N.tail e) (N.tail e) (e :: Q) :=
        (path_cons N _ _ e Q).2 ⟨rfl, htf ▸ hQ⟩
      exact List.cons_ne_nil e Q (hN _ _ hc)

theorem path_length_le [Fintype V] (hN : N.Acyclic) {u w : V} {P : List E}
    (hP : N.IsPathFrom u w P) : P.length ≤ Fintype.card V := by
  have := (path_nodup N hN P u w hP).length_le_card
  simpa using this

theorem longest_bdd [Fintype V] (hN : N.Acyclic) (v w : V) :
    BddAbove {n : ℕ | ∃ P : List E, N.IsPathFrom v w P ∧ P.length = n} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨P, hP, rfl⟩
  exact path_length_le N hN hP

theorem le_longest [Fintype V] (hN : N.Acyclic) {v w : V} {P : List E}
    (hP : N.IsPathFrom v w P) : P.length ≤ N.longest v w := by
  unfold Network.longest
  exact le_csSup (longest_bdd N hN v w) (show P.length ∈ {n : ℕ | ∃ P : List E, N.IsPathFrom v w P ∧ P.length = n} from ⟨P, hP, rfl⟩)

theorem longest_spec [Fintype V] (hN : N.Acyclic) {v w : V} (h : Reach N v w) :
    ∃ P : List E, N.IsPathFrom v w P ∧ P.length = N.longest v w := by
  obtain ⟨P, hP⟩ := h
  unfold Network.longest
  exact Nat.sSup_mem (s := {n : ℕ | ∃ P : List E, N.IsPathFrom v w P ∧ P.length = n}) ⟨P.length, P, hP, rfl⟩ (longest_bdd N hN v w)

/-- `L(v,d) ≤ L(u,d)` when `u ⇝ v ⇝ d`. -/
theorem longest_mono [Fintype V] (hN : N.Acyclic) {u v d : V} (huv : Reach N u v)
    (hvd : Reach N v d) : N.longest v d ≤ N.longest u d := by
  obtain ⟨P, hP, hl⟩ := longest_spec N hN hvd
  obtain ⟨Q, hQ⟩ := huv
  have := le_longest N hN (path_append N Q P _ _ _ hQ hP)
  simp at this; omega

/-- `L(tail e, d) ≥ L(head e, d) + 1` when `head e ⇝ d`. -/
theorem longest_edge [Fintype V] (hN : N.Acyclic) {e : E} {d : V} (h : Reach N (N.head e) d) :
    N.longest (N.head e) d + 1 ≤ N.longest (N.tail e) d := by
  obtain ⟨P, hP, hl⟩ := longest_spec N hN h
  have := le_longest N hN ((path_cons N (N.tail e) d e P).2 ⟨rfl, hP⟩)
  simp at this; omega

end Graph

section Run

variable {V E ι : Type} (N : Network V E) (R : RunData ι E V)

theorem arrive_zero (i : ι) : R.arrive i 0 = (R.entry i : ℕ∞) := by simp [RunData.arrive]

theorem arrive_succ (i : ι) (j : ℕ) : R.arrive i (j+1) = R.leave i j + 1 := by
  simp [RunData.arrive]

variable {N R}

theorem arrive_le_leave (hR : IsADR N R) {i : ι} {j : ℕ} (hj : j < (R.route i).length) :
    R.arrive i j ≤ R.leave i j := hR.2.2.1 i j hj

theorem leave_add_one_le_arrive (hR : IsADR N R) {i : ι} {j j' : ℕ} (hjj : j < j')
    (hj' : j' < (R.route i).length) : R.leave i j + 1 ≤ R.arrive i j' := by
  induction j', hjj using Nat.le_induction with
  | base => rw [arrive_succ]
  | succ m hm ih =>
      rw [arrive_succ]
      calc R.leave i j + 1 ≤ R.arrive i m := ih (by omega)
        _ ≤ R.leave i m := arrive_le_leave hR (by omega)
        _ ≤ R.leave i m + 1 := le_self_add

theorem leave_mono (hR : IsADR N R) {i : ι} {j j' : ℕ} (hjj : j ≤ j')
    (hj' : j' < (R.route i).length) : R.leave i j ≤ R.leave i j' := by
  rcases Nat.eq_or_lt_of_le hjj with h | h
  · rw [h]
  · calc R.leave i j ≤ R.leave i j + 1 := le_self_add
      _ ≤ R.arrive i j' := leave_add_one_le_arrive hR h hj'
      _ ≤ R.leave i j' := arrive_le_leave hR hj'

theorem inBuf_unique (hR : IsADR N R) {i : ι} {j j' s : ℕ} (h : R.inBuf i j s)
    (h' : R.inBuf i j' s) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have h1 := leave_add_one_le_arrive hR hl h'.1
    have h2 : (s : ℕ∞) + 1 ≤ R.leave i j + 1 := add_le_add_left h.2.2 1
    have h3 := le_trans (le_trans h2 h1) h'.2.1
    exact absurd h3 (by simpa using (ENat.coe_lt_coe.2 (Nat.lt_succ_self s)))
  · have h1 := leave_add_one_le_arrive hR hl h.1
    have h2 : (s : ℕ∞) + 1 ≤ R.leave i j' + 1 := add_le_add_left h'.2.2 1
    have h3 := le_trans (le_trans h2 h1) h.2.1
    exact absurd h3 (by simpa using (ENat.coe_lt_coe.2 (Nat.lt_succ_self s)))

theorem inBuf_of_leave (hR : IsADR N R) {i : ι} {j s : ℕ} (hj : j < (R.route i).length)
    (hl : R.leave i j = (s : ℕ∞)) : R.inBuf i j s :=
  ⟨hj, hl ▸ arrive_le_leave hR hj, hl.ge⟩

theorem leaver_spec {e : E} {s : ℕ} {a : ι} {j : ℕ} (h : leaver R e s = some (a, j)) :
    j < (R.route a).length ∧ (R.route a)[j]? = some e ∧ R.leave a j = (s : ℕ∞) := by
  unfold leaver at h
  split_ifs at h with hh
  have := Classical.choose_spec hh
  rw [Option.some.inj h] at this
  exact this

theorem leaver_eq (hR : IsADR N R) {e : E} {s : ℕ} {a : ι} {j : ℕ}
    (h : j < (R.route a).length ∧ (R.route a)[j]? = some e ∧ R.leave a j = (s : ℕ∞)) :
    leaver R e s = some (a, j) := by
  have hne : ∃ i j, R.inBuf i j s ∧ (R.route i)[j]? = some e :=
    ⟨a, j, inBuf_of_leave hR h.1 h.2.2, h.2.1⟩
  obtain ⟨p, hp, huniq⟩ := hR.2.2.2 e s hne
  have hex : ∃ p : ι × ℕ, p.2 < (R.route p.1).length ∧ (R.route p.1)[p.2]? = some e ∧
      R.leave p.1 p.2 = (s : ℕ∞) := ⟨(a, j), h⟩
  unfold leaver
  rw [dif_pos hex]
  congr 1
  rw [huniq _ (Classical.choose_spec hex), huniq (a, j) h]

theorem leaver_some (hR : IsADR N R) {e : E} {s : ℕ}
    (hne : ∃ i j, R.inBuf i j s ∧ (R.route i)[j]? = some e) : ∃ p, leaver R e s = some p := by
  obtain ⟨p, hp, _⟩ := hR.2.2.2 e s hne
  unfold leaver
  rw [dif_pos ⟨p, hp⟩]
  exact ⟨_, rfl⟩

theorem zBuf_eq (hR : IsADR N R) {ζ : ι} {j s : ℕ} (h : R.inBuf ζ j s) :
    zBuf R ζ s = (R.route ζ)[j]? := by
  have hex : ∃ j, R.inBuf ζ j s := ⟨j, h⟩
  unfold zBuf
  rw [dif_pos hex, inBuf_unique hR (Classical.choose_spec hex) h]

theorem zBuf_some {ζ : ι} {s : ℕ} {U : E} (h : zBuf R ζ s = some U) :
    ∃ j, R.inBuf ζ j s ∧ (R.route ζ)[j]? = some U := by
  unfold zBuf at h
  split_ifs at h with hh
  exact ⟨_, Classical.choose_spec hh, h⟩

theorem inside_inBuf (hR : IsADR N R) {i : ι} {t : ℕ} (h : R.inside i t) :
    ∃ j, R.inBuf i j t := by
  obtain ⟨h1, h2⟩ := h
  have hlen : 0 < (R.route i).length := List.length_pos_iff.2 (hR.1 i).2
  have h3 : (t : ℕ∞) ≤ R.leave i ((R.route i).length - 1) :=
    ENat.natCast_lt_add_one_iff.mp h2
  have hex : ∃ j, (t : ℕ∞) ≤ R.leave i j ∧ j < (R.route i).length :=
    ⟨_, h3, by omega⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).2, ?_, (Nat.find_spec hex).1⟩
  rcases hm : Nat.find hex with _ | m
  · rw [arrive_zero]; exact_mod_cast h1
  · have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
    have hm' : m < (R.route i).length := by have := (Nat.find_spec hex).2; omega
    have : R.leave i m < (t : ℕ∞) := by
      by_contra hc; exact hmin ⟨not_lt.1 hc, hm'⟩
    rw [arrive_succ]; exact Order.add_one_le_of_lt this

theorem mem_Gz_iff {ζ : ι} {e : E} :
    e ∈ Gz N R ζ ↔ Reach N (R.orig ζ) (N.tail e) ∧ Reach N (N.head e) (R.dest ζ) := by
  constructor
  · rintro ⟨P, hP, he⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
    exact reach_of_get N hP hi
  · rintro ⟨⟨Q, hQ⟩, ⟨Q', hQ'⟩⟩
    refine ⟨Q ++ e :: Q', path_append N Q (e :: Q') _ _ _ hQ ((path_cons N _ _ e Q').2 ⟨rfl, hQ'⟩), ?_⟩
    simp

theorem route_mem_Gz (hR : IsADR N R) {ζ : ι} {j : ℕ} {e : E} (h : (R.route ζ)[j]? = some e) :
    e ∈ Gz N R ζ :=
  ⟨R.route ζ, (hR.1 ζ).1, List.mem_of_getElem? h⟩

/-- Contiguity of `route a ∩ Gζ`. -/
theorem Gz_contig (hR : IsADR N R) {ζ a : ι} {j j' : ℕ} {x y f : E}
    (hx : (R.route a)[j]? = some x) (hxG : x ∈ Gz N R ζ)
    (hy : (R.route a)[j']? = some y) (hyG : y ∈ Gz N R ζ) (hjj : j < j')
    (hf : (R.route a)[j+1]? = some f) : f ∈ Gz N R ζ := by
  have hP := (hR.1 a).1
  rw [mem_Gz_iff] at hxG hyG ⊢
  refine ⟨?_, ?_⟩
  · rw [← path_consec N hP hx hf]
    exact reach_trans N hxG.1 (reach_edge N x)
  · rcases Nat.eq_or_lt_of_le (show j + 1 ≤ j' by omega) with h | h
    · subst h; rw [hf] at hy; cases hy; exact hyG.2
    · exact reach_trans N (reach_between N hP hf hy h)
        (reach_trans N (reach_edge N y) hyG.2)

end Run

section Tok

variable {V E ι : Type} {N : Network V E} {R : RunData ι E V}

theorem move_none {s k : ℕ} {pos : ℕ → Option E} (h : pos k = none) :
    moveTokens R s pos k = none := by
  simp [moveTokens, h]

theorem move_stay1 {s k : ℕ} {pos : ℕ → Option E} {e : E} (hk : pos k = some e)
    (h : ∃ h < k, pos h = some e) : moveTokens R s pos k = some e := by
  have : ¬ ∀ h < k, pos h ≠ some e := by push_neg; exact h
  simp only [moveTokens, hk]
  rw [if_neg this]

theorem move_stay2 {s k : ℕ} {pos : ℕ → Option E} {e : E} (hk : pos k = some e)
    (h : ∀ h < k, pos h ≠ some e) (hl : leaver R e s = none) : moveTokens R s pos k = some e := by
  simp only [moveTokens, hk]
  rw [if_pos h, hl]

theorem move_go {s k : ℕ} {pos : ℕ → Option E} {e : E} {a : ι} {j : ℕ} (hk : pos k = some e)
    (h : ∀ h < k, pos h ≠ some e) (hl : leaver R e s = some (a, j)) :
    moveTokens R s pos k = (R.route a)[j+1]? := by
  simp only [moveTokens, hk]
  rw [if_pos h, hl]

theorem move_cases {s k : ℕ} {pos : ℕ → Option E} {e : E} (hm : moveTokens R s pos k = some e) :
    ∃ e0, pos k = some e0 ∧
      (((∃ h < k, pos h = some e0) ∧ e = e0) ∨
       ((∀ h < k, pos h ≠ some e0) ∧ leaver R e0 s = none ∧ e = e0) ∨
       ((∀ h < k, pos h ≠ some e0) ∧ ∃ a j, leaver R e0 s = some (a, j) ∧
          (R.route a)[j+1]? = some e)) := by
  rcases hk : pos k with _ | e0
  · rw [move_none hk] at hm; cases hm
  refine ⟨e0, rfl, ?_⟩
  by_cases h1 : ∃ h < k, pos h = some e0
  · rw [move_stay1 hk h1] at hm; cases hm; exact Or.inl ⟨h1, rfl⟩
  have h1' : ∀ h < k, pos h ≠ some e0 := by push_neg at h1; exact h1
  rcases hl : leaver R e0 s with _ | ⟨a, j⟩
  · rw [move_stay2 hk h1' hl] at hm; cases hm; exact Or.inr (Or.inl ⟨h1', rfl, rfl⟩)
  · rw [move_go hk h1' hl] at hm; exact Or.inr (Or.inr ⟨h1', a, j, rfl, hm⟩)

variable (ζ : ι) (r0 : ℕ)

theorem step_cases (d : ℕ) :
    (∃ U, zBuf R ζ (r0+d+1) = some U ∧
      (∀ k, moveTokens R (r0+d) (tokState R ζ r0 d).2 k ≠ some U) ∧
      tokState R ζ r0 (d+1) = ((tokState R ζ r0 d).1 + 1,
        Function.update (moveTokens R (r0+d) (tokState R ζ r0 d).2)
          ((tokState R ζ r0 d).1 + 1) (some U))) ∨
    (tokState R ζ r0 (d+1) = ((tokState R ζ r0 d).1, moveTokens R (r0+d) (tokState R ζ r0 d).2) ∧
      ∀ U, zBuf R ζ (r0+d+1) = some U →
        ∃ k, moveTokens R (r0+d) (tokState R ζ r0 d).2 k = some U) := by
  rcases hz : zBuf R ζ (r0+d+1) with _ | U
  · right
    refine ⟨?_, by simp⟩
    rw [tokState.eq_2, hz]
  · by_cases hU : ∀ k, moveTokens R (r0+d) (tokState R ζ r0 d).2 k ≠ some U
    · left
      refine ⟨U, rfl, hU, ?_⟩
      rw [tokState.eq_2, hz]
      simp only
      rw [if_pos hU]
    · right
      refine ⟨?_, ?_⟩
      · rw [tokState.eq_2, hz]
        simp only
        rw [if_neg hU]
      · intro U' hU'
        cases hU'
        push_neg at hU
        exact hU

theorem tok_zero (k : ℕ) :
    (tokState R ζ r0 0).2 k = match zBuf R ζ r0 with
      | some U => if k = 1 then some U else none
      | none => none := by
  rw [tokState.eq_1]
  rcases zBuf R ζ r0 with _ | U <;> rfl

theorem cnt_zero : (tokState R ζ r0 0).1 ≤ 1 := by
  rw [tokState.eq_1]
  rcases zBuf R ζ r0 with _ | U <;> simp

/-- I1: existing tokens have indices in `[1, count]`. -/
theorem inv1 : ∀ d k, (tokState R ζ r0 d).2 k ≠ none → 1 ≤ k ∧ k ≤ (tokState R ζ r0 d).1 := by
  intro d
  induction d with
  | zero =>
    intro k hk
    rw [tok_zero] at hk
    rw [tokState.eq_1]
    rcases hz : zBuf R ζ r0 with _ | U
    · simp [hz] at hk
    · simp only [hz] at hk ⊢
      split_ifs at hk with h1
      · omega
      · exact absurd rfl hk
  | succ d ih =>
    intro k hk
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq] at hk ⊢
      simp only at hk ⊢
      by_cases hkc : k = (tokState R ζ r0 d).1 + 1
      · omega
      · rw [Function.update_of_ne hkc] at hk
        have : (tokState R ζ r0 d).2 k ≠ none := fun h => hk (move_none h)
        have := ih k this; omega
    · rw [heq] at hk ⊢
      simp only at hk ⊢
      exact ih k (fun h => hk (move_none h))

/-- I2: after production, `ζ`'s buffer holds a token. -/
theorem inv2 (d : ℕ) (U : E) (hz : zBuf R ζ (r0+d) = some U) :
    ∃ h, (tokState R ζ r0 d).2 h = some U := by
  cases d with
  | zero =>
    refine ⟨1, ?_⟩
    rw [tok_zero]
    simp only [Nat.add_zero] at hz
    simp [hz]
  | succ d =>
    rw [← Nat.add_assoc] at hz
    rcases step_cases ζ r0 d with ⟨U', hz', hU, heq⟩ | ⟨heq, hex⟩
    · rw [hz] at hz'; cases hz'
      exact ⟨(tokState R ζ r0 d).1 + 1, by rw [heq]; simp⟩
    · obtain ⟨k, hk⟩ := hex U hz
      exact ⟨k, by rw [heq]; exact hk⟩

theorem zBuf_props (hR : IsADR N R) {s : ℕ} {U : E} (hz : zBuf R ζ s = some U) :
    Reach N (R.orig ζ) (N.tail U) ∧ U ∈ Gz N R ζ := by
  obtain ⟨j, -, hj⟩ := zBuf_some hz
  exact ⟨(reach_of_get N (hR.1 ζ).1 hj).1, route_mem_Gz hR hj⟩

/-- I3: every token sits on an edge whose tail is reachable from `oζ`. -/
theorem inv3 (hR : IsADR N R) : ∀ d k e, (tokState R ζ r0 d).2 k = some e →
    Reach N (R.orig ζ) (N.tail e) := by
  intro d
  induction d with
  | zero =>
    intro k e hk
    rw [tok_zero] at hk
    rcases hz : zBuf R ζ r0 with _ | U
    · simp [hz] at hk
    · simp only [hz] at hk
      split_ifs at hk
      · cases hk; exact (zBuf_props ζ hR hz).1
  | succ d ih =>
    have key : ∀ k e, moveTokens R (r0+d) (tokState R ζ r0 d).2 k = some e →
        Reach N (R.orig ζ) (N.tail e) := by
      intro k e hm
      obtain ⟨e0, hk, hc⟩ := move_cases hm
      rcases hc with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, a, j, hl, hj⟩
      · exact ih k _ hk
      · exact ih k _ hk
      · have hs := leaver_spec hl
        rw [← path_consec N (hR.1 a).1 hs.2.1 hj]
        exact reach_trans N (ih k _ hk) (reach_edge N e0)
    intro k e hk
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq] at hk
      simp only at hk
      by_cases hkc : k = (tokState R ζ r0 d).1 + 1
      · subst hkc; simp at hk; subst hk; exact (zBuf_props ζ hR hz).1
      · rw [Function.update_of_ne hkc] at hk; exact key k e hk
    · rw [heq] at hk; exact key k e hk

end Tok

section Count

variable {V E ι : Type} {N : Network V E} {R : RunData ι E V}

def Occ (R : RunData ι E V) (s : ℕ) (e : E) : Set (ι × ℕ) :=
  {p | R.inBuf p.1 p.2 s ∧ (R.route p.1)[p.2]? = some e}

theorem encard_le_of_sub_single {α β : Type} {S : Set α} {T : Set β} {x : α} (hS : S ⊆ {x})
    (hT : S.Nonempty → T.Nonempty) : S.encard ≤ T.encard := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · calc S.encard ≤ ({x} : Set α).encard := Set.encard_le_encard hS
      _ = 1 := Set.encard_singleton x
      _ ≤ T.encard := Set.one_le_encard_iff_nonempty.2 (hT h)

theorem no_self_loop (hN : N.Acyclic) (hR : IsADR N R) {a : ι} {j : ℕ} {e : E}
    (h1 : (R.route a)[j]? = some e) (h2 : (R.route a)[j+1]? = some e) : False := by
  have hc := path_consec N (hR.1 a).1 h1 h2
  have : N.IsPathFrom (N.tail e) (N.tail e) [e] :=
    (path_cons N _ _ e []).2 ⟨rfl, (path_nil N _ _).2 hc⟩
  exact List.cons_ne_nil e [] (hN _ _ this)

variable (ζ : ι) (r0 : ℕ)

/-- Core of (p1): tokens moved into/kept in `e` are no more than agents in `e` at `s+1`. -/
theorem core_count (hN : N.Acyclic) (hR : IsADR N R) (s : ℕ) (pos : ℕ → Option E)
    (hI4 : ∀ e, {k | pos k = some e}.encard ≤ (Occ R s e).encard) (e : E) :
    {k | moveTokens R s pos k = some e}.encard ≤ (Occ R (s+1) e).encard := by
  set Stay : Set ℕ := {k | pos k = some e ∧ moveTokens R s pos k = some e}
  set In : Set ℕ := {k | pos k ≠ some e ∧ moveTokens R s pos k = some e}
  set OS : Set (ι × ℕ) := {p | p ∈ Occ R s e ∧ R.leave p.1 p.2 ≠ (s : ℕ∞)}
  set OI : Set (ι × ℕ) := {p | ∃ j, p.2 = j + 1 ∧ j + 1 < (R.route p.1).length ∧
      R.leave p.1 j = (s : ℕ∞) ∧ (R.route p.1)[j+1]? = some e}
  have hM : {k | moveTokens R s pos k = some e} ⊆ Stay ∪ In := by
    intro k hk
    by_cases h : pos k = some e
    · exact Or.inl ⟨h, hk⟩
    · exact Or.inr ⟨h, hk⟩
  -- Stay
  have hStay : Stay.encard ≤ OS.encard := by
    by_cases hT : ∃ k, pos k = some e
    · have hne : (Occ R s e).Nonempty := by
        obtain ⟨k, hk⟩ := hT
        have h1 : ({k | pos k = some e} : Set ℕ).Nonempty := ⟨k, hk⟩
        have := le_trans (Set.one_le_encard_iff_nonempty.2 h1) (hI4 e)
        exact Set.one_le_encard_iff_nonempty.1 this
      obtain ⟨⟨i0, j0⟩, hp0⟩ := hne
      obtain ⟨⟨a, j⟩, hl⟩ := leaver_some hR ⟨i0, j0, hp0.1, hp0.2⟩
      have hs := leaver_spec hl
      obtain ⟨m, hm, hmin⟩ : ∃ m, pos m = some e ∧ ∀ h < m, pos h ≠ some e := by
        classical
        exact ⟨Nat.find hT, Nat.find_spec hT, fun h hh => Nat.find_min hT hh⟩
      have hmv : moveTokens R s pos m ≠ some e := by
        rw [move_go hm hmin hl]
        intro h2; exact no_self_loop hN hR hs.2.1 h2
      have hsub : Stay ⊆ {k | pos k = some e} \ {m} := by
        intro k ⟨hk1, hk2⟩
        refine ⟨hk1, ?_⟩
        rintro rfl; exact hmv hk2
      have hOS : OS = Occ R s e \ {(a, j)} := by
        ext ⟨i, jj⟩
        simp only [OS, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rintro ⟨⟩; exact h2 hs.2.2
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun h3 => h2 ?_⟩
          have := leaver_eq hR ⟨h1.1.1, h1.2, h3⟩
          rw [hl] at this; exact (Option.some.inj this).symm
      have hmem : (a, j) ∈ Occ R s e := ⟨inBuf_of_leave hR hs.1 hs.2.2, hs.2.1⟩
      have e1 := Set.encard_diff_singleton_add_one (s := {k | pos k = some e}) hm
      have e2 := Set.encard_diff_singleton_add_one hmem
      have h3 : ({k | pos k = some e} \ {m}).encard + 1 ≤ (Occ R s e \ {(a, j)}).encard + 1 := by
        rw [e1, e2]; exact hI4 e
      rw [hOS]
      exact le_trans (Set.encard_le_encard hsub)
        ((ENat.add_le_add_iff_right ENat.one_ne_top).1 h3)
    · have : Stay = ∅ := by
        ext k; simp only [Stay, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -⟩; exact hT ⟨k, h1⟩
      rw [this]; simp
  -- In
  have hIn : In.encard ≤ OI.encard := by
    let f : ℕ → Option (ι × ℕ) := fun k =>
      ((pos k).bind (fun e0 => leaver R e0 s)).map (fun p => (p.1, p.2 + 1))
    have hspec : ∀ k ∈ In, ∃ e0 a j, pos k = some e0 ∧ (∀ h < k, pos h ≠ some e0) ∧
        leaver R e0 s = some (a, j) ∧ (R.route a)[j+1]? = some e ∧ f k = some (a, j+1) := by
      intro k ⟨hk1, hk2⟩
      obtain ⟨e0, hk, hc⟩ := move_cases hk2
      rcases hc with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨hmin, a, j, hl, hj⟩
      · exact absurd hk hk1
      · exact absurd hk hk1
      · exact ⟨e0, a, j, hk, hmin, hl, hj, by simp [f, hk, hl]⟩
    have hmaps : Set.MapsTo f In (Option.some '' OI) := by
      intro k hk
      obtain ⟨e0, a, j, hk, hmin, hl, hj, hf⟩ := hspec k hk
      have hs := leaver_spec hl
      refine ⟨(a, j+1), ⟨j, rfl, ?_, hs.2.2, hj⟩, hf.symm⟩
      exact (List.getElem?_eq_some_iff.1 hj).1
    have hinj : Set.InjOn f In := by
      intro k hk k' hk' hff
      obtain ⟨e0, a, j, hk0, hmin, hl, hj, hf⟩ := hspec k hk
      obtain ⟨e0', a', j', hk0', hmin', hl', hj', hf'⟩ := hspec k' hk'
      rw [hf, hf'] at hff
      simp only [Option.some.injEq, Prod.mk.injEq] at hff
      obtain ⟨rfl, hjj⟩ := hff
      have hjj' : j = j' := by omega
      subst hjj'
      have e0eq : e0 = e0' := by
        have h1 := (leaver_spec hl).2.1; have h2 := (leaver_spec hl').2.1
        rw [h1] at h2; exact Option.some.inj h2
      subst e0eq
      rcases lt_trichotomy k k' with h | h | h
      · exact absurd hk0 (hmin' k h)
      · exact h
      · exact absurd hk0' (hmin k' h)
    have := Set.encard_le_encard_of_injOn hmaps hinj
    rwa [Option.some_injective _ |>.encard_image] at this
  have hdisj : Disjoint OS OI := by
    rw [Set.disjoint_left]
    rintro ⟨i, jj⟩ ⟨⟨hb, _⟩, _⟩ ⟨j, hj, -, hl, -⟩
    simp only at hj hl hb
    subst hj
    have h1 := hb.2.1
    rw [arrive_succ, hl] at h1
    exact absurd h1 (by simpa using (ENat.coe_lt_coe.2 (Nat.lt_succ_self s)))
  have hsubOcc : OS ∪ OI ⊆ Occ R (s+1) e := by
    rintro ⟨i, jj⟩ (⟨⟨hb, hr⟩, hl⟩ | ⟨j, hj, hlen, hl, hr⟩)
    · refine ⟨⟨hb.1, le_trans hb.2.1 (by exact_mod_cast Nat.le_succ s), ?_⟩, hr⟩
      have : (s : ℕ∞) < R.leave i jj := lt_of_le_of_ne hb.2.2 (Ne.symm hl)
      exact_mod_cast Order.add_one_le_of_lt this
    · simp only at hj hlen hl hr
      subst hj
      refine ⟨⟨hlen, ?_, ?_⟩, hr⟩
      · rw [arrive_succ, hl]; push_cast; exact le_rfl
      · have := arrive_le_leave hR hlen
        rw [arrive_succ, hl] at this; exact_mod_cast this
  calc {k | moveTokens R s pos k = some e}.encard ≤ (Stay ∪ In).encard := Set.encard_le_encard hM
    _ ≤ Stay.encard + In.encard := Set.encard_union_le _ _
    _ ≤ OS.encard + OI.encard := add_le_add hStay hIn
    _ = (OS ∪ OI).encard := (Set.encard_union_eq hdisj).symm
    _ ≤ (Occ R (s+1) e).encard := Set.encard_le_encard hsubOcc

/-- I4 ((p1)): the number of tokens in a buffer is at most the number of agents in it. -/
theorem inv4 (hN : N.Acyclic) (hR : IsADR N R) : ∀ d e,
    {k | (tokState R ζ r0 d).2 k = some e}.encard ≤ (Occ R (r0 + d) e).encard := by
  intro d
  induction d with
  | zero =>
    intro e
    apply encard_le_of_sub_single (x := 1)
    · intro k hk
      simp only [Set.mem_setOf_eq] at hk
      rw [tok_zero] at hk
      rcases hz : zBuf R ζ r0 with _ | U
      · simp [hz] at hk
      · simp only [hz] at hk; split_ifs at hk with h; exact h
    · rintro ⟨k, hk⟩
      simp only [Set.mem_setOf_eq] at hk
      rw [tok_zero] at hk
      rcases hz : zBuf R ζ r0 with _ | U
      · simp [hz] at hk
      · simp only [hz] at hk
        split_ifs at hk
        cases hk
        obtain ⟨j, hj1, hj2⟩ := zBuf_some hz
        exact ⟨(ζ, j), hj1, hj2⟩
  | succ d ih =>
    intro e
    have hc := core_count hN hR (r0 + d) _ ih e
    rw [show r0 + (d+1) = r0 + d + 1 by omega]
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq]
      simp only
      by_cases heU : e = U
      · subst heU
        apply encard_le_of_sub_single (x := (tokState R ζ r0 d).1 + 1)
        · intro k hk
          simp only [Set.mem_setOf_eq] at hk
          by_contra hne
          rw [Function.update_of_ne hne] at hk; exact hU k hk
        · intro _
          obtain ⟨j, hj1, hj2⟩ := zBuf_some hz
          exact ⟨(ζ, j), hj1, hj2⟩
      · refine le_trans (Set.encard_le_encard ?_) hc
        intro k hk
        simp only [Set.mem_setOf_eq] at hk ⊢
        by_cases hkc : k = (tokState R ζ r0 d).1 + 1
        · subst hkc; simp at hk; exact absurd hk.symm heU
        · rwa [Function.update_of_ne hkc] at hk
    · rw [heq]; exact hc

theorem occ_nonempty (hN : N.Acyclic) (hR : IsADR N R) {d k : ℕ} {e : E}
    (hk : (tokState R ζ r0 d).2 k = some e) :
    ∃ i j, R.inBuf i j (r0 + d) ∧ (R.route i)[j]? = some e := by
  have h1 : ({k | (tokState R ζ r0 d).2 k = some e} : Set ℕ).Nonempty := ⟨k, hk⟩
  have := le_trans (Set.one_le_encard_iff_nonempty.2 h1) (inv4 ζ r0 hN hR d e)
  obtain ⟨⟨i, j⟩, hp⟩ := Set.one_le_encard_iff_nonempty.1 this
  exact ⟨i, j, hp.1, hp.2⟩

end Count

section Main

variable {V E ι : Type} [Fintype V] {N : Network V E} {R : RunData ι E V}
variable (ζ : ι) (r0 : ℕ)

/-- Lemma 1 of the paper, in time-indexed form: a token `k` sitting in the buffer of an edge
`e ∈ Gζ` at time `r0 + d` satisfies `r0 + d + L_{tail e, dζ} + 1 ≤ r0 + L_{oζ dζ} + k`. -/
theorem invP (hN : N.Acyclic) (hR : IsADR N R) (hr0 : R.entry ζ ≤ r0) : ∀ d k e,
    (tokState R ζ r0 d).2 k = some e → e ∈ Gz N R ζ →
    r0 + d + N.longest (N.tail e) (R.dest ζ) + 1 ≤
      r0 + N.longest (R.orig ζ) (R.dest ζ) + k := by
  intro d
  induction d with
  | zero =>
    intro k e hk he
    rw [tok_zero] at hk
    rcases hz : zBuf R ζ r0 with _ | U
    · simp [hz] at hk
    · simp only [hz] at hk
      split_ifs at hk with h1
      cases hk
      have hG := mem_Gz_iff.1 he
      have := longest_mono N hN (zBuf_props ζ hR hz).1
        (reach_trans N (reach_edge N _) hG.2)
      omega
  | succ d ih =>
    have key : ∀ k e, moveTokens R (r0+d) (tokState R ζ r0 d).2 k = some e → e ∈ Gz N R ζ →
        r0 + (d+1) + N.longest (N.tail e) (R.dest ζ) + 1 ≤
          r0 + N.longest (R.orig ζ) (R.dest ζ) + k := by
      intro k e hm he
      obtain ⟨e0, hk, hc⟩ := move_cases hm
      rcases hc with ⟨⟨h, hh, hph⟩, rfl⟩ | ⟨_, hl, rfl⟩ | ⟨_, a, j, hl, hj⟩
      · have := ih h e hph he; omega
      · obtain ⟨i, jj, hb, hr⟩ := occ_nonempty ζ r0 hN hR hk
        obtain ⟨p, hp⟩ := leaver_some hR ⟨i, jj, hb, hr⟩
        rw [hl] at hp; cases hp
      · have hs := leaver_spec hl
        have hcons := path_consec N (hR.1 a).1 hs.2.1 hj
        have hG := mem_Gz_iff.1 he
        have hhd : Reach N (N.head e0) (R.dest ζ) := by
          rw [hcons]; exact reach_trans N (reach_edge N e) hG.2
        have he0 : e0 ∈ Gz N R ζ := mem_Gz_iff.2 ⟨inv3 ζ r0 hR d k e0 hk, hhd⟩
        have h1 := ih k e0 hk he0
        have h2 := longest_edge N hN hhd
        rw [hcons] at h2
        omega
    intro k e hk he
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq] at hk
      simp only at hk
      by_cases hkc : k = (tokState R ζ r0 d).1 + 1
      · subst hkc
        simp at hk
        subst hk
        obtain ⟨j', hin, hj'⟩ := zBuf_some hz
        by_cases harr : R.arrive ζ j' ≤ ((r0 + d : ℕ) : ℕ∞)
        · have hin' : R.inBuf ζ j' (r0 + d) :=
            ⟨hin.1, harr, le_trans (by exact_mod_cast Nat.le_succ (r0+d)) hin.2.2⟩
          have hz' : zBuf R ζ (r0 + d) = some U := by rw [zBuf_eq hR hin', hj']
          obtain ⟨h, hh⟩ := inv2 ζ r0 d U hz'
          have h1 := ih h U hh he
          have h2 := inv1 ζ r0 d h (by rw [hh]; simp)
          omega
        · exfalso
          rcases j' with _ | m
          · rw [arrive_zero] at harr
            exact harr (by exact_mod_cast (show R.entry ζ ≤ r0 + d by omega))
          · rw [arrive_succ] at harr
            have h1 := hin.2.1
            rw [arrive_succ] at h1
            have hle : R.leave ζ m ≤ ((r0 + d : ℕ) : ℕ∞) := by
              have : R.leave ζ m + 1 ≤ ((r0 + d : ℕ) : ℕ∞) + 1 := by exact_mod_cast h1
              exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
            have heqm : R.leave ζ m = ((r0 + d : ℕ) : ℕ∞) := by
              refine le_antisymm hle ?_
              by_contra hc
              exact harr (Order.add_one_le_of_lt (lt_of_not_ge hc))
            have hmlen : m < (R.route ζ).length := by have := hin.1; omega
            have hinm := inBuf_of_leave hR hmlen heqm
            obtain ⟨U', hU'⟩ : ∃ U', (R.route ζ)[m]? = some U' :=
              ⟨_, List.getElem?_eq_getElem hmlen⟩
            have hz' : zBuf R ζ (r0 + d) = some U' := by rw [zBuf_eq hR hinm, hU']
            obtain ⟨h0, hh0⟩ := inv2 ζ r0 d U' hz'
            classical
            have hex : ∃ h, (tokState R ζ r0 d).2 h = some U' := ⟨h0, hh0⟩
            have hl := leaver_eq hR ⟨hmlen, hU', heqm⟩
            have := move_go (Nat.find_spec hex) (fun h hh => Nat.find_min hex hh) hl
            rw [hj'] at this
            exact hU _ this
      · rw [Function.update_of_ne hkc] at hk; exact key k e hk he
    · rw [heq] at hk; exact key k e hk he

/-- Every token with index in `[1, count]` has been produced in `ζ`'s buffer at some time. -/
theorem invE : ∀ d k, 1 ≤ k → k ≤ (tokState R ζ r0 d).1 →
    ∃ d' U, (tokState R ζ r0 d').2 k = some U ∧ zBuf R ζ (r0 + d') = some U := by
  intro d
  induction d with
  | zero =>
    intro k hk1 hk2
    rcases hz : zBuf R ζ r0 with _ | U
    · rw [tokState.eq_1, hz] at hk2; simp at hk2; omega
    · have : k = 1 := by have := cnt_zero (R := R) ζ r0; omega
      subst this
      exact ⟨0, U, by rw [tok_zero, hz]; simp, by simpa using hz⟩
  | succ d ih =>
    intro k hk1 hk2
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq] at hk2; simp only at hk2
      by_cases hkc : k = (tokState R ζ r0 d).1 + 1
      · subst hkc
        exact ⟨d+1, U, by rw [heq]; simp, by rw [← Nat.add_assoc]; exact hz⟩
      · exact ih k hk1 (by omega)
    · rw [heq] at hk2; exact ih k hk1 hk2

/-- Each token that was once in `Gζ` eventually exits `Gζ`, carried by the agent leaving its
buffer. -/
theorem exit_lemma (hN : N.Acyclic) (hR : IsADR N R) (hr0 : R.entry ζ ≤ r0) {d0 k : ℕ} {e0 : E}
    (h0 : (tokState R ζ r0 d0).2 k = some e0) (hG : e0 ∈ Gz N R ζ) :
    ∃ d e a j, (tokState R ζ r0 d).2 k = some e ∧ e ∈ Gz N R ζ ∧
      (∀ h < k, (tokState R ζ r0 d).2 h ≠ some e) ∧ leaver R e (r0 + d) = some (a, j) ∧
      (∀ f, (R.route a)[j+1]? = some f → f ∉ Gz N R ζ) ∧
      (∀ e', (tokState R ζ r0 (d+1)).2 k = some e' → e' ∉ Gz N R ζ) := by
  set S : Set ℕ := {d | ∃ e, e ∈ Gz N R ζ ∧ (tokState R ζ r0 d).2 k = some e}
  have hbdd : BddAbove S := by
    refine ⟨N.longest (R.orig ζ) (R.dest ζ) + k, ?_⟩
    rintro d ⟨e, he, hk⟩
    have := invP ζ r0 hN hR hr0 d k e hk he; omega
  have hmem : sSup S ∈ S := Nat.sSup_mem ⟨d0, e0, hG, h0⟩ hbdd
  have hnot : sSup S + 1 ∉ S := fun h => by have := le_csSup hbdd h; omega
  obtain ⟨e, he, hk⟩ := hmem
  set d := sSup S
  have hmv : (tokState R ζ r0 (d+1)).2 k = moveTokens R (r0+d) (tokState R ζ r0 d).2 k := by
    rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
    · rw [heq]; simp only
      have := inv1 ζ r0 d k (by rw [hk]; simp)
      rw [Function.update_of_ne (by omega)]
    · rw [heq]
  by_cases hsm : ∃ h < k, (tokState R ζ r0 d).2 h = some e
  · exact absurd ⟨e, he, by rw [hmv, move_stay1 hk hsm]⟩ hnot
  have hmin : ∀ h < k, (tokState R ζ r0 d).2 h ≠ some e := by push_neg at hsm; exact hsm
  rcases hl : leaver R e (r0 + d) with _ | ⟨a, j⟩
  · exact absurd ⟨e, he, by rw [hmv, move_stay2 hk hmin hl]⟩ hnot
  refine ⟨d, e, a, j, hk, he, hmin, hl, ?_, ?_⟩
  · intro f hf hfG
    exact hnot ⟨f, hfG, by rw [hmv, move_go hk hmin hl, hf]⟩
  · intro e' he' he'G
    exact hnot ⟨e', he'G, he'⟩

end Main


section Extra

variable {V E ι : Type} [Fintype V] {N : Network V E} {R : RunData ι E V}
variable (ζ : ι) (r0 : ℕ)

theorem tokAt_eq {s k : ℕ} (h : r0 ≤ s) :
    tokAt R ζ r0 s k = (tokState R ζ r0 (s - r0)).2 k := by
  simp [tokAt, h]

theorem le_of_tokAt {s k : ℕ} {e : E} (h : tokAt R ζ r0 s k = some e) : r0 ≤ s := by
  by_contra hc; simp [tokAt, hc] at h

theorem tokAt_bound (hN : N.Acyclic) (hR : IsADR N R) (hr0 : R.entry ζ ≤ r0) {s k : ℕ} {e : E}
    (h : tokAt R ζ r0 s k = some e) (he : e ∈ Gz N R ζ) :
    s + N.longest (N.tail e) (R.dest ζ) + 1 ≤ r0 + N.longest (R.orig ζ) (R.dest ζ) + k := by
  have hs := le_of_tokAt ζ r0 h
  rw [tokAt_eq ζ r0 hs] at h
  have := invP ζ r0 hN hR hr0 _ k e h he
  omega

/-- (p3): a production at time `r0 + d + 1` happens only while `ζ` stays in his buffer. -/
theorem prod_stay (hR : IsADR N R) (hr0 : R.entry ζ ≤ r0) (d : ℕ) (U : E)
    (hz : zBuf R ζ (r0 + d + 1) = some U)
    (hU : ∀ k, moveTokens R (r0 + d) (tokState R ζ r0 d).2 k ≠ some U) :
    ∃ j, R.inBuf ζ j (r0 + d) ∧ R.inBuf ζ j (r0 + d + 1) := by
  obtain ⟨j', hin, hj'⟩ := zBuf_some hz
  by_cases harr : R.arrive ζ j' ≤ ((r0 + d : ℕ) : ℕ∞)
  · exact ⟨j', ⟨hin.1, harr, le_trans (by exact_mod_cast Nat.le_succ (r0+d)) hin.2.2⟩, hin⟩
  · exfalso
    rcases j' with _ | m
    · rw [arrive_zero] at harr
      exact harr (by exact_mod_cast (show R.entry ζ ≤ r0 + d by omega))
    · rw [arrive_succ] at harr
      have h1 := hin.2.1
      rw [arrive_succ] at h1
      have hle : R.leave ζ m ≤ ((r0 + d : ℕ) : ℕ∞) := by
        have : R.leave ζ m + 1 ≤ ((r0 + d : ℕ) : ℕ∞) + 1 := by exact_mod_cast h1
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
      have heqm : R.leave ζ m = ((r0 + d : ℕ) : ℕ∞) := by
        refine le_antisymm hle ?_
        by_contra hc
        exact harr (Order.add_one_le_of_lt (lt_of_not_ge hc))
      have hmlen : m < (R.route ζ).length := by have := hin.1; omega
      have hinm := inBuf_of_leave hR hmlen heqm
      obtain ⟨U', hU'⟩ : ∃ U', (R.route ζ)[m]? = some U' :=
        ⟨_, List.getElem?_eq_getElem hmlen⟩
      have hz' : zBuf R ζ (r0 + d) = some U' := by rw [zBuf_eq hR hinm, hU']
      obtain ⟨h0, hh0⟩ := inv2 ζ r0 d U' hz'
      classical
      have hex : ∃ h, (tokState R ζ r0 d).2 h = some U' := ⟨h0, hh0⟩
      have hl := leaver_eq hR ⟨hmlen, hU', heqm⟩
      have := move_go (Nat.find_spec hex) (fun h hh => Nat.find_min hex hh) hl
      rw [hj'] at this
      exact hU _ this

end Extra

end ADRT1Aux

open ADRT1Aux

theorem solution {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (s : ℕ) (hs : r0 < s) (hnew : produced R ζ r0 (s - 1) < produced R ζ r0 s) : ∃ j : ℕ, R.inBuf ζ j (s - 1) ∧ R.inBuf ζ j s := by
  obtain ⟨d, rfl⟩ : ∃ d, s = r0 + d + 1 := ⟨s - r0 - 1, by omega⟩
  rw [produced, if_pos (by omega), show r0 + d + 1 - 1 - r0 = d by omega,
    produced, if_pos (by omega), show r0 + d + 1 - r0 = d + 1 by omega] at hnew
  rw [show r0 + d + 1 - 1 = r0 + d by omega]
  rcases step_cases ζ r0 d with ⟨U, hz, hU, heq⟩ | ⟨heq, _⟩
  · exact prod_stay ζ r0 hR hr0 d U hz hU
  · rw [heq] at hnew; exact absurd hnew (lt_irrefl _)
