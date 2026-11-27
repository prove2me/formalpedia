-- Prove2me | solution 1 for AtomicDynRouting.ResidenceTime.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:25.346867+00:00
-- url     : https://prove2.me/submissions/11dbdb1f-aa75-482c-8acf-e0073ebf4f78

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_CapacityRun

open AtomicDynRouting
open AtomicDynRouting.ResidenceTime
open AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem solution {ι V E : Type} [Fintype ι] [Fintype V] [Fintype E] (N : Network V E) (hN : N.Acyclic) (c : ℕ) (hc : 0 < c) (R : RunData ι E V) (hR : IsADRc N c R) (hsame : ∀ i j, R.entry i = R.entry j) (ζ : ι) : R.residenceTime ζ ≤ ((N.longest (R.orig ζ) (R.dest ζ) + (Fintype.card ι - 1) / c : ℕ) : ℕ∞) := by
  obtain ⟨hpath, hfin, hord, hcap⟩ := hR
  -- path concatenation
  have happ : ∀ (P Q : List E) (a b : V), N.IsPathFrom a b (P ++ Q) ↔
      ∃ v, N.IsPathFrom a v P ∧ N.IsPathFrom v b Q := by
    intro P
    induction P with
    | nil => intro Q a b; simp [Network.IsPathFrom]
    | cons e P ih =>
      intro Q a b
      simp only [List.cons_append, Network.IsPathFrom, ih]
      constructor
      · rintro ⟨h1, v, h2, h3⟩; exact ⟨v, ⟨h1, h2⟩, h3⟩
      · rintro ⟨v, ⟨h1, h2⟩, h3⟩; exact ⟨h1, v, h2, h3⟩
  -- every path of an acyclic network repeats no edge
  have hnodup : ∀ (P : List E) (a b : V), N.IsPathFrom a b P → P.Nodup := by
    intro P
    induction P with
    | nil => intro a b _; exact List.nodup_nil
    | cons e P ih =>
      intro a b h
      obtain ⟨h1, h2⟩ := h
      refine List.nodup_cons.2 ⟨?_, ih _ _ h2⟩
      intro he
      obtain ⟨P1, P2, rfl⟩ := List.append_of_mem he
      obtain ⟨v, hv1, hv2⟩ := (happ P1 (e :: P2) _ _).1 h2
      have hv : v = N.tail e := hv2.1.symm
      subst hv
      have hcyc : N.IsPathFrom (N.tail e) (N.tail e) (e :: P1) := ⟨rfl, hv1⟩
      exact List.cons_ne_nil _ _ (hN _ _ hcyc)
  have hlen : ∀ (P : List E) (a b : V), N.IsPathFrom a b P → P.length ≤ Fintype.card E := by
    intro P a b h
    exact (hnodup P a b h).length_le_card
  have hbdd : ∀ a b : V, BddAbove {n : ℕ | ∃ P : List E, N.IsPathFrom a b P ∧ P.length = n} := by
    intro a b
    refine ⟨Fintype.card E, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hlen P a b hP
  have hlong : ∀ (P : List E) (a b : V), N.IsPathFrom a b P → P.length ≤ N.longest a b := by
    intro P a b h
    exact le_csSup (hbdd a b) ⟨P, h, rfl⟩
  have hmL : (R.route ζ).length ≤ N.longest (R.orig ζ) (R.dest ζ) :=
    hlong _ _ _ (hpath ζ).1
  -- longest paths to the destination drop by at least one along any edge that can reach it
  have hstep : ∀ (e : E) (w : V) (P : List E), N.IsPathFrom (N.head e) w P →
      N.longest (N.head e) w + 1 ≤ N.longest (N.tail e) w := by
    intro e w P hP
    have hne : {n : ℕ | ∃ P : List E, N.IsPathFrom (N.head e) w P ∧ P.length = n}.Nonempty :=
      ⟨_, P, hP, rfl⟩
    obtain ⟨Q, hQ, hQl⟩ := Nat.sSup_mem hne (hbdd _ _)
    have := hlong (e :: Q) (N.tail e) w ⟨rfl, hQ⟩
    simp only [List.length_cons] at this
    unfold Network.longest at this ⊢
    rw [← hQl]; exact this
  -- the pairs (agent, route position) form a finite set
  have hpairs : {p : ι × ℕ | p.2 < (R.route p.1).length}.Finite := by
    have : {p : ι × ℕ | p.2 < (R.route p.1).length} ⊆
        (Set.univ : Set ι) ×ˢ (Set.Iio (Finset.univ.sup fun i => (R.route i).length)) := by
      rintro ⟨i, j⟩ hj
      simp only [Set.mem_ofPred_eq] at hj
      refine ⟨Set.mem_univ _, ?_⟩
      simp only [Set.mem_Iio]
      exact lt_of_lt_of_le hj (Finset.le_sup (f := fun i => (R.route i).length) (Finset.mem_univ i))
    exact Set.Finite.subset (Set.finite_univ.prod (Set.finite_Iio _)) this
  -- blocking: if ζ waits in the buffer of `e` at `s`, then the buffer holds more than `c`
  -- agents and exactly `c` others leave it at `s`
  have hblock : ∀ (i : ι) (j s : ℕ) (e : E), R.inBuf i j s → (R.route i)[j]? = some e →
      R.leave i j ≠ (s : ℕ∞) → c < bufCount R e s ∧ leaveCount R e s = c := by
    intro i j s e hin he hne
    have hsub : {p : ι × ℕ | p.2 < (R.route p.1).length ∧ (R.route p.1)[p.2]? = some e ∧
        R.leave p.1 p.2 = (s : ℕ∞)} ⊂
        {p : ι × ℕ | R.inBuf p.1 p.2 s ∧ (R.route p.1)[p.2]? = some e} := by
      refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
      · rintro ⟨a, k⟩ ⟨hk, hke, hkl⟩
        refine ⟨⟨hk, ?_, hkl.ge⟩, hke⟩
        rw [← hkl]; exact hord a k hk
      · intro heq
        have hmem : (i, j) ∈ {p : ι × ℕ | R.inBuf p.1 p.2 s ∧ (R.route p.1)[p.2]? = some e} :=
          ⟨hin, he⟩
        rw [← heq] at hmem
        exact hne hmem.2.2
    have hfinB : {p : ι × ℕ | R.inBuf p.1 p.2 s ∧ (R.route p.1)[p.2]? = some e}.Finite :=
      hpairs.subset (fun p hp => hp.1.1)
    have hlt : leaveCount R e s < bufCount R e s := Set.ncard_lt_ncard hsub hfinB
    have := hcap e s
    constructor
    · by_contra hh; push Not at hh; rw [min_eq_right hh] at this; omega
    · rw [this]; apply min_eq_left; by_contra hh; push Not at hh
      rw [min_eq_right hh.le] at this; omega
  -- an agent visits the buffers of his route in order
  have hchain : ∀ (i : ι) (j d : ℕ), j + d < (R.route i).length →
      R.leave i j + 1 ≤ R.arrive i (j + d + 1) := by
    intro i j d
    induction d with
    | zero => intro _; simp [RunData.arrive]
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hord i (j + d + 1) (by omega)
      have h3 : R.arrive i (j + (d + 1) + 1) = R.leave i (j + d + 1) + 1 := by
        simp [RunData.arrive]; ring_nf
      rw [h3]
      exact le_trans h1 (le_trans h2 le_self_add)
  -- an agent is in at most one buffer at a time
  have huniq : ∀ (i : ι) (j k s : ℕ), R.inBuf i j s → R.inBuf i k s → j = k := by
    have aux : ∀ (i : ι) (j k s : ℕ), R.inBuf i j s → R.inBuf i k s → j < k → False := by
      intro i j k s hj hk hjk
      obtain ⟨d, rfl⟩ : ∃ d, k = j + d + 1 := ⟨k - j - 1, by omega⟩
      have h1 := hchain i j d (by have := hk.1; omega)
      have h2 : R.leave i j + 1 ≤ (s : ℕ∞) := le_trans h1 hk.2.1
      have h3 : R.leave i j ≤ (s : ℕ∞) := le_trans le_self_add h2
      have h4 : R.leave i j = (s : ℕ∞) := le_antisymm h3 hj.2.2
      rw [h4] at h2
      norm_cast at h2
      omega
    intro i j k s hj hk
    rcases lt_trichotomy j k with h | h | h
    · exact (aux i j k s hj hk h).elim
    · exact h
    · exact (aux i k j s hk hj h).elim
  classical
  have hm : 0 < (R.route ζ).length := List.length_pos_of_ne_nil (hpath ζ).2
  obtain ⟨r, hr⟩ : ∃ r, R.entry ζ = r := ⟨_, rfl⟩
  have hent : ∀ i, R.entry i = r := fun i => (hsame i ζ).trans hr
  obtain ⟨h, hhdef⟩ : ∃ h : V → ℕ, ∀ v, h v = N.longest v (R.dest ζ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Rel, hRel⟩ : ∃ Rel : E → Prop, ∀ e, Rel e ↔
      ∃ P : List E, N.IsPathFrom (N.head e) (R.dest ζ) P := ⟨_, fun _ => Iff.rfl⟩
  have hstep' : ∀ e, Rel e → h (N.head e) + 1 ≤ h (N.tail e) := by
    intro e he; obtain ⟨P, hP⟩ := (hRel e).1 he; rw [hhdef, hhdef]; exact hstep e _ P hP
  have hRelback : ∀ e e', Rel e' → N.head e = N.tail e' → Rel e := by
    intro e e' he' hh
    obtain ⟨P, hP⟩ := (hRel e').1 he'
    exact (hRel e).2 ⟨e' :: P, hh.symm, hP⟩
  have hconsec : ∀ (P : List E) (a b : V), N.IsPathFrom a b P → ∀ (j : ℕ) (e e' : E),
      P[j]? = some e → P[j+1]? = some e' → N.head e = N.tail e' := by
    intro P
    induction P with
    | nil => intro a b _ j e e' he; simp at he
    | cons x P ih =>
      intro a b hP j e e' he he'
      obtain ⟨h1, h2⟩ := hP
      cases j with
      | zero =>
        simp at he he'
        subst he
        cases P with
        | nil => simp at he'
        | cons y Q =>
          simp at he'
          subst he'
          exact h2.1.symm
      | succ j =>
        simp only [List.getElem?_cons_succ] at he he'
        exact ih _ _ h2 j e e' he he'
  have hsuf : ∀ (P : List E) (a b : V), N.IsPathFrom a b P → ∀ (j : ℕ) (e : E),
      P[j]? = some e → ∃ Q : List E, N.IsPathFrom (N.head e) b Q := by
    intro P
    induction P with
    | nil => intro a b _ j e he; simp at he
    | cons x P ih =>
      intro a b hP j e he
      cases j with
      | zero => simp at he; subst he; exact ⟨P, hP.2⟩
      | succ j => simp only [List.getElem?_cons_succ] at he; exact ih _ _ hP.2 j e he
  have htrans : ∀ (i : ι) (k s : ℕ), r ≤ s → R.inBuf i k (s+1) →
      (R.inBuf i k s ∧ R.leave i k ≠ (s : ℕ∞)) ∨
      (1 ≤ k ∧ R.inBuf i (k-1) s ∧ R.leave i (k-1) = (s : ℕ∞)) := by
    intro i k s hs hin
    obtain ⟨hk, ha, hl⟩ := hin
    by_cases hk0 : k = 0
    · subst hk0
      left
      have ha0 : R.arrive i 0 = (r : ℕ∞) := by simp [RunData.arrive, hent]
      refine ⟨⟨hk, ?_, ?_⟩, ?_⟩
      · rw [ha0]; exact_mod_cast hs
      · exact le_trans (by exact_mod_cast Nat.le_succ s) hl
      · intro h'; rw [h'] at hl; norm_cast at hl; omega
    · have hak : R.arrive i k = R.leave i (k-1) + 1 := by simp [RunData.arrive, hk0]
      rw [hak] at ha
      have hlt : R.leave i (k-1) ≠ ⊤ := by
        intro ht; rw [ht] at ha; simp at ha
      obtain ⟨n, hn⟩ : ∃ n : ℕ, R.leave i (k-1) = n := ⟨_, (ENat.coe_toNat hlt).symm⟩
      rw [hn] at ha
      norm_cast at ha
      rcases Nat.lt_or_ge n s with hns | hns
      · left
        refine ⟨⟨hk, ?_, le_trans (by exact_mod_cast Nat.le_succ s) hl⟩, ?_⟩
        · rw [hak, hn]; exact_mod_cast hns
        · intro h'; rw [h'] at hl; norm_cast at hl; omega
      · right
        have hns' : n = s := by omega
        subst hns'
        refine ⟨by omega, ⟨by omega, ?_, hn.ge⟩, hn⟩
        rw [← hn]; exact hord i (k-1) (by omega)
  obtain ⟨Lv, hLv⟩ : ∃ Lv : ℕ → ι → ℕ → Prop, ∀ s i y, Lv s i y ↔ ∃ j e, R.inBuf i j s ∧
      (R.route i)[j]? = some e ∧ Rel e ∧ y ≤ s + h (N.tail e) := ⟨_, fun _ _ _ => Iff.rfl⟩
  have hback : ∀ (i : ι) (s y : ℕ), r ≤ s → Lv (s+1) i (y+1) → Lv s i (y+1) ∨
      ∃ j e, R.inBuf i j s ∧ (R.route i)[j]? = some e ∧ Rel e ∧ s + h (N.tail e) = y ∧
        R.leave i j ≠ (s : ℕ∞) := by
    intro i s y hs hL
    obtain ⟨k, e', hin, he', hrel, hy⟩ := (hLv _ _ _).1 hL
    rcases htrans i k s hs hin with ⟨hin0, hne⟩ | ⟨hk1, hin0, heq⟩
    · by_cases hlt : y + 1 ≤ s + h (N.tail e')
      · left; exact (hLv _ _ _).2 ⟨k, e', hin0, he', hrel, hlt⟩
      · right; exact ⟨k, e', hin0, he', hrel, by omega, hne⟩
    · left
      obtain ⟨e'', he''⟩ : ∃ e'', (R.route i)[k-1]? = some e'' :=
        ⟨_, List.getElem?_eq_getElem hin0.1⟩
      have hc := hconsec _ _ _ (hpath i).1 (k-1) e'' e' he''
        (by rw [Nat.sub_add_cancel hk1]; exact he')
      have hrel'' := hRelback e'' e' hrel hc
      have := hstep' e'' hrel''
      rw [hc] at this
      exact (hLv _ _ _).2 ⟨k-1, e'', hin0, he'', hrel'', by omega⟩
  have hmove : ∀ (i : ι) (j s y : ℕ) (e : E), r ≤ s → R.inBuf i j s →
      R.leave i j = (s : ℕ∞) → (R.route i)[j]? = some e → Lv (s+1) i y →
      Rel e ∧ y ≤ s + h (N.tail e) := by
    intro i j s y e hs hin hl he hL
    obtain ⟨k, e', hin', he', hrel, hy⟩ := (hLv _ _ _).1 hL
    rcases htrans i k s hs hin' with ⟨hin0, hne⟩ | ⟨hk1, hin0, heq⟩
    · have := huniq i j k s hin hin0; subst this; exact absurd hl hne
    · have hjk := huniq i j (k-1) s hin hin0
      have hc := hconsec _ _ _ (hpath i).1 j e e' he
        (by rw [hjk, Nat.sub_add_cancel hk1]; exact he')
      have hrel'' := hRelback e e' hrel hc
      have := hstep' e hrel''
      rw [hc] at this
      exact ⟨hrel'', by omega⟩
  have hin0 : R.inBuf ζ 0 r := by
    refine ⟨hm, ?_, ?_⟩
    · simp [RunData.arrive, hr]
    · have := hord ζ 0 hm
      simp only [RunData.arrive, if_pos rfl, hr] at this
      exact this
  obtain ⟨y0, hy0⟩ : ∃ y0, y0 = r + h (R.orig ζ) := ⟨_, rfl⟩
  have hinv : ∀ d : ℕ, ∃ T : Finset ι, ζ ∈ T ∧ ∀ y, y0 < y →
      (T.filter (fun i => Lv (r+d) i y)).Nonempty →
      (T.filter (fun i => Lv (r+d) i y)).card + c * (y - y0) ≤ T.card := by
    intro d
    induction d with
    | zero =>
      refine ⟨{ζ}, Finset.mem_singleton_self _, ?_⟩
      intro y hy hne
      exfalso
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_singleton] at hi
      obtain ⟨hiζ, hL⟩ := hi
      rw [hiζ] at hL
      obtain ⟨j, e, hin, he, -, hle⟩ := (hLv _ _ _).1 hL
      have := huniq ζ j 0 _ hin (by simpa using hin0)
      subst this
      obtain ⟨x, P, hxP⟩ := List.exists_cons_of_ne_nil (hpath ζ).2
      have hp := (hpath ζ).1
      rw [hxP] at hp he
      simp at he
      subst he
      rw [hp.1] at hle
      omega
    | succ d ih =>
      obtain ⟨T, hζT, hI⟩ := ih
      obtain ⟨s, hs⟩ : ∃ s, s = r + d := ⟨_, rfl⟩
      rw [← hs] at hI
      obtain ⟨New, hNew⟩ : ∃ New : Finset ι, ∀ i, i ∈ New ↔ ∃ j e, j < (R.route i).length ∧
          (R.route i)[j]? = some e ∧ R.leave i j = (s : ℕ∞) ∧ ∃ k ∈ T, ∃ j',
          R.inBuf k j' s ∧ (R.route k)[j']? = some e ∧ R.leave k j' ≠ (s : ℕ∞) :=
        ⟨Finset.univ.filter (fun i => ∃ j e, j < (R.route i).length ∧
          (R.route i)[j]? = some e ∧ R.leave i j = (s : ℕ∞) ∧ ∃ k ∈ T, ∃ j',
          R.inBuf k j' s ∧ (R.route k)[j']? = some e ∧ R.leave k j' ≠ (s : ℕ∞)),
          fun i => by simp⟩
      refine ⟨T ∪ New, Finset.mem_union_left _ hζT, ?_⟩
      intro y hy hne
      have hrs : r ≤ s := by omega
      have hs1 : r + (d+1) = s + 1 := by omega
      rw [hs1] at hne ⊢
      obtain ⟨x, rfl⟩ : ∃ x, y = x + 1 := ⟨y - 1, by omega⟩
      have hTsub : T ⊆ T ∪ New := Finset.subset_union_left
      have hcardsd : ((T ∪ New) \ T).card = (T ∪ New).card - T.card :=
        Finset.card_sdiff_of_subset hTsub
      have hTle : T.card ≤ (T ∪ New).card := Finset.card_le_card hTsub
      by_cases hA : ∃ k ∈ T, ∃ j e, R.inBuf k j s ∧ (R.route k)[j]? = some e ∧ Rel e ∧
          s + h (N.tail e) = x ∧ R.leave k j ≠ (s : ℕ∞)
      · obtain ⟨k, hkT, j, e, hin, he, hrel, hlev, hne'⟩ := hA
        obtain ⟨-, hlc⟩ := hblock k j s e hin he hne'
        obtain ⟨S, hS⟩ : ∃ S : Finset ι, ∀ i, i ∈ S ↔ ∃ j, j < (R.route i).length ∧
            (R.route i)[j]? = some e ∧ R.leave i j = (s : ℕ∞) :=
          ⟨Finset.univ.filter (fun i => ∃ j, j < (R.route i).length ∧
            (R.route i)[j]? = some e ∧ R.leave i j = (s : ℕ∞)), fun i => by simp⟩
        have hSc : S.card = c := by
          rw [← hlc]
          unfold leaveCount
          rw [← Set.ncard_coe_finset]
          have hSeq : (S : Set ι) = Prod.fst '' {p : ι × ℕ | p.2 < (R.route p.1).length ∧
              (R.route p.1)[p.2]? = some e ∧ R.leave p.1 p.2 = (s : ℕ∞)} := by
            ext i
            constructor
            · intro hi
              obtain ⟨j', hj', he', hl'⟩ := (hS i).1 (Finset.mem_coe.1 hi)
              exact ⟨(i, j'), ⟨hj', he', hl'⟩, rfl⟩
            · rintro ⟨⟨i', j'⟩, ⟨hj', he', hl'⟩, rfl⟩
              exact Finset.mem_coe.2 ((hS i').2 ⟨j', hj', he', hl'⟩)
          rw [hSeq]
          apply Set.ncard_image_of_injOn
          rintro ⟨i, j1⟩ ⟨hj1, he1, -⟩ ⟨i', j2⟩ ⟨hj2, he2, -⟩ hii
          simp only at hii
          subst hii
          have hnd := hnodup _ _ _ (hpath i).1
          simp only at hj1 hj2 he1 he2
          rw [List.getElem?_eq_getElem hj1] at he1
          rw [List.getElem?_eq_getElem hj2] at he2
          have := (hnd.getElem_inj_iff (i := j1) (j := j2) (hi := hj1) (hj := hj2)).1
            (by rw [Option.some_inj.1 he1, Option.some_inj.1 he2])
          rw [this]
        have hsub1 : (T ∪ New).filter (fun i => Lv (s+1) i (x+1)) ∪ S ⊆
            T.filter (fun i => Lv s i x) ∪ ((T ∪ New) \ T) := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · rw [Finset.mem_filter] at hi
            obtain ⟨hiT', hL⟩ := hi
            by_cases hiT : i ∈ T
            · apply Finset.mem_union_left
              rw [Finset.mem_filter]
              refine ⟨hiT, ?_⟩
              rcases hback i s x hrs hL with h' | ⟨j', e', hin', he', hrel', hlev', -⟩
              · obtain ⟨j', e', a1, a2, a3, a4⟩ := (hLv _ _ _).1 h'
                exact (hLv _ _ _).2 ⟨j', e', a1, a2, a3, by omega⟩
              · exact (hLv _ _ _).2 ⟨j', e', hin', he', hrel', by omega⟩
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hiT', hiT⟩)
          · obtain ⟨j', hj', he', hl'⟩ := (hS i).1 hi
            have hin' : R.inBuf i j' s := ⟨hj', by rw [← hl']; exact hord i j' hj', hl'.ge⟩
            by_cases hiT : i ∈ T
            · exact Finset.mem_union_left _ (Finset.mem_filter.2
                ⟨hiT, (hLv _ _ _).2 ⟨j', e, hin', he', hrel, hlev.ge⟩⟩)
            · refine Finset.mem_union_right _ (Finset.mem_sdiff.2
                ⟨Finset.mem_union_right _ ?_, hiT⟩)
              exact (hNew i).2 ⟨j', e, hj', he', hl', k, hkT, j, hin, he, hne'⟩
        have hdisj : Disjoint ((T ∪ New).filter (fun i => Lv (s+1) i (x+1))) S := by
          rw [Finset.disjoint_left]
          intro i hi hiS
          obtain ⟨-, hL⟩ := Finset.mem_filter.1 hi
          obtain ⟨j', hj', he', hl'⟩ := (hS i).1 hiS
          have hin' : R.inBuf i j' s := ⟨hj', by rw [← hl']; exact hord i j' hj', hl'.ge⟩
          obtain ⟨-, hle⟩ := hmove i j' s (x+1) e hrs hin' hl' he' hL
          omega
        have h1 := Finset.card_le_card hsub1
        rw [Finset.card_union_of_disjoint hdisj] at h1
        have h2 := Finset.card_union_le (T.filter (fun i => Lv s i x)) ((T ∪ New) \ T)
        rw [hcardsd] at h2
        by_cases hx : y0 < x
        · have hne2 : (T.filter (fun i => Lv s i x)).Nonempty :=
            ⟨k, Finset.mem_filter.2 ⟨hkT, (hLv _ _ _).2 ⟨j, e, hin, he, hrel, hlev.ge⟩⟩⟩
          have h3 := hI x hx hne2
          have hmul : c * (x + 1 - y0) = c * (x - y0) + c := by
            rw [show x + 1 - y0 = (x - y0) + 1 by omega, mul_add, mul_one]
          rw [hmul]
          omega
        · have hmul : c * (x + 1 - y0) = c := by
            rw [show x + 1 - y0 = 1 by omega, mul_one]
          rw [hmul]
          have := Finset.card_filter_le T (fun i => Lv s i x)
          omega
      · have hsub : (T ∪ New).filter (fun i => Lv (s+1) i (x+1)) ⊆
            T.filter (fun i => Lv s i (x+1)) ∪ ((T ∪ New) \ T) := by
          intro i hi
          obtain ⟨hiT', hL⟩ := Finset.mem_filter.1 hi
          by_cases hiT : i ∈ T
          · apply Finset.mem_union_left
            refine Finset.mem_filter.2 ⟨hiT, ?_⟩
            rcases hback i s x hrs hL with h' | ⟨j', e', hin', he', hrel', hlev', hne'⟩
            · exact h'
            · exact absurd ⟨i, hiT, j', e', hin', he', hrel', hlev', hne'⟩ hA
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hiT', hiT⟩)
        have hne2 : (T.filter (fun i => Lv s i (x+1))).Nonempty := by
          obtain ⟨i, hi⟩ := hne
          obtain ⟨hiT', hL⟩ := Finset.mem_filter.1 hi
          by_cases hiT : i ∈ T
          · rcases hback i s x hrs hL with h' | ⟨j', e', hin', he', hrel', hlev', hne'⟩
            · exact ⟨i, Finset.mem_filter.2 ⟨hiT, h'⟩⟩
            · exact absurd ⟨i, hiT, j', e', hin', he', hrel', hlev', hne'⟩ hA
          · have hiN : i ∈ New := by
              rcases Finset.mem_union.1 hiT' with h' | h'
              · exact absurd h' hiT
              · exact h'
            obtain ⟨j', e', hj', he', hl', k, hkT, j'', hin'', he'', hne''⟩ := (hNew i).1 hiN
            have hin' : R.inBuf i j' s := ⟨hj', by rw [← hl']; exact hord i j' hj', hl'.ge⟩
            obtain ⟨hrel, hle⟩ := hmove i j' s (x+1) e' hrs hin' hl' he' hL
            exact ⟨k, Finset.mem_filter.2 ⟨hkT, (hLv _ _ _).2 ⟨j'', e', hin'', he'', hrel, hle⟩⟩⟩
        have h3 := hI (x+1) hy hne2
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (T.filter (fun i => Lv s i (x+1))) ((T ∪ New) \ T)
        omega
  obtain ⟨K, hK⟩ : ∃ K, K = (Fintype.card ι - 1) / c := ⟨_, rfl⟩
  have hbound : ∀ (s j : ℕ) (e : E), r ≤ s → R.inBuf ζ j s → (R.route ζ)[j]? = some e →
      s + h (N.tail e) ≤ y0 + K := by
    intro s j e hs hin he
    obtain ⟨d, rfl⟩ : ∃ d, s = r + d := ⟨s - r, by omega⟩
    obtain ⟨T, hζT, hI⟩ := hinv d
    have hrel : Rel e := (hRel e).2 (hsuf _ _ _ (hpath ζ).1 j e he)
    by_contra hcon
    push_neg at hcon
    have hy : y0 < r + d + h (N.tail e) := by omega
    have hne : (T.filter (fun i => Lv (r+d) i (r + d + h (N.tail e)))).Nonempty :=
      ⟨ζ, Finset.mem_filter.2 ⟨hζT, (hLv _ _ _).2 ⟨j, e, hin, he, hrel, le_rfl⟩⟩⟩
    have h1 := hI _ hy hne
    have h2 := hne.card_pos
    have h3 : T.card ≤ Fintype.card ι := Finset.card_le_univ T
    have h4 : c * (r + d + h (N.tail e) - y0) ≤ Fintype.card ι - 1 := by omega
    have h5 : r + d + h (N.tail e) - y0 ≤ (Fintype.card ι - 1) / c :=
      (Nat.le_div_iff_mul_le hc).2 (by rw [mul_comm]; exact h4)
    omega
  have hreach : ∀ d : ℕ, (∃ j, R.inBuf ζ j (r + d)) ∨
      R.leave ζ ((R.route ζ).length - 1) < ((r + d : ℕ) : ℕ∞) := by
    intro d
    induction d with
    | zero => left; exact ⟨0, by simpa using hin0⟩
    | succ d ih =>
      rcases ih with ⟨j, hin⟩ | hlt
      · by_cases hl : R.leave ζ j = ((r + d : ℕ) : ℕ∞)
        · by_cases hj : j + 1 < (R.route ζ).length
          · left
            have ha : R.arrive ζ (j+1) = ((r + (d+1) : ℕ) : ℕ∞) := by
              simp [RunData.arrive, hl]; push_cast; ring
            refine ⟨j+1, hj, ha.le, ?_⟩
            rw [← ha]; exact hord ζ (j+1) hj
          · right
            have : j = (R.route ζ).length - 1 := by have := hin.1; omega
            rw [← this, hl]; exact_mod_cast (by omega : r + d < r + (d+1))
        · left
          refine ⟨j, hin.1, le_trans hin.2.1 (by exact_mod_cast (by omega : r+d ≤ r+(d+1))), ?_⟩
          have h2 : ((r+d : ℕ) : ℕ∞) < R.leave ζ j := lt_of_le_of_ne hin.2.2 (Ne.symm hl)
          have h3 := Order.add_one_le_of_lt h2
          have h4 : ((r + (d+1) : ℕ) : ℕ∞) = ((r+d : ℕ) : ℕ∞) + 1 := by push_cast; ring
          rw [h4]; exact h3
      · right; exact lt_of_lt_of_le hlt (by exact_mod_cast (by omega : r + d ≤ r + (d+1)))
  have hfinal : R.leave ζ ((R.route ζ).length - 1) + 1 ≤ ((y0 + K : ℕ) : ℕ∞) := by
    obtain ⟨d, hd⟩ : ∃ d, y0 + K = r + d := ⟨y0 + K - r, by omega⟩
    rcases hreach d with ⟨j, hin⟩ | hlt
    · exfalso
      obtain ⟨e, he⟩ : ∃ e, (R.route ζ)[j]? = some e := ⟨_, List.getElem?_eq_getElem hin.1⟩
      have h1 := hbound (r+d) j e (by omega) hin he
      have hrel := (hRel e).2 (hsuf _ _ _ (hpath ζ).1 j e he)
      have h2 := hstep' e hrel
      omega
    · rw [← hd] at hlt
      exact Order.add_one_le_of_lt hlt
  unfold RunData.residenceTime RunData.exitTime
  rw [tsub_le_iff_right, hr, ← hK]
  have : ((N.longest (R.orig ζ) (R.dest ζ) + K : ℕ) : ℕ∞) + (r : ℕ∞) = ((y0 + K : ℕ) : ℕ∞) := by
    rw [hy0, hhdef]; push_cast; ring
  rw [this]
  exact hfinal
