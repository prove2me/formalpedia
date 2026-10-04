-- Prove2me | solution 1 for AppliedComb.Graphs.dirac
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:13:46.74977+00:00
-- url     : https://prove2.me/submissions/937e1b56-e16d-462d-ade1-ff269ffb0f46

import Definitions.Def_AppliedComb_Graphs_IsHamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

namespace DiracProof

private lemma consecutive_of_count {V : Type*} (p q : V → Bool) (l : List V)
    (h : l.length - 1 < l.dropLast.countP p + l.tail.countP q) :
    ∃ l₁ x y l₂, l = l₁ ++ x :: y :: l₂ ∧ p x ∧ q y := by
  induction l using List.twoStepInduction with
  | nil => simp at h
  | singleton a => simp at h
  | cons_cons a b l _ ih =>
    by_cases hp : p a
    · by_cases hq : q b
      · exact ⟨[], a, b, l, rfl, hp, hq⟩
      · have hh : (b :: l).length - 1 <
            (b :: l).dropLast.countP p + (b :: l).tail.countP q := by
          simp only [List.length_cons, List.dropLast_cons_cons, List.tail_cons,
            List.countP_cons_of_pos hp, List.countP_cons_of_neg hq] at h ⊢
          omega
        obtain ⟨l₁, x, y, l₂, he, hx, hy⟩ := ih b hh
        exact ⟨a :: l₁, x, y, l₂, by simp [he], hx, hy⟩
    · have hh : (b :: l).length - 1 <
          (b :: l).dropLast.countP p + (b :: l).tail.countP q := by
        simp only [List.length_cons, List.dropLast_cons_cons, List.tail_cons,
          List.countP_cons_of_neg hp, List.countP_cons] at h ⊢
        split_ifs at h <;> omega
      obtain ⟨l₁, x, y, l₂, he, hx, hy⟩ := ih b hh
      exact ⟨a :: l₁, x, y, l₂, by simp [he], hx, hy⟩

private lemma longest {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length := by
  let s : Set ℕ := {k | ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = k}
  have hs : s.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro k ⟨l, hnd, _, rfl⟩
    exact hnd.length_le_card)
  obtain ⟨k, ⟨l, hnd, hc, hk⟩, hm⟩ :=
    Set.exists_max_image s id hs ⟨0, [], by simp⟩
  refine ⟨l, hnd, hc, fun l' hn' hc' => ?_⟩
  simpa [hk] using hm l'.length ⟨l', hn', hc', rfl⟩

private lemma reverse_chain {V : Type*} (G : SimpleGraph V) {l : List V}
    (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp (fun _ _ hxy => G.adj_symm hxy))

private lemma neighbors_mem {V : Type*} (G : SimpleGraph V) {a : V} {l : List V}
    (hnd : (a :: l).Nodup) (hc : (a :: l).IsChain G.Adj)
    (hm : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj →
      l'.length ≤ (a :: l).length) :
    ∀ v, G.Adj a v → v ∈ a :: l := by
  intro v hav
  by_contra hv
  have hn' : (v :: a :: l).Nodup := List.nodup_cons.mpr ⟨hv, hnd⟩
  have hc' : (v :: a :: l).IsChain G.Adj := hc.cons_cons (G.adj_symm hav)
  have := hm (v :: a :: l) hn' hc'
  simp only [List.length_cons] at this
  omega

private lemma degree_eq_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {l : List V} (hnd : l.Nodup) (a : V)
    (hmem : ∀ v, G.Adj a v → v ∈ l) :
    G.degree a = l.countP (fun v => decide (G.Adj a v)) := by
  classical
  have he : G.neighborFinset a = l.toFinset.filter (G.Adj a) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun hv => ⟨hmem v hv, hv⟩, fun hv => hv.2⟩
  rw [← G.card_neighborFinset_eq_degree a, he]
  exact hnd.card_eq_countP

private lemma close_path {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : List V} (hc : l.IsChain G.Adj) (a b : V)
    (ha : l.head? = some a) (hb : l.getLast? = some b)
    (hcount : l.length - 1 <
      l.dropLast.countP (fun v => decide (G.Adj b v)) +
      l.tail.countP (fun v => decide (G.Adj a v))) :
    ∃ c : List V, c.Perm l ∧ c.IsChain G.Adj ∧
      ∃ u v, c.head? = some u ∧ c.getLast? = some v ∧ G.Adj u v := by
  obtain ⟨l₁, x, y, l₂, he, hx, hy⟩ := consecutive_of_count
    (fun v => decide (G.Adj b v)) (fun v => decide (G.Adj a v)) l hcount
  have hx' : G.Adj x b := G.adj_symm (of_decide_eq_true hx)
  have hy' : G.Adj a y := of_decide_eq_true hy
  let L := l₁ ++ [x]
  let R := y :: l₂
  have he' : l = L ++ R := by simpa [L, R, List.append_assoc] using he
  have hLne : L ≠ [] := by simp [L]
  have hRne : R ≠ [] := by simp [R]
  have hLhead : L.head? = some a := by
    rw [he', List.head?_append_of_ne_nil L hLne] at ha
    exact ha
  have hRlast : R.getLast? = some b := by
    rw [he', List.getLast?_append_of_ne_nil L hRne] at hb
    exact hb
  have hp := List.isChain_append.mp (he' ▸ hc)
  refine ⟨L ++ R.reverse, ?_, ?_, a, y, ?_, ?_, hy'⟩
  · rw [he']
    exact List.Perm.append_left L (List.reverse_perm R)
  · apply hp.1.append (reverse_chain G hp.2.1)
    intro u hu v hv
    have hu' : x = u := by simpa [L] using hu
    have hv' : b = v := by simpa [hRlast] using hv
    simpa [hu', hv'] using hx'
  · simpa only [List.head?_append_of_ne_nil L hLne] using hLhead
  · rw [List.getLast?_append_of_ne_nil L (by simp [R]), List.getLast?_reverse]
    rfl

private lemma rotate_to {V : Type*} (G : SimpleGraph V) {c : List V}
    (hc : c.IsChain G.Adj)
    (hclose : ∃ a b, c.head? = some a ∧ c.getLast? = some b ∧ G.Adj a b)
    (v : V) (hv : v ∈ c) :
    ∃ r : List V, r.Perm c ∧ r.head? = some v ∧ r.IsChain G.Adj := by
  obtain ⟨s, t, rfl, _⟩ := List.eq_append_cons_of_mem hv
  obtain ⟨a, b, ha, hb, hab⟩ := hclose
  have hp := List.isChain_append.mp hc
  refine ⟨(v :: t) ++ s, List.perm_append_comm, by simp, ?_⟩
  apply hp.2.1.append hp.1
  intro x hx y hy
  have hb' : (v :: t).getLast? = some b := by simpa using hb
  have hx' : b = x := by simpa [hb'] using hx
  have hy' : a = y := by
    have := List.mem_head?_append_of_mem_head? (t := v :: t) hy
    simpa [ha] using this
  simpa [hx', hy'] using G.adj_symm hab

theorem dirac_list {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, (Fintype.card V + 1) / 2 ≤ G.degree v) :
    ∃ c : List V, c.Nodup ∧ (∀ v, v ∈ c) ∧ c.IsChain G.Adj ∧
      ∃ a b, c.head? = some a ∧ c.getLast? = some b ∧ G.Adj a b := by
  classical
  obtain ⟨l, hnd, hc, hm⟩ := longest G
  have hne : l ≠ [] := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have h := hm [v] (by simp) (by simp)
    intro he
    simp [he] at h
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  let l := a :: t
  have hbne : l.reverse ≠ [] := by simp [l]
  obtain ⟨b, s, hbs⟩ := List.exists_cons_of_ne_nil hbne
  have ha : l.head? = some a := rfl
  have hb : l.getLast? = some b := by rw [← List.head?_reverse, hbs]; rfl
  have hma : ∀ v, G.Adj a v → v ∈ l := neighbors_mem G hnd hc hm
  have hmr : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj →
      l'.length ≤ (b :: s).length := by
    intro l' hn' hc'
    simpa only [← hbs, List.length_reverse] using hm l' hn' hc'
  have hnb : (b :: s).Nodup := by
    rw [← hbs]
    exact (List.reverse_perm l).symm.nodup hnd
  have hcb : (b :: s).IsChain G.Adj := by rw [← hbs]; exact reverse_chain G hc
  have hmb : ∀ v, G.Adj b v → v ∈ l := by
    intro v hv
    have h := neighbors_mem G hnb hcb hmr v hv
    simpa [← hbs] using h
  have hda := degree_eq_count G hnd a hma
  have hdb := degree_eq_count G hnd b hmb
  change G.degree b = l.countP (fun v => decide (G.Adj b v)) at hdb
  have hdat : G.degree a = l.tail.countP (fun v => decide (G.Adj a v)) := by
    simpa [l] using hda
  have hdbd : G.degree b = l.dropLast.countP (fun v => decide (G.Adj b v)) := by
    obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hb
    simpa [hu] using hdb
  have hlen : l.length ≤ Fintype.card V := hnd.length_le_card
  have hcount : l.length - 1 <
      l.dropLast.countP (fun v => decide (G.Adj b v)) +
      l.tail.countP (fun v => decide (G.Adj a v)) := by
    rw [← hdbd, ← hdat]
    have h1 := hdeg a
    have h2 := hdeg b
    have hn := Fintype.card_pos (α := V)
    omega
  obtain ⟨c, hp, hcc, hclose⟩ := close_path G hc a b ha hb hcount
  have hcn : c.Nodup := hp.symm.nodup hnd
  have hclen : c.length = t.length + 1 := by simpa [l] using hp.length_eq
  have hlarge : (Fintype.card V + 1) / 2 < c.length := by
    have h := List.countP_le_length (p := fun v => decide (G.Adj a v)) (l := l.tail)
    rw [← hdat, List.length_tail] at h
    simp only [l, List.length_cons, Nat.add_sub_cancel_right] at h
    have := hdeg a
    omega
  refine ⟨c, hcn, ?_, hcc, hclose⟩
  intro v
  by_contra hv
  have hex : ∃ w, G.Adj v w ∧ w ∈ c := by
    by_contra hh
    push Not at hh
    have hd : Disjoint (G.neighborFinset v) c.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hw hc'
      exact hh w (by simpa using hw) (by simpa using hc')
    have hcard := Finset.card_le_univ (G.neighborFinset v ∪ c.toFinset)
    rw [Finset.card_union_of_disjoint hd, G.card_neighborFinset_eq_degree,
      List.toFinset_card_of_nodup hcn] at hcard
    have := hdeg v
    omega
  obtain ⟨w, hvw, hwc⟩ := hex
  obtain ⟨r, hrp, hrhead, hrc⟩ := rotate_to G hcc hclose w hwc
  have hvr : v ∉ r := fun h => hv (hrp.mem_iff.mp h)
  have hrn : r.Nodup := hrp.symm.nodup hcn
  have hvrc : (v :: r).IsChain G.Adj := hrc.cons (by simpa [hrhead] using hvw)
  have hmax := hm (v :: r) (List.nodup_cons.mpr ⟨hvr, hrn⟩) hvrc
  have hrlen := hrp.length_eq
  simp only [List.length_cons] at hmax
  omega

end DiracProof

/-- Keller–Trotter, Applied Combinatorics (2017), Theorem 5.18.
The proof follows the longest-path and pigeonhole argument on page 80. -/
theorem solution {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (hdeg : ∀ v : V, (n + 1) / 2 ≤ G.degree v) :
    AppliedComb.Graphs.IsHamiltonian G := by
  exact DiracProof.dirac_list G (by simpa only [hn] using hdeg)

#print axioms solution
