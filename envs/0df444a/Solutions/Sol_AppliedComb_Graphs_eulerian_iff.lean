-- Prove2me | solution 1 for AppliedComb.Graphs.eulerian_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:28:18.180157+00:00
-- url     : https://prove2.me/submissions/02e35313-e4fe-4723-92fe-889c12adf1e0

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsEulerian

open SimpleGraph

namespace EulerAux

variable {V : Type*} {G : SimpleGraph V}

lemma list_to_walk (G : SimpleGraph V) :
    ∀ (l : List V) (a : V), List.IsChain G.Adj (a :: l) →
      ∃ (b : V) (p : G.Walk a b), p.support = a :: l := by
  intro l
  induction l with
  | nil => intro a _; exact ⟨a, Walk.nil, rfl⟩
  | cons x l ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨b, p, hp⟩ := ih x h.2
    exact ⟨b, Walk.cons h.1 p, by simp [hp]⟩

lemma edges_getElem_eq {u v : V} (p : G.Walk u v) {i : ℕ} (hi : i < p.edges.length) :
    p.edges[i] = s(p.support[i]'(by have := p.length_support; have := p.length_edges; omega),
      p.support[i+1]'(by have := p.length_support; have := p.length_edges; omega)) := by
  rw [Walk.getElem_edges_eq_edge_getElem_darts]
  have hd : i < p.darts.length := by simpa using hi
  show s((p.darts[i]).fst, (p.darts[i]).snd) = _
  rw [Walk.fst_darts_getElem, Walk.snd_darts_getElem]
  simp [List.getElem_dropLast, List.getElem_tail]

lemma countP_incident_eq_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {u v : V}
    (p : G.Walk u v) (hp : p.IsTrail) (x : V)
    (hall : ∀ w, G.Adj x w → s(x, w) ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  rw [← card_incidenceFinset_eq_degree, List.countP_eq_length_filter]
  have hnd : (p.edges.filter (fun e => x ∈ e)).Nodup := hp.edges_nodup.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  rw [G.incidenceFinset_eq_filter x]
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
    mem_edgeFinset]
  constructor
  · rintro ⟨he, hx⟩
    exact ⟨Walk.edges_subset_edgeSet p he, hx⟩
  · rintro ⟨he, hx⟩
    refine ⟨?_, hx⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hall b he
      · rw [Sym2.eq_swap]; exact hall a he.symm

/-- A longest trail in a connected graph with all degrees even is a closed Eulerian trail. -/
lemma exists_closed_eulerian [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  obtain ⟨v0⟩ := hconn.nonempty
  let S : Set ℕ := {n | ∃ (a b : V) (q : G.Walk a b), q.IsTrail ∧ q.length = n}
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    rintro n ⟨a, b, q, hq, rfl⟩
    rw [← Walk.length_edges]
    exact hq.edges_nodup.length_le_card
  have hne : S.Nonempty := ⟨0, v0, v0, Walk.nil, by simp, rfl⟩
  obtain ⟨u, v, p, hp, hlen⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ {a b : V} (q : G.Walk a b), q.IsTrail → q.length ≤ p.length := by
    intro a b q hq
    rw [hlen]
    exact le_csSup hbdd ⟨a, b, q, hq, rfl⟩
  -- every edge at the end `v` is used
  have hend : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := by
    intro w hvw
    by_contra hnot
    have hq : (Walk.cons hvw.symm p.reverse).IsTrail := by
      rw [Walk.isTrail_cons]
      refine ⟨hp.reverse, ?_⟩
      rw [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap]
      exact hnot
    have := hmax _ hq
    simp at this
  -- parity at `v` forces the trail to be closed
  have huv : u = v := by
    by_contra hne
    have h1 := (hp.even_countP_edges_iff v).not.mpr (by
      intro h
      exact (h hne).2 rfl)
    rw [countP_incident_eq_degree p hp v hend] at h1
    exact h1 (heven v)
  subst huv
  -- every edge at a vertex of the trail is used
  have hall : ∀ y ∈ p.support, ∀ z, G.Adj y z → s(y, z) ∈ p.edges := by
    intro y hy z hyz
    by_contra hnot
    have hq : (Walk.cons hyz.symm (p.rotate y hy)).IsTrail := by
      rw [Walk.isTrail_cons]
      refine ⟨hp.rotate hy, ?_⟩
      intro hmem
      have := ((Walk.rotate_edges p y hy).mem_iff).mp hmem
      rw [Sym2.eq_swap] at this
      exact hnot this
    have := hmax _ hq
    simp at this
  -- the support is closed under adjacency, so (connectedness) is everything
  have hclosed : ∀ {a b : V} (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h q ih =>
      intro ha
      refine ih ?_
      exact Walk.snd_mem_support_of_mem_edges p (hall _ ha _ h)
  have hsupp : ∀ x, x ∈ p.support := by
    intro x
    obtain ⟨q⟩ := hconn.preconnected u x
    exact hclosed q p.start_mem_support
  refine ⟨u, p, hp.isEulerian_of_forall_mem fun e he => ?_⟩
  induction e using Sym2.ind with
  | _ a b => exact hall a (hsupp a) b he


lemma eulerian_of_walk [DecidableEq V] {u : V} (p : G.Walk u u) (hp : p.IsEulerian) :
    AppliedComb.Graphs.IsEulerian G := by
  have hlen : p.support.length = p.edges.length + 1 := by simp
  refine ⟨p.support, Walk.support_ne_nil p, ?_, Walk.isChain_adj_support p, ?_⟩
  · have h1 : p.support.head? = some u := by rw [← Walk.cons_tail_support p]; rfl
    have h2 : p.support.getLast? = some u := by
      rw [List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil p), Walk.getLast_support]
    rw [h1, h2]
  · intro e he
    have hem : e ∈ p.edges := ((Walk.isEulerian_iff p).mp hp).2 e he
    have hnd := hp.isTrail.edges_nodup
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hem
    refine ⟨i, ⟨by omega, ?_⟩, ?_⟩
    · rw [← hie, edges_getElem_eq]
    · rintro j ⟨hj, hje⟩
      have hj' : j < p.edges.length := by omega
      have h3 : p.edges[j] = p.edges[i] := by
        rw [edges_getElem_eq p hj', hie, hje]
      exact (hnd.getElem_inj_iff).mp h3

/-- An eulerian circuit list is the support of a closed Eulerian trail. -/
lemma eulerian_walk_of_circuit [DecidableEq V] {xs : List V}
    (hxs : AppliedComb.Graphs.IsEulerianCircuit G xs) :
    ∃ (a : V) (p : G.Walk a a), p.IsEulerian ∧ p.support = xs := by
  obtain ⟨hne, hht, hch, hed⟩ := hxs
  obtain ⟨a, l, hxl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, p, hp0⟩ := list_to_walk G l a (hxl ▸ hch)
  have hp : p.support = xs := by rw [hxl]; exact hp0
  subst hp
  have hlast : p.support.getLast? = some b := by
    rw [List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil p), Walk.getLast_support]
  have hab : a = b := by
    have h1 : p.support.head? = some a := by rw [hp0]; rfl
    rw [hlast] at hht
    have := hht.symm.trans h1
    exact (Option.some.inj this).symm
  subst hab
  have hlen : p.support.length = p.edges.length + 1 := by simp
  have hcov : ∀ e ∈ G.edgeSet, e ∈ p.edges := by
    intro e he
    obtain ⟨i, ⟨hi, hie⟩, -⟩ := hed e he
    have hi' : i < p.edges.length := by omega
    have : p.edges[i] = e := by rw [edges_getElem_eq p hi', hie]
    rw [← this]
    exact List.getElem_mem hi'
  have hnd : p.edges.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j hij
    have hi' : (i : ℕ) < p.edges.length := i.2
    have hj' : (j : ℕ) < p.edges.length := j.2
    have hij' : p.edges[(i : ℕ)] = p.edges[(j : ℕ)] := hij
    have he : p.edges[(i : ℕ)] ∈ G.edgeSet := Walk.edges_subset_edgeSet p (List.getElem_mem hi')
    obtain ⟨k, hk, huniq⟩ := hed _ he
    have hi2 := huniq i ⟨by omega, edges_getElem_eq p hi'⟩
    have hj2 := huniq j ⟨by omega, by rw [hij']; exact edges_getElem_eq p hj'⟩
    exact Fin.ext (hi2.trans hj2.symm)
  exact ⟨a, p, (Walk.isEulerian_iff p).mpr ⟨⟨hnd⟩, hcov⟩, rfl⟩

end EulerAux

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v : V, ∃ w : V, G.Adj v w) :
    AppliedComb.Graphs.IsEulerian G ↔ G.Connected ∧ ∀ v : V, Even (G.degree v) := by
  classical
  constructor
  · rintro ⟨xs, hxs⟩
    obtain ⟨a, p, hp, hsup⟩ := EulerAux.eulerian_walk_of_circuit hxs
    have hmem : ∀ x : V, x ∈ p.support := by
      intro x
      obtain ⟨w, hw⟩ := hG x
      have : s(x, w) ∈ p.edges := hp.mem_edges_iff.mpr hw
      exact Walk.fst_mem_support_of_mem_edges p this
    refine ⟨?_, fun x => ?_⟩
    · have : Nonempty V := ⟨a⟩
      refine ⟨fun x y => ?_⟩
      have hx : G.Reachable a x := ⟨p.takeUntil x (hmem x)⟩
      have hy : G.Reachable a y := ⟨p.takeUntil y (hmem y)⟩
      exact hx.symm.trans hy
    · exact (hp.even_degree_iff (x := x)).mpr (fun h => absurd rfl h)
  · rintro ⟨hconn, heven⟩
    obtain ⟨u, p, hp⟩ := EulerAux.exists_closed_eulerian hconn heven
    exact EulerAux.eulerian_of_walk p hp
