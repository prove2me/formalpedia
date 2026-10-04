-- Prove2me | solution 1 for AppliedComb.GraphAlg.dijkstra_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:33:04.027024+00:00
-- url     : https://prove2.me/submissions/045519f7-0e97-4361-a7e6-11578ad0488f

import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

set_option autoImplicit false


open AppliedComb.GraphAlg AppliedComb.GraphAlg.DijkstraState

namespace GraphAlgProof

variable {V : Type*} {G : WeightedDigraph V} {r : V} {s : DijkstraState V}

def Ordered (s : DijkstraState V) : Prop :=
  s.σ.Pairwise (fun u v => s.δ u ≤ s.δ v) ∧
  ∀ u ∈ s.σ, ∀ v, v ∉ s.σ → s.δ u ≤ s.δ v

theorem ordered_init (G : WeightedDigraph V) (r : V) : Ordered (init G r) := by
  classical
  constructor
  · simp [init]
  · intro u hu v hv
    simp only [init, List.mem_singleton] at hu
    subst u
    simp [init]

theorem ordered_permanent (hs : Ordered s) {x : V} (hx : s.IsMinTemp x) :
    Ordered (s.makePermanent x) := by
  constructor
  · simp only [makePermanent, List.pairwise_append, List.pairwise_singleton, true_and,
      and_true, List.mem_singleton]
    exact ⟨hs.1, fun u hu v hv => hv ▸ hs.2 u hu x hx.1⟩
  · intro u hu v hv
    simp only [makePermanent, List.mem_append, List.mem_singleton, not_or] at hu hv ⊢
    rcases hu with hu | rfl
    · exact hs.2 u hu v hv.1
    · exact hx.2 v hv.1

theorem ordered_last (hs : Ordered s) {v : V} (hv : s.σ.getLast? = some v)
    {u : V} (hu : u ∈ s.σ) : s.δ u ≤ s.δ v := by
  have h := hs.1.rel_getLast_of_rel_getLast_getLast hu (le_refl _)
  have he : s.σ.getLast (List.ne_nil_of_mem hu) = v := by
    simpa [List.getLast?_eq_getLast (List.ne_nil_of_mem hu)] using hv
  simpa [he] using h

theorem scan_perm {v u : V} (hu : u ∈ s.σ) : (scan G s v).δ u = s.δ u := by
  simp [scan,hu]

theorem ordered_scan (hs : Ordered s) {v : V} (hv : s.σ.getLast? = some v) :
    Ordered (scan G s v) := by
  classical
  have he : ∀ u ∈ s.σ, (scan G s v).δ u = s.δ u := fun u hu => scan_perm hu
  constructor
  · change s.σ.Pairwise _
    exact hs.1.imp_of_mem (fun {u v} hu hv huv => by simpa [he u hu,he v hv] using huv)
  · intro u hu x hx
    change u ∈ s.σ at hu
    change x ∉ s.σ at hx
    rw [he u hu]
    simp only [scan,hx,if_pos]
    exact le_min (hs.2 u hu x hx) ((ordered_last hs hv hu).trans (le_self_add))

theorem run_ordered [Fintype V] {i : ℕ} (hs : DijkstraRun G r i s) : Ordered s := by
  induction hs with
  | init => exact ordered_init _ _
  | first hx => exact ordered_permanent (ordered_init _ _) hx
  | step hrun hi hin hv hx ih => exact ordered_permanent (ordered_scan ih hv) hx

end GraphAlgProof


open AppliedComb.GraphAlg

namespace GraphAlgProof

variable {V : Type*} (G : WeightedDigraph V)

@[simp] theorem pathLength_nil : G.pathLength [] = 0 := rfl
@[simp] theorem pathLength_single (a : V) : G.pathLength [a] = 0 := rfl
@[simp] theorem pathLength_cons (a b : V) (L : List V) :
    G.pathLength (a :: b :: L) = G.w a b + G.pathLength (b :: L) := rfl

theorem pathLength_append_edge {P : List V} {v x : V} (hp : P.getLast? = some v) :
    G.pathLength (P ++ [x]) = G.pathLength P + G.w v x := by
  induction P with
  | nil => simp at hp
  | cons a L ih =>
    cases L with
    | nil => simp_all
    | cons b L =>
      simp only [List.getLast?_cons_cons] at hp
      simpa only [List.cons_append,pathLength_cons,Nat.add_assoc] using
        congrArg (G.w a b + ·) (ih hp)

theorem path_append_edge {a v x : V} {P : List V} (hp : G.IsDirPath a v P)
    (hx : x ∉ P) (hadj : G.Adj v x) : G.IsDirPath a x (P ++ [x]) := by
  refine ⟨?_,by simp,?_,?_⟩
  · simp [List.head?_append,hp.1]
  · simpa using hp.2.2.1.concat hx
  · apply hp.2.2.2.append (List.IsChain.singleton x)
    intro u hu y hy
    simp only [hp.2.1,Option.mem_def,Option.some.injEq] at hu
    simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hy
    simpa [hu,hy] using hadj

theorem path_tail {a b z : V} {L : List V} (hp : G.IsDirPath a z (a :: b :: L)) :
    G.IsDirPath b z (b :: L) := by
  exact ⟨rfl,by simpa using hp.2.1,hp.2.2.1.tail,hp.2.2.2.tail⟩

theorem path_suffix {r z a : V} {P : List V} (hp : G.IsDirPath r z P) (ha : a ∈ P) :
    ∃ Q, G.IsDirPath a z Q ∧ G.pathLength Q ≤ G.pathLength P := by
  induction P generalizing r with
  | nil => simp at ha
  | cons u L ih =>
    have hr : u = r := by simpa using hp.1
    subst r
    by_cases hau : a = u
    · subst a; exact ⟨u::L,hp,le_rfl⟩
    have haL : a ∈ L := (List.mem_cons.mp ha).resolve_left hau
    cases L with
    | nil => simp at haL
    | cons v L =>
      obtain ⟨Q,hQ,hlen⟩ := ih (path_tail G hp) haL
      exact ⟨Q,hQ,hlen.trans (by simp only [pathLength_cons]; omega)⟩

theorem walk_to_path {r z : V} {P : List V} (hh : P.head? = some r)
    (hl : P.getLast? = some z) (hc : P.IsChain G.Adj) :
    ∃ Q, G.IsDirPath r z Q ∧ G.pathLength Q ≤ G.pathLength P := by
  classical
  induction P generalizing r with
  | nil => simp at hh
  | cons a L ih =>
    have hr : a = r := by simpa using hh
    subst r
    cases L with
    | nil =>
      have hz : a = z := by simpa using hl
      subst z
      exact ⟨[a],⟨rfl,rfl,by simp,by simp⟩,le_rfl⟩
    | cons b L =>
      obtain ⟨Q,hQ,hlen⟩ := ih rfl (by simpa using hl) hc.tail
      by_cases ha : a ∈ Q
      · obtain ⟨R,hR,hRlen⟩ := path_suffix G hQ ha
        exact ⟨R,hR,hRlen.trans (hlen.trans (by simp only [pathLength_cons]; omega))⟩
      · cases Q with
        | nil => simp [WeightedDigraph.IsDirPath] at hQ
        | cons c R =>
          have hb : c = b := by simpa using hQ.1
          subst c
          refine ⟨a::b::R,⟨rfl,by simpa using hQ.2.1,?_,?_⟩,?_⟩
          · exact List.nodup_cons.mpr ⟨ha,hQ.2.2.1⟩
          · exact List.isChain_cons_cons.mpr ⟨hc.rel,hQ.2.2.2⟩
          · simpa only [pathLength_cons] using Nat.add_le_add_left hlen (G.w a b)

end GraphAlgProof


open AppliedComb.GraphAlg AppliedComb.GraphAlg.DijkstraState

namespace GraphAlgProof

variable {V : Type*} {G : WeightedDigraph V} {r : V} {s : DijkstraState V}

def Settled (G : WeightedDigraph V) (s : DijkstraState V) : Prop :=
  ∀ u ∈ s.σ, s.σ.getLast? ≠ some u → ∀ x, s.δ x ≤ s.δ u + G.ext u x

theorem scan_le (v x : V) : (scan G s v).δ x ≤ s.δ x := by
  classical
  by_cases hx : x ∈ s.σ
  · simp [scan,hx]
  · simp only [scan,hx,not_false_eq_true,if_true]
    exact min_le_left _ _

theorem scan_outgoing (ho : Ordered s) {v : V} (hv : s.σ.getLast? = some v) (x : V) :
    (scan G s v).δ x ≤ (scan G s v).δ v + G.ext v x := by
  classical
  have hv' : v ∈ s.σ := List.mem_of_mem_getLast? hv
  rw [scan_perm hv']
  by_cases hx : x ∈ s.σ
  · rw [scan_perm hx]
    exact (ordered_last ho hv hx).trans le_self_add
  · simp only [scan,hx,not_false_eq_true,if_true]
    exact min_le_right _ _

theorem scan_settled (hs : Settled G s) (ho : Ordered s)
    {v : V} (hv : s.σ.getLast? = some v) :
    ∀ u ∈ s.σ, ∀ x, (scan G s v).δ x ≤ (scan G s v).δ u + G.ext u x := by
  intro u hu x
  by_cases huv : u = v
  · subst u; exact scan_outgoing ho hv x
  · rw [scan_perm hu]
    exact (scan_le v x).trans (hs u hu (by simpa [hv,eq_comm] using huv) x)

theorem settled_permanent {x : V}
    (hs : ∀ u ∈ s.σ, ∀ y, s.δ y ≤ s.δ u + G.ext u y) :
    Settled G (s.makePermanent x) := by
  intro u hu hlast y
  simp only [makePermanent,List.mem_append,List.mem_singleton] at hu
  rcases hu with hu | rfl
  · exact hs u hu y
  · simp [makePermanent] at hlast

theorem init_outgoing (G : WeightedDigraph V) (r : V) :
    ∀ u ∈ (init G r).σ, ∀ x, (init G r).δ x ≤ (init G r).δ u + G.ext u x := by
  classical
  intro u hu x
  have hu' : u = r := by simpa [init] using hu
  subst u
  simp only [init,if_pos,zero_add]
  split_ifs
  · exact zero_le
  · exact le_rfl

theorem run_settled [Fintype V] {i : ℕ} (hs : DijkstraRun G r i s) : Settled G s := by
  induction hs with
  | init => exact fun u hu _ x => init_outgoing _ _ u hu x
  | first hx => exact settled_permanent (init_outgoing _ _)
  | step hrun hi hin hv hx ih =>
    exact settled_permanent (scan_settled ih (run_ordered hrun) hv)

theorem run_vertices [Fintype V] {i : ℕ} (hs : DijkstraRun G r i s) :
    s.σ.Nodup ∧ s.σ.length = i ∧ r ∈ s.σ ∧ s.δ r = 0 := by
  classical
  induction hs with
  | init => simp [init]
  | @first x hx =>
    have hx' : x ∉ [r] := hx.1
    simp_all [makePermanent,init,List.nodup_append,eq_comm]
  | @step i s v x hrun hi hin hv hx ih =>
    rcases ih with ⟨hnd,hlen,hr,hzero⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa [makePermanent,scan,List.concat_eq_append] using hnd.concat hx.1
    · simpa [makePermanent,scan,hlen]
    · exact List.mem_append_left _ hr
    · exact (scan_perm hr).trans hzero

theorem halted_mem [Fintype V] (hs : DijkstraRun G r (Fintype.card V) s) (x : V) :
    x ∈ s.σ := by
  classical
  have h := run_vertices hs
  have he : s.σ.toFinset = Finset.univ := Finset.eq_univ_of_card _
    (by simpa [List.toFinset_card_of_nodup h.1] using h.2.1)
  simpa [← he] using (Finset.mem_univ x)

theorem halted_bellman [Fintype V] (hs : DijkstraRun G r (Fintype.card V) s) (u x : V) :
    s.δ x ≤ s.δ u + G.ext u x := by
  by_cases hu : s.σ.getLast? = some u
  · exact (ordered_last (run_ordered hs) hu (halted_mem hs x)).trans le_self_add
  · exact run_settled hs u (halted_mem hs u) hu x

theorem bellman_path_bound (d : V → ℕ∞)
    (hd : ∀ u x, d x ≤ d u + G.ext u x) {a b : V} {P : List V}
    (hh : P.head? = some a) (hl : P.getLast? = some b) (hc : P.IsChain G.Adj) :
    d b ≤ d a + (G.pathLength P : ℕ∞) := by
  classical
  induction P generalizing a with
  | nil => simp at hh
  | cons u L ih =>
    have hu : u = a := by simpa using hh
    subst a
    cases L with
    | nil =>
      have hb : u = b := by simpa using hl
      subst b
      simp
    | cons v L =>
      have h := ih rfl (by simpa using hl) hc.tail
      have hedge : G.ext u v = (G.w u v : ℕ∞) := by simp [WeightedDigraph.ext,hc.rel]
      have hb := hd u v
      rw [hedge] at hb
      simpa only [pathLength_cons, Nat.cast_add,add_assoc] using
        h.trans (add_le_add hb le_rfl)

end GraphAlgProof


open AppliedComb.GraphAlg AppliedComb.GraphAlg.DijkstraState

namespace GraphAlgProof

variable {V : Type*} {G : WeightedDigraph V} {r : V} {s : DijkstraState V}

def Feasible (G : WeightedDigraph V) (r : V) (s : DijkstraState V) : Prop :=
  ∀ x, s.δ x ≠ ⊤ → G.IsDirPath r x (s.P x) ∧
    (G.pathLength (s.P x) : ℕ∞) = s.δ x ∧ ∀ y ∈ s.P x, y = x ∨ y ∈ s.σ

theorem feasible_init (G : WeightedDigraph V) (r : V) : Feasible G r (init G r) := by
  classical
  intro x hfin
  by_cases hx : x = r
  · subst x
    simp [init,WeightedDigraph.IsDirPath]
  · have hadj : G.Adj r x := by
      by_contra h
      simp [init,hx,WeightedDigraph.ext,h] at hfin
    simp [init,hx,WeightedDigraph.IsDirPath,Ne.symm hx,hadj,WeightedDigraph.ext]

theorem feasible_permanent (hs : Feasible G r s) (x : V) : Feasible G r (s.makePermanent x) := by
  intro u hfin
  obtain ⟨hp,hlen,hmem⟩ := hs u hfin
  refine ⟨hp,hlen,?_⟩
  intro y hy
  rcases hmem y hy with he | hm
  · exact Or.inl he
  · exact Or.inr (List.mem_append_left _ hm)

theorem feasible_scan (hs : Feasible G r s) {v : V} (hv : v ∈ s.σ) :
    Feasible G r (scan G s v) := by
  classical
  intro x hfin
  by_cases hi : x ∉ s.σ ∧ s.δ v + G.ext v x < s.δ x
  · have hd : (scan G s v).δ x = s.δ v + G.ext v x := by
      simp [scan,hi.1,min_eq_right (le_of_lt hi.2)]
    have hp : (scan G s v).P x = s.P v ++ [x] := by simp [scan,hi]
    have hvfin : s.δ v ≠ ⊤ := by
      intro ht
      simp [ht] at hi
    have hadj : G.Adj v x := by
      by_contra h
      simp [WeightedDigraph.ext,h] at hi
    obtain ⟨hvp,hvlen,hvmem⟩ := hs v hvfin
    have hall : ∀ y ∈ s.P v, y ∈ s.σ := by
      intro y hy
      rcases hvmem y hy with rfl | hy
      · exact hv
      · exact hy
    have hxn : x ∉ s.P v := fun h => hi.1 (hall x h)
    refine ⟨?_,?_,?_⟩
    · rw [hp]
      exact path_append_edge G hvp hxn hadj
    · rw [hp,pathLength_append_edge G hvp.2.1,Nat.cast_add,hvlen,hd]
      simp [WeightedDigraph.ext,hadj]
    · intro y hy
      rw [hp,List.mem_append,List.mem_singleton] at hy
      exact hy.elim (fun h => Or.inr (hall y h)) Or.inl
  · have hd : (scan G s v).δ x = s.δ x := by
      by_cases hx : x ∈ s.σ
      · exact scan_perm hx
      · have hle : s.δ x ≤ s.δ v + G.ext v x := not_lt.mp (fun h => hi ⟨hx,h⟩)
        simp [scan,hx,min_eq_left hle]
    have hp : (scan G s v).P x = s.P x := by simp [scan,hi]
    rw [hd] at hfin
    have hσ : (scan G s v).σ = s.σ := rfl
    simpa only [hp,hd,hσ] using hs x hfin

theorem run_feasible [Fintype V] {i : ℕ} (hs : DijkstraRun G r i s) : Feasible G r s := by
  induction hs with
  | init => exact feasible_init _ _
  | first hx => exact feasible_permanent (feasible_init _ _) _
  | step hrun hi hin hv hx ih =>
    exact feasible_permanent (feasible_scan ih (List.mem_of_mem_getLast? hv)) _

end GraphAlgProof


open AppliedComb.GraphAlg GraphAlgProof

theorem solution {V : Type*} [Fintype V] (G : WeightedDigraph V) (r : V)
    (s : DijkstraState V) (hs : DijkstraRun G r (Fintype.card V) s) :
    ∀ x : V, s.δ x = G.dist r x ∧ (G.dist r x ≠ ⊤ → G.IsShortestPath r x (s.P x)) := by
  intro x
  have hbound (P : List V) (hp : G.IsDirPath r x P) : s.δ x ≤ (G.pathLength P : ℕ∞) := by
    have h := bellman_path_bound s.δ (halted_bellman hs) hp.1 hp.2.1 hp.2.2.2
    simpa [(run_vertices hs).2.2.2] using h
  have hlo : s.δ x ≤ G.dist r x := le_iInf fun P => le_iInf fun hp => hbound P hp
  have hhi : G.dist r x ≤ s.δ x := by
    by_cases hx : s.δ x = ⊤
    · simp [hx]
    · obtain ⟨hp,hlen,_⟩ := run_feasible hs x hx
      rw [← hlen]
      exact iInf_le_of_le (s.P x) (iInf_le_of_le hp le_rfl)
  have he : s.δ x = G.dist r x := le_antisymm hlo hhi
  refine ⟨he,?_⟩
  intro hx
  obtain ⟨hp,hlen,_⟩ := run_feasible hs x (he ▸ hx)
  refine ⟨hp,?_⟩
  intro Q hQ
  have h := hbound Q hQ
  rw [← hlen] at h
  exact_mod_cast h

#print axioms solution
