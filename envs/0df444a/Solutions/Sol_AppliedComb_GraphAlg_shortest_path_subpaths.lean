-- Prove2me | solution 1 for AppliedComb.GraphAlg.shortest_path_subpaths
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:27:36.992859+00:00
-- url     : https://prove2.me/submissions/8b978fc3-41b8-4392-9b38-29aa4c3b9659

import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

set_option autoImplicit false


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


open AppliedComb.GraphAlg

namespace GraphAlgProof

variable {V : Type*} (G : WeightedDigraph V)

theorem pathLength_split (L R : List V) (v : V) :
    G.pathLength (L ++ v :: R) = G.pathLength (L ++ [v]) + G.pathLength (v :: R) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases L with
    | nil => simp
    | cons b L =>
      simpa only [List.cons_append,pathLength_cons,Nat.add_assoc] using
        congrArg (G.w a b + ·) ih

theorem shortest_split {r x v : V} (L R : List V)
    (hP : G.IsShortestPath r x (L ++ v :: R)) :
    G.IsShortestPath r v (L ++ [v]) ∧ G.IsShortestPath v x (v :: R) := by
  have hh : (L ++ [v]).head? = some r := by
    cases L <;> simpa using hP.1.1
  have hl : (v :: R).getLast? = some x := by simpa using hP.1.2.1
  have hc := List.isChain_split.mp hP.1.2.2.2
  have hpref : G.IsDirPath r v (L ++ [v]) := by
    refine ⟨hh,by simp,?_,hc.1⟩
    exact hP.1.2.2.1.sublist
      (List.Sublist.append (List.Sublist.refl L) (List.singleton_sublist.mpr (by simp)))
  have hsuff : G.IsDirPath v x (v :: R) :=
    ⟨rfl,hl,hP.1.2.2.1.sublist (List.sublist_append_right L _),hc.2⟩
  have hlen := pathLength_split G L R v
  constructor
  · refine ⟨hpref,?_⟩
    intro Q hQ
    have he : Q.dropLast ++ [v] = Q := List.dropLast_append_getLast? v hQ.2.1
    have hhead : (Q.dropLast ++ v :: R).head? = some r := by
      have h := hQ.1
      rw [← he] at h
      cases heq : Q.dropLast <;> simpa [heq] using h
    obtain ⟨W,hW,hWlen⟩ := walk_to_path G hhead (by simpa using hl)
      (List.isChain_split.mpr ⟨by rw [he]; exact hQ.2.2.2,hc.2⟩)
    have hshort := hP.2 W hW
    have hsplit := pathLength_split G Q.dropLast R v
    rw [he] at hsplit
    omega
  · refine ⟨hsuff,?_⟩
    intro Q hQ
    cases Q with
    | nil => simp [WeightedDigraph.IsDirPath] at hQ
    | cons a S =>
      have ha : a = v := by simpa using hQ.1
      subst a
      have hhead : (L ++ v :: S).head? = some r := by
        cases L <;> simpa using hh
      obtain ⟨W,hW,hWlen⟩ := walk_to_path G hhead (by simpa using hQ.2.1)
        (List.isChain_split.mpr ⟨hc.1,hQ.2.2.2⟩)
      have hshort := hP.2 W hW
      have hsplit := pathLength_split G L S v
      omega

end GraphAlgProof


open AppliedComb.GraphAlg

theorem solution {V : Type*} (G : WeightedDigraph V) (r x : V) (P : List V)
    (hP : G.IsShortestPath r x P) (j : ℕ) (hj0 : 0 < j) (hjt : j < P.length - 1) :
    G.IsShortestPath r (P[j]'(by omega)) (P.take (j + 1)) ∧
      G.IsShortestPath (P[j]'(by omega)) x (P.drop j) := by
  have hj : j < P.length := by omega
  have he : P.take j ++ P[j] :: P.drop (j+1) = P := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hp := GraphAlgProof.shortest_split G (P.take j) (P.drop (j+1)) (he ▸ hP)
  simpa only [← List.take_succ_eq_append_getElem hj, ← List.drop_eq_getElem_cons hj] using hp

#print axioms solution
