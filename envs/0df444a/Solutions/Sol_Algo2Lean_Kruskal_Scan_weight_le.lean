-- Prove2me | solution 1 for Algo2Lean.Kruskal.Scan.weight_le
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:58.523803+00:00
-- url     : https://prove2.me/submissions/7b89afc8-f4bb-4453-8219-bd3261dc6ee0

import Definitions.Def_Algo2LeanLib_KruskalMath


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal







theorem Adjacent.symm {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Adjacent edges v u := by
  obtain ⟨e, member, forward | backward⟩ := edge
  · exact ⟨e, member, Or.inr forward⟩
  · exact ⟨e, member, Or.inl backward⟩

theorem Adjacent.connected {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Connected edges u v := .step edge (.refl _)

theorem Connected.trans {edges : List Edge} {u v w : Int}
    (first : Connected edges u v) (second : Connected edges v w) : Connected edges u w := by
  induction first with
  | refl => exact second
  | step edge path ih => exact .step edge (ih second)

theorem Connected.symm {edges : List Edge} {u v : Int} (path : Connected edges u v) :
    Connected edges v u := by
  induction path with
  | refl => exact .refl _
  | step edge path ih => exact ih.trans edge.symm.connected

theorem Connected.mono {before after : List Edge} {u v : Int}
    (subset : ∀ edge ∈ before, edge ∈ after) (path : Connected before u v) :
    Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step edge path ih =>
    obtain ⟨e, member, direction⟩ := edge
    exact .step ⟨e, subset e member, direction⟩ ih

theorem Connected.replace {before after : List Edge} {u v : Int}
    (edges : ∀ edge ∈ before, Connected after edge.source edge.target)
    (path : Connected before u v) : Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step adjacent path ih =>
    obtain ⟨edge, member, forward | backward⟩ := adjacent
    · obtain ⟨rfl, rfl⟩ := forward
      exact (edges edge member).trans ih
    · obtain ⟨rfl, rfl⟩ := backward
      exact (edges edge member).symm.trans ih



theorem edge_connected {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    Connected edges edge.source edge.target :=
  Adjacent.connected ⟨edge, member, Or.inl ⟨rfl, rfl⟩⟩
































theorem Joined.trans {edges : List Edge} {a b u v w : Int}
    (one : Joined edges a b u v) (two : Joined edges a b v w) :
    Joined edges a b u w := by
  rcases one with old | forward | backward
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inl (old.trans oldTwo)
    · exact Or.inr (Or.inl ⟨old.trans forwardTwo.1, forwardTwo.2⟩)
    · exact Or.inr (Or.inr ⟨old.trans backwardTwo.1, backwardTwo.2⟩)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inl ⟨forward.1, forward.2.trans oldTwo⟩)
    · exact Or.inr (Or.inl ⟨forward.1, forwardTwo.2⟩)
    · exact Or.inl (forward.1.trans backwardTwo.2)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inr ⟨backward.1, backward.2.trans oldTwo⟩)
    · exact Or.inl (backward.1.trans forwardTwo.2)
    · exact Or.inr (Or.inr ⟨backward.1, backwardTwo.2⟩)

theorem connected_cons {edge : Edge} {edges : List Edge} {u v : Int} :
    Connected (edge :: edges) u v ↔ Joined edges edge.source edge.target u v := by
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl (.refl _)
    | @step u next v adjacent rest ih =>
      apply Joined.trans (v := next) ?_ ih
      obtain ⟨candidate, member, direction⟩ := adjacent
      rcases List.mem_cons.mp member with rfl | member
      · rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _, .refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _, .refl _⟩)
      · exact Or.inl (Adjacent.connected ⟨candidate, member, direction⟩)
  · intro joined
    have lift {x y} (path : Connected edges x y) : Connected (edge :: edges) x y :=
      path.mono (fun _ member => List.mem_cons_of_mem edge member)
    rcases joined with old | forward | backward
    · exact lift old
    · exact (lift forward.1).trans ((edge_connected (by simp)).trans (lift forward.2))
    · exact (lift backward.1).trans ((edge_connected (by simp)).symm.trans (lift backward.2))

/-- An inserted forest edge cannot already occur in the remaining list. -/
theorem Forest.fresh {edge : Edge} {edges : List Edge} (forest : Forest (edge :: edges)) :
    edge ∉ edges := by
  intro member
  exact forest.2 (edge_connected member)



/-- Joining different components cannot create an alternate route inside an
    existing component, even after some of that component's edges are removed. -/
theorem disconnected_extension {edge : Edge} {before after : List Edge} {u v : Int}
    (subset : ∀ candidate ∈ after, candidate ∈ before)
    (separate : ¬ Connected before edge.source edge.target)
    (old : Connected before u v) (path : Connected (edge :: after) u v) :
    Connected after u v := by
  rcases connected_cons.mp path with unchanged | forward | backward
  · exact unchanged
  · exact False.elim (separate ((forward.1.mono subset).symm.trans
      (old.trans (forward.2.mono subset).symm)))
  · exact False.elim (separate ((backward.2.mono subset).trans
      (old.symm.trans (backward.1.mono subset))))


/-- Deleting an edge preserves acyclicity. -/
theorem Forest.erase {edges : List Edge} (forest : Forest edges) (removed : Edge) :
    Forest (edges.erase removed) := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
    by_cases same : edge = removed
    · subst edge; simpa using forest.1
    · simp only [List.erase_cons, beq_iff_eq, same, ↓reduceIte]
      exact ⟨ih forest.1, fun path => forest.2
        (path.mono (fun _ member => List.mem_of_mem_erase member))⟩

/-- Every edge of a forest is a bridge. -/
theorem Forest.bridge {edges : List Edge} (forest : Forest edges)
    {edge : Edge} (member : edge ∈ edges) :
    ¬ Connected (edges.erase edge) edge.source edge.target := by
  induction edges with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simpa using forest.2
    · have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
      intro path
      exact ih forest.1 member (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2
        (edge_connected member) path)

/-- A forest path can be reconstructed from the edges whose deletion separates
    its endpoints. This avoids choosing a particular list representation of a path. -/
theorem Forest.essential_cover {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v)
    (contains : ∀ edge ∈ edges, ¬ Connected (edges.erase edge) u v → edge ∈ selected) :
    Connected selected u v := by
  classical
  induction edges generalizing u v with
  | nil => exact connected_nil.mp path ▸ Connected.refl u
  | cons first rest ih =>
    have removed {edge : Edge} (member : edge ∈ rest) :
        (first :: rest).erase edge = first :: rest.erase edge := by
      have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp [different]
    by_cases old : Connected rest u v
    · apply ih forest.1 old
      intro edge member necessary
      apply contains edge (by simp [member])
      rw [removed member]
      intro alternative
      exact necessary (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2 old alternative)
    · have join (x y : Int) (left : Connected rest x first.source)
          (right : Connected rest first.target y) (separate : ¬ Connected rest x y)
          (covered : ∀ edge ∈ first :: rest,
            ¬ Connected ((first :: rest).erase edge) x y → edge ∈ selected) :
          Connected selected x y := by
        have selectedFirst : first ∈ selected := covered first (by simp) (by simpa)
        have selectedLeft : Connected selected x first.source := by
          apply ih forest.1 left
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.1
          · exact forest.2 (left.symm.trans
              (backward.1.mono (fun _ included => List.mem_of_mem_erase included)))
        have selectedRight : Connected selected first.target y := by
          apply ih forest.1 right
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.2
          · exact forest.2 ((backward.2.mono
              (fun _ included => List.mem_of_mem_erase included)).trans right.symm)
        exact selectedLeft.trans ((edge_connected selectedFirst).trans selectedRight)
      rcases connected_cons.mp path with impossible | forward | backward
      · exact False.elim (old impossible)
      · exact join u v forward.1 forward.2 old contains
      · apply Connected.symm
        apply join v u backward.2.symm backward.1.symm (fun p => old p.symm)
        intro edge member necessary
        exact contains edge member (fun p => necessary p.symm)

/-- If a smaller edge set fails to connect a pair, some essential edge of a
    connecting forest is missing from that set. -/
theorem Forest.missing_bridge {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v) (separate : ¬ Connected selected u v) :
    ∃ edge ∈ edges, edge ∉ selected ∧ ¬ Connected (edges.erase edge) u v := by
  classical
  apply Classical.byContradiction
  intro absent
  apply separate
  apply forest.essential_cover path
  intro edge member necessary
  apply Classical.byContradiction
  intro missing
  exact absent ⟨edge, member, missing, necessary⟩

/-- Exchanging a bridge on the new edge's path preserves all connected components. -/
theorem exchange_connectivity {edges : List Edge} {added removed : Edge}
    (member : removed ∈ edges) (linked : Connected edges added.source added.target)
    (separate : ¬ Connected (edges.erase removed) added.source added.target) :
    ∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v := by
  have permutation := List.perm_cons_erase member
  have existing : Connected (removed :: edges.erase removed) added.source added.target :=
    linked.mono (fun _ present => permutation.mem_iff.mp present)
  have removedLinked : Connected (added :: edges.erase removed) removed.source removed.target := by
    have lift {x y} (path : Connected (edges.erase removed) x y) :
        Connected (added :: edges.erase removed) x y :=
      path.mono (fun _ present => List.mem_cons_of_mem added present)
    have addedLinked : Connected (added :: edges.erase removed) added.source added.target :=
      edge_connected (by simp)
    rcases connected_cons.mp existing with impossible | forward | backward
    · exact False.elim (separate impossible)
    · exact (lift forward.1).symm.trans (addedLinked.trans (lift forward.2).symm)
    · exact (lift backward.2).trans (addedLinked.symm.trans (lift backward.1))
  intro u v
  constructor
  · intro path
    apply path.replace
    intro edge present
    rcases List.mem_cons.mp present with rfl | present
    · exact linked
    · exact edge_connected (List.mem_of_mem_erase present)
  · intro path
    apply path.replace
    intro edge present
    by_cases same : edge = removed
    · subst edge; exact removedLinked
    · exact edge_connected (by simp [((List.mem_erase_of_ne same).mpr present)])

/-- The forest exchange lemma: add an edge between different selected
    components and remove a forest-path edge outside the selected set. -/
theorem Forest.exchange {edges selected : List Edge} (forest : Forest edges)
    {added : Edge} (linked : Connected edges added.source added.target)
    (separate : ¬ Connected selected added.source added.target) :
    ∃ removed ∈ edges, removed ∉ selected ∧
      Forest (added :: edges.erase removed) ∧
      (∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v) := by
  obtain ⟨removed, member, missing, necessary⟩ := forest.missing_bridge linked separate
  exact ⟨removed, member, missing, ⟨forest.erase removed, necessary⟩,
    exchange_connectivity member linked necessary⟩





theorem weight_perm {one two : List Edge} (same : one.Perm two) : weight one = weight two := by
  induction same with
  | nil => rfl
  | cons edge same ih => simp [ih]
  | swap first second rest => simp [Int.add_left_comm]
  | trans first second ihOne ihTwo => exact ihOne.trans ihTwo

theorem weight_erase {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    weight edges = edge.weight + weight (edges.erase edge) :=
  (weight_perm (List.perm_cons_erase member)).trans (weight_cons edge _)

/-- A forest edge not in a selected subgraph cannot have its endpoints already
    connected by that subgraph: otherwise it would not be a bridge. -/
theorem Forest.outside_disconnected {edges selected : List Edge} (forest : Forest edges)
    (subset : ∀ edge ∈ selected, edge ∈ edges) {edge : Edge}
    (member : edge ∈ edges) (missing : edge ∉ selected) :
    ¬ Connected selected edge.source edge.target := by
  intro path
  apply forest.bridge member
  apply path.mono
  intro candidate present
  have different : candidate ≠ edge := by intro same; exact missing (same ▸ present)
  exact (List.mem_erase_of_ne different).mpr (subset candidate present)

/-- Forests with exactly the same edge occurrences have the same total weight. -/
theorem Forest.weight_eq {one two : List Edge} (first : Forest one) (second : Forest two)
    (same : ∀ edge, edge ∈ one ↔ edge ∈ two) : weight one = weight two := by
  induction one generalizing two with
  | nil =>
    cases two with
    | nil => rfl
    | cons edge rest => have absent := (same edge).mpr (by simp); simp at absent
  | cons edge rest ih =>
    have present : edge ∈ two := (same edge).mp (by simp)
    have deleted : edge ∉ two.erase edge := by
      intro member
      exact second.bridge present (edge_connected member)
    have remaining : ∀ candidate, candidate ∈ rest ↔ candidate ∈ two.erase edge := by
      intro candidate
      constructor
      · intro member
        have different : candidate ≠ edge := by intro equal; exact first.fresh (equal ▸ member)
        exact (List.mem_erase_of_ne different).mpr ((same candidate).mp (by simp [member]))
      · intro member
        rcases List.mem_cons.mp ((same candidate).mpr (List.mem_of_mem_erase member)) with equal | present
        · exact False.elim (deleted (equal ▸ member))
        · exact present
    rw [weight_cons, weight_erase present, ih first.1 (second.erase edge) remaining]

/-- The exchange argument maintains an arbitrary competitor forest. Its edges
    are either already selected or still pending. Each accepted edge can replace
    an equally heavy or heavier competitor edge, preserving all connectivity. -/
theorem Scan.weight_le {pending selected result : List Edge} (scan : Scan pending selected result)
    (ordered : Sorted pending) (selectedForest : Forest selected)
    (other : List Edge) (otherForest : Forest other)
    (retains : ∀ edge ∈ selected, edge ∈ other)
    (remaining : ∀ edge ∈ other, edge ∈ pending ∨ edge ∈ selected)
    (covers : ∀ edge ∈ pending, Connected other edge.source edge.target) :
    weight result ≤ weight other := by
  classical
  induction scan generalizing other with
  | done selected =>
    have same : ∀ edge, edge ∈ selected ↔ edge ∈ other := by
      intro edge
      exact ⟨retains edge, fun member => by simpa using remaining edge member⟩
    exact Int.le_of_eq (selectedForest.weight_eq otherForest same)
  | @reject edge pending selected result linked rest ih =>
    apply ih (List.pairwise_cons.mp ordered).2 selectedForest other otherForest retains
    · intro candidate member
      rcases remaining candidate member with pendingMember | selectedMember
      · rcases List.mem_cons.mp pendingMember with same | pendingMember
        · by_cases selectedMember : candidate ∈ selected
          · exact Or.inr selectedMember
          · exact False.elim (otherForest.outside_disconnected retains member selectedMember
              (same.symm ▸ linked))
        · exact Or.inl pendingMember
      · exact Or.inr selectedMember
    · exact fun candidate member => covers candidate (by simp [member])
  | @accept edge pending selected result separate rest ih =>
    have selectedNext : Forest (edge :: selected) := ⟨selectedForest, separate⟩
    have tailOrdered : Sorted pending := (List.pairwise_cons.mp ordered).2
    by_cases present : edge ∈ other
    · apply ih tailOrdered selectedNext other otherForest
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact same ▸ present
        · exact retains candidate old
      · intro candidate member
        rcases remaining candidate member with pendingMember | selectedMember
        · rcases List.mem_cons.mp pendingMember with same | pendingMember
          · exact Or.inr (by simp [same])
          · exact Or.inl pendingMember
        · exact Or.inr (by simp [selectedMember])
      · exact fun candidate member => covers candidate (by simp [member])
    · obtain ⟨removed, removedMember, removedOutside, exchangedForest, connectivity⟩ :=
        otherForest.exchange (covers edge (by simp)) separate
      have removedPending : removed ∈ pending := by
        rcases remaining removed removedMember with waiting | old
        · rcases List.mem_cons.mp waiting with same | waiting
          · exact False.elim (present (same ▸ removedMember))
          · exact waiting
        · exact False.elim (removedOutside old)
      have cheap : edge.weight ≤ removed.weight := (List.pairwise_cons.mp ordered).1 removed removedPending
      have exchangeBound : weight (edge :: other.erase removed) ≤ weight other := by
        rw [weight_cons, weight_erase removedMember]
        omega
      apply Int.le_trans (b := weight (edge :: other.erase removed)) ?_ exchangeBound
      apply ih tailOrdered selectedNext (edge :: other.erase removed) exchangedForest
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact by simp [same]
        · have different : candidate ≠ removed := by intro same; exact removedOutside (same ▸ old)
          exact List.mem_cons_of_mem edge ((List.mem_erase_of_ne different).mpr (retains candidate old))
      · intro candidate member
        rcases List.mem_cons.mp member with same | old
        · exact Or.inr (by simp [same])
        · rcases remaining candidate (List.mem_of_mem_erase old) with waiting | already
          · rcases List.mem_cons.mp waiting with same | waiting
            · exact Or.inr (by simp [same])
            · exact Or.inl waiting
          · exact Or.inr (by simp [already])
      · intro candidate member
        exact (connectivity _ _).mpr (covers candidate (by simp [member]))




























end Algo2Lean.Kruskal

end

set_option autoImplicit false
theorem solution :
    ∀ {pending selected result : List.{0} Algo2Lean.Kruskal.Edge},
      Algo2Lean.Kruskal.Scan pending selected result →
        Algo2Lean.Kruskal.Sorted pending →
          Algo2Lean.Kruskal.Forest selected →
            ∀ (other : List.{0} Algo2Lean.Kruskal.Edge),
              Algo2Lean.Kruskal.Forest other →
                (∀ (edge : Algo2Lean.Kruskal.Edge),
                    Membership.mem.{0, 0} selected edge → Membership.mem.{0, 0} other edge) →
                  (∀ (edge : Algo2Lean.Kruskal.Edge),
                      Membership.mem.{0, 0} other edge →
                        Membership.mem.{0, 0} pending edge ∨ Membership.mem.{0, 0} selected edge) →
                    (∀ (edge : Algo2Lean.Kruskal.Edge),
                        Membership.mem.{0, 0} pending edge →
                          Algo2Lean.Kruskal.Connected other edge.source edge.target) →
                      LE.le.{0} (Algo2Lean.Kruskal.weight result) (Algo2Lean.Kruskal.weight other) :=
  Algo2Lean.Kruskal.Scan.weight_le
