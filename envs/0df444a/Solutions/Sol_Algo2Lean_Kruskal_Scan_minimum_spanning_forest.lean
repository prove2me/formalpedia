-- Prove2me | solution 1 for Algo2Lean.Kruskal.Scan.minimum_spanning_forest
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:35.345024+00:00
-- url     : https://prove2.me/submissions/15ace917-aae6-47da-a707-5f630abac0c8

import Definitions.Def_Algo2LeanLib_KruskalMath
import Theorems.Thm_Algo2Lean_Kruskal_Scan_weight_le


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

















theorem Scan.forest {pending selected result : List Edge} (scan : Scan pending selected result)
    (forest : Forest selected) : Forest result := by
  induction scan with
  | done => exact forest
  | reject linked rest ih => exact ih forest
  | accept unlinked rest ih => exact ih ⟨forest, unlinked⟩

theorem Scan.retains {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ selected, edge ∈ result := by
  induction scan with
  | done => exact fun _ member => member
  | reject linked rest ih => exact ih
  | accept unlinked rest ih => exact fun edge member => ih edge (by simp [member])

theorem Scan.subset {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ result, edge ∈ pending ∨ edge ∈ selected := by
  induction scan with
  | done => exact fun edge member => Or.inr member
  | @reject edge pending selected result linked rest ih =>
    intro candidate member
    rcases ih candidate member with scanned | old
    · exact Or.inl (by simp [scanned])
    · exact Or.inr old
  | @accept edge pending selected result unlinked rest ih =>
    intro candidate member
    rcases ih candidate member with scanned | old
    · exact Or.inl (by simp [scanned])
    · rcases List.mem_cons.mp old with same | old
      · exact Or.inl (by simp [same])
      · exact Or.inr old

theorem Scan.covers {pending selected result : List Edge} (scan : Scan pending selected result) :
    ∀ edge ∈ pending, Connected result edge.source edge.target := by
  induction scan with
  | done => simp
  | @reject edge pending selected result linked rest ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact linked.mono rest.retains
    · exact ih candidate member
  | @accept edge pending selected result unlinked rest ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge_connected (rest.retains candidate (by simp))
    · exact ih candidate member

/-- Even without the weight-order hypothesis, the completed scan produces a
    forest with exactly the input's connected components. -/
theorem Scan.spanning_forest {input result : List Edge} (scan : Scan input [] result) :
    Forest result ∧ Spans input result := by
  refine ⟨scan.forest trivial, ?_⟩
  constructor
  · intro edge member
    simpa using scan.subset edge member
  · intro u v path
    exact path.replace scan.covers











































/-- Kruskal's sorted-edge scan returns a minimum spanning forest. The comparison
    is against every spanning forest, and edge weights may be arbitrary integers. -/
theorem Scan.minimum_spanning_forest {input result : List Edge}
    (scan : Scan input [] result) (ordered : Sorted input) :
    MinimumSpanningForest input result := by
  obtain ⟨forest, spanning⟩ := scan.spanning_forest
  refine ⟨forest, spanning, ?_⟩
  intro other otherForest otherSpanning
  apply scan.weight_le ordered trivial other otherForest
  · simp
  · exact fun edge member => Or.inl (otherSpanning.subset edge member)
  · exact fun edge member => otherSpanning.connected _ _ (edge_connected member)


























end Algo2Lean.Kruskal

end

set_option autoImplicit false
theorem solution :
    ∀ {input result : List.{0} Algo2Lean.Kruskal.Edge},
      Algo2Lean.Kruskal.Scan input List.nil.{0} result →
        Algo2Lean.Kruskal.Sorted input → Algo2Lean.Kruskal.MinimumSpanningForest input result :=
  Algo2Lean.Kruskal.Scan.minimum_spanning_forest
