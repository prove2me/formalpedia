-- Prove2me | solution 1 for Algo2Lean.Fibonacci.Represented.delete_minimum
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:01.79099+00:00
-- url     : https://prove2.me/submissions/69e78959-6252-4f42-9b9f-1a02f084ae22

import Definitions.Def_Algo2LeanLib_FibonacciDeleteMin
import Theorems.Thm_Algo2Lean_Fibonacci_degree_logarithmic
import Theorems.Thm_Algo2Lean_Fibonacci_RootBoundary_cut


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci






theorem minimumNodes_step (degree : Nat) :
    minimumNodes (degree + 1) = minimumNodes degree + minimumNodes (degree - 1) := by
  cases degree with
  | zero => rfl
  | succ degree => simp only [Nat.add_sub_cancel, minimumNodes]

theorem minimumNodes_mono_step (degree : Nat) : minimumNodes degree ≤ minimumNodes (degree + 1) := by
  rw [minimumNodes_step]
  omega

theorem minimumNodes_mono {first second : Nat} (ordered : first ≤ second) :
    minimumNodes first ≤ minimumNodes second := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | @step second ordered ih => exact Nat.le_trans ih (minimumNodes_mono_step second)















/-- The children's induction bounds and link order force the parent's
    Fibonacci bound; no subtree-size conclusion is assumed for the parent. -/
theorem ranked_children_bound (children : List Tree)
    (ordered : RankOrder children)
    (childrenBound : ∀ child ∈ children, minimumNodes child.degree ≤ child.nodes) :
    minimumNodes children.length ≤ 1 + (children.map Tree.nodes).sum := by
  induction children with
  | nil => simp
  | cons child older ih =>
    have rest := ih ordered.2 (fun tree member => childrenBound tree (by simp [member]))
    have head := childrenBound child (by simp)
    have degreeBound : older.length - 1 ≤ child.degree := by have := ordered.1; omega
    have headMinimum := minimumNodes_mono degreeBound
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rw [minimumNodes_step]
    omega

/-- Every tree satisfying the local rank invariant has exponentially many
    nodes in its degree, with the sharper Fibonacci lower bound. -/
theorem Tree.Ranked.subtree_bound {tree : Tree} (ranked : tree.Ranked) :
    minimumNodes tree.degree ≤ tree.nodes := by
  induction ranked with
  | node ordered children ih => simpa only [Tree.degree, Tree.nodes] using ranked_children_bound _ ordered ih





/-- One common heap-size bound applies to every represented subtree. -/
theorem Tree.Ranked.degree_bound_of_size {tree : Tree} {heapSize : Nat}
    (ranked : tree.Ranked) (contained : tree.nodes ≤ heapSize) :
    tree.degree ≤ 2 * heapSize.log2 + 1 :=
  degree_logarithmic (Nat.le_trans ranked.subtree_bound contained)





























































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite logical forests for the mutable Fibonacci heap.

Vertex handles and keys are mathematical integers. Child lists are newest-first
in link order, matching insertion before the physical child-ring head. A ring
representation still needs to prove that its traversal realizes this finite
forest, with unique handles and the observable parent/mark/degree fields.
-/

namespace Algo2Lean.Fibonacci



































/-- Shape size counts the actual finite list of represented entries. -/
theorem Node.shape_size (node : Node) : node.shape.nodes = node.entries.length := by
  apply Node.rec
    (motive_1 := fun node => node.shape.nodes = node.entries.length)
    (motive_2 := fun children => (children.map (fun child => child.shape.nodes)).sum =
      (children.flatMap Node.entries).length) _ _ _ node
  · intro vertex key marked children ih
    simp only [Node.shape, Tree.nodes, Node.entries, List.map_map, Function.comp_def, List.length_cons]
    omega
  · simp
  · intro child children childSize tailSize
    simp [childSize, tailSize]

















/-- Forgetting marks gives the weaker rank invariant used for the Fibonacci bound. -/
theorem ChildOrder.shape {children : List Node} (ordered : ChildOrder children) :
    RankOrder (children.map Node.shape) := by
  induction children with
  | nil => trivial
  | cons child older ih =>
    refine ⟨?_, ih ordered.2⟩
    have capacity := ordered.1
    simp only [List.length_map, Node.shape_degree]
    unfold Node.rankCapacity at capacity
    have allowance : (if child.marked then 1 else 0) ≤ (1 : Nat) := by split <;> decide
    omega

theorem Node.Ranked.shape_ranked {node : Node} (ranked : node.Ranked) : node.shape.Ranked := by
  induction ranked with
  | make ordered valid ih =>
    simp only [Node.shape]
    apply Tree.Ranked.node ordered.shape
    intro shape member
    obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp member
    exact ih child inChildren







/-- Changes to a root's mark do not alter its internal heap order or rank history. -/
theorem Node.Ordered.withMark {node : Node} (ordered : node.Ordered) (marked : Bool) :
    (node.withMark marked).Ordered := by
  cases ordered with
  | make bounds children => exact .make bounds children

theorem Node.Ranked.withMark {node : Node} (ranked : node.Ranked) (marked : Bool) :
    (node.withMark marked).Ranked := by
  cases ranked with
  | make ordered children => exact .make ordered children





/-- Surviving children retain their history order after cuts. -/
theorem ChildOrder.sublist {children kept : List Node} (ordered : ChildOrder children)
    (remaining : kept.Sublist children) : ChildOrder kept := by
  induction remaining with
  | slnil => trivial
  | cons child remaining ih => exact ih ordered.2
  | _ child remaining ih => exact ⟨Nat.le_trans remaining.length_le ordered.1, ih ordered.2⟩

theorem Node.Ordered.prune {node : Node} (ordered : node.Ordered) (kept : List Node)
    (remaining : kept.Sublist node.children) : (node.withChildren kept).Ordered := by
  cases ordered with
  | make bounds children =>
    exact .make (fun child member => bounds child (remaining.subset member))
      (fun child member => children child (remaining.subset member))

theorem Node.Ranked.prune {node : Node} (ranked : node.Ranked) (kept : List Node)
    (remaining : kept.Sublist node.children) : (node.withChildren kept).Ranked := by
  cases ranked with
  | make ordered children =>
    exact .make (ordered.sublist remaining) (fun child member => children child (remaining.subset member))









/-- Removing one child separates exactly that subtree from its parent. -/
theorem Node.cut_entries (parent : Node) (earlier suffix : List Node) (child : Node)
    (located : parent.children = earlier ++ child :: suffix) :
    parent.entries.Perm ((parent.withChildren (earlier ++ suffix)).entries ++ child.entries) := by
  cases parent with
  | make vertex key marked children =>
    change children = earlier ++ child :: suffix at located
    subst children
    simpa only [Node.entries, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
      List.flatMap_append, List.flatMap_cons, List.cons_append, List.append_assoc] using
      ((List.perm_append_comm (l₁ := child.entries) (l₂ := suffix.flatMap Node.entries)).append_left
        (earlier.flatMap Node.entries)).cons (vertex, key)















/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique





theorem Forest.cutRootChild_entries (parent child : Node) (earlier later : List Node) (rest : Forest)
    (located : parent.children = earlier ++ child :: later) :
    (cutRootChild parent child earlier later rest).entries.Perm (Forest.entries (parent :: rest)) := by
  simpa [Forest.cutRootChild, Forest.entries, List.append_assoc] using
    (parent.cut_entries earlier later child located).symm.append_right rest.entries





/-- Cutting a child of a root preserves content, heap order, rank history and
    unique handles. The detached subtree becomes an unmarked root. -/
theorem Forest.Valid.cut_root_child {parent child : Node} {rest : Forest}
    (valid : (Forest.Valid (parent :: rest))) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later) :
    (cutRootChild parent child earlier later rest).Valid := by
  have parentMember : parent ∈ parent :: rest := by simp
  have childMember : child ∈ parent.children := by rw [located]; simp
  have remaining : (earlier ++ later).Sublist parent.children := by
    rw [located]
    exact (List.Sublist.refl earlier).append ((List.Sublist.refl later).cons child)
  have parentOrdered := valid.2.1 parent parentMember
  have parentRanked := valid.2.2.1 parent parentMember
  have childOrdered : child.Ordered := by cases parentOrdered with | make _ children => exact children child childMember
  have childRanked : child.Ranked := by cases parentRanked with | make _ children => exact children child childMember
  refine ⟨valid.1.of_entries_perm (Forest.cutRootChild_entries parent child earlier later rest located), ?_, ?_, ?_⟩
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact parentOrdered.prune _ remaining
    rcases List.mem_cons.mp tail with rfl | old
    · exact childOrdered.withMark false
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact parentRanked.prune _ remaining
    rcases List.mem_cons.mp tail with rfl | old
    · exact childRanked.withMark false
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | tail
    · exact valid.2.2.2 parent parentMember
    rcases List.mem_cons.mp tail with rfl | old
    · rfl
    · exact valid.2.2.2 node (by simp [old])







theorem Node.clear_mark_count (node : Node) :
    (node.withMark false).marks + (if node.marked then 1 else 0) = node.marks := by
  cases node
  simp [Node.withMark, Node.marks, Node.vertex, Node.key, Node.children, Node.marked, Nat.add_comm]

theorem Node.clear_mark_le (node : Node) : (node.withMark false).marks ≤ node.marks := by
  have count := node.clear_mark_count
  omega











theorem Forest.promoteChildren_entries (minimum : Node) (rest : Forest) :
    (Forest.entries (minimum :: rest)) =
      (minimum.vertex, minimum.key) :: (Forest.promoteChildren minimum rest).entries := by
  cases minimum
  simp [Forest.promoteChildren, Forest.entries, Node.entries, Node.children, Node.vertex, Node.key,
    List.flatMap_map]



/-- Promotion supplies the exact root-count equation and nonincreasing mark
    count used by the amortized extraction theorem. -/
theorem Forest.promoteChildren_accounting (minimum : Node) (rest : Forest) :
    (promoteChildren minimum rest).counts.roots + 1 =
      (Forest.counts (minimum :: rest)).roots + minimum.degree ∧
    (promoteChildren minimum rest).counts.marks ≤ (Forest.counts (minimum :: rest)).marks := by
  have clear : ∀ children : List Node,
      ((children.map (fun child => child.withMark false)).map Node.marks).sum ≤
        (children.map Node.marks).sum := by
    intro children
    induction children with
    | nil => simp
    | cons child children ih =>
      simp only [List.map_cons, List.sum_cons]
      have bound := child.clear_mark_le
      omega
  constructor
  · simp [Forest.counts, Forest.promoteChildren, Node.degree, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have marks := clear minimum.children
    cases minimum
    simp only [Forest.counts, Forest.marks, Forest.promoteChildren, Node.children,
      List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, Node.marks]
    simp only [Node.children] at marks
    omega









end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite circular doubly linked lists for Fibonacci-heap pointer proofs.

The representation is independent of heaps and sequence references: `left` and
`right` are the integer-indexed pointer arrays observed through an allocated
sequence. Primitive effects below follow the source's precise write order.
-/

namespace Algo2Lean.Fibonacci.Rings













theorem Chain.first_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : first ∈ vertices := by
  cases chain <;> simp

theorem Chain.last_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : last ∈ vertices := by
  induction chain with
  | singleton => simp
  | cons first _ _ _ ih => simp [ih]

theorem Chain.head {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : ∃ tail, vertices = first :: tail := by
  cases chain <;> exact ⟨_, rfl⟩



/-- Open chains can be joined at one new edge. -/
theorem Chain.append {left right : Int → Int} {first middle next last : Int}
    {front back : List Int} (one : Chain left right first front middle)
    (two : Chain left right next back last) (forward : right middle = next)
    (backward : left next = middle) : Chain left right first (front ++ back) last := by
  induction one with
  | singleton => exact .cons _ forward backward two
  | cons first rightFirst leftNext tail ih => exact .cons first rightFirst leftNext (ih forward backward)

/-- Pointer updates at a chain's external endpoints do not affect its
    internal links. All other observations only need agree on this chain. -/
theorem Chain.frame {left right newLeft newRight : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (unique : vertices.Nodup)
    (leftSame : ∀ vertex ∈ vertices, vertex ≠ first → newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, vertex ≠ last → newRight vertex = right vertex) :
    Chain newLeft newRight first vertices last := by
  induction chain with
  | singleton => exact .singleton _
  | @cons first next last tail forward backward chain ih =>
    obtain ⟨firstAbsent, tailUnique⟩ := List.nodup_cons.mp unique
    have firstLast : first ≠ last := by intro same; exact firstAbsent (same.symm ▸ chain.last_mem)
    have nextFirst : next ≠ first := by intro same; exact firstAbsent (same ▸ chain.first_mem)
    refine Chain.cons first (next := next) ?_ ?_ ?_
    · rw [rightSame first (by simp) firstLast]
      exact forward
    · rw [leftSame next (by simp [chain.first_mem]) nextFirst]
      exact backward
    · apply ih tailUnique
      · intro vertex member _
        apply leftSame vertex (by simp [member])
        intro same
        subst vertex
        exact firstAbsent member
      · intro vertex member different
        exact rightSame vertex (by simp [member]) different

/-- Equal pointer values on ring members preserve the ring; other array entries
    may differ. -/
theorem Ring.frame {left right newLeft newRight : Int → Int} {vertices : List Int}
    (ring : Ring left right vertices)
    (leftSame : ∀ vertex ∈ vertices, newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, newRight vertex = right vertex) :
    Ring newLeft newRight vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  refine ⟨ring.unique, first, last, chain.frame ring.unique (fun v member _ => leftSame v member)
    (fun v member _ => rightSame v member), ?_, ?_⟩
  · rw [rightSame last chain.last_mem]
    exact forward
  · rw [leftSame first chain.first_mem]
    exact backward

/-- Every pointer read at a ring member stays within that finite ring. -/
theorem Chain.neighbors {left right : Int → Int} {first last vertex : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (member : vertex ∈ vertices) :
    (vertex = first ∨ left vertex ∈ vertices) ∧ (vertex = last ∨ right vertex ∈ vertices) := by
  induction chain with
  | singleton =>
    have same := List.mem_singleton.mp member
    exact ⟨Or.inl same, Or.inl same⟩
  | @cons first next last tail forward backward chain ih =>
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨Or.inl rfl, Or.inr (by rw [forward]; simp [chain.first_mem])⟩
    · obtain ⟨leftNeighbor, rightNeighbor⟩ := ih inTail
      constructor
      · rcases leftNeighbor with rfl | inside
        · exact Or.inr (by rw [backward]; simp)
        · exact Or.inr (by simp [inside])
      · rcases rightNeighbor with same | inside
        · exact Or.inl same
        · exact Or.inr (by simp [inside])

theorem Ring.neighbors {left right : Int → Int} {vertex : Int} {vertices : List Int}
    (ring : Ring left right vertices) (member : vertex ∈ vertices) :
    left vertex ∈ vertices ∧ right vertex ∈ vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨leftNeighbor, rightNeighbor⟩ := chain.neighbors member
  constructor
  · rcases leftNeighbor with rfl | inside
    · rw [backward]; exact chain.last_mem
    · exact inside
  · rcases rightNeighbor with rfl | inside
    · rw [forward]; exact chain.first_mem
    · exact inside

/-- A displayed list head is the first endpoint of its open chain. -/
theorem Ring.open_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) :
    ∃ last, Chain left right head (head :: tail) last ∧ right last = head ∧ left head = last := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨rest, same⟩ := chain.head
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  exact ⟨last, chain, forward, backward⟩











/-- Inserting a fresh vertex before the chosen head realizes list prepend.
    The inserted vertex's previous pointers need not already be self-links. -/
theorem Ring.insert_before {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      (vertex :: head :: tail) := by
  obtain ⟨last, chain, closesRight, closesLeft⟩ := ring.open_head
  have vertexHead : vertex ≠ head := by intro same; exact fresh (by simp [same])
  have oldDifferent (other : Int) (member : other ∈ head :: tail) : other ≠ vertex := by
    intro same
    exact fresh (same ▸ member)
  have vertexLast : vertex ≠ last := Ne.symm (oldDifferent last chain.last_mem)
  have inside : Chain (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      head (head :: tail) last := by
    apply chain.frame ring.unique
    · intro other member notHead
      simp [insertBeforeLeft, write, oldDifferent other member, notHead]
    · intro other member notLast
      simp [insertBeforeRight, write, closesLeft, oldDifferent other member, notLast]
  refine ⟨List.nodup_cons.mpr ⟨fresh, ring.unique⟩, vertex, last,
    Chain.cons vertex (next := head) ?_ ?_ inside, ?_, ?_⟩
  · simp [insertBeforeRight, write, closesLeft, vertexLast]
  · simp [insertBeforeLeft, write]
  · simp [insertBeforeRight, write, closesLeft]
  · simp [insertBeforeLeft, write, closesLeft, vertexHead]



/-- Removing the displayed head leaves its tail as the surviving ring, or
    leaves no surviving ring when the original was a singleton. -/
theorem Ring.remove_head {left right : Int → Int} {vertex : Int} {tail : List Int}
    (ring : Ring left right (vertex :: tail)) :
    RingOrEmpty (removeLeft left right vertex) (removeRight left right vertex) tail := by
  obtain ⟨last, chain, closesRight, closesLeft⟩ := ring.open_head
  cases chain with
  | singleton => exact Or.inl rfl
  | @cons first next last tail forward backward chain =>
    obtain ⟨firstAbsent, tailUnique⟩ := List.nodup_cons.mp ring.unique
    have nextFirst : next ≠ vertex := by intro same; exact firstAbsent (same ▸ chain.first_mem)
    have lastFirst : last ≠ vertex := by intro same; exact firstAbsent (same ▸ chain.last_mem)
    have tailDifferent (other : Int) (member : other ∈ tail) : other ≠ vertex := by
      intro same
      exact firstAbsent (same ▸ member)
    refine Or.inr ⟨tailUnique, next, last, ?_, ?_, ?_⟩
    · apply chain.frame tailUnique
      · intro other member notNext
        simp [removeLeft, write, forward, notNext, tailDifferent other member]
      · intro other member notLast
        simp [removeRight, write, closesLeft, notLast, tailDifferent other member]
    · simp [removeRight, write, closesLeft, forward, lastFirst]
    · simp [removeLeft, write, closesLeft, forward, nextFirst]

/-- Choosing the next node as the head rotates the list but changes no pointers. -/
theorem Ring.rotate_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) : Ring left right (tail ++ [head]) := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  have unique : (tail ++ [head]).Nodup := by
    exact (List.perm_append_comm (l₁ := tail) (l₂ := [head])).nodup_iff.mpr ring.unique
  cases chain with
  | singleton => exact ring
  | @cons first next last tail rightHead leftNext rest =>
    exact ⟨unique, next, head, rest.append (.singleton head) forward backward, rightHead, leftNext⟩

/-- Any cyclic rotation describes the same ring. -/
theorem Ring.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : Ring left right (front ++ back)) : Ring left right (back ++ front) := by
  induction front generalizing back with
  | nil => simpa using ring
  | cons head front ih =>
    have rotated := ring.rotate_head
    change Ring left right ((front ++ back) ++ [head]) at rotated
    have nextRing : Ring left right (front ++ (back ++ [head])) := by
      simpa only [List.append_assoc] using rotated
    have final := ih (back ++ [head]) nextRing
    simpa only [List.append_assoc, List.singleton_append] using final

theorem RingOrEmpty.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : RingOrEmpty left right (front ++ back)) : RingOrEmpty left right (back ++ front) := by
  rcases ring with empty | ring
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp empty
    exact Or.inl rfl
  · exact Or.inr (ring.rotate_append front back)









theorem Ring.singleton_pointers {left right : Int → Int} {vertex : Int}
    (ring : Ring left right [vertex]) : left vertex = vertex ∧ right vertex = vertex := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  cases chain with
  | singleton => exact ⟨backward, forward⟩
  | cons _ _ _ rest => cases rest

theorem Ring.head_next {left right : Int → Int} {head next : Int} {tail : List Int}
    (ring : Ring left right (head :: next :: tail)) : right head = next ∧ left next = head := by
  obtain ⟨last, chain, _, _⟩ := ring.open_head
  cases chain with
  | @cons _ child _ _ forward backward rest =>
    obtain ⟨remaining, same⟩ := rest.head
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    exact ⟨forward, backward⟩





/-- Insertion after a representative is insertion before its successor, so
    the resulting ring order is `head :: vertex :: tail`. -/
theorem Ring.insert_after {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertAfterLeft left right head vertex) (insertAfterRight right head vertex)
      (head :: vertex :: tail) := by
  cases tail with
  | nil =>
    obtain ⟨selfLeft, selfRight⟩ := ring.singleton_pointers
    have result := (ring.insert_before fresh).rotate_head
    simpa [insertBeforeLeft, insertBeforeRight, insertAfterLeft, insertAfterRight, selfLeft, selfRight] using result
  | cons next rest =>
    obtain ⟨forward, backward⟩ := ring.head_next
    have rotated : Ring left right (next :: (rest ++ [head])) := ring.rotate_head
    have freshRotated : vertex ∉ next :: (rest ++ [head]) := by
      simpa [or_comm, or_left_comm, or_assoc] using fresh
    have inserted := rotated.insert_before freshRotated
    have restored := inserted.rotate_append (vertex :: next :: rest) [head]
    simpa only [List.singleton_append, insertBeforeLeft, insertBeforeRight,
      insertAfterLeft, insertAfterRight, forward, backward] using restored



end Algo2Lean.Fibonacci.Rings

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The representation boundary between Fibonacci forests and mutable indexed storage.
Snapshots contain ordinary array observations, not a compiler configuration or a
transcript. A compiled operation must establish preservation of this relation.
-/

namespace Algo2Lean.Fibonacci





theorem Stored.root_key {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.keys node.vertex = node.key := by
  cases stored
  assumption





/-- Storage reads agree with every logical entry, not only the root. -/
theorem Stored.entries {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.entries →
      state.keys vertex = key ∧ state.present vertex = 1 := by
  induction stored with
  | node key parent mark degree present childHead ring children ih =>
    intro vertex value member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, member⟩
    · exact ⟨key, present⟩
    · exact ih child inChildren vertex value member













/-- A represented root obeys the same logarithmic bound used in consolidation. -/
theorem Represented.root_degree_bound {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {root : Node} (member : root ∈ forest) :
    root.degree ≤ 2 * forest.entries.length.log2 + 1 := by
  have included : root.entries.length ≤ forest.entries.length := by
    obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp member
    rw [equal]
    simp [Forest.entries, List.flatMap_append]
    omega
  have contained : root.shape.nodes ≤ forest.entries.length := by
    simpa only [Node.shape_size] using included
  simpa only [Node.shape_degree] using
    (represented.valid.2.2.1 root member).shape_ranked.degree_bound_of_size contained







theorem Node.child_entries {node child : Node} (childMember : child ∈ node.children)
    {vertex key : Int} (inside : (vertex, key) ∈ child.entries) : (vertex, key) ∈ node.entries := by
  cases node
  simp only [Node.children] at childMember
  simp only [Node.entries, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨child, childMember, inside⟩

theorem Node.descendant_entries {node : Node} {vertex key : Int}
    (member : (vertex, key) ∈ node.children.flatMap Node.entries) : (vertex, key) ∈ node.entries := by
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  exact Node.child_entries childMember inside

theorem Stored.root_parent {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.parents node.vertex = parent := by
  cases stored
  assumption

/-- A stored subtree can be reused when its metadata and its descendants'
    sibling pointers are preserved. The root's own sibling pointers are irrelevant. -/
theorem Stored.frame {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    have rootFields := fields vertex key (by simp [Node.entries])
    refine Stored.node (rootFields.key.trans readKey) (rootFields.parent.trans readParent)
      (rootFields.mark.trans readMark) (rootFields.degree.trans readDegree)
      (rootFields.present.trans readPresent)
      (by cases children <;> exact rootFields.child.trans readChild) ?_ ?_
    · rcases ring with empty | ring
      · exact Or.inl empty
      · apply Or.inr
        apply ring.frame
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).1
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).2
    · intro child member
      apply ih child member
      · intro vertex key inside
        apply fields vertex key
        exact Node.child_entries member inside
      · intro vertex key inside
        apply links vertex key
        exact List.mem_flatMap.mpr ⟨child, member, Node.descendant_entries inside⟩

/-- Nonroot entries have nonnegative parent handles. This lets root-ring
    rewiring be separated from every stored subtree's internal child rings. -/
theorem Stored.parents_nonnegative {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (parentNonnegative : 0 ≤ parent)
    (verticesNonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex) :
    ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ state.parents vertex := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, childMember, inside⟩
    · simpa only [readParent] using parentNonnegative
    · apply ih child childMember _ _ value weight inside
      · exact verticesNonnegative vertex key (by simp [Node.entries])
      · intro descendant descendantKey descendantMember
        exact verticesNonnegative descendant descendantKey (Node.child_entries childMember descendantMember)

/-- Preserving all active nonroot pointers suffices to preserve each old tree
    when only root-ring links and previously absent array cells are changed. -/
theorem Stored.frame_roots {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex, before.present vertex = 1 → 0 ≤ before.parents vertex →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  apply stored.frame fields
  intro vertex key member
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  have childrenStored : ∀ child ∈ node.children, Stored before node.vertex child := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children
  have childStored := childrenStored child childMember
  apply links vertex ((childStored.entries vertex key inside).2)
  exact childStored.parents_nonnegative (nonnegative node.vertex node.key node.root_entry)
    (fun value weight inside => nonnegative value weight (Node.child_entries childMember inside)) vertex key inside


/-- Reordering roots changes neither heap order nor the rank history inside a tree. -/
theorem Forest.Valid.perm {before after : Forest} (valid : before.Valid)
    (permutation : after.Perm before) : after.Valid := by
  refine ⟨valid.1.of_entries_perm (permutation.flatMap_right Node.entries), ?_, ?_, ?_⟩
  · intro root member
    exact valid.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.2 root (permutation.mem_iff.mp member)

/-- A cyclic choice of the first root does not alter the represented snapshot. -/
theorem Represented.rotate {state : Snapshot} {front back : Forest}
    (represented : Represented state (front ++ back)) : Represented state (back ++ front) := by
  have permutation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have contents := permutation.flatMap_right Node.entries
  refine ⟨represented.valid.perm permutation, ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · simpa only [List.map_append] using (Rings.RingOrEmpty.rotate_append (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.roots))
  · intro root member
    exact represented.stored root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.minimum with ⟨empty, pointer⟩ | ⟨root, member, pointer, least⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, permutation.mem_iff.mpr member, pointer,
        fun other member => least other (permutation.mem_iff.mp member)⟩











theorem Represented.root_parent {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int} (member : vertex ∈ forest.map Node.vertex) :
    state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (represented.stored root inForest).root_parent
















/-- The two parts of a unique forest have disjoint addresses. This is the
    separation fact needed when a root is detached and later linked. -/
theorem Forest.Unique.disjoint {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    ∀ vertex, front.Has vertex → ¬back.Has vertex := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  have separate := (List.nodup_append.mp unique).2.2
  intro vertex inFront inBack
  exact separate vertex ((front.has_iff_map vertex).mp inFront)
    vertex ((back.has_iff_map vertex).mp inBack) rfl







/-- A root-ring vertex cannot be an entry in a separate forest component. -/
theorem Forest.Unique.roots_disjoint {front back : Forest}
    (unique : Forest.Unique (front ++ back)) :
    ∀ vertex ∈ front.map Node.vertex, vertex ∉ back.entries.map Prod.fst := by
  intro vertex member inside
  obtain ⟨root, member, same⟩ := List.mem_map.mp member
  exact unique.disjoint vertex
    ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
    ((back.has_iff_map vertex).mpr inside)



















/-- Whole-heap representation starts consolidation with no detached roots. -/
theorem Represented.split {state : Snapshot} {forest : Forest} (represented : Represented state forest) :
    SplitRepresented state forest [] := by
  refine ⟨?_, ?_, represented.roots, by simp, ?_, ?_, ?_, ?_⟩
  · simpa using represented.valid
  · simpa using represented.stored
  · simpa using represented.nonnegative
  · simpa [Forest.Has] using represented.presence
  · simpa using represented.size
  · rcases represented.minimum with empty | ⟨root, member, pointer, _⟩
    · exact Or.inl empty
    · exact Or.inr ⟨root, member, pointer⟩







theorem Forest.Unique.tail {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    rest.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).2.1























/-- A finite child ring identifies both neighbors as children of the same parent. -/
theorem Stored.child_neighbors {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    state.parents (state.left child.vertex) = parent.vertex ∧
      state.parents (state.right child.vertex) = parent.vertex := by
  cases stored with
  | @node vertex key outer marked childList _ _ _ _ _ _ ring children =>
    have childRing : Rings.Ring state.left state.right (childList.map Node.vertex) := by
      rcases ring with impossible | ring
      · have childMember : child.vertex ∈ childList.map Node.vertex := List.mem_map.mpr ⟨child, member, rfl⟩
        rw [impossible] at childMember
        simp at childMember
      · exact ring
    have neighbors := childRing.neighbors (List.mem_map.mpr ⟨child, member, rfl⟩)
    constructor
    · obtain ⟨previous, inChildren, same⟩ := List.mem_map.mp neighbors.1
      rw [← same]
      exact (children previous inChildren).root_parent
    · obtain ⟨next, inChildren, same⟩ := List.mem_map.mp neighbors.2
      rw [← same]
      exact (children next inChildren).root_parent

/-- Removing a child only changes the pointers of that child's two neighbors. -/
theorem Stored.removeChild_links {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) {vertex : Int}
    (notChild : vertex ≠ child.vertex) (otherParent : state.parents vertex ≠ parent.vertex) :
    (state.removeChild child.vertex parent.vertex).left vertex = state.left vertex ∧
      (state.removeChild child.vertex parent.vertex).right vertex = state.right vertex := by
  obtain ⟨leftParent, rightParent⟩ := stored.child_neighbors member
  have notLeft : vertex ≠ state.left child.vertex := by intro same; subst vertex; exact otherParent leftParent
  have notRight : vertex ≠ state.right child.vertex := by intro same; subst vertex; exact otherParent rightParent
  simp [Snapshot.removeChild, Rings.removeLeft, Rings.removeRight, Rings.write, notChild, notLeft, notRight]















end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



theorem SplitRepresented.pending_parent {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {vertex : Int}
    (member : vertex ∈ pending.map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inPending, same⟩ := List.mem_map.mp member
  exact same ▸ (represented.stored root (by simp [inPending])).root_parent

theorem SplitRepresented.detach_stored {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (root : Node) (member : root ∈ pending ++ detached)
    (cursor : state.minimum ∈ pending.map Node.vertex) :
    Stored state.detachMinimum (-1) root := by
  have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp [empty] at cursor
    · exact ring
  obtain ⟨leftMember, rightMember⟩ := ring.neighbors cursor
  apply (represented.stored root member).frame_roots
  · intro vertex key inside
    exact represented.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, member, inside⟩)
  · intro vertex key inside
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro vertex present nonroot
    have different (other : Int) (inside : other ∈ pending.map Node.vertex) : vertex ≠ other := by
      intro same
      have rootParent := represented.pending_parent inside
      rw [same, rootParent] at nonroot
      omega
    constructor
    · simp only [Snapshot.detachMinimum, Rings.removeLeft, Rings.write]
      rw [if_neg (different _ cursor), if_neg (different _ rightMember)]
    · simp only [Snapshot.detachMinimum, Rings.removeRight, Rings.write]
      rw [if_neg (different _ cursor), if_neg (different _ leftMember)]

/-- Detachment preserves every other detached root's self-ring. -/
theorem SplitRepresented.detach_singletons {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached)
    (cursor : state.minimum ∈ pending.map Node.vertex) (root : Node) (member : root ∈ detached) :
    state.detachMinimum.left root.vertex = root.vertex ∧
      state.detachMinimum.right root.vertex = root.vertex := by
  have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp [empty] at cursor
    · exact ring
  obtain ⟨leftMember, rightMember⟩ := ring.neighbors cursor
  have separate (vertex : Int) (inside : vertex ∈ pending.map Node.vertex) : root.vertex ≠ vertex := by
    intro same
    apply represented.valid.1.roots_disjoint vertex inside
    apply List.mem_map.mpr
    exact ⟨(root.vertex, root.key), List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩, same⟩
  constructor
  · simpa only [Snapshot.detachMinimum, Rings.removeLeft, Rings.write,
      if_neg (separate _ cursor), if_neg (separate _ rightMember)] using
      (represented.detachedRings root member).1
  · simpa only [Snapshot.detachMinimum, Rings.removeRight, Rings.write,
      if_neg (separate _ cursor), if_neg (separate _ leftMember)] using
      (represented.detachedRings root member).2

/-- Moving the displayed cursor root to detached storage strictly shrinks
    the finite pending list without changing contents or tree invariants. -/
theorem SplitRepresented.detach_head {state : Snapshot} {root : Node} {pending detached : Forest}
    (represented : SplitRepresented state (root :: pending) detached) (cursor : state.minimum = root.vertex) :
    SplitRepresented state.detachMinimum pending (root :: detached) := by
  have permutation : (pending ++ root :: detached).Perm ((root :: pending) ++ detached) := by
    simpa only [List.cons_append] using (List.perm_middle (a := root) (l₁ := pending) (l₂ := detached))
  have contents := permutation.flatMap_right Node.entries
  have ring : Rings.Ring state.left state.right (root.vertex :: pending.map Node.vertex) := by
    rcases represented.pendingRing with empty | ring
    · simp at empty
    · exact ring
  have member : state.minimum ∈ (root :: pending).map Node.vertex := by simp [cursor]
  refine ⟨represented.valid.perm permutation, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro other inForest
    exact represented.detach_stored other (permutation.mem_iff.mp inForest) member
  · simpa only [Snapshot.detachMinimum, cursor] using ring.remove_head
  · intro other inDetached
    rcases List.mem_cons.mp inDetached with rfl | old
    · simp [Snapshot.detachMinimum, cursor, Rings.removeLeft, Rings.removeRight]
    · exact represented.detach_singletons member other old
  · intro vertex key inside
    exact represented.nonnegative vertex key (contents.mem_iff.mp inside)
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · cases pending with
    | nil =>
      left
      refine ⟨rfl, ?_⟩
      have self : state.right root.vertex = root.vertex := by
        obtain ⟨last, chain, forward, backward⟩ := ring.open_head
        cases chain with
        | singleton => exact forward
        | cons _ _ _ rest =>
          have impossible := rest.first_mem
          simp at impossible
      simp [Snapshot.detachMinimum, cursor, self]
    | cons first rest =>
      right
      refine ⟨first, by simp, ?_⟩
      have next : state.right root.vertex = first.vertex := by
        obtain ⟨last, chain, forward, backward⟩ := ring.open_head
        cases chain with
        | cons _ edge _ chain =>
          obtain ⟨tail, equal⟩ := chain.head
          simp only [List.map_cons, List.cons.injEq] at equal
          exact edge.trans equal.1.symm
      have different : first.vertex ≠ root.vertex := by
        intro same
        exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
      simp [Snapshot.detachMinimum, cursor, next, different]


























theorem Forest.marks_perm {before after : Forest} (permutation : after.Perm before) :
    after.marks = before.marks := by
  unfold Forest.marks
  exact (permutation.map Node.marks).sum_nat











































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci





















theorem Represented.stored_forest {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : StoredForest state forest :=
  ⟨represented.valid.1, represented.stored, represented.nonnegative⟩















end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci









theorem Represented.boundary {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : RootBoundary state forest := by
  refine ⟨represented.stored_forest, ⟨forest.map Node.vertex, .refl _, represented.roots⟩,
    represented.presence, represented.size, ?_, represented.scratch⟩
  rcases represented.minimum with empty | ⟨root, member, pointer, least⟩
  · exact Or.inl empty
  · right
    refine ⟨root, member, pointer, ?_⟩
    intro other inForest
    rw [pointer, (represented.stored root member).root_key, (represented.stored other inForest).root_key]
    exact least other inForest
































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



/-- Deleting a childless selected root clears precisely its membership and
    leaves a represented pending ring ready for consolidation. -/
theorem Represented.extract_childless {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest))
    (minimum : state.minimum = root.vertex) (childless : root.children = []) :
    SplitRepresented (state.extractRoot root.vertex) rest [] ∧
      (∀ degree, (state.extractRoot root.vertex).table degree < 0) := by
  have detached := represented.split.detach_head minimum
  have entries : root.entries = [(root.vertex,root.key)] := by
    cases root with
    | make vertex key marked children =>
      change children = [] at childless
      simp [childless,Node.entries,Node.vertex,Node.key]
  have rootAbsent : ¬Forest.Has rest root.vertex := by
    have disjoint := represented.valid.1.disjoint (front := [root]) (back := rest)
    exact disjoint root.vertex ⟨root.key, by simp [Forest.entries,entries]⟩
  have unequal (vertex key : Int) (inside : (vertex,key) ∈ rest.entries) : vertex ≠ root.vertex := by
    intro same
    exact rootAbsent (same ▸ ⟨key,inside⟩)
  have valid : rest.Valid := by
    refine ⟨represented.valid.1.tail, ?_, ?_, ?_⟩ <;>
      intro node member
    · exact represented.valid.2.1 node (by simp [member])
    · exact represented.valid.2.2.1 node (by simp [member])
    · exact represented.valid.2.2.2 node (by simp [member])
  refine ⟨⟨by simpa using valid, ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩, represented.scratch⟩
  · intro node member
    simp only [List.append_nil] at member
    apply (detached.stored node (by simp [member])).frame
    · intro vertex key inside
      have different := unequal vertex key (List.mem_flatMap.mpr ⟨node,member,inside⟩)
      constructor <;> simp [Snapshot.extractRoot,Snapshot.detachMinimum,Rings.write,different]
    · intro vertex key inside
      exact ⟨by simp [Snapshot.extractRoot,Snapshot.detachMinimum,minimum],
        by simp [Snapshot.extractRoot,Snapshot.detachMinimum,minimum]⟩
  · simpa only [Snapshot.extractRoot,Snapshot.detachMinimum,minimum] using detached.pendingRing
  · intro vertex key inside
    simp only [List.append_nil] at inside
    obtain ⟨node,member,inside⟩ := List.mem_flatMap.mp inside
    exact represented.nonnegative vertex key
      (List.mem_flatMap.mpr ⟨node,by simp [member],inside⟩)
  · intro vertex
    change Rings.write state.present root.vertex 0 vertex ≠ 0 ↔ Forest.Has (rest ++ []) vertex
    simp only [List.append_nil]
    by_cases same : vertex = root.vertex
    · subst vertex
      simp only [Rings.write_same,ne_self_iff_false,false_iff]
      exact rootAbsent
    · rw [Rings.write,if_neg same,represented.presence]
      simp only [Forest.entries,List.flatMap_cons,entries,List.singleton_append,List.mem_cons,
        Prod.mk.injEq, same,false_and,false_or,Forest.Has]
  · change state.size - 1 = (Forest.entries (rest ++ [])).length
    rw [represented.size]
    simp [Forest.entries,entries]
  · simpa only [Snapshot.extractRoot,Snapshot.detachMinimum,minimum] using detached.cursor

/-- A root boundary, valid forest, and matching physical ring establish the
    full representation in the supplied forest order. -/
theorem RootBoundary.close_with_ring {state : Snapshot} {forest : Forest}
    (boundary : RootBoundary state forest) (valid : forest.Valid)
    (ring : Rings.RingOrEmpty state.left state.right (forest.map Node.vertex)) :
    Represented state forest := by
  refine ⟨valid,ring,boundary.trees.stored,boundary.trees.nonnegative,
    boundary.presence,boundary.size,?_,boundary.scratch⟩
  rcases boundary.minimum with empty | ⟨root,member,pointer,least⟩
  · exact Or.inl empty
  · refine Or.inr ⟨root,member,pointer,?_⟩
    intro other inside
    have bound := least other inside
    rw [pointer,(boundary.trees.stored root member).root_key,
      (boundary.trees.stored other inside).root_key] at bound
    exact bound

/-- Promote the displayed first child; root pruning preserves rank, and heap
    order prevents the strict minimum comparison from changing the cursor. -/
theorem Represented.promote_child {state : Snapshot} {root child : Node} {tail rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex)
    (children : root.children = child :: tail) :
    Represented (state.cut child.vertex root.vertex)
      (root.withChildren tail :: child.withMark false :: rest) ∧
    (state.cut child.vertex root.vertex).minimum = root.vertex := by
  have changed := represented.boundary.cut (context := []) [] tail (child := child) children
  have valid := represented.valid.cut_root_child [] tail children
  have rootStored := represented.stored root (by simp)
  have childMember : child ∈ root.children := by rw [children]; simp
  have childStored : Stored state root.vertex child := by
    cases rootStored with | node _ _ _ _ _ _ _ subtrees => exact subtrees child childMember
  have rootNonnegative : 0 ≤ root.vertex :=
    represented.nonnegative root.vertex root.key (List.mem_flatMap.mpr ⟨root,by simp,root.root_entry⟩)
  have roots : Rings.Ring state.left state.right ((root :: rest).map Node.vertex) := by
    rcases represented.roots with impossible | ring
    · simp at impossible
    · exact ring
  have detachedRing : Rings.Ring (state.removeChild child.vertex root.vertex).left
      (state.removeChild child.vertex root.vertex).right ((root :: rest).map Node.vertex) := by
    have links (vertex : Int) (member : vertex ∈ (root :: rest).map Node.vertex) :
        (state.removeChild child.vertex root.vertex).left vertex = state.left vertex ∧
          (state.removeChild child.vertex root.vertex).right vertex = state.right vertex := by
      have parent := represented.root_parent member
      apply rootStored.removeChild_links childMember
      · intro same
        have otherParent := childStored.root_parent
        rw [same] at parent
        omega
      · omega
    exact roots.frame (fun vertex member => (links vertex member).1)
      (fun vertex member => (links vertex member).2)
  have fresh : child.vertex ∉ (root :: rest).map Node.vertex := by
    intro member
    have parent := represented.root_parent member
    have other := childStored.root_parent
    omega
  have rootLessChild : root.key ≤ child.key := by
    have ordered := represented.valid.2.1 root (by simp)
    cases ordered with | make least _ => exact least child childMember
  have noBetter : ¬state.keys child.vertex < state.keys root.vertex := by
    rw [childStored.root_key,rootStored.root_key]
    omega
  constructor
  · apply changed.close_with_ring valid
    apply Or.inr
    have inserted := detachedRing.insert_after fresh
    change Rings.Ring (state.cut child.vertex root.vertex).left
      (state.cut child.vertex root.vertex).right (root.vertex :: child.vertex :: rest.map Node.vertex)
    simpa only [Snapshot.cut,Snapshot.addRoot,Snapshot.removeChild,minimum,
      if_neg (by omega : ¬root.vertex < 0),List.map_cons] using inserted
  · simp [Snapshot.cut,Snapshot.addRoot,Snapshot.removeChild,minimum,
      show ¬root.vertex < 0 by omega,noBetter]





/-- The child ring supplies the finite promotion count. Newly promoted roots
    appear after the minimum in reverse promotion order. -/
theorem promote_children_finite (children : List Node) :
    ∀ (state : Snapshot) (vertex key : Int) (marked : Bool) (rest : Forest),
      Represented state (Node.make vertex key marked children :: rest) → state.minimum = vertex →
      ∃ after pending,
        PromotionRun vertex state after children.length ∧
        Represented after (Node.make vertex key marked [] :: pending) ∧
        pending.Perm ((children.map (fun child => child.withMark false)).reverse ++ rest) ∧
        after.minimum = vertex := by
  induction children with
  | nil =>
    intro state vertex key marked rest represented minimum
    have read : state.children vertex = -1 := by
      have stored := represented.stored (.make vertex key marked []) (by simp)
      cases stored
      assumption
    exact ⟨state,rest,.done state (by omega),represented,by simp,minimum⟩
  | cons child children ih =>
    intro state vertex key marked rest represented minimum
    have childHead : state.children vertex = child.vertex := by
      have stored := represented.stored (.make vertex key marked (child :: children)) (by simp)
      cases stored
      assumption
    have nonnegative : 0 ≤ child.vertex := represented.nonnegative child.vertex child.key
      (List.mem_flatMap.mpr ⟨.make vertex key marked (child :: children),by simp,
        Node.child_entries (by simp [Node.children]) child.root_entry⟩)
    have promoted := represented.promote_child (child := child) minimum rfl
    obtain ⟨after,pending,run,representedAfter,permutation,minimumAfter⟩ :=
      ih (state.cut child.vertex vertex) vertex key marked (child.withMark false :: rest)
        promoted.1 promoted.2
    refine ⟨after,pending,?_,representedAfter,?_,minimumAfter⟩
    · apply PromotionRun.next (by omega)
      simpa only [Snapshot.promoteChild,childHead] using run
    · simpa [List.reverse_cons,List.append_assoc] using permutation

/-- All promotions keep the selected root's identity and exhaust its children. -/
theorem Represented.promote_all {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex) :
    ∃ after pending,
      PromotionRun root.vertex state after root.degree ∧
      Represented after (root.withChildren [] :: pending) ∧
      pending.Perm (Forest.promoteChildren root rest) ∧
      after.minimum = root.vertex := by
  cases root with
  | make vertex key marked children =>
    obtain ⟨after,pending,run,representedAfter,permutation,minimumAfter⟩ :=
      promote_children_finite children state vertex key marked rest represented minimum
    refine ⟨after,pending,run,representedAfter,?_,minimumAfter⟩
    exact permutation.trans ((List.reverse_perm _).append_right rest)



/-- Deletion removes exactly one minimum entry. The root and mark accounting
    is the interface consumed by the logarithmic consolidation cost proof. -/
theorem Represented.delete_minimum_head {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) (minimum : state.minimum = root.vertex) :
    ∃ after pending,
      DeleteMinimum root.vertex state after root.degree ∧
      SplitRepresented after pending [] ∧
      (∀ degree, after.table degree < 0) ∧
      ((root.vertex,root.key) :: pending.entries).Perm (Forest.entries (root :: rest)) ∧
      pending.length + 1 = (root :: rest).length + root.degree ∧
      pending.marks ≤ Forest.marks (root :: rest) ∧
      root.degree ≤ 2 * (Forest.entries (root :: rest)).length.log2 + 1 := by
  obtain ⟨promoted,pending,run,representedAfter,permutation,minimumAfter⟩ :=
    represented.promote_all minimum
  have extracted := representedAfter.extract_childless minimumAfter rfl
  have contents := permutation.flatMap_right Node.entries
  have accounting := Forest.promoteChildren_accounting root rest
  have marks : Forest.marks pending = (Forest.promoteChildren root rest).marks :=
    Forest.marks_perm permutation
  refine ⟨promoted.extractRoot root.vertex,pending,.finish run,extracted.1,extracted.2,?_,?_,?_,
    represented.root_degree_bound (by simp)⟩
  · rw [Forest.promoteChildren_entries]
    exact contents.cons _
  · have length := permutation.length_eq
    have roots := accounting.1
    change (Forest.promoteChildren root rest).length + 1 = (root :: rest).length + root.degree at roots
    omega
  · rw [marks]
    exact accounting.2

/-- Removing the current minimum works for every physical root rotation.
    The returned pending representation is exactly the input required by
    consolidation, with membership deletion and amortized accounting attached. -/
theorem Represented.delete_minimum {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    ∃ after pending promotions,
      DeleteMinimum state.minimum state after promotions ∧
      SplitRepresented after pending [] ∧
      (∀ degree, after.table degree < 0) ∧
      ((state.minimum,state.keys state.minimum) :: Forest.entries pending).Perm forest.entries ∧
      pending.length + 1 = forest.length + promotions ∧
      Forest.marks pending ≤ forest.marks ∧
      promotions ≤ 2 * forest.entries.length.log2 + 1 := by
  obtain ⟨root,member,pointer,least⟩ := represented.minimum.resolve_left (fun empty => nonempty empty.1)
  have readKey := (represented.stored root member).root_key
  obtain ⟨front,back,located⟩ := List.mem_iff_append.mp member
  have original : Represented state (front ++ root :: back) := located ▸ represented
  have rotated : Represented state (root :: (back ++ front)) := original.rotate
  have permutation : (root :: (back ++ front)).Perm forest := by
    rw [located]
    simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
  have lengths := permutation.length_eq
  have entryLengths := (permutation.flatMap_right Node.entries).length_eq
  have marks := Forest.marks_perm permutation
  obtain ⟨after,pending,run,split,scratch,entries,roots,marked,degree⟩ :=
    rotated.delete_minimum_head pointer
  refine ⟨after,pending,root.degree,?_,split,scratch,?_,?_,?_,?_⟩
  · simpa only [pointer] using run
  · rw [pointer,readKey]
    exact entries.trans (permutation.flatMap_right Node.entries)
  · omega
  · omega
  · simpa only [Forest.entries,entryLengths] using degree



end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {forest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.Represented state forest →
        Ne.{1} forest List.nil.{0} →
          Exists.{1} fun after =>
            Exists.{1} fun pending =>
              Exists.{1} fun promotions =>
                Algo2Lean.Fibonacci.DeleteMinimum state.minimum state after promotions ∧
                  Algo2Lean.Fibonacci.SplitRepresented after pending List.nil.{0} ∧
                    (∀ (degree : Int), LT.lt.{0} (after.table degree) (0 : Int)) ∧
                      List.Perm.{0}
                          (List.cons.{0} (Prod.mk.{0, 0} state.minimum (state.keys state.minimum))
                            pending.entries)
                          forest.entries ∧
                        Eq.{1} (HAdd.hAdd.{0, 0, 0} (List.length.{0} pending) (1 : Nat))
                            (HAdd.hAdd.{0, 0, 0} (List.length.{0} forest) promotions) ∧
                          LE.le.{0} pending.marks forest.marks ∧
                            LE.le.{0} promotions
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (List.length.{0} forest.entries).log2)
                                (1 : Nat)) :=
  Algo2Lean.Fibonacci.Represented.delete_minimum
