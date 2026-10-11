-- Prove2me | solution 1 for Algo2Lean.Fibonacci.RootBoundary.cut
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:42.966698+00:00
-- url     : https://prove2.me/submissions/768e8c15-5d28-4dab-bed6-2424332bb5ae

import Definitions.Def_Algo2LeanLib_FibonacciDecrease


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

/-- Removal preserves the relative order of every survivor, including when
    the removed vertex is not the chosen list head. -/
theorem Ring.remove_from_decomposition {left right : Int → Int} (front back : List Int) (vertex : Int)
    (ring : Ring left right (front ++ vertex :: back)) :
    RingOrEmpty (removeLeft left right vertex) (removeRight left right vertex) (front ++ back) := by
  have rotated : Ring left right (vertex :: (back ++ front)) := ring.rotate_append front (vertex :: back)
  exact rotated.remove_head.rotate_append back front







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

theorem Stored.root_present {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.present node.vertex = 1 := by
  cases stored
  assumption

theorem Stored.root_degree {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.degrees node.vertex = node.degree := by
  cases stored
  assumption























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





/-- Every root's own address is separate from its strict descendants. -/
theorem Node.unique_root {node : Node} (unique : (node.entries.map Prod.fst).Nodup) :
    ¬Forest.Has node.children node.vertex := by
  cases node with
  | make vertex key marked children =>
    simp only [Node.entries, List.map_cons] at unique
    simpa [Node.entries, Node.children, Node.vertex, Forest.has_iff_map, Forest.entries] using
      (List.nodup_cons.mp unique).1



/-- Metadata of a subtree's root may be changed independently from all its
    strict descendants, including its parent pointer and mark. -/
theorem Stored.change_header {before after : Snapshot} {parent newParent : Int} {node : Node}
    (stored : Stored before parent node) (marked : Bool)
    (key : after.keys node.vertex = node.key)
    (readParent : after.parents node.vertex = newParent)
    (mark : after.marks node.vertex = if marked then 1 else 0)
    (degree : after.degrees node.vertex = node.degree)
    (present : after.present node.vertex = 1)
    (head : after.children node.vertex = before.children node.vertex)
    (fields : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      Snapshot.SameFields before after vertex)
    (links : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after newParent (node.withMark marked) := by
  cases stored with
  | @node vertex value parent oldMark children oldKey oldParent oldMarked oldDegree oldPresent oldHead ring subtrees =>
    apply Stored.node key readParent mark degree present
      (by cases children <;> exact head.trans oldHead)
    · rcases ring with empty | ring
      · exact Or.inl empty
      · apply Or.inr
        apply ring.frame
        · intro value member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
          subst value
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).1
        · intro value member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
          subst value
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).2
    · intro child member
      apply (subtrees child member).frame
      · intro vertex key inside
        exact fields vertex key (List.mem_flatMap.mpr ⟨child, member, inside⟩)
      · intro vertex key inside
        exact links vertex key (List.mem_flatMap.mpr ⟨child, member, Node.descendant_entries inside⟩)

/-- The parent address of a strict descendant belongs to this finite tree. -/
theorem Stored.descendant_parent {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries → node.Has (state.parents vertex) := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
    cases child with
    | make childVertex childKey childMark grandchildren =>
      simp only [Node.entries, List.mem_cons, Prod.mk.injEq] at inside
      rcases inside with ⟨rfl, rfl⟩ | deeper
      · have pointer := (subtrees _ childMember).root_parent
        change state.parents value = vertex at pointer
        rw [pointer]
        exact ⟨key, by simp [Node.entries]⟩
      · obtain ⟨parentKey, parentEntry⟩ := ih _ childMember value weight deeper
        exact ⟨parentKey, Node.child_entries childMember parentEntry⟩





















theorem Forest.Unique.head {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    (root.entries.map Prod.fst).Nodup := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).1























theorem Snapshot.removeChild_fields {state : Snapshot} {child parent vertex : Int}
    (notParent : vertex ≠ parent) : SameFields state (state.removeChild child parent) vertex := by
  constructor <;> simp [Snapshot.removeChild, Rings.write, notParent]

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

/-- The child-head update performed by `cut` selects the first remaining child. -/
theorem Rings.Ring.remove_head_pointer {left right : Int → Int} {head child : Int}
    {front back : List Int} (ring : Rings.Ring left right (front ++ child :: back))
    (readHead : head = (front ++ child :: back).head!) :
    (if head = child then if right child = child then -1 else right child else head) =
      match front ++ back with | [] => -1 | first :: _ => first := by
  cases front with
  | nil =>
    have same : head = child := by simpa using! readHead
    rw [same, if_pos rfl]
    cases back with
    | nil => simp [ring.singleton_pointers.2]
    | cons next rest =>
      have pointers := ring.head_next
      have different : next ≠ child := by
        intro same
        exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
      simp [pointers.1, different]
  | cons first rest =>
    have same : head = first := by simpa using! readHead
    have different : first ≠ child := by
      intro same
      exact (List.nodup_cons.mp ring.unique).1 (by simp [same])
    simp [same, different]

/-- Every original child subtree survives sibling removal. Only its root's
    own sibling pointers change; the subtree remains reusable as a unit. -/
theorem Stored.removeChild_subtrees {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (childMember : child ∈ parent.children)
    (unique : (parent.entries.map Prod.fst).Nodup) :
    ∀ old ∈ parent.children, Stored (state.removeChild child.vertex parent.vertex) parent.vertex old := by
  have childrenStored : ∀ old ∈ parent.children, Stored state parent.vertex old := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children
  have different (old : Node) (member : old ∈ parent.children) (vertex key : Int)
      (inside : (vertex, key) ∈ old.entries) : vertex ≠ parent.vertex := by
    intro same
    exact parent.unique_root unique ⟨key, same ▸ List.mem_flatMap.mpr ⟨old, member, inside⟩⟩
  intro old member
  apply (childrenStored old member).frame
  · intro vertex key inside
    exact Snapshot.removeChild_fields (different old member vertex key inside)
  · intro vertex key inside
    have otherParent : state.parents vertex ≠ parent.vertex := by
      obtain ⟨parentKey, parentInside⟩ := (childrenStored old member).descendant_parent vertex key inside
      exact different old member (state.parents vertex) parentKey parentInside
    apply stored.removeChild_links childMember _ otherParent
    intro same
    have pointer := (childrenStored child childMember).root_parent
    exact otherParent (same ▸ pointer)

/-- Removing one selected child realizes list deletion, keeps the removed
    subtree intact, and produces a detached singleton sibling ring. Rank
    restoration (marking or cascading) is deliberately a later operation. -/
theorem Stored.removeChild {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (before after : List Node)
    (located : parent.children = before ++ child :: after)
    (unique : (parent.entries.map Prod.fst).Nodup) :
    Stored (state.removeChild child.vertex parent.vertex) outerParent (parent.withChildren (before ++ after)) ∧
      Stored (state.removeChild child.vertex parent.vertex) parent.vertex child ∧
      (state.removeChild child.vertex parent.vertex).left child.vertex = child.vertex ∧
      (state.removeChild child.vertex parent.vertex).right child.vertex = child.vertex := by
  have childMember : child ∈ parent.children := by rw [located]; simp
  have preserved := stored.removeChild_subtrees childMember unique
  refine ⟨?_, preserved child childMember, ?_, ?_⟩
  · cases stored with
    | @node vertex key outerParent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
      change children = before ++ child :: after at located
      have original : Rings.Ring state.left state.right ((before ++ child :: after).map Node.vertex) := by
        rcases ring with impossible | ring
        · simp only [List.map_eq_nil_iff] at impossible
          rw [located] at impossible
          simp at impossible
        · simpa only [located] using ring
      have readOriginal : state.children vertex = ((before ++ child :: after).map Node.vertex).head! := by
        rw [← located]
        cases children with
        | nil => simp [Node.children] at childMember
        | cons first rest => exact readHead
      change Stored _ outerParent (.make vertex key marked (before ++ after))
      refine Stored.node readKey readParent readMark ?_ readPresent ?_ ?_ ?_
      · simp only [Snapshot.removeChild, Node.vertex, Rings.write_same, readDegree,
          located, List.length_append, List.length_cons, Int.natCast_add, Int.natCast_one]
        omega
      · have result := Rings.Ring.remove_head_pointer
          (front := before.map Node.vertex) (back := after.map Node.vertex)
          (by simpa only [List.map_append, List.map_cons] using original)
          (by simpa only [List.map_append, List.map_cons] using readOriginal)
        change (Rings.write state.children vertex _ vertex) = _
        rw [Rings.write_same]
        cases before <;> cases after <;> simpa using! result
      · have remaining := Rings.Ring.remove_from_decomposition
          (front := before.map Node.vertex) (back := after.map Node.vertex) child.vertex
          (by simpa only [List.map_append, List.map_cons] using original)
        simpa only [Snapshot.removeChild, Node.vertex, List.map_append] using remaining
      · intro old member
        apply preserved old
        change old ∈ children
        rw [located]
        simp only [List.mem_append, List.mem_cons]
        simp only [List.mem_append] at member
        rcases member with first | last
        · exact Or.inl first
        · exact Or.inr (Or.inr last)
  · simp [Snapshot.removeChild, Rings.removeLeft]
  · simp [Snapshot.removeChild, Rings.removeRight]









end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



























/-- Entry accounting can be propagated through any ancestor context. -/
theorem Ancestors.entries_replace {context : List Ancestor} {before after : Node} {removed : List (Int × Int)}
    (contents : before.entries.Perm (after.entries ++ removed)) :
    (Ancestors.plug context before).entries.Perm ((Ancestors.plug context after).entries ++ removed) := by
  induction context generalizing before after with
  | nil => exact contents
  | cons frame rest ih =>
    apply ih
    have first := ((contents.append_right (frame.after.flatMap Node.entries)).append_left
      (frame.before.flatMap Node.entries)).cons (frame.vertex, frame.key)
    have second := (List.perm_append_comm (l₁ := removed) (l₂ := frame.after.flatMap Node.entries)).append_left
      ((frame.vertex, frame.key) :: (frame.before.flatMap Node.entries ++ after.entries))
    simp only [List.append_assoc, List.cons_append] at first second
    exact (by simpa only [Ancestor.plug, Node.entries, List.flatMap_append,
      List.flatMap_cons, List.append_assoc, List.cons_append] using first.trans second)



















end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



/-- Filling a stored hole requires a subtree contract and its address, rather
    than reopening every ancestor's fields and siblings. -/
theorem StoredAncestor.fill {state : Snapshot} {parent address : Int} {frame : Ancestor} {node : Node}
    (ancestor : StoredAncestor state parent frame address) (sameAddress : node.vertex = address)
    (stored : Stored state frame.vertex node) : Stored state parent (frame.plug node) := by
  cases frame with
  | mk vertex key marked before after =>
    refine Stored.node ancestor.key ancestor.parent ancestor.mark ?_ ancestor.present ?_ ?_ ?_
    · simpa [Ancestor.plug, List.length_append, List.length_cons, Nat.add_assoc, Int.natCast_add,
        Int.add_assoc, Int.add_comm, Int.add_left_comm] using ancestor.degree
    · cases before with
      | nil => exact ancestor.childHead.trans sameAddress.symm
      | cons first rest => exact ancestor.childHead
    · apply Or.inr
      simpa only [List.map_append, List.map_cons, sameAddress] using ancestor.ring
    · intro child member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inBefore | rfl | inAfter
      · exact ancestor.siblings child (by simp [inBefore])
      · exact stored
      · exact ancestor.siblings child (by simp [inAfter])

/-- Opening an existing stored ancestor produces its reusable hole contract. -/
theorem Stored.ancestor {state : Snapshot} {parent : Int} {frame : Ancestor} {node : Node}
    (stored : Stored state parent (frame.plug node)) : StoredAncestor state parent frame node.vertex := by
  cases frame with
  | mk vertex key marked before after =>
    cases stored with
    | node readKey readParent readMark degree present head ring children =>
      refine ⟨readKey, readParent, readMark, ?_, present, ?_, ?_, ?_⟩
      · simpa [List.length_append, List.length_cons, Nat.add_assoc, Int.natCast_add,
          Int.add_assoc, Int.add_comm, Int.add_left_comm] using degree
      · cases before <;> exact head
      · rcases ring with impossible | ring
        · simp at impossible
        · simpa only [List.map_append, List.map_cons] using ring
      · intro sibling member
        apply children sibling
        simp only [List.mem_append] at member
        rcases member with inBefore | inAfter
        · simp [inBefore]
        · simp [inAfter]





/-- Any finite stored tree can be opened along a chosen logical ancestor path. -/
theorem Stored.open_context {state : Snapshot} {rootParent : Int} {context : List Ancestor} {node : Node}
    (stored : Stored state rootParent (Ancestors.plug context node)) :
    ∃ focusParent, StoredContext state rootParent context node.vertex focusParent ∧ Stored state focusParent node := by
  induction context generalizing node with
  | nil => exact ⟨rootParent, .nil _, stored⟩
  | cons frame rest ih =>
    obtain ⟨frameParent, surrounding, frameStored⟩ := ih stored
    have focus : Stored state frame.vertex node := by
      cases frameStored with | node _ _ _ _ _ _ _ children => exact children node (by simp)
    exact ⟨frame.vertex, .cons surrounding frameStored.ancestor, focus⟩










/-- The focused subtree and its siblings occupy disjoint addresses. -/
theorem Ancestor.unique_parts {frame : Ancestor} {node : Node}
    (unique : ((frame.plug node).entries.map Prod.fst).Nodup) :
    (node.entries.map Prod.fst).Nodup ∧ ¬node.Has frame.vertex ∧
      (∀ vertex, Forest.Has (frame.before ++ frame.after) vertex → ¬node.Has vertex) := by
  have childrenUnique : Forest.Unique (frame.before ++ node :: frame.after) := by
    have expanded := unique
    simp only [Ancestor.plug, Node.entries, List.map_cons] at expanded
    exact (List.nodup_cons.mp expanded).2
  have reordered : Forest.Unique (node :: (frame.before ++ frame.after)) :=
    childrenUnique.of_entries_perm (List.perm_middle.symm.flatMap_right Node.entries)
  refine ⟨reordered.head, ?_, ?_⟩
  · intro present
    exact (frame.plug node).unique_root unique
      (by obtain ⟨key, member⟩ := present
          exact ⟨key, List.mem_flatMap.mpr ⟨node, by simp [Ancestor.plug, Node.children], member⟩⟩)
  · intro vertex siblings focus
    apply (Forest.Unique.disjoint (front := [node]) (back := frame.before ++ frame.after) reordered) vertex
    · simpa [Forest.Has, Forest.entries] using focus
    · exact siblings

/-- All unrelated stored subtrees survive a local edit. -/
theorem Stored.frame_local {before after : Snapshot} {parent : Int} {focus other : Node}
    (stored : Stored before parent other) (change : Snapshot.LocalChange before after focus)
    (separate : ∀ vertex, other.Has vertex → ¬focus.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ other.entries → 0 ≤ vertex) :
    Stored after parent other := by
  apply stored.frame
  · intro vertex key member
    exact change.fields vertex (separate vertex ⟨key, member⟩)
  · intro vertex key member
    apply change.links vertex
    · obtain ⟨parentKey, parentMember⟩ := stored.descendant_parent vertex key member
      exact nonnegative _ _ parentMember
    · intro inside
      exact separate vertex ⟨key, Node.descendant_entries member⟩
        (by obtain ⟨key, member⟩ := inside; exact ⟨key, Node.descendant_entries member⟩)

/-- A local edit preserves the stored open ancestor around its focused node. -/
theorem StoredAncestor.frame_local {before after : Snapshot} {parent : Int} {frame : Ancestor} {node : Node}
    (ancestor : StoredAncestor before parent frame node.vertex)
    (focusStored : Stored before frame.vertex node)
    (unique : ((frame.plug node).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (frame.plug node).entries → 0 ≤ vertex)
    (change : Snapshot.LocalChange before after node) : StoredAncestor after parent frame node.vertex := by
  have parts := Ancestor.unique_parts unique
  have rootFields := change.fields frame.vertex parts.2.1
  refine ⟨rootFields.key.trans ancestor.key, rootFields.parent.trans ancestor.parent,
    rootFields.mark.trans ancestor.mark, rootFields.degree.trans ancestor.degree,
    rootFields.present.trans ancestor.present, rootFields.child.trans ancestor.childHead, ?_, ?_⟩
  · apply ancestor.ring.frame
    all_goals
      intro vertex member
      have pointer : before.parents vertex = frame.vertex := by
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · obtain ⟨sibling, inBefore, same⟩ := List.mem_map.mp inBefore
          rw [← same]
          exact (ancestor.siblings sibling (by simp [inBefore])).root_parent
        · exact focusStored.root_parent
        · obtain ⟨sibling, inAfter, same⟩ := List.mem_map.mp inAfter
          rw [← same]
          exact (ancestor.siblings sibling (by simp [inAfter])).root_parent
      have bound : 0 ≤ before.parents vertex := by
        rw [pointer]
        exact nonnegative frame.vertex frame.key (by simp [Ancestor.plug, Node.entries])
      have outside : ¬Forest.Has node.children vertex := by
        intro inside
        have inFocus : node.Has vertex := by
          obtain ⟨key, member⟩ := inside
          exact ⟨key, Node.descendant_entries member⟩
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · obtain ⟨sibling, inBefore, same⟩ := List.mem_map.mp inBefore
          exact parts.2.2 vertex ⟨sibling.key, same ▸ List.mem_flatMap.mpr
            ⟨sibling, by simp [inBefore], sibling.root_entry⟩⟩ inFocus
        · exact node.unique_root parts.1 inside
        · obtain ⟨sibling, inAfter, same⟩ := List.mem_map.mp inAfter
          exact parts.2.2 vertex ⟨sibling.key, same ▸ List.mem_flatMap.mpr
            ⟨sibling, by simp [inAfter], sibling.root_entry⟩⟩ inFocus
      first | exact (change.links vertex bound outside).1 | exact (change.links vertex bound outside).2
  · intro sibling member
    apply (ancestor.siblings sibling member).frame_local change
    · intro vertex inside
      exact parts.2.2 vertex (by obtain ⟨key, inside⟩ := inside; exact ⟨key, List.mem_flatMap.mpr ⟨sibling, member, inside⟩⟩)
    · intro vertex key inside
      apply nonnegative vertex key
      apply Node.child_entries _ inside
      simp only [Ancestor.plug, Node.children, List.mem_append, List.mem_cons]
      simp only [List.mem_append] at member
      rcases member with first | last
      · exact Or.inl first
      · exact Or.inr (Or.inr last)

theorem Snapshot.LocalChange.enclose {before after : Snapshot} {node : Node}
    (change : LocalChange before after node) (frame : Ancestor) :
    LocalChange before after (frame.plug node) := by
  constructor
  · intro vertex outside
    apply change.fields vertex
    rintro ⟨key, member⟩
    exact outside ⟨key, Node.child_entries (by simp [Ancestor.plug, Node.children]) member⟩
  · intro vertex nonroot outside
    apply change.links vertex nonroot
    rintro ⟨key, member⟩
    exact outside ⟨key, List.mem_flatMap.mpr
      ⟨node, by simp [Ancestor.plug, Node.children], Node.descendant_entries member⟩⟩

theorem Ancestor.entries_sublist (frame : Ancestor) (node : Node) :
    node.entries.Sublist (frame.plug node).entries := by
  have first := List.sublist_append_left node.entries (frame.after.flatMap Node.entries)
  have second := List.sublist_append_right (frame.before.flatMap Node.entries)
    (node.entries ++ frame.after.flatMap Node.entries)
  simpa only [Ancestor.plug, Node.entries, List.flatMap_append, List.flatMap_cons] using
    (first.trans second).cons (frame.vertex, frame.key)

theorem Ancestors.entries_sublist (context : List Ancestor) (node : Node) :
    node.entries.Sublist (Ancestors.plug context node).entries := by
  induction context generalizing node with
  | nil => exact List.Sublist.refl _
  | cons frame rest ih => exact (frame.entries_sublist node).trans (ih (frame.plug node))



theorem StoredContext.focus_parent {state : Snapshot} {rootParent focusParent address : Int}
    {context : List Ancestor} (surrounding : StoredContext state rootParent context address focusParent) :
    focusParent = Ancestors.parent context rootParent := by cases surrounding <;> rfl

theorem Stored.focus_context {state : Snapshot} {rootParent : Int} {context : List Ancestor} {node : Node}
    (stored : Stored state rootParent (Ancestors.plug context node)) :
    Stored state (Ancestors.parent context rootParent) node := by
  obtain ⟨_, surrounding, focus⟩ := stored.open_context
  simpa only [surrounding.focus_parent] using focus

/-- A local subtree proof lifts through every stored ancestor. Root-list
    rewiring is allowed because ancestor child rings contain only nonroots. -/
theorem Stored.lift_context {before after : Snapshot} {rootParent : Int} {context : List Ancestor}
    {node replacement : Node} (stored : Stored before rootParent (Ancestors.plug context node))
    (unique : ((Ancestors.plug context node).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex)
    (change : Snapshot.LocalChange before after node)
    (sameAddress : replacement.vertex = node.vertex)
    (replacementStored : Stored after (Ancestors.parent context rootParent) replacement) :
    Stored after rootParent (Ancestors.plug context replacement) := by
  induction context generalizing node replacement with
  | nil => exact replacementStored
  | cons frame rest ih =>
    have frameStored := stored.focus_context (context := rest)
    have focusStored : Stored before frame.vertex node := by
      cases frameStored with | node _ _ _ _ _ _ _ children => exact children node (by simp)
    have included := Ancestors.entries_sublist rest (frame.plug node)
    have frameUnique := (included.map Prod.fst).nodup unique
    have frameNonnegative : ∀ vertex key, (vertex, key) ∈ (frame.plug node).entries → 0 ≤ vertex :=
      fun vertex key member => nonnegative vertex key (included.subset member)
    have ancestor := frameStored.ancestor.frame_local focusStored frameUnique frameNonnegative change
    have next := ancestor.fill sameAddress replacementStored
    exact ih stored unique nonnegative (change.enclose frame) rfl next

/-- Ring neighbors are concrete entries in the same finite child list. -/
theorem Stored.child_neighbors_inside {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    Forest.Has parent.children (state.left child.vertex) ∧
      Forest.Has parent.children (state.right child.vertex) := by
  cases stored with
  | @node vertex key outer marked children _ _ _ _ _ _ ring subtrees =>
    have childMember : child.vertex ∈ children.map Node.vertex := List.mem_map.mpr ⟨child, member, rfl⟩
    have actual : Rings.Ring state.left state.right (children.map Node.vertex) := by
      rcases ring with impossible | ring
      · rw [impossible] at childMember; simp at childMember
      · exact ring
    have neighbors := actual.neighbors childMember
    constructor
    · obtain ⟨left, inChildren, same⟩ := List.mem_map.mp neighbors.1
      exact ⟨left.key, same ▸ List.mem_flatMap.mpr ⟨left, inChildren, left.root_entry⟩⟩
    · obtain ⟨right, inChildren, same⟩ := List.mem_map.mp neighbors.2
      exact ⟨right.key, same ▸ List.mem_flatMap.mpr ⟨right, inChildren, right.root_entry⟩⟩

theorem Stored.removeChild_local {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children) :
    Snapshot.LocalChange state (state.removeChild child.vertex parent.vertex) parent := by
  constructor
  · intro vertex outside
    apply Snapshot.removeChild_fields
    intro same
    exact outside (same ▸ ⟨parent.key, parent.root_entry⟩)
  · intro vertex _ outside
    have neighbors := stored.child_neighbors_inside member
    have notChild : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, List.mem_flatMap.mpr ⟨child, member, child.root_entry⟩⟩)
    have notLeft : vertex ≠ state.left child.vertex := fun same => outside (same ▸ neighbors.1)
    have notRight : vertex ≠ state.right child.vertex := fun same => outside (same ▸ neighbors.2)
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



















/-- Metadata at every other vertex is unaffected, even when the inserted tree
    still has an old parent or a mark that the helper will clear. -/
theorem Snapshot.addRoot_other_fields (state : Snapshot) (vertex index : Int)
    (different : index ≠ vertex) : SameFields state (state.addRoot vertex) index := by
  constructor <;> simp [Snapshot.addRoot, Rings.write, different]

/-- The only rewritten ring addresses are the new root, the cursor, and the
    cursor's old successor. -/
theorem Snapshot.addRoot_other_links (state : Snapshot) (vertex index : Int)
    (different : index ≠ vertex)
    (outside : 0 ≤ state.minimum → index ≠ state.minimum ∧ index ≠ state.right state.minimum) :
    (state.addRoot vertex).left index = state.left index ∧
      (state.addRoot vertex).right index = state.right index := by
  by_cases empty : state.minimum < 0
  · simp [Snapshot.addRoot, empty, Rings.write, different]
  · have separate := outside (by omega)
    simp [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
      Rings.write, different, separate.1, separate.2]

end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci





/-- Adding a separate subtree only changes its own header and root pointers. -/
theorem Stored.addRoot_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) : Stored (state.addRoot vertex) parent node := by
  apply stored.frame
  · intro value key member
    apply state.addRoot_other_fields
    intro same
    exact absent (same ▸ ⟨key, member⟩)
  · intro value key member
    have active : node.Has value := ⟨key, Node.descendant_entries member⟩
    have different : value ≠ vertex := fun same => absent (same ▸ active)
    obtain ⟨parentKey, parentInside⟩ := stored.descendant_parent value key member
    have nonroot := nonnegative _ _ parentInside
    apply state.addRoot_other_links _ _ different
    intro existsRoot
    obtain ⟨first, next⟩ := endpoints existsRoot
    constructor
    · intro same; rw [same, first] at nonroot; omega
    · intro same; rw [same, next] at nonroot; omega

/-- A detached subtree becomes an unmarked root with its internal structure intact. -/
theorem Stored.addRoot_self {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) : Stored (state.addRoot node.vertex) (-1) (node.withMark false) := by
  apply stored.change_header (after := state.addRoot node.vertex) false
  · exact stored.root_key
  · simp [Snapshot.addRoot]
  · simp [Snapshot.addRoot]
  · exact stored.root_degree
  · exact stored.root_present
  · rfl
  · intro vertex key member
    apply state.addRoot_other_fields
    intro same
    exact node.unique_root unique ⟨key, same ▸ member⟩
  · intro vertex key member
    have different : vertex ≠ node.vertex := by
      intro same
      exact node.unique_root unique ⟨key, same ▸ member⟩
    obtain ⟨parentKey, parentInside⟩ := stored.descendant_parent vertex key member
    have nonroot := nonnegative _ _ parentInside
    apply state.addRoot_other_links _ _ different
    intro existsRoot
    obtain ⟨first, next⟩ := endpoints existsRoot
    constructor
    · intro same; rw [same, first] at nonroot; omega
    · intro same; rw [same, next] at nonroot; omega

/-- A child-ring removal cannot change the existing root-ring endpoints. -/
theorem Stored.removeChild_endpoints {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children)
    (parentNonnegative : 0 ≤ parent.vertex) (endpoints : state.RootEndpoints) :
    (state.removeChild child.vertex parent.vertex).RootEndpoints := by
  intro nonempty
  change 0 ≤ state.minimum at nonempty
  obtain ⟨head, next⟩ := endpoints nonempty
  have childStored : Stored state parent.vertex child := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children child member
  have different : state.minimum ≠ child.vertex := by
    intro same
    have childParent := childStored.root_parent
    rw [same] at head
    omega
  have unchanged := stored.removeChild_links member different (by omega)
  change state.parents state.minimum = -1 ∧
    state.parents ((state.removeChild child.vertex parent.vertex).right state.minimum) = -1
  rw [unchanged.2]
  exact ⟨head, next⟩



/-- Root insertion after a child removal remains a local edit of its old
    parent's subtree, with the permitted global root-ring rewiring. -/
theorem Stored.cut_local {state : Snapshot} {outerParent : Int} {parent child : Node}
    (stored : Stored state outerParent parent) (member : child ∈ parent.children)
    (parentNonnegative : 0 ≤ parent.vertex) (endpoints : state.RootEndpoints) :
    Snapshot.LocalChange state (state.cut child.vertex parent.vertex) parent := by
  have removal := stored.removeChild_local member
  have removedEndpoints := stored.removeChild_endpoints member parentNonnegative endpoints
  constructor
  · intro vertex outside
    have different : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, Node.child_entries member child.root_entry⟩)
    have first := removal.fields vertex outside
    have second := (state.removeChild child.vertex parent.vertex).addRoot_other_fields child.vertex vertex different
    exact ⟨second.key.trans first.key, second.parent.trans first.parent, second.child.trans first.child,
      second.degree.trans first.degree, second.mark.trans first.mark, second.present.trans first.present⟩
  · intro vertex nonroot outside
    have different : vertex ≠ child.vertex := by
      intro same
      exact outside (same ▸ ⟨child.key, List.mem_flatMap.mpr ⟨child, member, child.root_entry⟩⟩)
    have first := removal.links vertex nonroot outside
    have second := (state.removeChild child.vertex parent.vertex).addRoot_other_links child.vertex vertex different
      (by intro present
          obtain ⟨head, next⟩ := removedEndpoints present
          change state.parents _ = -1 at head next
          constructor
          · intro same; rw [same] at nonroot; omega
          · intro same; rw [same] at nonroot; omega)
    exact ⟨second.1.trans first.1, second.2.trans first.2⟩

/-- Inserting a node which was not a root preserves the root-endpoint invariant. -/
theorem Snapshot.addRoot_endpoints {state : Snapshot} {vertex : Int}
    (endpoints : state.RootEndpoints) (nonroot : 0 ≤ state.parents vertex) :
    (state.addRoot vertex).RootEndpoints := by
  intro _
  by_cases empty : state.minimum < 0
  · simp [Snapshot.addRoot, empty, Rings.write]
  · obtain ⟨head, next⟩ := endpoints (by omega)
    have notHead : vertex ≠ state.minimum := by intro same; rw [same, head] at nonroot; omega
    have notNext : vertex ≠ state.right state.minimum := by intro same; rw [same, next] at nonroot; omega
    by_cases better : state.keys vertex < state.keys state.minimum
    · simp [Snapshot.addRoot, empty, better, Rings.insertAfterRight, Rings.write,
        notHead, Ne.symm notNext, next]
    · simp [Snapshot.addRoot, empty, better, Rings.insertAfterRight, Rings.write,
        Ne.symm notHead, head]

/-- A complete `cut` preserves the finite main tree with the child removed and
    establishes a separate unmarked stored root, at arbitrary ancestor depth. -/
theorem Stored.cut_context {state : Snapshot} {rootParent : Int} {context : List Ancestor}
    {parent child : Node} (stored : Stored state rootParent (Ancestors.plug context parent))
    (unique : ((Ancestors.plug context parent).entries.map Prod.fst).Nodup)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context parent).entries → 0 ≤ vertex)
    (endpoints : state.RootEndpoints) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    Stored (state.cut child.vertex parent.vertex) rootParent
      (Ancestors.plug context (parent.withChildren (before ++ after))) ∧
      Stored (state.cut child.vertex parent.vertex) (-1) (child.withMark false) ∧
      (state.cut child.vertex parent.vertex).RootEndpoints := by
  have parentStored := stored.focus_context
  have included := Ancestors.entries_sublist context parent
  have parentUnique := (included.map Prod.fst).nodup unique
  have parentNonnegative : 0 ≤ parent.vertex := nonnegative parent.vertex parent.key
    (included.subset parent.root_entry)
  have childMember : child ∈ parent.children := by rw [located]; simp
  have removed := parentStored.removeChild before after located parentUnique
  have newUnique := ((parent.cut_entries before after child located).map Prod.fst).nodup_iff.mp parentUnique
  rw [List.map_append] at newUnique
  have parts := List.nodup_append.mp newUnique
  have removedEndpoints := parentStored.removeChild_endpoints childMember parentNonnegative endpoints
  have prunedContained : ∀ vertex key, (vertex, key) ∈ (parent.withChildren (before ++ after)).entries →
      (vertex, key) ∈ parent.entries := by
    intro vertex key member
    exact (parent.cut_entries before after child located).mem_iff.mpr (List.mem_append_left _ member)
  have childContained : ∀ vertex key, (vertex, key) ∈ child.entries → (vertex, key) ∈ parent.entries :=
    fun _ _ member => Node.child_entries childMember member
  have childNow := removed.2.1.addRoot_self parts.2.1
    (fun vertex key member => nonnegative vertex key (included.subset (childContained vertex key member))) removedEndpoints
  have childAbsent : ¬(parent.withChildren (before ++ after)).Has child.vertex := by
    intro inside
    exact parts.2.2 child.vertex ((Node.has_iff_map _ _).mp inside) child.vertex
      ((Node.has_iff_map _ _).mp ⟨child.key, child.root_entry⟩) rfl
  have parentNow := removed.1.addRoot_frame childAbsent
    (fun vertex key member => nonnegative vertex key (included.subset (prunedContained vertex key member))) removedEndpoints
  refine ⟨?_, childNow, ?_⟩
  · exact stored.lift_context unique nonnegative
      (parentStored.cut_local childMember parentNonnegative endpoints) rfl parentNow
  · apply Snapshot.addRoot_endpoints removedEndpoints
    have pointer := removed.2.1.root_parent
    rw [pointer]
    exact parentNonnegative







/-- A complete cut preserves all other roots, including previously promoted
    ancestors accumulated by the same cascading operation. -/
theorem StoredForest.cut {state : Snapshot} {context : List Ancestor} {parent child : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context parent :: rest))
    (endpoints : state.RootEndpoints) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    StoredForest (state.cut child.vertex parent.vertex)
      (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest) ∧
      (state.cut child.vertex parent.vertex).RootEndpoints := by
  let main := Ancestors.plug context parent
  have mainStored := forest.stored main (by simp [main])
  have mainUnique := forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ main.entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨main, by simp [main], member⟩)
  have cut := mainStored.cut_context mainUnique mainNonnegative endpoints before after located
  have parentStored := mainStored.focus_context
  have included := Ancestors.entries_sublist context parent
  have parentNonnegative := mainNonnegative parent.vertex parent.key (included.subset parent.root_entry)
  have member : child ∈ parent.children := by rw [located]; simp
  have change :=  parentStored.cut_local member parentNonnegative endpoints
  have contents := Ancestors.entries_replace (context := context) (parent.cut_entries before after child located)
  refine ⟨⟨?_, ?_, ?_⟩, cut.2.2⟩
  · apply forest.unique.of_entries_perm
    simpa [Forest.entries, List.append_assoc] using (contents.symm.append_right rest.entries)
  · intro root inForest
    rcases List.mem_cons.mp inForest with rfl | tail
    · exact cut.1
    rcases List.mem_cons.mp tail with rfl | old
    · exact cut.2.1
    · apply (forest.stored root (by simp [old])).frame_local change
      · intro vertex rootHas parentHas
        apply (Forest.Unique.disjoint (front := [main]) (back := rest) forest.unique) vertex
        · obtain ⟨key, inside⟩ := parentHas
          exact ⟨key, by simpa [Forest.entries] using included.subset inside⟩
        · obtain ⟨key, inside⟩ := rootHas
          exact ⟨key, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
      · intro vertex key inside
        exact forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, by simp [old], inside⟩)
  · intro vertex key inForest
    have all : (Forest.entries (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest)).Perm
        (Forest.entries (main :: rest)) := by
      simpa [Forest.entries, main, List.append_assoc] using contents.symm.append_right rest.entries
    exact forest.nonnegative vertex key (all.mem_iff.mp inForest)











end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci














theorem Ancestors.root_vertex (context : List Ancestor) {before after : Node}
    (same : before.vertex = after.vertex) :
    (Ancestors.plug context before).vertex = (Ancestors.plug context after).vertex := by
  induction context generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih rfl

theorem RootBoundary.root_parent {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    {vertex : Int} (member : vertex ∈ forest.map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (boundary.trees.stored root inForest).root_parent

theorem RootBoundary.root_nonnegative {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    {vertex : Int} (member : vertex ∈ forest.map Node.vertex) : 0 ≤ vertex := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact boundary.trees.nonnegative _ _ (List.mem_flatMap.mpr ⟨root, inForest, root.root_entry⟩)

theorem RootBoundary.minimum_addresses {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    (nonempty : forest ≠ []) : state.minimum ∈ forest.map Node.vertex ∧
      ∀ vertex ∈ forest.map Node.vertex, state.keys state.minimum ≤ state.keys vertex := by
  obtain ⟨root, member, pointer, least⟩ := boundary.minimum.resolve_left (fun empty => nonempty empty.1)
  constructor
  · rw [pointer]; exact List.mem_map.mpr ⟨root, member, rfl⟩
  · intro vertex member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    rw [← same]
    exact least other member

theorem RootBoundary.root_endpoints {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest) :
    state.RootEndpoints := by
  intro nonnegative
  obtain ⟨root, member, pointer, _⟩ := boundary.minimum.resolve_left (by rintro ⟨_, same⟩; omega)
  have rootMember : state.minimum ∈ forest.map Node.vertex := by rw [pointer]; exact List.mem_map.mpr ⟨root, member, rfl⟩
  obtain ⟨addresses, permutation, ring⟩ := boundary.roots
  have cursor := permutation.mem_iff.mpr rootMember
  have actual : Rings.Ring state.left state.right addresses := by
    rcases ring with empty | ring
    · rw [empty] at cursor; simp at cursor
    · exact ring
  exact ⟨boundary.root_parent rootMember, boundary.root_parent (permutation.mem_iff.mp (actual.neighbors cursor).2)⟩

/-- A physical cut preserves all boundary observations while moving exactly
    one child tree into the root ring. No rank assumption is made mid-cascade. -/
theorem RootBoundary.cut {state : Snapshot} {context : List Ancestor} {parent child : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context parent :: rest))
    (before after : List Node) (located : parent.children = before ++ child :: after) :
    RootBoundary (state.cut child.vertex parent.vertex)
      (Ancestors.plug context (parent.withChildren (before ++ after)) :: child.withMark false :: rest) := by
  let oldRoot := Ancestors.plug context parent
  let newRoot := Ancestors.plug context (parent.withChildren (before ++ after))
  have rootAddress : newRoot.vertex = oldRoot.vertex := Ancestors.root_vertex context rfl
  have contents := (Ancestors.entries_replace (context := context) (parent.cut_entries before after child located)).symm.append_right rest.entries
  have changed := boundary.trees.cut boundary.root_endpoints before after located
  have parentStored := (boundary.trees.stored oldRoot (by simp [oldRoot])).focus_context
  have childMember : child ∈ parent.children := by rw [located]; simp
  have childStored : Stored state parent.vertex child := by
    cases parentStored with | node _ _ _ _ _ _ _ children => exact children child childMember
  have parentNonnegative := boundary.trees.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨oldRoot, by simp [oldRoot], (Ancestors.entries_sublist context parent).subset parent.root_entry⟩)
  have oldMinimum := boundary.minimum_addresses (by simp)
  have minimumNonnegative := boundary.root_nonnegative oldMinimum.1
  have fresh : child.vertex ∉ (oldRoot :: rest).map Node.vertex := by
    intro member
    have rootParent := boundary.root_parent member
    have childParent := childStored.root_parent
    omega
  have afterAddresses : (newRoot :: child.withMark false :: rest).map Node.vertex =
      oldRoot.vertex :: child.vertex :: rest.map Node.vertex := by
    change newRoot.vertex :: child.vertex :: rest.map Node.vertex = oldRoot.vertex :: child.vertex :: rest.map Node.vertex
    rw [rootAddress]
  refine ⟨changed.1, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, roots⟩ := boundary.roots
    have cursor := permutation.mem_iff.mpr oldMinimum.1
    have actual : Rings.Ring state.left state.right addresses := by
      rcases roots with empty | ring
      · rw [empty] at cursor; simp at cursor
      · exact ring
    have removal : Rings.Ring (state.removeChild child.vertex parent.vertex).left
        (state.removeChild child.vertex parent.vertex).right addresses := by
      have pointers (vertex : Int) (member : vertex ∈ addresses) :
          (state.removeChild child.vertex parent.vertex).left vertex = state.left vertex ∧
            (state.removeChild child.vertex parent.vertex).right vertex = state.right vertex := by
        have root := boundary.root_parent (permutation.mem_iff.mp member)
        apply parentStored.removeChild_links childMember
        · intro same
          have childParent := childStored.root_parent
          rw [same] at root
          omega
        · omega
      exact actual.frame (fun vertex member => (pointers vertex member).1)
        (fun vertex member => (pointers vertex member).2)
    obtain ⟨front, back, order⟩ := List.mem_iff_append.mp cursor
    have rotated : Rings.Ring (state.removeChild child.vertex parent.vertex).left
        (state.removeChild child.vertex parent.vertex).right (state.minimum :: (back ++ front)) := by
      rw [order] at removal
      exact removal.rotate_append front (state.minimum :: back)
    have rotatedPermutation : (state.minimum :: (back ++ front)).Perm ((oldRoot :: rest).map Node.vertex) := by
      have rotation : (state.minimum :: (back ++ front)).Perm addresses := by
        rw [order]
        simpa only [List.cons_append] using (List.perm_append_comm (l₁ := state.minimum :: back) (l₂ := front))
      exact rotation.trans permutation
    have freshRotated := fun member => fresh (rotatedPermutation.mem_iff.mp member)
    refine ⟨state.minimum :: child.vertex :: (back ++ front), ?_, Or.inr ?_⟩
    · rw [afterAddresses]
      exact ((List.Perm.swap child.vertex state.minimum (back ++ front)).trans
        (rotatedPermutation.cons child.vertex)).trans (List.Perm.swap oldRoot.vertex child.vertex (rest.map Node.vertex))
    · have inserted := rotated.insert_after freshRotated
      simpa only [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, if_neg (by omega : ¬state.minimum < 0)] using inserted
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence]
    apply exists_congr
    intro key
    simpa [Forest.entries, newRoot, oldRoot, List.append_assoc] using (contents.mem_iff (a := (vertex, key))).symm
  · change state.size = _
    rw [boundary.size]
    exact congrArg Int.ofNat (by simpa [Forest.entries, List.append_assoc] using contents.length_eq.symm)
  · right
    have presentAfter (vertex : Int) (member : vertex ∈ (oldRoot :: rest).map Node.vertex) :
        vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := by
      rw [afterAddresses]
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · simp [member]
    by_cases better : state.keys child.vertex < state.keys state.minimum
    · refine ⟨child.withMark false, by simp, ?_, ?_⟩
      · change (if state.minimum < 0 then child.vertex else if state.keys child.vertex < state.keys state.minimum then child.vertex else state.minimum) = child.vertex
        rw [if_neg (by omega), if_pos better]
      · intro other member
        have memberAddr : other.vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := List.mem_map.mpr ⟨other, member, rfl⟩
        rw [afterAddresses] at memberAddr
        have bound : state.keys child.vertex ≤ state.keys other.vertex := by
          simp only [List.mem_cons] at memberAddr
          rcases memberAddr with same | same | old
          · have oldBound := oldMinimum.2 oldRoot.vertex (by simp [oldRoot])
            rw [same]; omega
          · rw [same]
            exact Int.le_refl _
          · have oldBound := oldMinimum.2 other.vertex (by simp [old]); omega
        simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using bound
    · obtain ⟨root, member, pointer⟩ := List.mem_map.mp (presentAfter state.minimum oldMinimum.1)
      refine ⟨root, member, ?_, ?_⟩
      · simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using pointer.symm
      · intro other member
        have memberAddr : other.vertex ∈ (newRoot :: child.withMark false :: rest).map Node.vertex := List.mem_map.mpr ⟨other, member, rfl⟩
        rw [afterAddresses] at memberAddr
        have bound : state.keys state.minimum ≤ state.keys other.vertex := by
          simp only [List.mem_cons] at memberAddr
          rcases memberAddr with same | same | old
          · exact oldMinimum.2 other.vertex (by simp [same, oldRoot])
          · rw [same]; omega
          · exact oldMinimum.2 other.vertex (by simp [old])
        simpa [Snapshot.cut, Snapshot.addRoot, Snapshot.removeChild, better, Int.not_lt.mpr minimumNonnegative] using bound

















end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {context : List.{0} Algo2Lean.Fibonacci.Ancestor}
      {parent child : Algo2Lean.Fibonacci.Node} {rest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.RootBoundary state
          (List.cons.{0} (Algo2Lean.Fibonacci.Ancestors.plug context parent) rest) →
        ∀ (before after : List.{0} Algo2Lean.Fibonacci.Node),
          Eq.{1} parent.children (HAppend.hAppend.{0, 0, 0} before (List.cons.{0} child after)) →
            Algo2Lean.Fibonacci.RootBoundary (state.cut child.vertex parent.vertex)
              (List.cons.{0}
                (Algo2Lean.Fibonacci.Ancestors.plug context
                  (parent.withChildren (HAppend.hAppend.{0, 0, 0} before after)))
                (List.cons.{0} (child.withMark Bool.false) rest)) :=
  Algo2Lean.Fibonacci.RootBoundary.cut
