-- Prove2me | solution 1 for Algo2Lean.Fibonacci.Represented.decrease
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:53:52.961977+00:00
-- url     : https://prove2.me/submissions/a7ab7d2b-464e-4608-b153-3807c72d9e12

import Definitions.Def_Algo2LeanLib_FibonacciKeyUpdate
import Theorems.Thm_Algo2Lean_Fibonacci_RootBoundary_cut


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



























































/-- Local parent-child order implies that the root is a lower bound for every
    key in its subtree, not merely its immediate children. -/
theorem Node.Ordered.root_minimum {node : Node} (ordered : node.Ordered) :
    ∀ vertex key, (vertex, key) ∈ node.entries → node.key ≤ key := by
  induction ordered with
  | make rootBound valid ih =>
    intro vertex key member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact Int.le_refl _
    · exact Int.le_trans (rootBound child inChildren) (ih child inChildren vertex key inside)

/-- A minimum among the roots is a minimum among all stored vertex/key pairs. -/
theorem Forest.minimum_of_roots {forest : Forest} {minimum : Node}
    (ordered : forest.Ordered) (present : minimum ∈ forest)
    (leastRoot : ∀ root ∈ forest, minimum.key ≤ root.key) :
    (minimum.vertex, minimum.key) ∈ forest.entries ∧
      ∀ vertex key, (vertex, key) ∈ forest.entries → minimum.key ≤ key := by
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨minimum, present, ?_⟩
    cases minimum
    simp [Node.entries, Node.vertex, Node.key]
  · intro vertex key member
    obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
    exact Int.le_trans (leastRoot root inForest) ((ordered root inForest).root_minimum vertex key inside)

/-- Changes to a root's mark do not alter its internal heap order or rank history. -/
theorem Node.Ordered.withMark {node : Node} (ordered : node.Ordered) (marked : Bool) :
    (node.withMark marked).Ordered := by
  cases ordered with
  | make bounds children => exact .make bounds children

theorem Node.Ranked.withMark {node : Node} (ranked : node.Ranked) (marked : Bool) :
    (node.withMark marked).Ranked := by
  cases ranked with
  | make ordered children => exact .make ordered children

/-- Decreasing a root key preserves all comparisons below that root. -/
theorem Node.Ordered.decrease_key {node : Node} (ordered : node.Ordered) (key : Int)
    (decreased : key ≤ node.key) : (node.withKey key).Ordered := by
  cases ordered with
  | make bounds children =>
    exact .make (fun child member => Int.le_trans decreased (bounds child member)) children

theorem Node.Ranked.withKey {node : Node} (ranked : node.Ranked) (key : Int) :
    (node.withKey key).Ranked := by
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

/-- Cutting an unmarked child once and marking it preserves the capacity its
    parent used in the rank-history invariant. This is why one loss is allowed. -/
theorem Node.first_loss_capacity (node : Node) (kept : List Node)
    (unmarked : node.marked = false) (oneLoss : kept.length + 1 = node.degree) :
    ((node.withChildren kept).withMark true).rankCapacity = node.rankCapacity := by
  cases node with
  | make vertex key marked children =>
    change marked = false at unmarked
    subst marked
    simpa only [Node.rankCapacity, Node.withChildren, Node.withMark, Node.degree, Node.children,
      Node.marked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using oneLoss

/-- Replacing a child by an equal-or-larger capacity preserves every history
    clause. Earlier siblings see the same number of older children. -/
theorem ChildOrder.replace (earlier suffix : List Node) (before after : Node)
    (ordered : ChildOrder (earlier ++ before :: suffix))
    (capacity : before.rankCapacity ≤ after.rankCapacity) :
    ChildOrder (earlier ++ after :: suffix) := by
  induction earlier with
  | nil => exact ⟨Nat.le_trans ordered.1 capacity, ordered.2⟩
  | cons child earlier ih =>
    exact ⟨by simpa using ordered.1, ih ordered.2⟩

/-- A child replacement with unchanged degree capacity can propagate up a
    tree without weakening any ancestor's rank-history invariant. -/
theorem Node.Ranked.replace_child {parent child replacement : Node}
    (ranked : parent.Ranked) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later)
    (replacementRanked : replacement.Ranked)
    (capacity : child.rankCapacity ≤ replacement.rankCapacity) :
    (parent.withChildren (earlier ++ replacement :: later)).Ranked := by
  cases ranked with
  | make ordered children =>
    simp only [Node.children] at located
    apply Node.Ranked.make
    · rw [located] at ordered
      exact ordered.replace earlier later child replacement capacity
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply children
        rw [located]
        simp [old]
      · exact replacementRanked
      · apply children
        rw [located]
        simp [old]

theorem Node.Ordered.replace_child {parent child replacement : Node}
    (ordered : parent.Ordered) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later)
    (replacementOrdered : replacement.Ordered) (sameKey : replacement.key = child.key) :
    (parent.withChildren (earlier ++ replacement :: later)).Ordered := by
  cases ordered with
  | @make vertex key marked originalChildren bounds children =>
    simp only [Node.children] at located
    have childMember : child ∈ originalChildren := by rw [located]; simp
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply bounds; rw [located]; simp [old]
      · rw [sameKey]; exact bounds child childMember
      · apply bounds; rw [located]; simp [old]
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply children; rw [located]; simp [old]
      · exact replacementOrdered
      · apply children; rw [located]; simp [old]







/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique



















theorem Node.clear_mark_count (node : Node) :
    (node.withMark false).marks + (if node.marked then 1 else 0) = node.marks := by
  cases node
  simp [Node.withMark, Node.marks, Node.vertex, Node.key, Node.children, Node.marked, Nat.add_comm]







theorem Node.cut_marks (parent child : Node) (earlier later : List Node)
    (located : parent.children = earlier ++ child :: later) :
    (parent.withChildren (earlier ++ later)).marks + child.marks = parent.marks := by
  cases parent with
  | make vertex key marked children =>
    change children = earlier ++ child :: later at located
    subst children
    simp [Node.withChildren, Node.vertex, Node.key, Node.marked,
      Node.marks, List.map_append, List.sum_append_nat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

















/-- Decreasing the key of a root needs no cut and preserves the forest invariants. -/
theorem Forest.Valid.decrease_root {root : Node} {rest : Forest}
    (valid : Forest.Valid (root :: rest)) (key : Int) (decreased : key ≤ root.key) :
    Forest.Valid (root.withKey key :: rest) := by
  have rootMember : root ∈ root :: rest := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have unique := valid.1
    simpa [Forest.Unique, Forest.entries] using unique
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.1 root rootMember).decrease_key key decreased
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.2.1 root rootMember).withKey key
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact valid.2.2.2 root rootMember
    · exact valid.2.2.2 node (by simp [old])

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





/-- A displayed list head is the first endpoint of its open chain. -/
theorem Ring.open_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) :
    ∃ last, Chain left right head (head :: tail) last ∧ right last = head ∧ left head = last := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨rest, same⟩ := chain.head
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  exact ⟨last, chain, forward, backward⟩

















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



theorem Represented.entry {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (member : (vertex, key) ∈ forest.entries) :
    state.keys vertex = key ∧ state.present vertex = 1 := by
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  exact (represented.stored root inForest).entries vertex key inside

theorem Represented.present_nonnegative {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int}
    (present : state.present vertex ≠ 0) : 0 ≤ vertex := by
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  exact represented.nonnegative vertex key member

/-- The public minimum pointer identifies a present globally minimum key. -/
theorem Represented.minimum_key {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    0 ≤ state.minimum ∧ state.present state.minimum = 1 ∧
      ∀ vertex, state.present vertex ≠ 0 → state.keys state.minimum ≤ state.keys vertex := by
  rcases represented.minimum with ⟨empty, _⟩ | ⟨root, inForest, pointer, least⟩
  · exact False.elim (nonempty empty)
  obtain ⟨rootEntry, minimum⟩ := Forest.minimum_of_roots represented.valid.2.1 inForest least
  have rootValues := represented.entry rootEntry
  rw [pointer]
  refine ⟨represented.nonnegative _ _ rootEntry, rootValues.2, ?_⟩
  intro vertex present
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  rw [rootValues.1, (represented.entry member).1]
  exact minimum vertex key member













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





































/-- Marking a node preserves its entire stored subtree. Unique addresses make
    the single changed cell separate from every strict descendant. -/
theorem Stored.setMark {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup) (marked : Bool) :
    Stored (state.setMark node.vertex marked) parent (node.withMark marked) := by
  apply stored.change_header (after := state.setMark node.vertex marked) marked stored.root_key stored.root_parent
  · simp [Snapshot.setMark]
  · exact stored.root_degree
  · exact stored.root_present
  · rfl
  · intro vertex key member
    have different : vertex ≠ node.vertex := by
      intro same
      exact node.unique_root unique ⟨key, same ▸ member⟩
    constructor <;> simp [Snapshot.setMark, Rings.write, different]
  · intro vertex key member
    exact ⟨rfl, rfl⟩

/-- A mark update can be framed through any disjoint stored subtree. -/
theorem Stored.setMark_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex) (marked : Bool) :
    Stored (state.setMark vertex marked) parent node := by
  apply stored.frame
  · intro value key member
    have different : value ≠ vertex := by intro same; exact absent (same ▸ ⟨key, member⟩)
    constructor <;> simp [Snapshot.setMark, Rings.write, different]
  · intro value key member
    exact ⟨rfl, rfl⟩



end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci









theorem Ancestor.focus_ranked {frame : Ancestor} {node : Node}
    (ranked : (frame.plug node).Ranked) : node.Ranked := by
  cases ranked with
  | make history children => exact children node (by simp)

theorem Ancestor.focus_ordered {frame : Ancestor} {node : Node}
    (ordered : (frame.plug node).Ordered) : node.Ordered := by
  cases ordered with
  | make bounds children => exact children node (by simp)

theorem Ancestors.focus_ranked {context : List Ancestor} {node : Node}
    (ranked : (Ancestors.plug context node).Ranked) : node.Ranked := by
  induction context generalizing node with
  | nil => exact ranked
  | cons frame rest ih => exact Ancestor.focus_ranked (ih ranked)

theorem Ancestors.focus_ordered {context : List Ancestor} {node : Node}
    (ordered : (Ancestors.plug context node).Ordered) : node.Ordered := by
  induction context generalizing node with
  | nil => exact ordered
  | cons frame rest ih => exact Ancestor.focus_ordered (ih ordered)

/-- An unchanged address/key with at least the old rank capacity can replace
    the focused subtree without changing any ancestor's rank-history clause. -/
theorem Ancestors.replace_ranked {context : List Ancestor} {before after : Node}
    (ranked : (Ancestors.plug context before).Ranked) (replacement : after.Ranked)
    (capacity : before.rankCapacity ≤ after.rankCapacity) : (Ancestors.plug context after).Ranked := by
  induction context generalizing before after with
  | nil => exact replacement
  | cons frame rest ih =>
    have old := Ancestors.focus_ranked (context := rest) ranked
    have next : (frame.plug after).Ranked :=
      old.replace_child frame.before frame.after rfl replacement capacity
    apply ih ranked next
    simp [Ancestor.plug, Node.rankCapacity, Node.degree, Node.children, Node.marked]

theorem Ancestors.replace_ordered {context : List Ancestor} {before after : Node}
    (ordered : (Ancestors.plug context before).Ordered) (replacement : after.Ordered)
    (sameKey : after.key = before.key) : (Ancestors.plug context after).Ordered := by
  induction context generalizing before after with
  | nil => exact replacement
  | cons frame rest ih =>
    have old := Ancestors.focus_ordered (context := rest) ordered
    have next : (frame.plug after).Ordered :=
      old.replace_child frame.before frame.after rfl replacement sameKey
    apply ih ordered next
    rfl

theorem Ancestors.plug_mark {context : List Ancestor} {before after : Node}
    (same : before.marked = after.marked) : (Ancestors.plug context before).marked = (Ancestors.plug context after).marked := by
  induction context generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih rfl

theorem Ancestors.nonempty_mark (frame : Ancestor) (rest : List Ancestor) (before after : Node) :
    (Ancestors.plug (frame :: rest) before).marked = (Ancestors.plug (frame :: rest) after).marked := by
  exact Ancestors.plug_mark (context := rest) rfl

/-- Cascade repair restores heap order and the stronger marked-child rank
    history, for any number of consecutively marked ancestors. -/
theorem cascadeForest_invariants (context : List Ancestor) (node : Node) (kept : List Node)
    (remaining : kept.Sublist node.children) (oneLoss : kept.length + 1 = node.degree)
    (ordered : (Ancestors.plug context node).Ordered) (ranked : (Ancestors.plug context node).Ranked)
    (rootUnmarked : (Ancestors.plug context node).marked = false) :
    (cascadeForest node kept context).Ordered ∧ (cascadeForest node kept context).Ranked ∧
      (cascadeForest node kept context).RootsUnmarked := by
  induction context generalizing node kept with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact ordered.prune kept remaining
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact ranked.prune kept remaining
    · intro root member
      have same := List.mem_singleton.mp member
      subst root
      exact rootUnmarked
  | cons frame rest ih =>
    have nodeOrdered := Ancestors.focus_ordered ordered
    have nodeRanked := Ancestors.focus_ranked ranked
    by_cases marked : node.marked = true
    · have retained : (frame.before ++ frame.after).Sublist (frame.plug node).children :=
        (List.Sublist.refl frame.before).append ((List.Sublist.refl frame.after).cons node)
      have one : (frame.before ++ frame.after).length + 1 = (frame.plug node).degree := by
        simp [Ancestor.plug, Node.degree, Node.children, Nat.add_assoc]
      have tail := ih (frame.plug node) (frame.before ++ frame.after) retained one ordered ranked rootUnmarked
      refine ⟨?_, ?_, ?_⟩
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · exact (nodeOrdered.prune kept remaining).withMark false
        · exact tail.1 root old
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · exact (nodeRanked.prune kept remaining).withMark false
        · exact tail.2.1 root old
      · intro root member
        simp only [cascadeForest, marked, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | old
        · rfl
        · exact tail.2.2 root old
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have capacity := node.first_loss_capacity kept unmarked oneLoss
      have newOrdered := Ancestors.replace_ordered ordered ((nodeOrdered.prune kept remaining).withMark true) rfl
      have newRanked := Ancestors.replace_ranked ranked ((nodeRanked.prune kept remaining).withMark true)
        (Nat.le_of_eq capacity.symm)
      refine ⟨?_, ?_, ?_⟩
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact newOrdered
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact newRanked
      · intro root member
        simp [cascadeForest, unmarked] at member
        subst root
        exact (Ancestors.nonempty_mark frame rest _ node).trans rootUnmarked

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

/-- Cascade removes exactly the initially cut entries. Promoting marked
    ancestors neither loses nor duplicates any remaining vertex or key. -/
theorem cascadeForest_entries (context : List Ancestor) (node : Node) (kept : List Node)
    (removed : List (Int × Int))
    (contents : node.entries.Perm ((node.withChildren kept).entries ++ removed)) :
    (Ancestors.plug context node).entries.Perm ((cascadeForest node kept context).entries ++ removed) := by
  induction context generalizing node kept removed with
  | nil => simpa [cascadeForest, Forest.entries] using! contents
  | cons frame rest ih =>
    by_cases marked : node.marked = true
    · have cut := (frame.plug node).cut_entries frame.before frame.after node rfl
      have recursive := ih (frame.plug node) (frame.before ++ frame.after) node.entries cut
      have replace := contents.append_left (cascadeForest (frame.plug node) (frame.before ++ frame.after) rest).entries
      have reorder := (List.perm_append_comm
          (l₁ := (cascadeForest (frame.plug node) (frame.before ++ frame.after) rest).entries)
          (l₂ := (node.withChildren kept).entries)).append_right removed
      simp only [List.append_assoc] at replace reorder
      apply recursive.trans
      simpa only [cascadeForest, marked, ↓reduceIte, Forest.entries, List.flatMap_cons,
        Node.entries_withMark, List.append_assoc] using replace.trans reorder
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have changed : node.entries.Perm (((node.withChildren kept).withMark true).entries ++ removed) := by
        simpa only [Node.entries_withMark] using contents
      have lifted := Ancestors.entries_replace (context := frame :: rest) changed
      simpa [cascadeForest, unmarked, Forest.entries] using lifted

/-- Cutting an arbitrary descendant and repairing its ancestors preserves the
    complete finite-forest invariant. The newly cut node is a separate root. -/
theorem cascadeForest_valid (context : List Ancestor) (node child : Node) (before after : List Node)
    (located : node.children = before ++ child :: after)
    (valid : Forest.Valid [Ancestors.plug context node]) :
    Forest.Valid (child.withMark false :: cascadeForest node (before ++ after) context) := by
  have rootMember : Ancestors.plug context node ∈ [Ancestors.plug context node] := by simp
  have ordered := valid.2.1 _ rootMember
  have ranked := valid.2.2.1 _ rootMember
  have unmarked := valid.2.2.2 _ rootMember
  have nodeOrdered := Ancestors.focus_ordered ordered
  have nodeRanked := Ancestors.focus_ranked ranked
  have member : child ∈ node.children := by rw [located]; simp
  have childOrdered : child.Ordered := by cases nodeOrdered with | make _ children => exact children child member
  have childRanked : child.Ranked := by cases nodeRanked with | make _ children => exact children child member
  have remaining : (before ++ after).Sublist node.children := by
    rw [located]
    exact (List.Sublist.refl before).append ((List.Sublist.refl after).cons child)
  have oneLoss : (before ++ after).length + 1 = node.degree := by
    unfold Node.degree
    rw [located]
    simp [Nat.add_assoc]
  have repaired := cascadeForest_invariants context node (before ++ after) remaining oneLoss ordered ranked unmarked
  have contents := cascadeForest_entries context node (before ++ after) child.entries
    (node.cut_entries before after child located)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply valid.1.of_entries_perm
    have permutation := List.perm_append_comm.trans contents.symm
    simpa [Forest.entries] using permutation
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact childOrdered.withMark false
    · exact repaired.1 root old
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact childRanked.withMark false
    · exact repaired.2.1 root old
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · rfl
    · exact repaired.2.2 root old





theorem Ancestor.plug_marks (frame : Ancestor) (node : Node) :
    (frame.plug node).marks = node.marks + frame.marks := by
  simp [Ancestor.plug, Node.marks, Ancestor.marks, Forest.marks,
    List.sum_append_nat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Ancestors.plug_marks (context : List Ancestor) (node : Node) :
    (Ancestors.plug context node).marks = node.marks + Ancestors.marks context := by
  induction context generalizing node with
  | nil => simp [Ancestors.plug, Ancestors.marks]
  | cons frame rest ih => simp [Ancestors.plug, ih, Ancestor.plug_marks, Ancestors.marks, Nat.add_assoc]



/-- Concrete ancestor repair realizes the potential-accounting cascade,
    including arbitrary roots and marks elsewhere in the forest. -/
theorem cascadeForest_accounting (context : List Ancestor) (node : Node) (kept : List Node)
    (otherRoots otherMarks : Nat) :
    Cascade ⟨1 + otherRoots, (Ancestors.plug context (node.withChildren kept)).marks + otherMarks⟩
      ⟨(cascadeForest node kept context).length + otherRoots,
        (cascadeForest node kept context).marks + otherMarks⟩ (cascadeCuts node context) := by
  induction context generalizing node kept otherRoots otherMarks with
  | nil => simpa [cascadeForest, cascadeCuts, Ancestors.plug, Forest.marks] using (Cascade.root
      (Counts.mk (1 + otherRoots) ((node.withChildren kept).marks + otherMarks)))
  | cons frame rest ih =>
    by_cases marked : node.marked = true
    · let detached := (node.withChildren kept).withMark false
      have prunedMarked : (node.withChildren kept).marked = true := marked
      have clearing : detached.marks + 1 = (node.withChildren kept).marks := by
        simpa only [detached, prunedMarked, ↓reduceIte] using
          (node.withChildren kept).clear_mark_count
      have parentMarks : ((frame.plug node).withChildren (frame.before ++ frame.after)).marks = frame.marks := by
        simp [Ancestor.plug, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.marks,
          Ancestor.marks, Forest.marks, List.sum_append_nat, Nat.add_assoc]
      have next := ih (frame.plug node) (frame.before ++ frame.after) (otherRoots + 1)
        (detached.marks + otherMarks)
      simp only [Ancestors.plug_marks, parentMarks] at next
      have nextNormalized : Cascade
          ⟨(1 + otherRoots) + 1, detached.marks + frame.marks + Ancestors.marks rest + otherMarks⟩
          ⟨(cascadeForest node kept (frame :: rest)).length + otherRoots,
            (cascadeForest node kept (frame :: rest)).marks + otherMarks⟩
          (cascadeCuts (frame.plug node) rest) := by
        simpa only [cascadeForest, marked, ↓reduceIte, List.length_cons, Forest.marks,
          List.map_cons, List.sum_cons, detached, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
      have result := Cascade.cut nextNormalized
      simpa only [cascadeCuts, marked, ↓reduceIte, Ancestors.plug_marks, Ancestors.marks,
        List.map_cons, List.sum_cons, ← clearing, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      have changed : ((node.withChildren kept).withMark true).marks = (node.withChildren kept).marks + 1 := by
        cases node
        simp_all [Node.withChildren, Node.withMark, Node.marks, Node.vertex, Node.key, Node.marked, Node.children, Nat.add_comm]
      simpa [cascadeForest, cascadeCuts, unmarked, Forest.marks, Ancestors.plug_marks, changed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Cascade.mark (1 + otherRoots) ((Ancestors.plug (frame :: rest) (node.withChildren kept)).marks + otherMarks)

/-- Full cut-and-cascade accounting agrees with the potential model, including
    marks in the cut subtree and any untouched roots. -/
theorem cascadeForest_decrease_accounting (context : List Ancestor) (node child : Node)
    (before after : List Node) (rest : Forest)
    (located : node.children = before ++ child :: after) :
    Decrease (Forest.counts (Ancestors.plug context node :: rest))
      (Forest.counts (child.withMark false :: cascadeForest node (before ++ after) context ++ rest))
      (cascadeCuts node context + 1) := by
  let final := Forest.counts (child.withMark false :: cascadeForest node (before ++ after) context ++ rest)
  let remainingMarks := (Ancestors.plug context (node.withChildren (before ++ after))).marks +
    (child.withMark false).marks + rest.marks
  have cascade : Cascade ⟨rest.length + 2, remainingMarks⟩ final (cascadeCuts node context) := by
    have result := cascadeForest_accounting context node (before ++ after) (rest.length + 1)
      ((child.withMark false).marks + rest.marks)
    simpa only [final, remainingMarks, Forest.counts, List.length_cons, List.length_append,
      Forest.marks, List.map_cons, List.map_append, List.sum_cons, List.sum_append_nat,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
  have originalMarks : (Ancestors.plug context node).marks + rest.marks =
      remainingMarks + (if child.marked then 1 else 0) := by
    have cut := node.cut_marks child before after located
    have clear := child.clear_mark_count
    simp only [remainingMarks, Ancestors.plug_marks]
    omega
  have originalCounts : Forest.counts (Ancestors.plug context node :: rest) =
      ⟨rest.length + 1, remainingMarks + (if child.marked then 1 else 0)⟩ := by
    simp only [Forest.counts, List.length_cons, Forest.marks, List.map_cons, List.sum_cons]
    simp only [Forest.marks] at originalMarks
    rw [originalMarks]
  rw [originalCounts]
  change Decrease _ final _
  cases marked : child.marked with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Decrease.unmarked cascade
  | true =>
    simp only [↓reduceIte]
    exact Decrease.marked cascade

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

theorem Ancestors.plug_append (first second : List Ancestor) (node : Node) :
    Ancestors.plug (first ++ second) node = Ancestors.plug second (Ancestors.plug first node) := by
  induction first generalizing node with
  | nil => rfl
  | cons frame rest ih => exact ih (frame.plug node)

/-- Every stored entry has a finite path of ancestors and a complete local
    subtree. This supplies a proof context for arbitrary active vertex handles. -/
theorem Stored.locate {state : Snapshot} {parent : Int} {tree : Node}
    (stored : Stored state parent tree) :
    ∀ vertex key, (vertex, key) ∈ tree.entries →
      ∃ context node, tree = Ancestors.plug context node ∧ node.vertex = vertex ∧ node.key = key := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact ⟨[], .make value weight marked children, rfl, rfl, rfl⟩
    · obtain ⟨context, focus, located, address, valueKey⟩ := ih child inChildren value weight inside
      obtain ⟨before, after, childrenEq⟩ := List.mem_iff_append.mp inChildren
      let frame : Ancestor := ⟨vertex, key, marked, before, after⟩
      refine ⟨context ++ [frame], focus, ?_, address, valueKey⟩
      simp only [Ancestors.plug_append, Ancestors.plug, Ancestor.plug, frame, childrenEq, ← located]






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





/-- Marking the focused node preserves a preceding local-change guarantee. -/
theorem Snapshot.LocalChange.setMark {before after : Snapshot} {node : Node}
    (change : LocalChange before after node) (marked : Bool) :
    LocalChange before (after.setMark node.vertex marked) node := by
  constructor
  · intro vertex outside
    have different : vertex ≠ node.vertex := by intro same; exact outside (same ▸ ⟨node.key, node.root_entry⟩)
    have fields := change.fields vertex outside
    exact ⟨fields.key, fields.parent, fields.child, fields.degree,
      by simpa [Snapshot.setMark, Rings.write, different] using fields.mark, fields.present⟩
  · exact change.links



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

theorem StoredForest.perm {state : Snapshot} {before after : Forest}
    (stored : StoredForest state before) (permutation : after.Perm before) : StoredForest state after := by
  have entries := permutation.flatMap_right Node.entries
  exact ⟨stored.unique.of_entries_perm entries,
    fun root member => stored.stored root (permutation.mem_iff.mp member),
    fun vertex key member => stored.nonnegative vertex key (entries.mem_iff.mp member)⟩



theorem Stored.root_mark {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.marks node.vertex = if node.marked then 1 else 0 := by
  cases stored
  assumption

theorem StoredForest.mark {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context node :: rest)) (marked : Bool) :
    StoredForest (state.setMark node.vertex marked) (Ancestors.plug context (node.withMark marked) :: rest) := by
  have mainStored := forest.stored (Ancestors.plug context node) (by simp)
  have included := Ancestors.entries_sublist context node
  have nodeUnique := (included.map Prod.fst).nodup forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨_, by simp, member⟩)
  have change : Snapshot.LocalChange state (state.setMark node.vertex marked) node := by
    apply Snapshot.LocalChange.setMark (after := state)
    constructor
    · intro vertex _; constructor <;> rfl
    · intro vertex _ _; exact ⟨rfl, rfl⟩
  have contents : (Ancestors.plug context (node.withMark marked)).entries.Perm
      (Ancestors.plug context node).entries := by
    have lifted := Ancestors.entries_replace (context := context) (before := node.withMark marked)
      (after := node) (removed := []) (by simp)
    simpa using lifted
  refine ⟨forest.unique.of_entries_perm ?_, ?_, ?_⟩
  · simpa [Forest.entries] using contents.append_right rest.entries
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact mainStored.lift_context forest.unique.head mainNonnegative change rfl
        (mainStored.focus_context.setMark nodeUnique marked)
    · apply (forest.stored root (by simp [old])).setMark_frame
      intro inside
      apply (Forest.Unique.disjoint (front := [Ancestors.plug context node]) (back := rest) forest.unique) node.vertex
      · exact ⟨node.key, by simpa [Forest.entries] using included.subset node.root_entry⟩
      · obtain ⟨key, inside⟩ := inside
        exact ⟨key, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
  · intro vertex key member
    have all := contents.append_right rest.entries
    exact forest.nonnegative vertex key (all.mem_iff.mp member)







end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci





/-- A permutation of mapped addresses can be realized by reordering the
    original nodes. No globally injective address function is required. -/
theorem lift_map_permutation {α β : Type} (f : α → β) {nodes : List α} {values : List β}
    (permutation : values.Perm (nodes.map f)) :
    ∃ ordered : List α, ordered.Perm nodes ∧ ordered.map f = values := by
  induction values generalizing nodes with
  | nil =>
    have empty := permutation.length_eq
    simp only [List.length_nil, List.length_map, Eq.comm, List.length_eq_zero_iff] at empty
    subst nodes
    exact ⟨[], List.Perm.refl [], rfl⟩
  | cons value tail ih =>
    have member : value ∈ nodes.map f := permutation.mem_iff.mp (by simp)
    obtain ⟨node, inNodes, address⟩ := List.mem_map.mp member
    obtain ⟨before, after, located⟩ := List.mem_iff_append.mp inNodes
    subst nodes
    have move : (before ++ node :: after).Perm (node :: (before ++ after)) := List.perm_middle
    have rest : tail.Perm ((before ++ after).map f) := by
      have moved := permutation.trans (move.map f)
      rw [List.map_cons, address] at moved
      exact moved.cons_inv
    obtain ⟨ordered, order, mapped⟩ := ih rest
    exact ⟨node :: ordered, (order.cons node).trans move.symm, by simp [mapped, address]⟩



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

/-- Restoring semantic invariants turns the temporary boundary relation back
    into the original public representation, with a harmless root permutation. -/
theorem RootBoundary.close {state : Snapshot} {forest : Forest} (boundary : RootBoundary state forest)
    (valid : forest.Valid) : ∃ ordered, ordered.Perm forest ∧ Represented state ordered := by
  obtain ⟨addresses, permutation, ring⟩ := boundary.roots
  obtain ⟨ordered, order, mapped⟩ := lift_map_permutation Node.vertex permutation
  have entries := order.flatMap_right Node.entries
  refine ⟨ordered, order, valid.perm order, ?_, ?_, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · simpa only [mapped] using ring
  · intro root member
    exact boundary.trees.stored root (order.mem_iff.mp member)
  · intro vertex key member
    exact boundary.trees.nonnegative vertex key (entries.mem_iff.mp member)
  · intro vertex
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · rcases boundary.minimum with ⟨empty, pointer⟩ | ⟨root, rootMember, pointer, least⟩
    · exact Or.inl ⟨by have length := order.length_eq; simp [empty] at length; exact length, pointer⟩
    · right
      refine ⟨root, order.mem_iff.mpr rootMember, pointer, ?_⟩
      intro other member
      have old := order.mem_iff.mp member
      have bound := least other old
      rw [pointer, (boundary.trees.stored root rootMember).root_key, (boundary.trees.stored other old).root_key] at bound
      exact bound


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









theorem RootBoundary.perm {state : Snapshot} {before after : Forest}
    (boundary : RootBoundary state before) (order : after.Perm before) : RootBoundary state after := by
  have entries := order.flatMap_right Node.entries
  refine ⟨boundary.trees.perm order, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, permutation.trans (order.map Node.vertex).symm, ring⟩
  · intro vertex
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · rcases boundary.minimum with ⟨empty, pointer⟩ | ⟨root, member, pointer, least⟩
    · exact Or.inl ⟨by have length := order.length_eq; simp [empty] at length; exact length, pointer⟩
    · exact Or.inr ⟨root, order.mem_iff.mpr member, pointer,
        fun other member => least other (order.mem_iff.mp member)⟩

/-- The marking branch preserves the whole physical boundary, with only the
    focused logical node's mark changed. -/
theorem RootBoundary.mark {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context node :: rest)) (marked : Bool) :
    RootBoundary (state.setMark node.vertex marked) (Ancestors.plug context (node.withMark marked) :: rest) := by
  have address := Ancestors.root_vertex context (before := node.withMark marked) (after := node) rfl
  have rootMap : (Ancestors.plug context (node.withMark marked) :: rest).map Node.vertex =
      (Ancestors.plug context node :: rest).map Node.vertex := by simp only [List.map_cons, address]
  have contents : (Ancestors.plug context (node.withMark marked)).entries.Perm (Ancestors.plug context node).entries := by
    have lifted := Ancestors.entries_replace (context := context) (before := node.withMark marked)
      (after := node) (removed := []) (by simp)
    simpa using lifted
  have entries : (Forest.entries (Ancestors.plug context (node.withMark marked) :: rest)).Perm
      (Forest.entries (Ancestors.plug context node :: rest)) := by
    simpa [Forest.entries] using contents.append_right rest.entries
  refine ⟨boundary.trees.mark marked, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, by simpa only [rootMap] using permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence]
    exact exists_congr (fun _ => entries.mem_iff.symm)
  · exact boundary.size.trans (congrArg Int.ofNat entries.length_eq.symm)
  · have least := boundary.minimum_addresses (by simp)
    have member : state.minimum ∈ (Ancestors.plug context (node.withMark marked) :: rest).map Node.vertex := by
      rw [rootMap]; exact least.1
    obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
    right
    refine ⟨root, member, pointer.symm, ?_⟩
    intro other member
    have present : other.vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex := by
      rw [← rootMap]
      exact List.mem_map.mpr ⟨other, member, rfl⟩
    exact least.2 other.vertex present

/-- Actual cascades preserve root rings, minimum, exact membership, size and
    scratch storage, in addition to the finite stored trees. -/
theorem cascade_boundary_exists (context : List Ancestor) (node : Node) (kept : List Node)
    (state : Snapshot) (rest : Forest)
    (boundary : RootBoundary state (Ancestors.plug context (node.withChildren kept) :: rest)) :
    ∃ final, CascadeRun state final node.vertex (cascadeCuts node context) ∧
      RootBoundary final (cascadeForest node kept context ++ rest) := by
  induction context generalizing node kept state rest with
  | nil =>
    have stored := boundary.trees.stored (node.withChildren kept) (by simp [Ancestors.plug])
    have parent := stored.root_parent
    change state.parents node.vertex = -1 at parent
    exact ⟨state, .root (by omega), boundary⟩
  | cons frame ancestors ih =>
    have mainStored := boundary.trees.stored (Ancestors.plug (frame :: ancestors) (node.withChildren kept)) (by simp)
    have focus := mainStored.focus_context
    have parent : state.parents node.vertex = frame.vertex := focus.root_parent
    have readMark : state.marks node.vertex = if node.marked then 1 else 0 := focus.root_mark
    have frameMember : (frame.vertex, frame.key) ∈ (Ancestors.plug (frame :: ancestors) (node.withChildren kept)).entries :=
      (Ancestors.entries_sublist ancestors (frame.plug (node.withChildren kept))).subset (by simp [Ancestor.plug, Node.entries])
    have frameNonnegative := boundary.trees.nonnegative frame.vertex frame.key (List.mem_flatMap.mpr ⟨_, by simp, frameMember⟩)
    by_cases marked : node.marked = true
    · have cut := boundary.cut (context := ancestors) (parent := frame.plug (node.withChildren kept))
        (child := node.withChildren kept) frame.before frame.after rfl
      obtain ⟨final, run, repaired⟩ := ih (frame.plug node) (frame.before ++ frame.after)
        (state.cut node.vertex frame.vertex) ((node.withChildren kept).withMark false :: rest) cut
      refine ⟨final, ?_, ?_⟩
      · have sourceRun : CascadeRun state final node.vertex (cascadeCuts (frame.plug node) ancestors + 1) :=
          CascadeRun.cut (by omega) (by simp [marked] at readMark; omega) (by simpa only [parent] using! run)
        simpa only [cascadeCuts, marked, ↓reduceIte] using sourceRun
      · apply repaired.perm
        simp only [cascadeForest, marked, ↓reduceIte, List.cons_append]
        exact List.perm_middle.symm
    · have unmarked : node.marked = false := by cases equal : node.marked <;> simp_all
      refine ⟨state.setMark node.vertex true, ?_, ?_⟩
      · simpa [cascadeCuts, unmarked] using CascadeRun.mark (by omega : 0 ≤ state.parents node.vertex)
          (by simpa [unmarked] using readMark)
      · simpa [cascadeForest, unmarked] using! boundary.mark true

theorem Forest.counts_perm {before after : Forest} (order : after.Perm before) : after.counts = before.counts := by
  unfold Forest.counts Forest.marks
  rw [order.length_eq, (order.map Node.marks).sum_nat]

/-- Cascade validity is stable under arbitrary untouched roots. -/
theorem Forest.Valid.cascade {context : List Ancestor} {parent child : Node} {rest : Forest}
    (valid : Forest.Valid (Ancestors.plug context parent :: rest)) (before after : List Node)
    (located : parent.children = before ++ child :: after) :
    Forest.Valid (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest) := by
  let root := Ancestors.plug context parent
  have single : Forest.Valid [root] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Forest.Unique, Forest.entries, root] using valid.1.head
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.1 _ (by simp [root])
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.2.1 _ (by simp [root])
    · intro node member
      have same := List.mem_singleton.mp member
      subst node
      exact valid.2.2.2 _ (by simp [root])
  have localValid := cascadeForest_valid context parent child before after located single
  have contents := cascadeForest_entries context parent (before ++ after) child.entries
    (parent.cut_entries before after child located)
  have permutation : (Forest.entries (child.withMark false :: cascadeForest parent (before ++ after) context ++ rest)).Perm
      (Forest.entries (Ancestors.plug context parent :: rest)) := by
    have reordered := (List.perm_append_comm (l₁ := child.entries)
      (l₂ := (cascadeForest parent (before ++ after) context).entries)).trans contents.symm
    simpa [Forest.entries, List.flatMap_append, List.append_assoc] using reordered.append_right rest.entries
  refine ⟨valid.1.of_entries_perm permutation, ?_, ?_, ?_⟩
  all_goals
    intro node member
    change node ∈ (child.withMark false :: cascadeForest parent (before ++ after) context) ++ rest at member
    rcases List.mem_append.mp member with repaired | old
    first | exact localValid.2.1 node repaired | exact localValid.2.2.1 node repaired | exact localValid.2.2.2 node repaired
    first | exact valid.2.1 node (by simp [old]) | exact valid.2.2.1 node (by simp [old]) | exact valid.2.2.2 node (by simp [old])



end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Algo2Lean.Fibonacci



theorem Node.entries_head (node : Node) : node.entries = (node.vertex, node.key) :: node.children.flatMap Node.entries := by cases node; simp [Node.entries, Node.vertex, Node.key, Node.children]



theorem Ancestors.entries_surrounding (context : List Ancestor) (node : Node) :
    (Ancestors.plug context node).entries.Perm (node.entries ++ Ancestors.surrounding context) := by
  induction context generalizing node with
  | nil => simp [Ancestors.plug, Ancestors.surrounding]
  | cons frame rest ih =>
    apply (ih (frame.plug node)).trans
    simp only [Ancestor.plug, Node.entries, List.flatMap_append, List.flatMap_cons]
    simpa [Ancestors.surrounding, Forest.entries, List.append_assoc] using
      (List.perm_append_comm (l₁ := (frame.vertex, frame.key) :: frame.before.flatMap Node.entries)
        (l₂ := node.entries)).append_right (frame.after.flatMap Node.entries ++ Ancestors.surrounding rest)

theorem Ancestors.key_change (context : List Ancestor) (node : Node) (rest : Forest) (key : Int) :
    EntryChange (Forest.entries (Ancestors.plug context node :: rest))
      (Forest.entries (Ancestors.plug context (node.withKey key) :: rest)) node.vertex node.key key := by
  refine ⟨node.children.flatMap Node.entries ++ Ancestors.surrounding context ++ rest.entries, ?_, ?_⟩
  · simpa [Forest.entries, Node.entries_head, List.append_assoc] using
      (Ancestors.entries_surrounding context node).append_right rest.entries
  · simpa [Forest.entries, Node.entries_head, List.append_assoc] using!
      (Ancestors.entries_surrounding context (node.withKey key)).append_right rest.entries

theorem EntryChange.vertices {before after : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) :
    (after.map Prod.fst).Perm (before.map Prod.fst) := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact (new.map Prod.fst).trans (old.map Prod.fst).symm

theorem Stored.lowerKey_frame {state : Snapshot} {parent vertex : Int} {node : Node}
    (stored : Stored state parent node) (absent : ¬node.Has vertex) (key : Int) :
    Stored (state.lowerKey vertex key) parent node := by
  apply stored.frame
  · intro value old member
    have different : value ≠ vertex := by intro same; exact absent (same ▸ ⟨old, member⟩)
    constructor <;> simp [Snapshot.lowerKey, Rings.write, different]
  · intro value old member
    exact ⟨rfl, rfl⟩

theorem Stored.lowerKey {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (unique : (node.entries.map Prod.fst).Nodup) (key : Int) :
    Stored (state.lowerKey node.vertex key) parent (node.withKey key) := by
  have outside := node.unique_root unique
  cases stored with
  | @node vertex value parent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    refine Stored.node ?_ readParent readMark readDegree readPresent ?_ ring ?_
    · simp [Snapshot.lowerKey, Node.vertex]
    · cases children <;> exact readHead
    · intro child member
      apply (subtrees child member).lowerKey_frame (key := key)
      rintro ⟨old, inside⟩
      exact outside ⟨old, List.mem_flatMap.mpr ⟨child, member, inside⟩⟩

theorem Snapshot.LocalChange.lowerKey (state : Snapshot) (node : Node) (key : Int) :
    Snapshot.LocalChange state (state.lowerKey node.vertex key) node := by
  constructor
  · intro vertex outside
    have different : vertex ≠ node.vertex := by intro same; exact outside (same ▸ ⟨node.key, node.root_entry⟩)
    constructor <;> simp [Snapshot.lowerKey, Rings.write, different]
  · intro vertex parent outside
    exact ⟨rfl, rfl⟩

theorem StoredForest.lowerKey {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (forest : StoredForest state (Ancestors.plug context node :: rest)) (key : Int) :
    StoredForest (state.lowerKey node.vertex key) (Ancestors.plug context (node.withKey key) :: rest) := by
  have mainStored := forest.stored (Ancestors.plug context node) (by simp)
  have included := Ancestors.entries_sublist context node
  have nodeUnique := (included.map Prod.fst).nodup forest.unique.head
  have mainNonnegative : ∀ vertex key, (vertex, key) ∈ (Ancestors.plug context node).entries → 0 ≤ vertex :=
    fun vertex key member => forest.nonnegative vertex key (List.mem_flatMap.mpr ⟨_, by simp, member⟩)
  have vertices := (Ancestors.key_change context node rest key).vertices
  refine ⟨vertices.nodup_iff.mpr forest.unique, ?_, ?_⟩
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact mainStored.lift_context forest.unique.head mainNonnegative (Snapshot.LocalChange.lowerKey state node key) rfl
        (mainStored.focus_context.lowerKey nodeUnique key)
    · apply (forest.stored root (by simp [old])).lowerKey_frame
      intro inside
      apply (Forest.Unique.disjoint (front := [Ancestors.plug context node]) (back := rest) forest.unique) node.vertex
      · exact ⟨node.key, by simpa [Forest.entries] using included.subset node.root_entry⟩
      · obtain ⟨oldKey, inside⟩ := inside
        exact ⟨oldKey, List.mem_flatMap.mpr ⟨root, old, inside⟩⟩
  · intro vertex value member
    have old := vertices.mem_iff.mp (List.mem_map.mpr ⟨(vertex, value), member, rfl⟩)
    obtain ⟨⟨oldVertex, oldKey⟩, member, same⟩ := List.mem_map.mp old
    change oldVertex = vertex at same
    subst oldVertex
    exact forest.nonnegative vertex oldKey member

/-- Lowering a nonroot key leaves the root boundary intact; the parent-edge
    order may temporarily fail and is repaired by the following cut. -/
theorem RootBoundary.lower_nonroot {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (Ancestors.plug context node :: rest)) (key : Int)
    (nonroot : 0 ≤ state.parents node.vertex) :
    RootBoundary (state.lowerKey node.vertex key) (Ancestors.plug context (node.withKey key) :: rest) := by
  have vertices := (Ancestors.key_change context node rest key).vertices
  have address := Ancestors.root_vertex context (before := node.withKey key) (after := node) rfl
  have rootMap : (Ancestors.plug context (node.withKey key) :: rest).map Node.vertex =
      (Ancestors.plug context node :: rest).map Node.vertex := by simp only [List.map_cons, address]
  have different (vertex : Int) (member : vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex) :
      vertex ≠ node.vertex := by
    intro same
    have parent := boundary.root_parent member
    rw [same] at parent
    omega
  have least := boundary.minimum_addresses (by simp)
  refine ⟨boundary.trees.lowerKey key, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, by simpa only [rootMap] using permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence, Forest.has_iff_map, Forest.has_iff_map]
    exact vertices.mem_iff.symm
  · change state.size = _
    rw [boundary.size]
    have length := vertices.length_eq
    simp only [List.length_map] at length
    exact congrArg Int.ofNat length.symm
  · have member : state.minimum ∈ (Ancestors.plug context (node.withKey key) :: rest).map Node.vertex := by rw [rootMap]; exact least.1
    obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
    refine Or.inr ⟨root, member, pointer.symm, ?_⟩
    intro other member
    have old : other.vertex ∈ (Ancestors.plug context node :: rest).map Node.vertex := by
      rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
    simpa [Snapshot.lowerKey, Rings.write, different state.minimum least.1, different other.vertex old]
      using least.2 other.vertex old







/-- Changing a focused key changes neither roots nor marks. -/
theorem Ancestors.key_counts (context : List Ancestor) (node : Node) (rest : Forest) (key : Int) :
    Forest.counts (Ancestors.plug context (node.withKey key) :: rest) =
      Forest.counts (Ancestors.plug context node :: rest) := by
  simp [Forest.counts, Forest.marks, Ancestors.plug_marks]

theorem Node.Ordered.replace_child_bound {parent child replacement : Node}
    (ordered : parent.Ordered) (before after : List Node)
    (located : parent.children = before ++ child :: after)
    (replacementOrdered : replacement.Ordered) (bound : parent.key ≤ replacement.key) :
    (parent.withChildren (before ++ replacement :: after)).Ordered := by
  cases ordered with
  | @make vertex key marked children bounds subtrees =>
    change children = before ++ child :: after at located
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply bounds; rw [located]; simp [old]
      · exact bound
      · apply bounds; rw [located]; simp [old]
    · intro node member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with old | rfl | old
      · apply subtrees; rw [located]; simp [old]
      · exact replacementOrdered
      · apply subtrees; rw [located]; simp [old]

/-- A decreased root needs only the final minimum comparison. -/
theorem RootBoundary.lower_root {state : Snapshot} {node : Node} {rest : Forest}
    (boundary : RootBoundary state (node :: rest)) (key : Int) (decreased : key ≤ node.key) :
    RootBoundary ((state.lowerKey node.vertex key).finishDecrease node.vertex) (node.withKey key :: rest) := by
  let lowered := state.lowerKey node.vertex key
  have vertices := (Ancestors.key_change [] node rest key).vertices
  have rootMap : (node.withKey key :: rest).map Node.vertex = (node :: rest).map Node.vertex := rfl
  have least := boundary.minimum_addresses (by simp)
  have oldKey := (boundary.trees.stored node (by simp)).root_key
  have keyAt : lowered.keys node.vertex = key := by simp [lowered, Snapshot.lowerKey]
  have keyElse (vertex : Int) (different : vertex ≠ node.vertex) : lowered.keys vertex = state.keys vertex := by
    simp [lowered, Snapshot.lowerKey, Rings.write, different]
  have keyMonotone (vertex : Int) : lowered.keys vertex ≤ state.keys vertex := by
    by_cases same : vertex = node.vertex
    · rw [same, keyAt, oldKey]; exact decreased
    · rw [keyElse vertex same]; exact Int.le_refl _
  have others (vertex : Int) (member : vertex ∈ (node :: rest).map Node.vertex) (different : vertex ≠ node.vertex) :
      lowered.keys state.minimum ≤ lowered.keys vertex := by
    rw [keyElse vertex different]
    exact Int.le_trans (keyMonotone state.minimum) (least.2 vertex member)
  have stored : StoredForest (lowered.finishDecrease node.vertex) (node.withKey key :: rest) := by
    have base := boundary.trees.lowerKey (context := []) key
    refine ⟨base.unique, ?_, base.nonnegative⟩
    intro root member
    apply (base.stored root member).frame
    · intro vertex key inside; constructor <;> rfl
    · intro vertex key inside; exact ⟨rfl, rfl⟩
  refine ⟨stored, ?_, ?_, ?_, ?_, boundary.scratch⟩
  · obtain ⟨addresses, permutation, ring⟩ := boundary.roots
    exact ⟨addresses, permutation, ring⟩
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [boundary.presence, Forest.has_iff_map, Forest.has_iff_map]
    exact vertices.mem_iff.symm
  · change state.size = _
    rw [boundary.size]
    have length := vertices.length_eq
    simp only [List.length_map] at length
    exact congrArg Int.ofNat length.symm
  · by_cases better : lowered.keys node.vertex < lowered.keys state.minimum
    · refine Or.inr ⟨node.withKey key, by simp, ?_, ?_⟩
      · change (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) = node.vertex
        rw [if_pos better]
      · intro other member
        have old : other.vertex ∈ (node :: rest).map Node.vertex := by
          rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
        change lowered.keys (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) ≤ lowered.keys other.vertex
        rw [if_pos better]
        by_cases same : other.vertex = node.vertex
        · rw [same]; exact Int.le_refl _
        · exact Int.le_trans (Int.le_of_lt better) (others other.vertex old same)
    · have member : state.minimum ∈ (node.withKey key :: rest).map Node.vertex := by rw [rootMap]; exact least.1
      obtain ⟨root, member, pointer⟩ := List.mem_map.mp member
      refine Or.inr ⟨root, member, ?_, ?_⟩
      · change (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) = root.vertex
        rw [if_neg better, pointer]
      · intro other member
        have old : other.vertex ∈ (node :: rest).map Node.vertex := by
          rw [← rootMap]; exact List.mem_map.mpr ⟨other, member, rfl⟩
        change lowered.keys (if lowered.keys node.vertex < lowered.keys state.minimum then node.vertex else state.minimum) ≤ lowered.keys other.vertex
        rw [if_neg better]
        by_cases same : other.vertex = node.vertex
        · rw [same]; omega
        · exact others other.vertex old same

/-- An unchanged minimum comparison is a no-op after the queue invariant has
    already established that the chosen root is globally least. -/
theorem Represented.finishDecrease {state : Snapshot} {forest : Forest} (represented : Represented state forest)
    {vertex key : Int} (member : (vertex, key) ∈ forest.entries) : state.finishDecrease vertex = state := by
  have read := represented.entry member
  have nonempty : forest ≠ [] := by rintro rfl; simp [Forest.entries] at member
  have least := (represented.minimum_key nonempty).2.2 vertex (by omega)
  simp [Snapshot.finishDecrease, Int.not_lt.mpr least]

theorem Forest.Valid.lower_ordered {frame : Ancestor} {context : List Ancestor} {node : Node} {rest : Forest}
    (valid : Forest.Valid (Ancestors.plug (frame :: context) node :: rest))
    (key : Int) (decreased : key ≤ node.key) (bound : frame.key ≤ key) :
    Forest.Valid (Ancestors.plug (frame :: context) (node.withKey key) :: rest) := by
  have rootOrdered := valid.2.1 (Ancestors.plug (frame :: context) node) (by simp)
  have rootRanked := valid.2.2.1 (Ancestors.plug (frame :: context) node) (by simp)
  have nodeOrdered := Ancestors.focus_ordered rootOrdered
  have nodeRanked := Ancestors.focus_ranked rootRanked
  refine ⟨(Ancestors.key_change (frame :: context) node rest key).vertices.nodup_iff.mpr valid.1, ?_, ?_, ?_⟩
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · have frameOrdered := Ancestors.focus_ordered (context := context) rootOrdered
      have repaired : (frame.plug (node.withKey key)).Ordered :=
        frameOrdered.replace_child_bound frame.before frame.after rfl (nodeOrdered.decrease_key key decreased) bound
      exact Ancestors.replace_ordered (context := context) (before := frame.plug node) rootOrdered repaired rfl
    · exact valid.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact Ancestors.replace_ranked rootRanked (nodeRanked.withKey key) (Nat.le_refl _)
    · exact valid.2.2.1 root (by simp [old])
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · rw [← Ancestors.plug_mark (context := frame :: context) (before := node) (after := node.withKey key) rfl]
      exact valid.2.2.2 _ (by simp)
    · exact valid.2.2.2 root (by simp [old])

theorem cascadeForest_same_header (context : List Ancestor) {before after : Node} (kept : List Node)
    (vertex : before.vertex = after.vertex) (key : before.key = after.key) (marked : before.marked = after.marked) :
    cascadeForest before kept context = cascadeForest after kept context := by
  have same : before.withChildren kept = after.withChildren kept := by
    simp only [Node.withChildren, vertex, key, marked]
  induction context generalizing before after kept with
  | nil => simp only [cascadeForest, same]
  | cons frame rest ih =>
    simp only [cascadeForest, marked, same]
    split
    · rw [ih (before := frame.plug before) (after := frame.plug after) (frame.before ++ frame.after) rfl rfl rfl rfl]
    · rfl



theorem EntryChange.perm_after {before after result : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) (permutation : result.Perm after) :
    EntryChange before result vertex oldKey newKey := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact ⟨unchanged, old, permutation.trans new⟩

theorem EntryChange.perm_before {before after initial : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) (permutation : initial.Perm before) :
    EntryChange initial after vertex oldKey newKey := by
  obtain ⟨unchanged, old, new⟩ := changed
  exact ⟨unchanged, permutation.trans old, new⟩

/-- Lowering and cutting a selected nonroot, followed by the actual cascade,
    restores the full finite forest and its amortized potential invariant. -/
theorem represented_lower_cut {state : Snapshot} {context : List Ancestor} {frame : Ancestor}
    {node : Node} {rest : Forest}
    (represented : Represented state (Ancestors.plug (frame :: context) node :: rest))
    (key : Int) (decreased : key ≤ node.key) :
    ∃ middle outputForest,
      CascadeRun ((state.lowerKey node.vertex key).cut node.vertex frame.vertex) middle
        frame.vertex (cascadeCuts (frame.plug node) context) ∧
      Represented middle outputForest ∧
      EntryChange (Forest.entries (Ancestors.plug (frame :: context) node :: rest))
        outputForest.entries node.vertex node.key key ∧
      Decrease (Forest.counts (Ancestors.plug (frame :: context) node :: rest)) outputForest.counts
        (cascadeCuts (frame.plug node) context + 1) := by
  have rootStored := represented.stored (Ancestors.plug (frame :: context) node) (by simp)
  have parent : state.parents node.vertex = frame.vertex := rootStored.focus_context.root_parent
  have frameStored := rootStored.focus_context (context := context)
  have framePresent : state.present frame.vertex = 1 := frameStored.root_present
  have nonnegative := represented.present_nonnegative (by omega : state.present frame.vertex ≠ 0)
  have lowered := represented.boundary.lower_nonroot key (by omega)
  have cut := lowered.cut (context := context) (parent := frame.plug (node.withKey key))
    (child := node.withKey key) frame.before frame.after rfl
  obtain ⟨middle, run, boundary⟩ := cascade_boundary_exists context (frame.plug node)
    (frame.before ++ frame.after) ((state.lowerKey node.vertex key).cut node.vertex frame.vertex)
    ((node.withKey key).withMark false :: rest) cut
  have canonical := boundary.perm List.perm_middle.symm
  have oldValid := represented.valid.cascade (context := context) (parent := frame.plug node)
    (child := node) frame.before frame.after rfl
  have valid : Forest.Valid ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) := by
    simpa only [Node.withMark, Node.withKey, Node.vertex, Node.key, Node.marked, Node.children]
      using! oldValid.decrease_root key decreased
  obtain ⟨outputForest, order, output⟩ := canonical.close valid
  have content := cascadeForest_entries context (frame.plug (node.withKey key))
    (frame.before ++ frame.after) (node.withKey key).entries
    ((frame.plug (node.withKey key)).cut_entries frame.before frame.after (node.withKey key) rfl)
  have cascadeSame := cascadeForest_same_header context (before := frame.plug (node.withKey key))
    (after := frame.plug node) (frame.before ++ frame.after) rfl rfl rfl
  rw [cascadeSame] at content
  have canonicalContent : (Forest.entries ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest)).Perm
      (Forest.entries (Ancestors.plug (frame :: context) (node.withKey key) :: rest)) := by
    have rearranged := (List.perm_append_comm (l₁ := (node.withKey key).entries)
      (l₂ := (cascadeForest (frame.plug node) (frame.before ++ frame.after) context).entries)).trans content.symm
    simpa [Forest.entries, List.flatMap_append, List.append_assoc, Ancestors.plug] using rearranged.append_right rest.entries
  refine ⟨middle, outputForest, run, output,
    (Ancestors.key_change (frame :: context) node rest key).perm_after ((order.flatMap_right Node.entries).trans canonicalContent), ?_⟩
  rw [Forest.counts_perm order]
  have countsSame : Forest.counts ((node.withKey key).withMark false ::
      cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) =
      Forest.counts (node.withMark false :: cascadeForest (frame.plug node) (frame.before ++ frame.after) context ++ rest) := by
    have markCommute : (node.withKey key).withMark false = (node.withMark false).withKey key := rfl
    simp [Forest.counts, Forest.marks, markCommute]
  simp only [List.cons_append] at countsSame
  rw [countsSame]
  exact cascadeForest_decrease_accounting context (frame.plug node) node frame.before frame.after rest rfl

theorem EntryChange.new_member {before after : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) : (vertex, newKey) ∈ after := by
  obtain ⟨unchanged, _, content⟩ := changed
  exact content.mem_iff.mpr (by simp)

/-- Strict decrease-key at an arbitrary finite ancestor context. The result
    exposes only the exact execution, represented queue, entry replacement,
    and reusable potential accounting. -/
theorem represented_decrease_focused {state : Snapshot} {context : List Ancestor} {node : Node} {rest : Forest}
    (represented : Represented state (Ancestors.plug context node :: rest))
    (key : Int) (decreased : key < node.key) :
    ∃ final outputForest cuts,
      DecreaseRun state final node.vertex key cuts ∧ Represented final outputForest ∧
      EntryChange (Forest.entries (Ancestors.plug context node :: rest)) outputForest.entries node.vertex node.key key ∧
      Decrease (Forest.counts (Ancestors.plug context node :: rest)) outputForest.counts cuts := by
  have rootStored := represented.stored (Ancestors.plug context node) (by simp)
  have nodeStored := rootStored.focus_context
  have readKey := nodeStored.root_key
  have strict : key < state.keys node.vertex := by rw [readKey]; exact decreased
  cases context with
  | nil =>
    have rootParent : state.parents node.vertex = -1 := nodeStored.root_parent
    have boundary := represented.boundary.lower_root key (Int.le_of_lt decreased)
    obtain ⟨outputForest, order, output⟩ := boundary.close (represented.valid.decrease_root key (Int.le_of_lt decreased))
    refine ⟨(state.lowerKey node.vertex key).finishDecrease node.vertex, outputForest, 0,
      .root strict (by omega), output,
      (Ancestors.key_change [] node rest key).perm_after (order.flatMap_right Node.entries), ?_⟩
    rw [Forest.counts_perm order]
    change Decrease (Forest.counts (node :: rest)) (Forest.counts (node.withKey key :: rest)) 0
    rw [show Forest.counts (node.withKey key :: rest) = Forest.counts (node :: rest) from Ancestors.key_counts [] node rest key]
    exact .unchanged _
  | cons frame context =>
    have parent : state.parents node.vertex = frame.vertex := nodeStored.root_parent
    have parentStored := rootStored.focus_context (context := context)
    have parentKey : state.keys frame.vertex = frame.key := parentStored.root_key
    have parentPresent : state.present frame.vertex = 1 := parentStored.root_present
    have parentNonnegative := represented.present_nonnegative (by omega : state.present frame.vertex ≠ 0)
    have unique := ((Ancestors.entries_sublist context (frame.plug node)).map Prod.fst).nodup represented.valid.1.head
    have different : frame.vertex ≠ node.vertex := by
      intro same
      exact (Ancestor.unique_parts unique).2.1 (same ▸ ⟨node.key, node.root_entry⟩)
    have loweredParent : (state.lowerKey node.vertex key).keys (state.parents node.vertex) = frame.key := by
      simp [Snapshot.lowerKey, Rings.write, parent, different, parentKey]
    by_cases ordered : frame.key ≤ key
    · have boundary := represented.boundary.lower_nonroot key (by omega)
      obtain ⟨outputForest, order, output⟩ := boundary.close
        (represented.valid.lower_ordered key (Int.le_of_lt decreased) ordered)
      have content := (Ancestors.key_change (frame :: context) node rest key).perm_after
        (order.flatMap_right Node.entries)
      have finish := output.finishDecrease content.new_member
      refine ⟨state.lowerKey node.vertex key, outputForest, 0, ?_, output, content, ?_⟩
      · have run := DecreaseRun.ordered strict (by omega : 0 ≤ state.parents node.vertex)
          (by rw [loweredParent]; exact ordered)
        simpa only [finish] using run
      · rw [Forest.counts_perm order, Ancestors.key_counts (frame :: context) node rest key]
        exact .unchanged _
    · obtain ⟨middle, outputForest, cascade, output, content, accounting⟩ :=
        represented_lower_cut represented key (Int.le_of_lt decreased)
      have finish := output.finishDecrease content.new_member
      refine ⟨middle, outputForest, cascadeCuts (frame.plug node) context + 1, ?_, output, content, accounting⟩
      have run := DecreaseRun.cascading strict (by omega : 0 ≤ state.parents node.vertex)
        (by rw [loweredParent]; omega) (by simpa only [parent] using cascade)
      simpa only [finish] using run

/-- Every strict decrease of an existing handle terminates, preserves the
    represented Fibonacci heap, changes exactly that key, and satisfies the
    constant-amortized decrease accounting relation. -/
theorem Represented.decrease {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (vertex key : Int)
    (active : state.present vertex ≠ 0) (decreased : key < state.keys vertex) :
    ∃ final outputForest cuts,
      DecreaseRun state final vertex key cuts ∧ Represented final outputForest ∧
      EntryChange forest.entries outputForest.entries vertex (state.keys vertex) key ∧
      Decrease forest.counts outputForest.counts cuts := by
  obtain ⟨oldKey, entry⟩ := (represented.presence vertex).mp active
  have readKey := (represented.entry entry).1
  obtain ⟨root, member, inside⟩ := List.mem_flatMap.mp entry
  obtain ⟨context, node, located, address, value⟩ := (represented.stored root member).locate vertex oldKey inside
  obtain ⟨front, back, position⟩ := List.mem_iff_append.mp member
  subst forest
  have rotated := represented.rotate (front := front) (back := root :: back)
  have permutation : (root :: (back ++ front)).Perm (front ++ root :: back) := by
    simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
  rw [located] at rotated
  obtain ⟨final, outputForest, cuts, run, output, changed, accounting⟩ :=
    represented_decrease_focused (by simpa only [List.cons_append] using rotated) key
      (by rw [value, ← readKey]; exact decreased)
  refine ⟨final, outputForest, cuts, ?_, output, ?_, ?_⟩
  · simpa only [address] using run
  · have entryPermutation := permutation.flatMap_right Node.entries
    rw [located] at entryPermutation
    have complete := changed.perm_before entryPermutation.symm
    simpa only [address, value, readKey, located] using! complete
  · have counts := Forest.counts_perm permutation
    rw [located] at counts
    rw [located, ← counts]
    exact accounting

end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {forest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.Represented state forest →
        ∀ (vertex key : Int),
          Ne.{1} (state.present vertex) (0 : Int) →
            LT.lt.{0} key (state.keys vertex) →
              Exists.{1} fun final =>
                Exists.{1} fun outputForest =>
                  Exists.{1} fun cuts =>
                    Algo2Lean.Fibonacci.DecreaseRun state final vertex key cuts ∧
                      Algo2Lean.Fibonacci.Represented final outputForest ∧
                        Algo2Lean.Fibonacci.EntryChange forest.entries outputForest.entries vertex
                            (state.keys vertex) key ∧
                          Algo2Lean.Fibonacci.Decrease forest.counts outputForest.counts cuts :=
  Algo2Lean.Fibonacci.Represented.decrease
