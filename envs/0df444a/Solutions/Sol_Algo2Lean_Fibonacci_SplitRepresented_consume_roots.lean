-- Prove2me | solution 1 for Algo2Lean.Fibonacci.SplitRepresented.consume_roots
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:01.073977+00:00
-- url     : https://prove2.me/submissions/3f48d329-e94f-4fb0-8416-c4c174e7b0b2

import Definitions.Def_Algo2LeanLib_FibonacciConsolidation
import Theorems.Thm_Algo2Lean_Fibonacci_degree_logarithmic


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













theorem Node.Ordered.link {parent child : Node} (parentOrdered : parent.Ordered)
    (childOrdered : child.Ordered) (winner : parent.key ≤ child.key) :
    (parent.link child).Ordered := by
  cases parentOrdered with
  | make bounds children =>
    apply Node.Ordered.make
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact winner
      · exact bounds node old
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact childOrdered.withMark false
      · exact children node old

theorem Node.Ranked.link {parent child : Node} (parentRanked : parent.Ranked)
    (childRanked : child.Ranked) (equalDegree : parent.degree = child.degree) :
    (parent.link child).Ranked := by
  cases parentRanked with
  | @make vertex key marked children ordered valid =>
    apply Node.Ranked.make
    · refine ⟨?_, ordered⟩
      change children.length ≤ child.degree
      exact Nat.le_of_eq equalDegree
    · intro node member
      simp only [List.mem_cons] at member
      rcases member with rfl | old
      · exact childRanked.withMark false
      · exact valid node old

/-- Linking changes only the representation of the two trees, not their entries. -/
theorem Node.link_entries (parent child : Node) :
    (parent.link child).entries.Perm (parent.entries ++ child.entries) := by
  cases parent with
  | make vertex key marked children =>
    simpa only [Node.link, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
      Node.entries, List.flatMap_cons, Node.entries_withMark, List.cons_append] using
      (List.perm_append_comm (l₁ := child.entries) (l₂ := children.flatMap Node.entries)).cons (vertex, key)

















/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique



theorem Forest.linkRoots_entries (parent child : Node) (rest : Forest) :
    (linkRoots parent child rest).entries.Perm (Forest.entries (parent :: child :: rest)) := by
  simpa [Forest.linkRoots, Forest.entries, List.append_assoc] using
    (parent.link_entries child).append_right rest.entries





/-- Linking the larger-key root under an equal-degree smaller-key root
    preserves all semantic invariants and all represented entries. -/
theorem Forest.Valid.link_roots {parent child : Node} {rest : Forest}
    (valid : (Forest.Valid (parent :: child :: rest)))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    (linkRoots parent child rest).Valid := by
  have parentMember : parent ∈ parent :: child :: rest := by simp
  have childMember : child ∈ parent :: child :: rest := by simp
  refine ⟨valid.1.of_entries_perm (Forest.linkRoots_entries parent child rest), ?_, ?_, ?_⟩
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.1 parent parentMember).link (valid.2.1 child childMember) winner
    · exact valid.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact (valid.2.2.1 parent parentMember).link (valid.2.2.1 child childMember) equalDegree
    · exact valid.2.2.1 node (by simp [old])
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact valid.2.2.2 parent parentMember
    · exact valid.2.2.2 node (by simp [old])









theorem Node.clear_mark_count (node : Node) :
    (node.withMark false).marks + (if node.marked then 1 else 0) = node.marks := by
  cases node
  simp [Node.withMark, Node.marks, Node.vertex, Node.key, Node.children, Node.marked, Nat.add_comm]



theorem Node.link_marks (parent child : Node) :
    (parent.link child).marks + (if child.marked then 1 else 0) = parent.marks + child.marks := by
  cases parent
  simp only [Node.link, Node.withChildren, Node.vertex, Node.key, Node.marked, Node.children,
    Node.marks, List.map_cons, List.sum_cons]
  have clear := child.clear_mark_count
  simp only [Node.marked] at clear
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









theorem singleton_ring (left right : Int → Int) (vertex : Int)
    (selfLeft : left vertex = vertex) (selfRight : right vertex = vertex) : Ring left right [vertex] :=
  ⟨by simp, vertex, vertex, Chain.singleton vertex, selfRight, selfLeft⟩

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

theorem Forest.Unique.left {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    front.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  exact (List.nodup_append.mp unique).1



/-- Every root's own address is separate from its strict descendants. -/
theorem Node.unique_root {node : Node} (unique : (node.entries.map Prod.fst).Nodup) :
    ¬Forest.Has node.children node.vertex := by
  cases node with
  | make vertex key marked children =>
    simp only [Node.entries, List.map_cons] at unique
    simpa [Node.entries, Node.children, Node.vertex, Forest.has_iff_map, Forest.entries] using
      (List.nodup_cons.mp unique).1

/-- A root-ring vertex cannot be an entry in a separate forest component. -/
theorem Forest.Unique.roots_disjoint {front back : Forest}
    (unique : Forest.Unique (front ++ back)) :
    ∀ vertex ∈ front.map Node.vertex, vertex ∉ back.entries.map Prod.fst := by
  intro vertex member inside
  obtain ⟨root, member, same⟩ := List.mem_map.mp member
  exact unique.disjoint vertex
    ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
    ((back.has_iff_map vertex).mpr inside)

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



/-- Link updates only the metadata of its two supplied roots. -/
theorem Snapshot.link_fields {state : Snapshot} {child parent vertex : Int}
    (notChild : vertex ≠ child) (notParent : vertex ≠ parent) :
    SameFields state (state.link child parent) vertex := by
  constructor <;> simp [Snapshot.link, Rings.write, notChild, notParent]

/-- The child head and its predecessor have the supplied root as their parent. -/
theorem Stored.child_ring_parents {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (nonempty : ¬state.children node.vertex < 0) :
    state.parents (state.children node.vertex) = node.vertex ∧
      state.parents (state.left (state.children node.vertex)) = node.vertex := by
  cases stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    cases children with
    | nil =>
      have negative : state.children vertex = -1 := readHead
      change ¬state.children vertex < 0 at nonempty
      omega
    | cons first rest =>
      change state.children vertex = first.vertex at readHead
      change state.parents (state.children vertex) = vertex ∧ state.parents (state.left (state.children vertex)) = vertex
      rw [readHead]
      have childRing : Rings.Ring state.left state.right (first.vertex :: rest.map Node.vertex) := by
        rcases ring with impossible | ring
        · simp at impossible
        · exact ring
      have predecessorMember := (childRing.neighbors (vertex := first.vertex) (by simp)).1
      change state.left first.vertex ∈ (first :: rest).map Node.vertex at predecessorMember
      obtain ⟨previous, member, same⟩ := List.mem_map.mp predecessorMember
      constructor
      · exact (subtrees first (by simp)).root_parent
      · rw [← same]
        exact (subtrees previous member).root_parent

/-- Rewiring one child ring leaves nodes with other parents untouched. -/
theorem Stored.link_links {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) {child vertex : Int}
    (notChild : vertex ≠ child) (otherParent : state.parents vertex ≠ node.vertex) :
    (state.link child node.vertex).left vertex = state.left vertex ∧
      (state.link child node.vertex).right vertex = state.right vertex := by
  by_cases empty : state.children node.vertex < 0
  · simp [Snapshot.link, empty, Rings.write, notChild]
  · obtain ⟨headParent, beforeParent⟩ := stored.child_ring_parents empty
    have notHead : vertex ≠ state.children node.vertex := by intro same; subst vertex; exact otherParent headParent
    have notBefore : vertex ≠ state.left (state.children node.vertex) := by intro same; subst vertex; exact otherParent beforeParent
    simp [Snapshot.link, empty, Rings.insertBeforeLeft, Rings.insertBeforeRight, Rings.write, notChild, notHead, notBefore]

/-- Linking two disjoint trees constructs exactly their logical parent/child
    combination. No global minimum, transcript, or degree table is needed. -/
theorem Stored.link {state : Snapshot} {outerParent : Int} {parent child : Node}
    (parentStored : Stored state outerParent parent) (childStored : Stored state (-1) child)
    (parentUnique : (parent.entries.map Prod.fst).Nodup)
    (childUnique : (child.entries.map Prod.fst).Nodup)
    (separate : ∀ vertex, parent.Has vertex → ¬child.Has vertex)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ parent.entries → 0 ≤ vertex) :
    Stored (state.link child.vertex parent.vertex) outerParent (parent.link child) := by
  have parentHas : parent.Has parent.vertex := ⟨parent.key, parent.root_entry⟩
  have childHas : child.Has child.vertex := ⟨child.key, child.root_entry⟩
  have different : child.vertex ≠ parent.vertex := by
    intro same
    exact separate parent.vertex parentHas (same ▸ childHas)
  have oldNotChild (vertex key : Int) (member : (vertex, key) ∈ parent.entries) : vertex ≠ child.vertex := by
    intro same
    exact separate child.vertex (same ▸ ⟨key, member⟩) childHas
  have descendantNotParent (vertex key : Int)
      (member : (vertex, key) ∈ parent.children.flatMap Node.entries) : vertex ≠ parent.vertex := by
    intro same
    exact parent.unique_root parentUnique ⟨key, same ▸ member⟩
  have childDescendantNotRoot (vertex key : Int)
      (member : (vertex, key) ∈ child.children.flatMap Node.entries) : vertex ≠ child.vertex := by
    intro same
    exact child.unique_root childUnique ⟨key, same ▸ member⟩
  have childNotParent (vertex key : Int) (member : (vertex, key) ∈ child.entries) : vertex ≠ parent.vertex := by
    intro same
    exact separate parent.vertex parentHas (same ▸ ⟨key, member⟩)
  have linkedChild : Stored (state.link child.vertex parent.vertex) parent.vertex (child.withMark false) := by
    apply childStored.change_header false
    · exact childStored.root_key
    · simp [Snapshot.link]
    · simp [Snapshot.link]
    · simpa [Snapshot.link, Rings.write, different] using childStored.root_degree
    · exact childStored.root_present
    · simp [Snapshot.link, Rings.write, different]
    · intro vertex key member
      exact Snapshot.link_fields (childDescendantNotRoot vertex key member)
        (childNotParent vertex key (Node.descendant_entries member))
    · intro vertex key member
      apply parentStored.link_links (childDescendantNotRoot vertex key member)
      intro same
      exact separate parent.vertex parentHas (same ▸ childStored.descendant_parent vertex key member)
  have oldChildren : ∀ old ∈ parent.children,
      Stored (state.link child.vertex parent.vertex) parent.vertex old := by
    have childrenStored : ∀ old ∈ parent.children, Stored state parent.vertex old := by
      cases parentStored with | node _ _ _ _ _ _ _ subtrees => exact subtrees
    intro old member
    apply (childrenStored old member).frame
    · intro vertex key inside
      exact Snapshot.link_fields (oldNotChild vertex key (Node.child_entries member inside))
        (descendantNotParent vertex key (List.mem_flatMap.mpr ⟨old, member, inside⟩))
    · intro vertex key inside
      apply parentStored.link_links (oldNotChild vertex key
        (Node.child_entries member (Node.descendant_entries inside)))
      intro same
      obtain ⟨parentKey, parentEntry⟩ := (childrenStored old member).descendant_parent vertex key inside
      exact parent.unique_root parentUnique ⟨parentKey,
        same ▸ List.mem_flatMap.mpr ⟨old, member, parentEntry⟩⟩
  cases parentStored with
  | @node vertex key outerParent marked children readKey readParent readMark readDegree readPresent readHead ring subtrees =>
    change child.vertex ≠ vertex at different
    change Stored _ outerParent (.make vertex key marked (child.withMark false :: children))
    refine Stored.node ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact readKey
    · simpa [Snapshot.link, Rings.write, Ne.symm different] using readParent
    · simpa [Snapshot.link, Rings.write, Ne.symm different] using readMark
    · simp [Snapshot.link, Node.vertex, readDegree, Int.natCast_add]
    · exact readPresent
    · simp [Snapshot.link, Node.vertex, Node.withMark]
    · cases children with
      | nil =>
        have empty : state.children vertex = -1 := readHead
        apply Or.inr
        apply Rings.singleton_ring <;>
          simp [Snapshot.link, Node.vertex, Node.withMark, empty]
      | cons first rest =>
        have head : state.children vertex = first.vertex := readHead
        have headNonnegative : 0 ≤ first.vertex :=
          nonnegative first.vertex first.key (Node.child_entries (by simp [Node.children]) first.root_entry)
        have notEmpty : ¬state.children vertex < 0 := by rw [head]; omega
        have original : Rings.Ring state.left state.right (first.vertex :: rest.map Node.vertex) := by
          rcases ring with impossible | ring
          · simp at impossible
          · exact ring
        have fresh : child.vertex ∉ first.vertex :: rest.map Node.vertex := by
          intro member
          change child.vertex ∈ (first :: rest).map Node.vertex at member
          obtain ⟨old, member, same⟩ := List.mem_map.mp member
          exact oldNotChild old.vertex old.key (Node.child_entries member old.root_entry) same
        apply Or.inr
        dsimp only [Snapshot.link]
        change Rings.Ring
          (if state.children vertex < 0 then _ else _)
          (if state.children vertex < 0 then _ else _)
          ((child.withMark false).vertex :: first.vertex :: rest.map Node.vertex)
        rw [if_neg notEmpty, if_neg notEmpty]
        simpa only [Node.vertex, Node.withMark, head] using original.insert_before fresh
    · intro node member
      rcases List.mem_cons.mp member with rfl | old
      · exact linkedChild
      · exact oldChildren node old

/-- Unrelated stored trees survive a link, including all their child rings. -/
theorem Stored.link_frame {state : Snapshot} {outerParent otherParent : Int} {parent other : Node}
    (parentStored : Stored state outerParent parent) (otherStored : Stored state otherParent other)
    {child : Int} (notParent : ¬other.Has parent.vertex) (notChild : ¬other.Has child) :
    Stored (state.link child parent.vertex) otherParent other := by
  have different (vertex key : Int) (member : (vertex, key) ∈ other.entries) :
      vertex ≠ child ∧ vertex ≠ parent.vertex := by
    constructor
    · intro same
      exact notChild (same ▸ ⟨key, member⟩)
    · intro same
      exact notParent (same ▸ ⟨key, member⟩)
  apply otherStored.frame
  · intro vertex key member
    exact Snapshot.link_fields (different vertex key member).1 (different vertex key member).2
  · intro vertex key member
    apply parentStored.link_links (different vertex key (Node.descendant_entries member)).1
    intro same
    exact notParent (same ▸ otherStored.descendant_parent vertex key member)





/-- One equal-degree collision preserves the abstract invariants wherever its
    two roots occur after a prefix of roots awaiting processing. -/
theorem Forest.Valid.link_after {pending rest : Forest} {parent child : Node}
    (valid : Forest.Valid (pending ++ parent :: child :: rest))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    Forest.Valid (pending ++ parent.link child :: rest) := by
  have reordered : Forest.Valid (parent :: child :: (rest ++ pending)) := by
    apply valid.perm
    simpa only [List.cons_append] using
      (List.perm_append_comm (l₁ := parent :: child :: rest) (l₂ := pending))
  have linked := reordered.link_roots winner equalDegree
  apply linked.perm
  simpa only [Forest.linkRoots, List.cons_append] using
    (List.perm_append_comm (l₁ := pending) (l₂ := parent.link child :: rest))

/-- The concrete pointer change of a collision leaves every pending root
    pointer intact, so traversal can continue over the same finite list. -/
theorem SplitRepresented.link_pending_ring {state : Snapshot} {pending rest : Forest} {parent child : Node}
    (represented : SplitRepresented state pending (parent :: child :: rest)) :
    Rings.RingOrEmpty (state.link child.vertex parent.vertex).left
      (state.link child.vertex parent.vertex).right (pending.map Node.vertex) := by
  have parentStored := represented.stored parent (by simp)
  have childStored := represented.stored child (by simp)
  have parentNonnegative := represented.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩)
  have childAbsent := represented.valid.1.disjoint
  rcases represented.pendingRing with empty | ring
  · exact Or.inl empty
  · apply Or.inr
    have pointers (vertex : Int) (member : vertex ∈ pending.map Node.vertex) :
        (state.link child.vertex parent.vertex).left vertex = state.left vertex ∧
          (state.link child.vertex parent.vertex).right vertex = state.right vertex := by
      obtain ⟨root, member, same⟩ := List.mem_map.mp member
      have stored := represented.stored root (by simp [member])
      apply parentStored.link_links
      · intro equal
        have inPending : Forest.Has pending child.vertex :=
          ⟨root.key, equal ▸ same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
        exact childAbsent child.vertex inPending ⟨child.key,
          List.mem_flatMap.mpr ⟨child, by simp, child.root_entry⟩⟩
      · have parent := stored.root_parent
        rw [same] at parent
        omega
    exact ring.frame (fun vertex member => (pointers vertex member).1)
      (fun vertex member => (pointers vertex member).2)

theorem Forest.Unique.head {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    (root.entries.map Prod.fst).Nodup := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).1

theorem Forest.Unique.tail {root : Node} {rest : Forest} (unique : Forest.Unique (root :: rest)) :
    rest.Unique := by
  unfold Forest.Unique at *
  simp only [Forest.entries, List.flatMap_cons, List.map_append] at unique
  exact (List.nodup_append.mp unique).2.1

/-- Linking two detached roots preserves pending traversal, exact membership,
    size, heap order, rank history, and all remaining detached singleton rings. -/
theorem SplitRepresented.link {state : Snapshot} {pending rest : Forest} {parent child : Node}
    (represented : SplitRepresented state pending (parent :: child :: rest))
    (winner : parent.key ≤ child.key) (equalDegree : parent.degree = child.degree) :
    SplitRepresented (state.link child.vertex parent.vertex) pending (parent.link child :: rest) := by
  have reordered : Forest.Valid ([parent, child] ++ (pending ++ rest)) := by
    apply represented.valid.perm
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using
      (List.perm_append_comm (l₁ := [parent, child]) (l₂ := pending)).append_right rest
  have separated := reordered.1.disjoint
  have pairUnique := reordered.1.left
  have parentStored := represented.stored parent (by simp)
  have childStored := represented.stored child (by simp)
  have parentNonnegative := represented.nonnegative parent.vertex parent.key
    (List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩)
  have parentChildSeparate : ∀ vertex, parent.Has vertex → ¬child.Has vertex := by
    intro vertex parentMember childMember
    apply (Forest.Unique.disjoint (front := [parent]) (back := [child]) pairUnique) vertex
    · simpa [Forest.Has, Forest.entries] using parentMember
    · simpa [Forest.Has, Forest.entries] using childMember
  have linked := parentStored.link childStored pairUnique.head pairUnique.tail.head parentChildSeparate
    (fun vertex key member => represented.nonnegative vertex key
      (List.mem_flatMap.mpr ⟨parent, by simp, member⟩))
  have different : parent.vertex ≠ child.vertex := by
    intro same
    exact parentChildSeparate child.vertex (same ▸ ⟨parent.key, parent.root_entry⟩) ⟨child.key, child.root_entry⟩
  have otherNotRoot (other : Node) (member : other ∈ pending ++ rest) :
      ¬other.Has parent.vertex ∧ ¬other.Has child.vertex := by
    constructor
    · rintro ⟨key, inside⟩
      exact separated parent.vertex
        ⟨parent.key, List.mem_flatMap.mpr ⟨parent, by simp, parent.root_entry⟩⟩
        ⟨key, List.mem_flatMap.mpr ⟨other, member, inside⟩⟩
    · rintro ⟨key, inside⟩
      exact separated child.vertex
        ⟨child.key, List.mem_flatMap.mpr ⟨child, by simp, child.root_entry⟩⟩
        ⟨key, List.mem_flatMap.mpr ⟨other, member, inside⟩⟩
  have contents : (Forest.entries (pending ++ parent.link child :: rest)).Perm
      (Forest.entries (pending ++ parent :: child :: rest)) := by
    simpa only [Forest.entries, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
      ((parent.link_entries child).append_right rest.entries).append_left pending.entries
  refine ⟨represented.valid.link_after winner equalDegree, ?_, represented.link_pending_ring, ?_, ?_, ?_, ?_, represented.cursor⟩
  · intro root member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inPending | rfl | inRest
    · exact parentStored.link_frame (represented.stored root (by simp [inPending]))
        (otherNotRoot root (by simp [inPending])).1 (otherNotRoot root (by simp [inPending])).2
    · exact linked
    · exact parentStored.link_frame (represented.stored root (by simp [inRest]))
        (otherNotRoot root (by simp [inRest])).1 (otherNotRoot root (by simp [inRest])).2
  · intro root member
    rcases List.mem_cons.mp member with rfl | inRest
    · have unchanged := parentStored.link_links (child := child.vertex) different
        (by have pointer := parentStored.root_parent; omega)
      exact ⟨unchanged.1.trans (represented.detachedRings parent (by simp)).1,
        unchanged.2.trans (represented.detachedRings parent (by simp)).2⟩
    · have rootStored := represented.stored root (by simp [inRest])
      have rootNotChild : root.vertex ≠ child.vertex := by
        intro same
        exact (otherNotRoot root (by simp [inRest])).2 (same ▸ ⟨root.key, root.root_entry⟩)
      have unchanged := parentStored.link_links rootNotChild
        (by have pointer := rootStored.root_parent; omega)
      exact ⟨unchanged.1.trans (represented.detachedRings root (by simp [inRest])).1,
        unchanged.2.trans (represented.detachedRings root (by simp [inRest])).2⟩
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    change state.present vertex ≠ 0 ↔ _
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)







































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

/-- The detached list is ghost bookkeeping: all its roots have self-rings. -/
theorem SplitRepresented.perm_detached {state : Snapshot} {pending before after : Forest}
    (represented : SplitRepresented state pending before) (permutation : after.Perm before) :
    SplitRepresented state pending after := by
  have whole := permutation.append_left pending
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, represented.pendingRing, ?_, ?_, ?_, ?_, represented.cursor⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · intro root member
    exact represented.detachedRings root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)

/-- Pending root lists may be rotated to expose the actual cursor. -/
theorem SplitRepresented.rotate_pending {state : Snapshot} {front back detached : Forest}
    (represented : SplitRepresented state (front ++ back) detached) :
    SplitRepresented state (back ++ front) detached := by
  have rotation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have whole := rotation.append_right detached
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, ?_, represented.detachedRings, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · simpa only [List.map_append] using Rings.RingOrEmpty.rotate_append
      (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.pendingRing)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.cursor with ⟨empty, pointer⟩ | ⟨root, member, pointer⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, rotation.mem_iff.mpr member, pointer⟩

/-- Updating scratch buckets changes no represented node or pending pointer. -/
theorem SplitRepresented.table_write {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (degree vertex : Int) :
    SplitRepresented {state with table := Rings.write state.table degree vertex} pending detached := by
  refine ⟨represented.valid, ?_, represented.pendingRing, represented.detachedRings,
    represented.nonnegative, represented.presence, represented.size, represented.cursor⟩
  intro root member
  apply (represented.stored root member).frame
  · intros; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩






theorem Buckets.perm {state : Snapshot} {before after : Forest} (buckets : Buckets state before)
    (permutation : after.Perm before) : Buckets state after := by
  refine ⟨(permutation.map Node.degree).nodup_iff.mpr buckets.unique, ?_, ?_, ?_⟩
  · intro root member
    exact buckets.read root (permutation.mem_iff.mp member)
  · intro degree occupied
    obtain ⟨root, member, same, read⟩ := buckets.complete degree occupied
    exact ⟨root, permutation.mem_iff.mpr member, same, read⟩
  · intro root member
    exact buckets.nonnegative root (permutation.mem_iff.mp member)

theorem Buckets.congr {before after : Snapshot} {roots : Forest} (buckets : Buckets before roots)
    (same : after.table = before.table) : Buckets after roots := by
  refine ⟨buckets.unique, ?_, ?_, buckets.nonnegative⟩
  · intro root member
    simpa only [same] using buckets.read root member
  · intro degree occupied
    simpa only [same] using buckets.complete degree (same ▸ occupied)

/-- Clearing the selected bucket removes exactly its root from scratch storage. -/
theorem Buckets.remove_head {state : Snapshot} {root : Node} {rest : Forest}
    (buckets : Buckets state (root :: rest)) :
    Buckets {state with table := Rings.write state.table root.degree (-1)} rest := by
  have separate := (List.nodup_cons.mp buckets.unique).1
  refine ⟨(List.nodup_cons.mp buckets.unique).2, ?_, ?_, ?_⟩
  · intro other member
    have different : (other.degree : Int) ≠ root.degree := by
      intro same
      have equal : other.degree = root.degree := by omega
      exact separate (List.mem_map.mpr ⟨other, member, equal⟩)
    simpa only [Rings.write, if_neg different] using buckets.read other (by simp [member])
  · intro degree occupied
    have different : degree ≠ root.degree := by
      intro same
      simp [Rings.write, same] at occupied
    change 0 ≤ Rings.write state.table root.degree (-1) degree at occupied
    rw [Rings.write, if_neg different] at occupied
    obtain ⟨other, member, readDegree, readVertex⟩ := buckets.complete degree occupied
    rcases List.mem_cons.mp member with rfl | tail
    · exact False.elim (different readDegree.symm)
    · exact ⟨other, tail, readDegree, by simpa only [Rings.write, if_neg different] using readVertex⟩
  · intro other member
    exact buckets.nonnegative other (by simp [member])

/-- An empty bucket accepts a root and preserves degree uniqueness. -/
theorem Buckets.insert {state : Snapshot} {roots : Forest} (buckets : Buckets state roots)
    (root : Node) (nonnegative : 0 ≤ root.vertex) (empty : state.table root.degree < 0) :
    Buckets {state with table := Rings.write state.table root.degree root.vertex} (root :: roots) := by
  have fresh : root.degree ∉ roots.map Node.degree := by
    rintro member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    have read := buckets.read other member
    have positive := buckets.nonnegative other member
    rw [same] at read
    omega
  refine ⟨List.nodup_cons.mpr ⟨fresh, buckets.unique⟩, ?_, ?_, ?_⟩
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · simp [Rings.write]
    · have different : (other.degree : Int) ≠ root.degree := by
        intro same
        have equal : other.degree = root.degree := by omega
        exact fresh (List.mem_map.mpr ⟨other, member, equal⟩)
      simpa only [Rings.write, if_neg different] using buckets.read other member
  · intro degree occupied
    by_cases same : degree = root.degree
    · refine ⟨root, by simp, same.symm, ?_⟩
      simp [Rings.write, same]
    · change 0 ≤ Rings.write state.table root.degree root.vertex degree at occupied
      rw [Rings.write, if_neg same] at occupied
      obtain ⟨other, member, readDegree, readVertex⟩ := buckets.complete degree occupied
      exact ⟨other, by simp [member], readDegree, by simpa only [Rings.write, if_neg same] using readVertex⟩
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact nonnegative
    · exact buckets.nonnegative other member

/-- An occupied degree identifies a root that can be moved to the head of the
    detached list without affecting the physical forest. -/
theorem Buckets.find {state : Snapshot} {roots : Forest} (buckets : Buckets state roots)
    (degree : Int) (occupied : 0 ≤ state.table degree) :
    ∃ root rest, (root :: rest).Perm roots ∧ (root.degree : Int) = degree ∧
      root.vertex = state.table degree ∧ roots.length = rest.length + 1 := by
  obtain ⟨root, member, same, pointer⟩ := buckets.complete degree occupied
  obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
  refine ⟨root, front ++ back, ?_, same, pointer, ?_⟩
  · rw [located]
    exact List.perm_middle.symm
  · simp [located, Nat.add_assoc]





theorem Forest.marks_perm {before after : Forest} (permutation : after.Perm before) :
    after.marks = before.marks := by
  unfold Forest.marks
  exact (permutation.map Node.marks).sum_nat

theorem Forest.link_marks {pending rest : Forest} {parent child : Node}
    (unmarked : child.marked = false) :
    (pending ++ parent.link child :: rest).marks = (pending ++ parent :: child :: rest).marks := by
  have linked : (parent.link child).marks = parent.marks + child.marks := by
    simpa only [unmarked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using parent.link_marks child
  simp only [Forest.marks, List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, linked]
  omega
theorem Forest.entries_perm {before after : Forest} (permutation : after.Perm before) :
    after.entries.Perm before.entries := by
  exact List.Perm.flatMap_right Node.entries permutation

theorem Forest.link_entries {pending rest : Forest} {parent child : Node} :
    (pending ++ parent.link child :: rest).entries.Perm
      (pending ++ parent :: child :: rest).entries := by
  simpa only [Forest.entries, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
    (parent.link_entries child).append_right rest.entries |>.append_left pending.entries








/-- One occupied bucket is consumed and one tree degree increases. The pending
    root ring and complete ranked forest are preserved by the actual writes. -/
theorem SplitRepresented.collide {state : Snapshot} {pending buckets : Forest} {current : Node}
    (represented : SplitRepresented state pending (current :: buckets))
    (table : Buckets state buckets) (occupied : 0 ≤ state.table current.degree) :
    ∃ result remaining,
      SplitRepresented (state.collision current.vertex current.degree) pending (result :: remaining) ∧
      Buckets (state.collision current.vertex current.degree) remaining ∧
      result.vertex = state.collisionParent current.vertex current.degree ∧
      result.degree = current.degree + 1 ∧ buckets.length = remaining.length + 1 ∧
      (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
      (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
  obtain ⟨other, remaining, permutation, equalDegree, pointer, shorter⟩ := table.find current.degree occupied
  have degrees : other.degree = current.degree := by omega
  have arranged := (permutation.cons current).append_left pending
  have ordered := represented.perm_detached (permutation.cons current)
  have otherTable := table.perm permutation
  have cleared := ordered.table_write current.degree (-1)
  have currentStored := ordered.stored current (by simp)
  have otherStored := ordered.stored other (by simp)
  have currentKey := currentStored.root_key
  have otherKey := otherStored.root_key
  have reduced : Buckets {state with table := Rings.write state.table current.degree (-1)} remaining := by
    simpa only [degrees] using otherTable.remove_head
  by_cases smaller : other.key < current.key
  · have switched := cleared.perm_detached (List.Perm.swap current other remaining)
    have linked := switched.link (Int.le_of_lt smaller) degrees
    refine ⟨other.link current, remaining, ?_, ?_, ?_, ?_, shorter, ?_, ?_⟩
    · simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using linked
    · have carried := reduced.congr (after :=
        ({state with table := Rings.write state.table current.degree (-1)} : Snapshot).link current.vertex other.vertex) rfl
      simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using carried
    · simp only [Node.link_vertex, Snapshot.collisionParent, ← pointer, currentKey, otherKey, smaller, ↓reduceIte]
    · simp [degrees]
    · exact Forest.link_entries.trans (Forest.entries_perm
        (((List.Perm.swap current other remaining).append_left pending).trans arranged))
    · exact (Forest.link_marks (ordered.valid.2.2.2 current (by simp))).trans
        (Forest.marks_perm (((List.Perm.swap current other remaining).append_left pending).trans arranged))
  · have winner : current.key ≤ other.key := by omega
    have linked := cleared.link winner degrees.symm
    refine ⟨current.link other, remaining, ?_, ?_, ?_, by simp, shorter, ?_, ?_⟩
    · simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using linked
    · have carried := reduced.congr (after :=
        ({state with table := Rings.write state.table current.degree (-1)} : Snapshot).link other.vertex current.vertex) rfl
      simpa only [Snapshot.collision, ← pointer, currentKey, otherKey, smaller, ↓reduceIte] using carried
    · simp only [Node.link_vertex, Snapshot.collisionParent, ← pointer, currentKey, otherKey, smaller, ↓reduceIte]
    · exact Forest.link_entries.trans (Forest.entries_perm arranged)
    · exact (Forest.link_marks (ordered.valid.2.2.2 other (by simp))).trans (Forest.marks_perm arranged)




/-- The actual collision loop terminates because every link consumes one
    occupied bucket. No external bound or pre-supplied collision trace is needed. -/
theorem SplitRepresented.resolve_collisions {state : Snapshot} {pending buckets : Forest} {current : Node}
    (represented : SplitRepresented state pending (current :: buckets))
    (table : Buckets state buckets) :
    ∃ after result remaining links,
      BucketCollisions state current.vertex current.degree after result.vertex result.degree links ∧
      SplitRepresented after pending (result :: remaining) ∧ Buckets after remaining ∧
      after.table result.degree < 0 ∧ links + remaining.length = buckets.length ∧
      (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
      (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
  have terminate : ∀ count : Nat, ∀ state current buckets,
      buckets.length = count → SplitRepresented state pending (current :: buckets) → Buckets state buckets →
      ∃ after result remaining links,
        BucketCollisions state current.vertex current.degree after result.vertex result.degree links ∧
        SplitRepresented after pending (result :: remaining) ∧ Buckets after remaining ∧
        after.table result.degree < 0 ∧ links + remaining.length = buckets.length ∧
        (pending ++ result :: remaining).entries.Perm (pending ++ current :: buckets).entries ∧
        (pending ++ result :: remaining).marks = (pending ++ current :: buckets).marks := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro before root entries size valid table
      by_cases empty : before.table root.degree < 0
      · exact ⟨before, root, entries, 0, .done _ _ _ empty, valid, table, empty, by simp, .refl _, rfl⟩
      have occupied : 0 ≤ before.table root.degree := by omega
      obtain ⟨next, rest, represented, nextTable, vertex, degree, shorter, stepEntries, stepMarks⟩ := valid.collide table occupied
      have smaller : rest.length < count := by omega
      obtain ⟨after, result, remaining, links, execution, finalValid, finalTable, unused, accounted, tailEntries, tailMarks⟩ :=
        ih rest.length smaller (before.collision root.vertex root.degree) next rest rfl represented nextTable
      refine ⟨after, result, remaining, links + 1, ?_, finalValid, finalTable, unused, by omega, tailEntries.trans stepEntries, tailMarks.trans stepMarks⟩
      apply BucketCollisions.step occupied
      simpa only [vertex, degree, Int.natCast_add, Int.natCast_one] using execution
  exact terminate buckets.length state current buckets rfl represented table









theorem ScratchBound.collision {state : Snapshot} {maximum : Int} (bound : ScratchBound state maximum)
    (vertex degree : Int) : ScratchBound (state.collision vertex degree) maximum := by
  intro index above
  rw [Snapshot.collision_table]
  unfold Rings.write
  split
  · omega
  · exact bound index above

theorem BucketCollisions.size {before after : Snapshot} {vertex degree result finalDegree : Int} {links : Nat}
    (execution : BucketCollisions before vertex degree after result finalDegree links) : after.size = before.size := by
  induction execution with
  | done => rfl
  | step occupied rest ih => exact ih.trans (Snapshot.collision_size _ _ _)

theorem BucketCollisions.scratch_bound {before after : Snapshot} {vertex degree result finalDegree maximum : Int} {links : Nat}
    (execution : BucketCollisions before vertex degree after result finalDegree links)
    (bound : ScratchBound before maximum) : ScratchBound after maximum := by
  induction execution with
  | done => exact bound
  | step occupied rest ih => exact ih (bound.collision _ _)

theorem ScratchBound.store {state : Snapshot} {maximum : Int} (bound : ScratchBound state maximum)
    (vertex degree : Int) :
    ScratchBound {state with table := Rings.write state.table degree vertex} (max maximum degree) := by
  intro index above
  have different : index ≠ degree := by omega
  simpa only [Rings.write, if_neg different] using bound index (by omega)

/-- A common finite size bounds every current tree, including trees produced
    during consolidation rather than only the final degree buckets. -/
theorem SplitRepresented.degree_bound {state : Snapshot} {pending detached : Forest} {root : Node}
    (represented : SplitRepresented state pending detached) (member : root ∈ pending ++ detached)
    (size : Nat) (readSize : state.size = size) : root.degree ≤ 2 * size.log2 + 1 := by
  have included : root.entries.length ≤ (Forest.entries (pending ++ detached)).length := by
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    rw [located]
    simp [Forest.entries, List.flatMap_append]
    omega
  have length : (Forest.entries (pending ++ detached)).length = size := by
    have storedSize := represented.size
    omega
  have ranked := represented.valid.2.2.1 root member
  have bound := ranked.shape_ranked.degree_bound_of_size
    (by simpa only [Node.shape_size, length] using included)
  simpa only [Node.shape_degree] using bound



/-- Starting from a finite represented pending forest and exact scratch table,
    every pending root is consumed once. All final roots have distinct degrees,
    the largest encountered degree is logarithmic, and links reduce root count. -/
theorem SplitRepresented.consume_roots {state : Snapshot} {pending buckets : Forest}
    (represented : SplitRepresented state pending buckets) (table : Buckets state buckets)
    (maximum : Int) (bound : ScratchBound state maximum) (size : Nat) (readSize : state.size = size)
    (maximumBound : maximum ≤ 2 * size.log2 + 1) :
    ∃ after finalBuckets finalMaximum links,
      RootConsumption state maximum after finalMaximum pending.length links ∧
      SplitRepresented after [] finalBuckets ∧ Buckets after finalBuckets ∧
      ScratchBound after finalMaximum ∧ finalMaximum ≤ 2 * size.log2 + 1 ∧
      links + finalBuckets.length = pending.length + buckets.length ∧ after.size = size ∧
      finalBuckets.entries.Perm (pending ++ buckets).entries ∧
      finalBuckets.marks = (pending ++ buckets).marks := by
  have terminate : ∀ count : Nat, ∀ before pending buckets maximum,
      pending.length = count → SplitRepresented before pending buckets → Buckets before buckets →
      ScratchBound before maximum → before.size = size → maximum ≤ 2 * size.log2 + 1 →
      ∃ after finalBuckets finalMaximum links,
        RootConsumption before maximum after finalMaximum pending.length links ∧
        SplitRepresented after [] finalBuckets ∧ Buckets after finalBuckets ∧
        ScratchBound after finalMaximum ∧ finalMaximum ≤ 2 * size.log2 + 1 ∧
        links + finalBuckets.length = pending.length + buckets.length ∧ after.size = size ∧
        finalBuckets.entries.Perm (pending ++ buckets).entries ∧
        finalBuckets.marks = (pending ++ buckets).marks := by
    intro count
    induction count using Nat.strongRecOn with
    | ind count ih =>
      intro before pending buckets maximum length valid table bound readSize maximumBound
      rcases valid.cursor with ⟨empty, pointer⟩ | ⟨root, member, pointer⟩
      · subst pending
        exact ⟨before, buckets, maximum, 0, .done _ _ (by omega), valid, table, bound,
          maximumBound, by simp, readSize, .refl _, rfl⟩
      · obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
        have rotated : SplitRepresented before (root :: (back ++ front)) buckets := by
          have rotate := (located ▸ valid).rotate_pending
          simpa only [List.cons_append] using rotate
        have smaller : (back ++ front).length < count := by
          simp only [located, List.length_append, List.length_cons] at length
          simp only [List.length_append]
          omega
        have rearranged : ((back ++ front) ++ root :: buckets).Perm (pending ++ buckets) := by
          have rotate : (root :: (back ++ front)).Perm pending := by
            rw [located]
            simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
          exact List.perm_middle.trans (by simpa only [List.cons_append] using rotate.append_right buckets)
        have detached := rotated.detach_head pointer
        have detachedTable : Buckets before.detachMinimum buckets := table.congr rfl
        obtain ⟨merged, result, remaining, links, collisions, mergedValid, mergedTable, emptyBucket, linkCount, collisionEntries, collisionMarks⟩ :=
          detached.resolve_collisions detachedTable
        have initialDegree : before.detachMinimum.degrees root.vertex = root.degree :=
          (rotated.stored root (by simp)).root_degree
        have collisionRun : BucketCollisions before.detachMinimum before.minimum
            (before.detachMinimum.degrees before.minimum) merged result.vertex result.degree links := by
          simpa only [pointer, initialDegree] using collisions
        have inputNonnegative := rotated.nonnegative root.vertex root.key
          (List.mem_flatMap.mpr ⟨root, by simp, root.root_entry⟩)
        have nodeNonnegative := mergedValid.nonnegative result.vertex result.key
          (List.mem_flatMap.mpr ⟨result, by simp, result.root_entry⟩)
        have prepared := mergedValid.table_write result.degree result.vertex
        have preparedTable := mergedTable.insert result nodeNonnegative emptyBucket
        have sizeSame : merged.size = size := collisions.size.trans readSize
        have currentDegree := mergedValid.degree_bound (root := result) (by simp) size sizeSame
        have beforeBound : ScratchBound before.detachMinimum maximum := bound
        have preparedBound := (collisions.scratch_bound beforeBound).store result.vertex result.degree
        have preparedMaximum : max maximum (result.degree : Int) ≤ 2 * size.log2 + 1 := by omega
        obtain ⟨after, finalBuckets, finalMaximum, tailLinks, rest, finalValid, finalTable, finalBound,
            finalMaximumBound, accounting, finalSize, tailEntries, tailMarks⟩ :=
          ih _ smaller {merged with table := Rings.write merged.table result.degree result.vertex}
            (back ++ front) (result :: remaining) (max maximum result.degree) rfl prepared preparedTable
            preparedBound sizeSame preparedMaximum
        refine ⟨after, finalBuckets, finalMaximum, links + tailLinks, ?_, finalValid, finalTable,
          finalBound, finalMaximumBound, ?_, finalSize,
          tailEntries.trans (collisionEntries.trans (Forest.entries_perm rearranged)),
          tailMarks.trans (collisionMarks.trans (Forest.marks_perm rearranged))⟩
        · have run := RootConsumption.step (before := before) (by omega : 0 ≤ before.minimum) collisionRun rest
          have number : (back ++ front).length + 1 = pending.length := by
            simp only [located, List.length_append, List.length_cons]
            omega
          simpa only [number] using run
        · simp only [List.length_cons, List.length_append] at accounting
          have number : pending.length = back.length + front.length + 1 := by
            simp only [located, List.length_append, List.length_cons]
            omega
          omega
  exact terminate pending.length state pending buckets maximum rfl represented table bound readSize maximumBound


end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {pending buckets : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.SplitRepresented state pending buckets →
        Algo2Lean.Fibonacci.Buckets state buckets →
          ∀ (maximum : Int),
            Algo2Lean.Fibonacci.ScratchBound state maximum →
              ∀ (size : Nat),
                Eq.{1} state.size (↑size : Int) →
                  LE.le.{0} maximum
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Int) (↑size.log2 : Int))
                        (1 : Int)) →
                    Exists.{1} fun after =>
                      Exists.{1} fun finalBuckets =>
                        Exists.{1} fun finalMaximum =>
                          Exists.{1} fun links =>
                            Algo2Lean.Fibonacci.RootConsumption state maximum after finalMaximum
                                (List.length.{0} pending) links ∧
                              Algo2Lean.Fibonacci.SplitRepresented after List.nil.{0} finalBuckets ∧
                                Algo2Lean.Fibonacci.Buckets after finalBuckets ∧
                                  Algo2Lean.Fibonacci.ScratchBound after finalMaximum ∧
                                    LE.le.{0} finalMaximum
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (2 : Int) (↑size.log2 : Int))
                                          (1 : Int)) ∧
                                      Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} finalBuckets))
                                          (HAdd.hAdd.{0, 0, 0} (List.length.{0} pending)
                                            (List.length.{0} buckets)) ∧
                                        Eq.{1} after.size (↑size : Int) ∧
                                          List.Perm.{0} finalBuckets.entries
                                              (HAppend.hAppend.{0, 0, 0} pending buckets).entries ∧
                                            Eq.{1} finalBuckets.marks
                                              (HAppend.hAppend.{0, 0, 0} pending buckets).marks :=
  Algo2Lean.Fibonacci.SplitRepresented.consume_roots
