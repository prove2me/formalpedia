-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part06
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part06
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T14:09:04.500215+00:00
-- url     : https://prove2.me/theorems/7b607b8d-b382-47a0-9578-9d0d943e0af5
-- title:
--   Rural postman algorithm — Euler traversal and original-link occurrence encoding
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for euler traversal and original-link occurrence encoding in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part05

/-! runtime/EulerCursor.lean -/
section RppSource_EulerCursor
namespace VehicleRoutingSurvey.Routing

/-- The stack lists incoming traversals from its top backward. The already
popped traversals form an output suffix. While exploring a detour, the top
vertex can differ from the start of that suffix. -/
structure EulerCursor {G : Network} (edges : List (Fin G.q))
    (root current outputStart : Fin G.n) where
  stack : List (Traversal G)
  output : List (Traversal G)
  unused : List (Fin G.q)
  stackPath : IsPath G root stack.reverse current
  outputPath : IsPath G outputStart output root
  covers : (output.map Prod.fst ++ (stack.reverse.map Prod.fst ++ unused)).Perm edges
  exhausted : ∀ step ∈ output, ¬ EdgeSupport G unused (finish G step)

def EulerCursor.initial {G : Network} (edges : List (Fin G.q))
    (root : Fin G.n) : EulerCursor edges root root root where
  stack := []
  output := []
  unused := edges
  stackPath := rfl
  outputPath := rfl
  covers := .refl _
  exhausted := by simp

def EulerCursor.push {G : Network} {edges : List (Fin G.q)}
    {root current outputStart : Fin G.n} (c : EulerCursor edges root current outputStart)
    (t : Traversal G) (present : t.1 ∈ c.unused)
    (step : IsPath G current [t] (finish G t)) : EulerCursor edges root (finish G t) outputStart where
  stack := t :: c.stack
  output := c.output
  unused := c.unused.erase t.1
  stackPath := by simpa only [List.reverse_cons] using isPath_append c.stackPath step
  outputPath := c.outputPath
  covers := by
    have consumes := ((List.perm_cons_erase present).symm.append_left
      (c.stack.reverse.map Prod.fst)).append_left (c.output.map Prod.fst)
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using consumes.trans c.covers
  exhausted := fun step used ⟨e, he, incident⟩ =>
    c.exhausted step used ⟨e, List.mem_of_mem_erase he, incident⟩

private theorem splitTraversalPath {G : Network} {u v : Fin G.n}
    {xs ys : List (Traversal G)} (path : IsPath G u (xs ++ ys) v) :
    ∃ w, IsPath G u xs w ∧ IsPath G w ys v := by
  induction xs generalizing u with
  | nil => exact ⟨u, rfl, path⟩
  | cons t rest ih =>
    obtain ⟨w, first, last⟩ := ih path.2.2
    exact ⟨w, ⟨path.1, path.2.1, first⟩, last⟩

def EulerCursor.pop {G : Network} {edges : List (Fin G.q)}
    {root current : Fin G.n} (c : EulerCursor edges root current current)
    (t : Traversal G) (rest : List (Traversal G)) (top : c.stack = t :: rest)
    (stuck : ¬ EdgeSupport G c.unused current) : EulerCursor edges root (start G t) (start G t) := by
  have together : IsPath G root (rest.reverse ++ [t]) current := by
    simpa only [top, List.reverse_cons] using c.stackPath
  have edge : IsPath G root rest.reverse (start G t) ∧ IsPath G (start G t) [t] current := by
    obtain ⟨mid, first, last⟩ := splitTraversalPath together
    have equal : mid = start G t := last.1
    exact ⟨equal ▸ first, equal ▸ last⟩
  refine ⟨rest, t :: c.output, c.unused, edge.1, ?_, ?_, ?_⟩
  · exact isPath_append edge.2 c.outputPath
  · simpa only [List.map_cons, List.cons_append, List.append_assoc] using
        (List.perm_middle (a := t.1) (l₁ := c.output.map Prod.fst ++ rest.reverse.map Prod.fst)
          (l₂ := c.unused)).symm.trans (by
            simpa only [top, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.singleton_append] using c.covers)
  · intro step present
    rcases List.mem_cons.mp present with first | old
    · have equal : finish G step = current := (congrArg (finish G) first).trans edge.2.2.2
      exact equal.symm ▸ stuck
    · exact c.exhausted step old

/-- This counts the successful stack operations still to be done. Unused
occurrences have yet to be pushed and popped. Stack entries only need a pop. -/
def EulerCursor.work {G : Network} {edges : List (Fin G.q)}
    {root current outputStart : Fin G.n} (c : EulerCursor edges root current outputStart) : ℕ :=
  2 * c.unused.length + c.stack.length

@[simp] theorem EulerCursor.push_work {G : Network} {edges : List (Fin G.q)}
    {root current outputStart : Fin G.n} (c : EulerCursor edges root current outputStart)
    (t : Traversal G) (present : t.1 ∈ c.unused) (step : IsPath G current [t] (finish G t)) :
    (c.push t present step).work + 1 = c.work := by
  have size := (List.perm_cons_erase present).length_eq
  simp only [List.length_cons] at size
  simp only [work, push, List.length_cons]
  omega

@[simp] theorem EulerCursor.pop_work {G : Network} {edges : List (Fin G.q)}
    {root current : Fin G.n} (c : EulerCursor edges root current current)
    (t : Traversal G) (rest : List (Traversal G)) (top : c.stack = t :: rest)
    (stuck : ¬ EdgeSupport G c.unused current) : (c.pop t rest top stuck).work + 1 = c.work := by
  simp [work, pop, top, Nat.add_assoc]

theorem EulerCursor.stuck_at_outputStart {G : Network} {edges : List (Fin G.q)}
    {root current outputStart : Fin G.n} (c : EulerCursor edges root current outputStart)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (stuck : ¬ EdgeSupport G c.unused current) : current = outputStart := by
  by_contra distinct
  have openPath := isPath_append c.outputPath c.stackPath
  have odd := degree_openPath_mod_two_at_finish openPath (Ne.symm distinct)
  have permuted := degree_eq_of_perm c.covers current
  have noDegree : degree G c.unused current = 0 :=
    degree_eq_zero_of_no_incident _ _ fun e he =>
      ⟨fun tail => stuck ⟨e, he, Or.inl tail⟩, fun head => stuck ⟨e, he, Or.inr head⟩⟩
  rw [List.map_append, degree_append] at odd
  rw [degree_append, degree_append, noDegree, Nat.add_zero] at permuted
  exact Nat.zero_ne_one (by rwa [permuted, even current] at odd)

/-- Once the stack is empty and the root has no unused edge, the suffix
is an Euler circuit, provided the original occurrence support is connected. -/
theorem EulerCursor.finished {G : Network} {edges : List (Fin G.q)}
    {root current outputStart : Fin G.n} (c : EulerCursor edges root current outputStart)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (connected : EdgeSupportConnected G edges) (supported : EdgeSupport G edges root)
    (emptyStack : c.stack = []) (stuck : ¬ EdgeSupport G c.unused current) :
    IsPath G root c.output root ∧ (c.output.map Prod.fst).Perm edges := by
  have currentRoot : root = current := by simpa [emptyStack, IsPath] using c.stackPath
  have rootStart : root = outputStart := currentRoot.trans (c.stuck_at_outputStart even stuck)
  have path : IsPath G root c.output root := by simpa only [rootStart] using c.outputPath
  have covers : (c.output.map Prod.fst ++ c.unused).Perm edges := by simpa [emptyStack] using c.covers
  have exhausted (v : Fin G.n) (seen : v ∈ pathVertices G root c.output) :
      ¬ EdgeSupport G c.unused v := by
    rcases List.mem_cons.mp seen with rfl | visited
    · simpa only [currentRoot] using stuck
    · obtain ⟨step, present, rfl⟩ := List.mem_map.mp visited
      exact c.exhausted step present
  have follows {u v : Fin G.n} (step : EdgeAdjacent G edges u v)
      (seen : u ∈ pathVertices G root c.output) : v ∈ pathVertices G root c.output := by
    obtain ⟨e, present, direction⟩ := step
    have notUnused : e ∉ c.unused := fun he =>
      exhausted u seen ⟨e, he, direction.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
    have used := (List.mem_append.mp (covers.mem_iff.mpr present)).resolve_right notUnused
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp used
    have startSeen : start G t ∈ pathVertices G root c.output := List.mem_toFinset.mp
      ((pathVertices_toFinset root c.output).symm ▸ traversal_start_visited path t ht)
    have finishSeen : finish G t ∈ pathVertices G root c.output :=
      List.mem_cons_of_mem root (List.mem_map_of_mem ht)
    have endpoints : G.tail t.1 ∈ pathVertices G root c.output ∧
        G.head t.1 ∈ pathVertices G root c.output := by
      cases orient : t.2
      · exact ⟨by simpa [finish, orient] using finishSeen, by simpa [start, orient] using startSeen⟩
      · exact ⟨by simpa [start, orient] using startSeen, by simpa [finish, orient] using finishSeen⟩
    exact direction.elim (fun h => h.2 ▸ endpoints.2) (fun h => h.2 ▸ endpoints.1)
  have visited {v : Fin G.n} (reach : Relation.ReflTransGen (EdgeAdjacent G edges) root v) :
      v ∈ pathVertices G root c.output := by
    induction reach with
    | refl => exact List.mem_cons_self
    | tail _ edge ih => exact follows edge ih
  have unusedEmpty : c.unused = [] := by
    by_contra remaining
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ remaining
    have original := covers.mem_iff.mp (List.mem_append.mpr (Or.inr he))
    have reached := connected root supported (G.tail e) ⟨e, original, Or.inl rfl⟩
    exact exhausted _ (visited reached) ⟨e, he, Or.inl rfl⟩
  exact ⟨path, by simpa [unusedEmpty] using covers⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerCursor

/-! runtime/EulerOccurrences.lean -/
section RppSource_EulerOccurrences
namespace VehicleRoutingSurvey.Routing

abbrev EulerDart (m : ℕ) := Fin m × Bool

def eulerTraversalOf {G : Network} (edges : List (Fin G.q)) (dart : EulerDart edges.length) :
    Traversal G :=
  (edges.get dart.1, dart.2)

/-- Use occurrence indices for activity, since one original link can occur
several times in the augmented network. Each unused occurrence has both
of its darts in their respective incident lists. -/
structure EulerOccurrences {G : Network} (edges : List (Fin G.q)) where
  live : List (Fin edges.length)
  incident : Fin G.n → List (EulerDart edges.length)
  liveNodup : live.Nodup
  atSource : ∀ v d, d ∈ incident v → start G (eulerTraversalOf edges d) = v
  available : ∀ d, d.1 ∈ live → d ∈ incident (start G (eulerTraversalOf edges d))

def EulerOccurrences.initial {G : Network} (edges : List (Fin G.q)) :
    EulerOccurrences edges where
  live := List.finRange edges.length
  incident v := ((List.finRange edges.length).flatMap fun i => [(i, true), (i, false)]).filter
    (fun d => decide (start G (eulerTraversalOf edges d) = v))
  liveNodup := List.nodup_finRange _
  atSource := fun _ _ h => of_decide_eq_true (List.mem_filter.mp h).2
  available := by
    rintro ⟨i, dir⟩ hi
    exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨i, hi, by cases dir <;> simp⟩, by simp⟩

theorem EulerOccurrences.initial_live {G : Network} (edges : List (Fin G.q)) :
    ((EulerOccurrences.initial edges).live.map edges.get) = edges := by
  simpa [initial, List.finRange, List.map_ofFn, Function.comp_def] using
    (List.ofFn_get (l := edges))

def EulerOccurrences.drop {G : Network} {edges : List (Fin G.q)} (a : EulerOccurrences edges)
    (v : Fin G.n) (dart : EulerDart edges.length) (rest : List (EulerDart edges.length))
    (head : a.incident v = dart :: rest) : EulerOccurrences edges where
  live := a.live.erase dart.1
  incident := Function.update a.incident v rest
  liveNodup := a.liveNodup.erase _
  atSource := by
    intro w d present
    by_cases equal : w = v
    · subst w
      rw [Function.update_self] at present
      exact a.atSource _ _ (by rw [head]; exact List.mem_cons_of_mem _ present)
    · exact a.atSource _ _ (by simpa [Function.update_of_ne equal] using present)
  available := by
    intro d remaining
    obtain ⟨distinct, old⟩ := a.liveNodup.mem_erase_iff.mp remaining
    have present := a.available d old
    by_cases equal : start G (eulerTraversalOf edges d) = v
    · rw [equal, Function.update_self]
      rw [equal, head] at present
      exact (List.mem_cons.mp present).resolve_left (fun h => distinct (congrArg Prod.fst h))
    · simpa [Function.update_of_ne equal] using present

theorem EulerOccurrences.no_support_of_empty {G : Network} {edges : List (Fin G.q)}
    (a : EulerOccurrences edges) {v : Fin G.n} (empty : a.incident v = []) :
    ¬ EdgeSupport G (a.live.map edges.get) v := by
  rintro ⟨e, used, incident⟩
  obtain ⟨i, alive, rfl⟩ := List.mem_map.mp used
  rcases incident with tail | head
  · have dart : (i, true) ∈ a.incident (G.tail (edges.get i)) := a.available (i, true) alive
    rw [tail, empty] at dart
    exact List.not_mem_nil dart
  · have dart : (i, false) ∈ a.incident (G.head (edges.get i)) := a.available (i, false) alive
    rw [head, empty] at dart
    exact List.not_mem_nil dart

/-- Converting occurrence indices back to original links commutes with
erasing one live occurrence, even when different indices have equal links. -/
theorem EulerOccurrences.erase_live_perm {G : Network} {edges : List (Fin G.q)}
    (a : EulerOccurrences edges) {unused : List (Fin G.q)} (rel : (a.live.map edges.get).Perm unused)
    {i : Fin edges.length} (alive : i ∈ a.live) :
    ((a.live.erase i).map edges.get).Perm (unused.erase (edges.get i)) := by
  have used := rel.mem_iff.mp (List.mem_map_of_mem (f := edges.get) alive)
  have before := ((List.perm_cons_erase alive).symm.map edges.get).trans rel
  exact (by simpa only [List.map_cons] using before.trans (List.perm_cons_erase used) :
    (edges.get i :: (a.live.erase i).map edges.get).Perm (edges.get i :: unused.erase (edges.get i))).cons_inv

def EulerOccurrences.dartCount {G : Network} {edges : List (Fin G.q)}
    (a : EulerOccurrences edges) : ℕ :=
  ∑ v, (a.incident v).length

theorem EulerOccurrences.drop_dartCount {G : Network} {edges : List (Fin G.q)}
    (a : EulerOccurrences edges) (v : Fin G.n) (dart : EulerDart edges.length)
    (rest : List (EulerDart edges.length)) (head : a.incident v = dart :: rest) :
    (a.drop v dart rest head).dartCount + 1 = a.dartCount := by
  have otherRows :
      (∑ w ∈ (Finset.univ : Finset (Fin G.n)).erase v, (Function.update a.incident v rest w).length) =
        ∑ w ∈ (Finset.univ : Finset (Fin G.n)).erase v, (a.incident w).length := by
    exact Finset.sum_congr rfl (fun w hw => by rw [Function.update_of_ne (Finset.mem_erase.mp hw).1])
  simp only [dartCount, drop]
  rw [← Finset.sum_erase_add Finset.univ (fun w => (Function.update a.incident v rest w).length)
    (Finset.mem_univ v), otherRows,
    ← Finset.sum_erase_add Finset.univ (fun w => (a.incident w).length) (Finset.mem_univ v),
    Function.update_self, head, List.length_cons, Nat.add_assoc]

private theorem sum_partition_size {α : Type*} {n : ℕ} (source : α → Fin n) (items : List α) :
    (∑ v, (items.filter fun d => decide (source d = v)).length) = items.length := by
  induction items with
  | nil => simp
  | cons d rest ih =>
    have count (v : Fin n) :
        ((d :: rest).filter fun d => decide (source d = v)).length =
          (if source d = v then 1 else 0) + (rest.filter fun d => decide (source d = v)).length := by
      by_cases h : source d = v <;> simp [h, Nat.add_comm]
    simp only [count, Finset.sum_add_distrib, ih, List.length_cons]
    simp [eq_comm, Nat.add_comm]

theorem EulerOccurrences.initial_dartCount {G : Network} (edges : List (Fin G.q)) :
    (EulerOccurrences.initial edges).dartCount = 2 * edges.length := by
  rw [dartCount]
  change (∑ v, (((List.finRange edges.length).flatMap fun i => [(i, true), (i, false)]).filter
    (fun d => decide (start G (eulerTraversalOf edges d) = v))).length) = 2 * edges.length
  rw [sum_partition_size]
  simp [List.length_flatMap, Nat.mul_comm]


end VehicleRoutingSurvey.Routing
end RppSource_EulerOccurrences

/-! runtime/EulerTraversal.lean -/
section RppSource_EulerTraversal
namespace VehicleRoutingSurvey.Routing

structure EulerTraversalState {G : Network} (edges : List (Fin G.q)) (root : Fin G.n) where
  current : Fin G.n
  outputStart : Fin G.n
  cursor : EulerCursor edges root current outputStart
  occurrences : EulerOccurrences edges
  agrees : (occurrences.live.map edges.get).Perm cursor.unused

namespace EulerTraversalState

variable {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}

def initial (edges : List (Fin G.q)) (root : Fin G.n) : EulerTraversalState edges root :=
  ⟨root, root, EulerCursor.initial edges root, EulerOccurrences.initial edges,
    by rw [EulerOccurrences.initial_live]; exact .refl _⟩

def done (s : EulerTraversalState edges root) : Prop :=
  s.occurrences.incident s.current = [] ∧ s.cursor.stack = []

/-- Count remaining stack work and the incident-list entries that may need
to be discarded, including entries for already used occurrences. -/
def work (s : EulerTraversalState edges root) : ℕ :=
  s.cursor.work + s.occurrences.dartCount

@[simp] theorem initial_work : (initial edges root).work = 4 * edges.length := by
  simp [initial, work, EulerCursor.initial, EulerCursor.work, EulerOccurrences.initial_dartCount]
  omega

theorem noIncident (s : EulerTraversalState edges root)
    (empty : s.occurrences.incident s.current = []) :
    ¬ EdgeSupport G s.cursor.unused s.current := by
  intro support
  obtain ⟨e, used, incident⟩ := support
  exact s.occurrences.no_support_of_empty empty ⟨e, s.agrees.mem_iff.mpr used, incident⟩

def skip (s : EulerTraversalState edges root) (d : EulerDart edges.length)
    (rest : List (EulerDart edges.length)) (head : s.occurrences.incident s.current = d :: rest)
    (stale : d.1 ∉ s.occurrences.live) : EulerTraversalState edges root :=
  { s with
    occurrences := s.occurrences.drop s.current d rest head
    agrees := by simpa only [EulerOccurrences.drop, List.erase_of_not_mem stale] using s.agrees }

private theorem takeDartPath (s : EulerTraversalState edges root) (undirected : Undirected G)
    (d : EulerDart edges.length) (rest : List (EulerDart edges.length))
    (head : s.occurrences.incident s.current = d :: rest) :
    IsPath G s.current [eulerTraversalOf edges d] (finish G (eulerTraversalOf edges d)) :=
  ⟨(s.occurrences.atSource _ d (by rw [head]; exact List.mem_cons_self)).symm,
    Or.inl (undirected _), rfl⟩

def advance (s : EulerTraversalState edges root) (undirected : Undirected G)
    (d : EulerDart edges.length) (rest : List (EulerDart edges.length))
    (head : s.occurrences.incident s.current = d :: rest)
    (fresh : d.1 ∈ s.occurrences.live) : EulerTraversalState edges root :=
  let t := eulerTraversalOf edges d
  let present : t.1 ∈ s.cursor.unused :=
    s.agrees.mem_iff.mp (List.mem_map_of_mem (f := edges.get) fresh)
  ⟨finish G t, s.outputStart, s.cursor.push t present (s.takeDartPath undirected d rest head),
    s.occurrences.drop s.current d rest head, s.occurrences.erase_live_perm s.agrees fresh⟩

private def popCursor {u a : Fin G.n} (c : EulerCursor edges root u a)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : ¬ EdgeSupport G c.unused u) (t : Traversal G) (rest : List (Traversal G))
    (top : c.stack = t :: rest) : EulerCursor edges root (start G t) (start G t) := by
  have align := c.stuck_at_outputStart even empty
  subst a
  exact c.pop t rest top empty

private theorem popCursor_unused {u a : Fin G.n} (c : EulerCursor edges root u a)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : ¬ EdgeSupport G c.unused u) (t : Traversal G) (rest : List (Traversal G))
    (top : c.stack = t :: rest) : (popCursor c even empty t rest top).unused = c.unused := by
  have align := c.stuck_at_outputStart even empty
  subst a
  rfl

private theorem popCursor_work {u a : Fin G.n} (c : EulerCursor edges root u a)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : ¬ EdgeSupport G c.unused u) (t : Traversal G) (rest : List (Traversal G))
    (top : c.stack = t :: rest) : (popCursor c even empty t rest top).work + 1 = c.work := by
  have align := c.stuck_at_outputStart even empty
  subst a
  exact c.pop_work t rest top empty

private theorem popCursor_stack_output {u a : Fin G.n} (c : EulerCursor edges root u a)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : ¬ EdgeSupport G c.unused u) (t : Traversal G) (rest : List (Traversal G))
    (top : c.stack = t :: rest) :
    (popCursor c even empty t rest top).stack = rest ∧
      (popCursor c even empty t rest top).output = t :: c.output := by
  have align := c.stuck_at_outputStart even empty
  subst a
  exact ⟨rfl, rfl⟩

def backtrack (s : EulerTraversalState edges root)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : s.occurrences.incident s.current = []) (t : Traversal G) (rest : List (Traversal G))
    (top : s.cursor.stack = t :: rest) : EulerTraversalState edges root :=
  ⟨start G t, start G t, popCursor s.cursor even (s.noIncident empty) t rest top, s.occurrences,
    by rw [popCursor_unused]; exact s.agrees⟩

theorem backtrack_stack_output (s : EulerTraversalState edges root)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : s.occurrences.incident s.current = []) (t : Traversal G) (rest : List (Traversal G))
    (top : s.cursor.stack = t :: rest) :
    (s.backtrack even empty t rest top).cursor.stack = rest ∧
      (s.backtrack even empty t rest top).cursor.output = t :: s.cursor.output :=
  popCursor_stack_output s.cursor even (s.noIncident empty) t rest top

def step (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (s : EulerTraversalState edges root) : EulerTraversalState edges root :=
  match head : s.occurrences.incident s.current with
  | [] =>
    match top : s.cursor.stack with
    | [] => s
    | t :: rest => s.backtrack even head t rest top
  | d :: rest =>
    if alive : d.1 ∈ s.occurrences.live then s.advance undirected d rest head alive
    else s.skip d rest head alive

theorem step_progress (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (s : EulerTraversalState edges root) :
    (s.done ∧ step undirected even s = s) ∨ (step undirected even s).work < s.work := by
  unfold step
  split
  · rename_i head
    split
    · exact Or.inl ⟨⟨head, by assumption⟩, rfl⟩
    · rename_i t rest top
      have decreases := popCursor_work s.cursor even (s.noIncident head) t rest top
      apply Or.inr
      simp only [backtrack, work]
      omega
  · rename_i d rest head
    have decreases := s.occurrences.drop_dartCount s.current d rest head
    split
    · rename_i fresh
      have present : (eulerTraversalOf edges d).1 ∈ s.cursor.unused :=
        s.agrees.mem_iff.mp (List.mem_map_of_mem (f := edges.get) fresh)
      have pushes := s.cursor.push_work _ present (s.takeDartPath undirected d rest head)
      apply Or.inr
      simp only [advance, work]
      omega
    · apply Or.inr
      simp only [skip, work]
      omega

theorem iterate_done (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (s : EulerTraversalState edges root) (n : ℕ) (bound : s.work < n) :
    ((step undirected even)^[n] s).done := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rcases step_progress undirected even s with ⟨halted, fixed⟩ | decreases
    · rw [fixed]
      have all (k : ℕ) : (step undirected even)^[k] s = s := by
        induction k with
        | zero => rfl
        | succ k old => rw [Function.iterate_succ_apply', old, fixed]
      rwa [all]
    · exact ih _ (by omega)

theorem output_correct (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (connected : EdgeSupportConnected G edges) (supported : EdgeSupport G edges root) :
    let final := (step undirected even)^[4 * edges.length + 1] (initial edges root)
    IsPath G root final.cursor.output root ∧ (final.cursor.output.map Prod.fst).Perm edges := by
  let final := (step undirected even)^[4 * edges.length + 1] (initial edges root)
  have finished : final.done :=
    iterate_done undirected even _ _ (by simp)
  exact final.cursor.finished even connected supported finished.2 (final.noIncident finished.1)

end EulerTraversalState


end VehicleRoutingSurvey.Routing
end RppSource_EulerTraversal

/-! runtime/EulerTick.lean -/
section RppSource_EulerTick
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- One iteration of the occurrence-stack Euler traversal. Registers 7, 8,
11, 12, and 13 hold the incident-list base, current vertex, stack cursor,
stack base, and output cursor. Register 10 contains zero, register 6
contains one, and registers 14 through 16 contain two through four. -/
def eulerTickBlock : List ArithmeticInstruction :=
  [-- Read the current head. On an empty list, try to pop the stack.
   .natAdd 0 7 8, .natLoad 9 0, .natBranch 9 10 16 3,
   -- Advance the list and read the dart's shared occurrence flag.
   .natLoad 1 9, .natAdd 4 9 15, .natLoad 2 4, .natLoad 3 2,
   .natAdd 4 9 14, .natLoad 4 4, .natStore 0 1, .natBranch 3 10 37 11,
   -- Mark a fresh occurrence used and push this dart.
   .natStore 2 10, .natStore 11 9, .natAdd 11 11 6, .natAdd 8 4 10, .jump 42,
   -- Backtrack over one dart, writing its two output fields from right to left.
   .natBranch 11 12 30 17, .natSub 11 11 6, .natLoad 9 11, .natAdd 0 9 6, .natLoad 8 0,
   .natAdd 0 9 16, .natLoad 1 0, .natAdd 0 0 6, .natLoad 4 0, .natSub 13 13 14,
   .natStore 13 1, .natAdd 0 13 6, .natStore 0 4, .jump 43,
   -- Equalize the instruction count so the block can use the counted loop.
   .jump 31, .jump 32, .jump 33, .jump 34, .jump 35, .jump 36, .jump 37,
   .jump 38, .jump 39, .jump 40, .jump 41, .jump 42, .jump 43]

structure EulerTickView where
  vertex : ℕ
  stackCursor : ℕ
  outputCursor : ℕ
  memory : ℕ → ℕ

def EulerTickView.read (s : ArithmeticState) : EulerTickView :=
  ⟨s.nr 8, s.nr 11, s.nr 13, s.nm⟩

/-- Read all dart and stack fields before writing any cells. Stale darts
advance the incident list, and a finished traversal stays in place. -/
def EulerTickView.next (heads stackBase : ℕ) (view : EulerTickView) : EulerTickView :=
  let head := heads + view.vertex
  let dart := view.memory head
  if dart = 0 then
    if view.stackCursor ≤ stackBase then view
    else
      let stack := view.stackCursor - 1
      let last := view.memory stack
      let output := view.outputCursor - 2
      ⟨view.memory (last + 1), stack, output,
        Function.update (Function.update view.memory output (view.memory (last + 4)))
          (output + 1) (view.memory (last + 5))⟩
  else
    let memory := Function.update view.memory head (view.memory dart)
    let flag := view.memory (dart + 3)
    if view.memory flag = 0 then {view with memory := memory}
    else ⟨view.memory (dart + 2), view.stackCursor + 1, view.outputCursor,
      Function.update (Function.update memory flag 0) view.stackCursor dart⟩

def eulerTickMemory (s : ArithmeticState) : EulerTickView :=
  (EulerTickView.read s).next (s.nr 7) (s.nr 12)

theorem eulerTickBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (two : s.nr 14 = 2)
    (three : s.nr 15 = 3) (four : s.nr 16 = 4) :
    ∃ t, BlockRuns eulerTickBlock 17 s t ∧ t.halted = false ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ [6, 7, 10, 12, 14, 15, 16, 17, 18, 19, 28], t.nr r = s.nr r) ∧
      EulerTickView.read t = eulerTickMemory s := by
  let t := (arithmeticStep eulerTickBlock)^[17] s
  have frame : t.halted = false ∧ t.pc = eulerTickBlock.length ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ [6, 7, 10, 12, 14, 15, 16, 17, 18, 19, 28], t.nr r = s.nr r) ∧
      EulerTickView.read t = eulerTickMemory s := by
    by_cases empty : s.nm (s.nr 7 + s.nr 8) = 0
    · by_cases done : s.nr 11 ≤ s.nr 12 <;>
        simp [t, eulerTickBlock, arithmeticStep, Function.iterate_succ_apply',
          entry, running, one, zero, two, four, empty, done, eulerTickMemory,
          EulerTickView.next, EulerTickView.read, Nat.add_assoc, or_imp, forall_and]
    · by_cases stale : s.nm (s.nm (s.nm (s.nr 7 + s.nr 8) + 3)) = 0 <;>
        simp [t, eulerTickBlock, arithmeticStep, Function.iterate_succ_apply',
          entry, running, one, zero, two, three, empty, stale, eulerTickMemory,
          EulerTickView.next, EulerTickView.read, or_imp, forall_and]
  exact ⟨t, BlockRuns.of_running_exit rfl frame.1 frame.2.1, frame.1, frame.2.2⟩

def eulerTraversalBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 17 18 eulerTickBlock

private structure EulerTraversalInvariant (s : ArithmeticState) (i : ℕ)
    (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 17 = i
  stable : ∀ r ∈ [6, 7, 10, 12, 14, 15, 16, 18, 19, 28], m.nr r = s.nr r
  realMemory : m.rm = s.rm
  realRegisters : m.rr = s.rr
  view : EulerTickView.read m =
    ((EulerTickView.next (s.nr 7) (s.nr 12))^[i]) (EulerTickView.read s)

theorem eulerTraversalBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (two : s.nr 14 = 2)
    (three : s.nr 15 = 3) (four : s.nr 16 = 4) :
    ∃ t, BlockRuns eulerTraversalBlock (1 + (s.nr 18 * 20 + 1)) s t ∧
      t.halted = false ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ [6, 7, 10, 12, 14, 15, 16, 18, 19, 28], t.nr r = s.nr r) ∧
      EulerTickView.read t =
        ((EulerTickView.next (s.nr 7) (s.nr 12))^[s.nr 18]) (EulerTickView.read s) := by
  have initial : EulerTraversalInvariant s 0
      {s with pc := 0, nr := Function.update s.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, by simp [EulerTickView.read]⟩
    intro r member
    have distinct : r ≠ 17 := by rintro rfl; simp at member
    exact Function.update_of_ne distinct _ _
  have control (i : ℕ) (m : ArithmeticState) (inv : EulerTraversalInvariant s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 18 = s.nr 18 :=
    ⟨inv.entry, inv.running, inv.index, inv.stable 18 (by simp)⟩
  have iterate (i : ℕ) (_ : i < s.nr 18) (m : ArithmeticState)
      (inv : EulerTraversalInvariant s i m) :
      ∃ t, BlockRuns eulerTickBlock 17 m t ∧ t.halted = false ∧
        EulerTraversalInvariant s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    obtain ⟨t, run, ready, rm, rr, stable, projection⟩ := eulerTickBlock_correct inv.entry inv.running
      ((inv.stable 6 (by simp)).trans one) ((inv.stable 10 (by simp)).trans zero)
      ((inv.stable 14 (by simp)).trans two) ((inv.stable 15 (by simp)).trans three)
      ((inv.stable 16 (by simp)).trans four)
    have index := (stable 17 (by simp)).trans inv.index
    have increment := ((stable 6 (by simp)).trans (inv.stable 6 (by simp))).trans one
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [index, increment], ?_, rm.trans inv.realMemory,
      rr.trans inv.realRegisters, ?_⟩⟩
    · intro r member
      have distinct : r ≠ 17 := by rintro rfl; simp at member
      exact (Function.update_of_ne distinct _ _).trans
        ((stable r (by simp at member ⊢; tauto)).trans (inv.stable r member))
    · have next := inv.stable 7 (by simp)
      have base := inv.stable 12 (by simp)
      rw [eulerTickMemory, next, base, inv.view] at projection
      simpa [EulerTickView.read, Function.iterate_succ_apply'] using projection
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 17 18 (s.nr 18) 17
    eulerTickBlock (EulerTraversalInvariant s) entry running initial control iterate
  exact ⟨_, run, inv.running, inv.realMemory, inv.realRegisters, inv.stable, inv.view⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerTick

/-! runtime/EulerMemory.lean -/
section RppSource_EulerMemory
namespace VehicleRoutingSurvey.Routing

/-- Cells 2 through 1 + 2m hold the emitted traversals. The working tables
have separate stack, activity, incident-head, and six-cell dart regions. -/
structure EulerLayout (n m : ℕ) where
  stack : ℕ
  active : ℕ
  heads : ℕ
  darts : ℕ
  outputEnd : 2 + 2 * m ≤ stack
  stackEnd : stack + m ≤ active
  activeEnd : active + m ≤ heads
  headEnd : heads + n < darts

def EulerLayout.dartAddress {n m : ℕ} (layout : EulerLayout n m) (d : EulerDart m) : ℕ :=
  layout.darts + 12 * d.1.val + if d.2 then 6 else 0

def EulerLayout.firstDart {n m : ℕ} (layout : EulerLayout n m) : List (EulerDart m) → ℕ
  | [] => 0
  | d :: _ => layout.dartAddress d

theorem EulerLayout.dartAddress_pos {n m : ℕ} (layout : EulerLayout n m) (d : EulerDart m) :
    0 < layout.dartAddress d := by
  have := layout.headEnd
  unfold dartAddress
  omega

def EulerDartChain {n m : ℕ} (layout : EulerLayout n m) (memory : ℕ → ℕ) :
    List (EulerDart m) → Prop
  | [] => True
  | d :: rest => memory (layout.dartAddress d) = layout.firstDart rest ∧
    EulerDartChain layout memory rest

def EulerStackCells {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) : List (Traversal G) → Prop
  | [] => True
  | t :: rest => (∃ d : EulerDart edges.length, eulerTraversalOf edges d = t ∧
      memory (layout.stack + rest.length) = layout.dartAddress d) ∧
    EulerStackCells layout memory rest

def EulerOutputCells {G : Network} (memory : ℕ → ℕ) : ℕ → List (Traversal G) → Prop
  | _, [] => True
  | offset, t :: rest => memory offset = t.1.val ∧
    memory (offset + 1) = (if t.2 then 1 else 0) ∧ EulerOutputCells memory (offset + 2) rest

structure EulerMemory {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    (layout : EulerLayout G.n edges.length) (view : EulerTickView)
    (s : EulerTraversalState edges root) : Prop where
  vertex : view.vertex = s.current.val
  stackCursor : view.stackCursor = layout.stack + s.cursor.stack.length
  outputCursor : view.outputCursor = 2 + 2 * edges.length - 2 * s.cursor.output.length
  headCells : ∀ v : Fin G.n, view.memory (layout.heads + v.val) =
    layout.firstDart (s.occurrences.incident v)
  chains : ∀ v, EulerDartChain layout view.memory (s.occurrences.incident v)
  dartCells : ∀ d : EulerDart edges.length,
    let addr := layout.dartAddress d
    let t := eulerTraversalOf edges d
    view.memory (addr + 1) = (start G t).val ∧
    view.memory (addr + 2) = (finish G t).val ∧
    view.memory (addr + 3) = layout.active + d.1.val ∧
    view.memory (addr + 4) = t.1.val ∧
    view.memory (addr + 5) = (if t.2 then 1 else 0)
  activeCells : ∀ i : Fin edges.length, view.memory (layout.active + i.val) =
    if i ∈ s.occurrences.live then 1 else 0
  stackCells : EulerStackCells (edges := edges) layout view.memory s.cursor.stack
  outputCells : EulerOutputCells view.memory view.outputCursor s.cursor.output

theorem EulerDartChain.of_memory {n m : ℕ} {layout : EulerLayout n m}
    {memory other : ℕ → ℕ} {ds : List (EulerDart m)}
    (chain : EulerDartChain layout memory ds)
    (same : ∀ d, other (layout.dartAddress d) = memory (layout.dartAddress d)) :
    EulerDartChain layout other ds := by
  induction ds with
  | nil => trivial
  | cons d rest ih =>
    exact ⟨(same d).trans chain.1, ih chain.2⟩

theorem EulerStackCells.of_memory {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {memory other : ℕ → ℕ} {stack : List (Traversal G)}
    (old : EulerStackCells (edges := edges) layout memory stack)
    (same : ∀ i < stack.length, other (layout.stack + i) = memory (layout.stack + i)) :
    EulerStackCells (edges := edges) layout other stack := by
  induction stack with
  | nil => trivial
  | cons t rest ih =>
    obtain ⟨⟨d, isDart, address⟩, tail⟩ := old
    exact ⟨⟨d, isDart, (same rest.length (by simp)).trans address⟩,
      ih tail (fun i hi => same i (by simpa using Nat.lt_succ_of_lt hi))⟩

theorem EulerOutputCells.of_memory {G : Network} {memory other : ℕ → ℕ}
    {output : List (Traversal G)} {offset : ℕ}
    (old : EulerOutputCells memory offset output)
    (same : ∀ i < 2 * output.length, other (offset + i) = memory (offset + i)) :
    EulerOutputCells other offset output := by
  induction output generalizing offset with
  | nil => trivial
  | cons t rest ih =>
    have grows : 2 * (t :: rest).length = 2 * rest.length + 2 := by simp [Nat.mul_succ]
    refine ⟨?_, (same 1 (by omega)).trans old.2.1, ih old.2.2 ?_⟩
    · exact (by simpa using same 0 (by omega) : other offset = memory offset).trans old.1
    · intro i hi
      rw [Nat.add_assoc]
      exact same (2 + i) (by omega)

theorem EulerCursor.length_total {G : Network} {edges : List (Fin G.q)}
    {root u a : Fin G.n} (c : EulerCursor edges root u a) :
    c.output.length + (c.stack.length + c.unused.length) = edges.length := by
  simpa using c.covers.length_eq

theorem EulerMemory.done_fixed {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (done : s.done) :
    view.next layout.heads layout.stack = view := by
  have noHead : view.memory (layout.heads + view.vertex) = 0 := by
    rw [rep.vertex, rep.headCells, done.1]
    rfl
  simp [EulerTickView.next, noHead, rep.stackCursor, done.2]

theorem EulerMemory.skip {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (d : EulerDart edges.length)
    (rest : List (EulerDart edges.length)) (head : s.occurrences.incident s.current = d :: rest)
    (stale : d.1 ∉ s.occurrences.live) :
    EulerMemory layout (view.next layout.heads layout.stack) (s.skip d rest head stale) := by
  let address := layout.heads + s.current.val
  let memory := Function.update view.memory address (layout.firstDart rest)
  have headRead : view.memory (layout.heads + view.vertex) = layout.dartAddress d := by
    rw [rep.vertex, rep.headCells, head]
    rfl
  have chain : EulerDartChain layout view.memory (d :: rest) := by
    simpa only [head] using rep.chains s.current
  have flagRead : view.memory (layout.dartAddress d + 3) = layout.active + d.1.val :=
    (rep.dartCells d).2.2.1
  have inactive : view.memory (layout.active + d.1.val) = 0 := by
    simp [rep.activeCells, stale]
  have next : view.next layout.heads layout.stack = {view with memory := memory} := by
    simp [EulerTickView.next, headRead, (layout.dartAddress_pos d).ne', flagRead, inactive,
      chain.1] <;> simp [memory, address, rep.vertex]
  rw [next]
  have dartUnchanged (dart : EulerDart edges.length) (k : ℕ) :
      memory (layout.dartAddress dart + k) = view.memory (layout.dartAddress dart + k) := by
    have limit := layout.headEnd
    have current := s.current.isLt
    exact Function.update_of_ne (by unfold address EulerLayout.dartAddress; omega) _ _
  have activeUnchanged (i : Fin edges.length) :
      memory (layout.active + i.val) = view.memory (layout.active + i.val) := by
    have limit := layout.activeEnd
    have index := i.isLt
    exact Function.update_of_ne (by unfold address; omega) _ _
  have ready := s.cursor.length_total
  have stackUnchanged (i : ℕ) (used : i < s.cursor.stack.length) :
      memory (layout.stack + i) = view.memory (layout.stack + i) := by
    have stackEnd := layout.stackEnd
    have activeEnd := layout.activeEnd
    exact Function.update_of_ne (by unfold address; omega) _ _
  have outputUnchanged (i : ℕ) (used : i < 2 * s.cursor.output.length) :
      memory (view.outputCursor + i) = view.memory (view.outputCursor + i) := by
    have outputEnd := layout.outputEnd
    have stackEnd := layout.stackEnd
    have activeEnd := layout.activeEnd
    exact Function.update_of_ne (by rw [rep.outputCursor]; unfold address; omega) _ _
  refine ⟨rep.vertex, rep.stackCursor, rep.outputCursor, ?_, ?_, ?_, ?_,
    rep.stackCells.of_memory stackUnchanged, rep.outputCells.of_memory outputUnchanged⟩
  · intro v
    change memory (layout.heads + v.val) =
      layout.firstDart (Function.update s.occurrences.incident s.current rest v)
    by_cases equal : v = s.current
    · subst v
      rw [Function.update_self]
      exact Function.update_self _ _ _
    · have valueNe : v.val ≠ s.current.val := fun h => equal (Fin.ext h)
      rw [Function.update_of_ne equal,
        show memory (layout.heads + v.val) = view.memory (layout.heads + v.val) from
          Function.update_of_ne (by unfold address; omega) _ _]
      exact rep.headCells v
  · intro v
    change EulerDartChain layout memory (Function.update s.occurrences.incident s.current rest v)
    by_cases equal : v = s.current
    · subst v
      rw [Function.update_self]
      exact chain.2.of_memory (fun dart => by simpa using dartUnchanged dart 0)
    · rw [Function.update_of_ne equal]
      exact (rep.chains v).of_memory (fun dart => by simpa using dartUnchanged dart 0)
  · intro dart
    simpa only [dartUnchanged] using rep.dartCells dart
  · intro i
    simp only [EulerTraversalState.skip, EulerOccurrences.drop, List.erase_of_not_mem stale]
    exact (activeUnchanged i).trans (rep.activeCells i)


theorem EulerMemory.advance {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (undirected : Undirected G) (d : EulerDart edges.length)
    (rest : List (EulerDart edges.length)) (head : s.occurrences.incident s.current = d :: rest)
    (fresh : d.1 ∈ s.occurrences.live) :
    EulerMemory layout (view.next layout.heads layout.stack) (s.advance undirected d rest head fresh) := by
  let headAddr := layout.heads + s.current.val
  let flagAddr := layout.active + d.1.val
  let stackAddr := layout.stack + s.cursor.stack.length
  let memory := Function.update
    (Function.update (Function.update view.memory headAddr (layout.firstDart rest)) flagAddr 0)
    stackAddr (layout.dartAddress d)
  let traversal := eulerTraversalOf edges d
  have headRead : view.memory (layout.heads + view.vertex) = layout.dartAddress d := by
    rw [rep.vertex, rep.headCells, head]
    rfl
  have chain : EulerDartChain layout view.memory (d :: rest) := by
    simpa only [head] using rep.chains s.current
  have targetRead : view.memory (layout.dartAddress d + 2) = (finish G traversal).val :=
    (rep.dartCells d).2.1
  have flagRead : view.memory (layout.dartAddress d + 3) = flagAddr := (rep.dartCells d).2.2.1
  have active : view.memory flagAddr = 1 := by simp [flagAddr, rep.activeCells, fresh]
  have next : view.next layout.heads layout.stack =
      ⟨(finish G traversal).val, stackAddr + 1, view.outputCursor, memory⟩ := by
    simp [EulerTickView.next, headRead, (layout.dartAddress_pos d).ne', flagRead, active, targetRead,
      chain.1] <;> simp [memory, headAddr, stackAddr, rep.vertex, rep.stackCursor]
  rw [next]
  have used : edges.get d.1 ∈ s.cursor.unused :=
    s.agrees.mem_iff.mp (List.mem_map_of_mem (f := edges.get) fresh)
  have someUnused := List.length_pos_of_mem used
  have lengths := s.cursor.length_total
  have stackEnd := layout.stackEnd
  have activeEnd := layout.activeEnd
  have headEnd := layout.headEnd
  have outputEnd := layout.outputEnd
  have current := s.current.isLt
  have occurrence := d.1.isLt
  have protect (addr : ℕ) (fromHead : addr ≠ headAddr) (fromFlag : addr ≠ flagAddr)
      (fromStack : addr ≠ stackAddr) : memory addr = view.memory addr := by
    simp [memory, Function.update_of_ne fromHead, Function.update_of_ne fromFlag,
      Function.update_of_ne fromStack]
  have dartUnchanged (dart : EulerDart edges.length) (k : ℕ) :
      memory (layout.dartAddress dart + k) = view.memory (layout.dartAddress dart + k) :=
    protect _ (by unfold EulerLayout.dartAddress headAddr; omega)
      (by unfold EulerLayout.dartAddress flagAddr; omega)
      (by unfold EulerLayout.dartAddress stackAddr; omega)
  have stackUnchanged (i : ℕ) (used : i < s.cursor.stack.length) :
      memory (layout.stack + i) = view.memory (layout.stack + i) :=
    protect _ (by unfold headAddr; omega) (by unfold flagAddr; omega) (by unfold stackAddr; omega)
  have outputUnchanged (i : ℕ) (used : i < 2 * s.cursor.output.length) :
      memory (view.outputCursor + i) = view.memory (view.outputCursor + i) :=
    protect _ (by rw [rep.outputCursor]; unfold headAddr; omega)
      (by rw [rep.outputCursor]; unfold flagAddr; omega)
      (by rw [rep.outputCursor]; unfold stackAddr; omega)
  refine ⟨rfl, rfl, rep.outputCursor, ?_, ?_, ?_, ?_, ?_,
    rep.outputCells.of_memory outputUnchanged⟩
  · intro v
    change memory (layout.heads + v.val) =
      layout.firstDart (Function.update s.occurrences.incident s.current rest v)
    have distinctStack : layout.heads + v.val ≠ stackAddr := by unfold stackAddr; omega
    have distinctFlag : layout.heads + v.val ≠ flagAddr := by unfold flagAddr; omega
    simp only [memory, Function.update_of_ne distinctStack, Function.update_of_ne distinctFlag]
    by_cases equal : v = s.current
    · subst v
      simp [headAddr]
    · have valueNe : v.val ≠ s.current.val := fun h => equal (Fin.ext h)
      rw [Function.update_of_ne equal,
        Function.update_of_ne (show layout.heads + v.val ≠ headAddr by unfold headAddr; omega)]
      exact rep.headCells v
  · intro v
    change EulerDartChain layout memory (Function.update s.occurrences.incident s.current rest v)
    by_cases equal : v = s.current
    · subst v
      rw [Function.update_self]
      exact chain.2.of_memory (fun dart => by simpa using dartUnchanged dart 0)
    · rw [Function.update_of_ne equal]
      exact (rep.chains v).of_memory (fun dart => by simpa using dartUnchanged dart 0)
  · intro dart
    simpa only [dartUnchanged] using rep.dartCells dart
  · intro i
    change memory (layout.active + i.val) = if i ∈ s.occurrences.live.erase d.1 then 1 else 0
    by_cases equal : i = d.1
    · subst i
      have distinctStack : flagAddr ≠ stackAddr := by unfold flagAddr stackAddr; omega
      simpa [memory, flagAddr, distinctStack, s.occurrences.liveNodup.not_mem_erase]
    · have index := i.isLt
      have distinctFlag : layout.active + i.val ≠ flagAddr := by
        have differentValues : i.val ≠ d.1.val := fun e => equal (Fin.ext e)
        unfold flagAddr
        omega
      rw [protect _ (by unfold headAddr; omega) distinctFlag (by unfold stackAddr; omega), rep.activeCells]
      simp [s.occurrences.liveNodup.mem_erase_iff, equal]
  · exact ⟨⟨d, rfl, Function.update_self _ _ _⟩, rep.stackCells.of_memory stackUnchanged⟩


theorem EulerMemory.backtrack {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (empty : s.occurrences.incident s.current = []) (t : Traversal G) (rest : List (Traversal G))
    (top : s.cursor.stack = t :: rest) :
    EulerMemory layout (view.next layout.heads layout.stack) (s.backtrack even empty t rest top) := by
  let offset := view.outputCursor - 2
  let direction := if t.2 then 1 else 0
  let memory := Function.update (Function.update view.memory offset t.1.val) (offset + 1) direction
  have stack : EulerStackCells (edges := edges) layout view.memory (t :: rest) := by
    simpa only [top] using rep.stackCells
  obtain ⟨⟨dart, describes, stackRead⟩, stackBelow⟩ := stack
  have noHead : view.memory (layout.heads + view.vertex) = 0 := by
    rw [rep.vertex, rep.headCells, empty]
    rfl
  have stackPos : view.stackCursor - 1 = layout.stack + rest.length := by
    rw [rep.stackCursor, top, List.length_cons]
    omega
  have notBottom : ¬view.stackCursor ≤ layout.stack := by
    rw [rep.stackCursor, top, List.length_cons]
    omega
  have sourceRead : view.memory (layout.dartAddress dart + 1) = (start G t).val := by
    have h := (rep.dartCells dart).1
    rwa [describes] at h
  have linkRead : view.memory (layout.dartAddress dart + 4) = t.1.val := by
    have h := (rep.dartCells dart).2.2.2.1
    rwa [describes] at h
  have directionRead : view.memory (layout.dartAddress dart + 5) = direction := by
    have h := (rep.dartCells dart).2.2.2.2
    rwa [describes] at h
  have next : view.next layout.heads layout.stack =
      ⟨(start G t).val, layout.stack + rest.length, offset, memory⟩ := by
    simp [EulerTickView.next, noHead, notBottom, stackPos, stackRead, sourceRead,
      linkRead, directionRead, memory, offset]
  rw [next]
  have lengths := s.cursor.length_total
  rw [top, List.length_cons] at lengths
  have adjoining : offset + 2 = view.outputCursor := by
    unfold offset
    rw [rep.outputCursor]
    omega
  have outputEnd := layout.outputEnd
  have stackEnd := layout.stackEnd
  have activeEnd := layout.activeEnd
  have headEnd := layout.headEnd
  have finishOffset : offset + 1 < layout.stack := by
    unfold offset
    rw [rep.outputCursor]
    omega
  have unchanged (a : ℕ) (later : offset + 1 < a) : memory a = view.memory a := by
    simp [memory, Function.update_of_ne (show a ≠ offset from by omega),
      Function.update_of_ne (show a ≠ offset + 1 from by omega)]
  have dartUnchanged (d : EulerDart edges.length) (k : ℕ) :
      memory (layout.dartAddress d + k) = view.memory (layout.dartAddress d + k) :=
    unchanged _ (by unfold EulerLayout.dartAddress; omega)
  obtain ⟨newStack, newOutput⟩ := s.backtrack_stack_output even empty t rest top
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [newStack]
  · simp only [newOutput, List.length_cons]
    change offset = 2 + 2 * edges.length - 2 * (s.cursor.output.length + 1)
    unfold offset
    rw [rep.outputCursor]
    omega
  · intro v
    exact (unchanged _ (by omega)).trans (rep.headCells v)
  · intro v
    exact (rep.chains v).of_memory (fun d => by simpa using dartUnchanged d 0)
  · intro d
    simpa only [dartUnchanged] using rep.dartCells d
  · intro i
    exact (unchanged _ (by omega)).trans (rep.activeCells i)
  · rw [newStack]
    exact stackBelow.of_memory (fun _ _ => unchanged _ (by omega))
  · rw [newOutput]
    change memory offset = t.1.val ∧ memory (offset + 1) = direction ∧
      EulerOutputCells memory (offset + 2) s.cursor.output
    refine ⟨?_, by simp [memory], ?_⟩
    · simp [memory, Function.update_of_ne (show offset ≠ offset + 1 by omega)]
    · rw [adjoining]
      exact rep.outputCells.of_memory (fun _ _ => unchanged _ (by omega))

theorem EulerMemory.step {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (undirected : Undirected G)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0) :
    EulerMemory layout (view.next layout.heads layout.stack)
      (EulerTraversalState.step undirected even s) := by
  unfold EulerTraversalState.step
  split
  · rename_i empty
    split
    · rename_i top
      rw [rep.done_fixed ⟨empty, top⟩]
      exact rep
    · rename_i t rest top
      exact rep.backtrack even empty t rest top
  · rename_i d rest head
    split
    · exact rep.advance undirected d rest head (by assumption)
    · exact rep.skip d rest head (by assumption)

theorem EulerMemory.iterate {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {view : EulerTickView} {s : EulerTraversalState edges root}
    (rep : EulerMemory layout view s) (undirected : Undirected G)
    (even : ∀ v : Fin G.n, degree G edges v % 2 = 0) (count : ℕ) :
    EulerMemory layout ((EulerTickView.next layout.heads layout.stack)^[count] view)
      ((EulerTraversalState.step undirected even)^[count] s) := by
  induction count with
  | zero => exact rep
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact ih.step undirected even


end VehicleRoutingSurvey.Routing
end RppSource_EulerMemory

/-! runtime/EulerBuildTable.lean -/
section RppSource_EulerBuildTable
namespace VehicleRoutingSurvey.Routing

theorem insertEulerDartMemory_elsewhere (memory : ℕ → ℕ)
    (head dart source target activity link direction atCell : ℕ)
    (otherHead : atCell ≠ head) (otherDart : atCell < dart ∨ dart + 6 ≤ atCell) :
    insertEulerDartMemory memory head dart source target activity link direction atCell =
      memory atCell := by
  have outside (slot : ℕ) (bound : slot < 6) : atCell ≠ dart + slot := by omega
  have notBase : atCell ≠ dart := by omega
  simp [insertEulerDartMemory, Function.update_of_ne otherHead, Function.update_of_ne notBase,
    Function.update_of_ne (outside 1 (by decide)), Function.update_of_ne (outside 2 (by decide)),
    Function.update_of_ne (outside 3 (by decide)), Function.update_of_ne (outside 4 (by decide)),
    Function.update_of_ne (outside 5 (by decide))]

theorem insertEulerDartMemory_record (memory : ℕ → ℕ) (head dart source target activity link direction : ℕ)
    (separated : head < dart) :
    let result := insertEulerDartMemory memory head dart source target activity link direction
    result head = dart ∧ result dart = memory head ∧ result (dart + 1) = source ∧
      result (dart + 2) = target ∧ result (dart + 3) = activity ∧ result (dart + 4) = link ∧
      result (dart + 5) = direction := by
  have before (k : ℕ) : head ≠ dart + k := by omega
  have different : dart ≠ head := by omega
  simp [insertEulerDartMemory, before, different]

theorem EulerLayout.dartRecords_disjoint {n m : ℕ} (layout : EulerLayout n m)
    {d e : EulerDart m} (different : d ≠ e) {slot : ℕ} (within : slot < 6) :
    layout.dartAddress d + slot < layout.dartAddress e ∨
      layout.dartAddress e + 6 ≤ layout.dartAddress d + slot := by
  obtain ⟨i, direction⟩ := d
  obtain ⟨j, otherDirection⟩ := e
  cases direction <;> cases otherDirection <;> simp [dartAddress]
  · have indices : i.val ≠ j.val := fun x => different (by rw [show i = j from Fin.ext x])
    omega
  · omega
  · omega
  · have indices : i.val ≠ j.val := fun x => different (by rw [show i = j from Fin.ext x])
    omega

private theorem EulerDartChain.of_same_records {n m : ℕ} {layout : EulerLayout n m}
    {memory other : ℕ → ℕ} {ds : List (EulerDart m)}
    (chain : EulerDartChain layout memory ds)
    (same : ∀ d ∈ ds, other (layout.dartAddress d) = memory (layout.dartAddress d)) :
    EulerDartChain layout other ds := by
  induction ds with
  | nil => trivial
  | cons d rest ih =>
    exact ⟨(same d List.mem_cons_self).trans chain.1,
      ih chain.2 (fun d hd => same d (List.mem_cons_of_mem _ hd))⟩

def EulerBuildIncident {G : Network} (edges : List (Fin G.q))
    (darts : List (EulerDart edges.length)) (v : Fin G.n) : List (EulerDart edges.length) :=
  darts.filter (fun d => decide (start G (eulerTraversalOf edges d) = v))

def EulerBuiltDart {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) (d : EulerDart edges.length) : Prop :=
  let addr := layout.dartAddress d
  let t := eulerTraversalOf edges d
  memory (addr + 1) = (start G t).val ∧ memory (addr + 2) = (finish G t).val ∧
    memory (addr + 3) = layout.active + d.1.val ∧ memory (addr + 4) = t.1.val ∧
    memory (addr + 5) = (if t.2 then 1 else 0)

structure EulerBuiltDarts {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) (darts : List (EulerDart edges.length)) :
    Prop where
  heads : ∀ v : Fin G.n, memory (layout.heads + v.val) =
    layout.firstDart (EulerBuildIncident edges darts v)
  chains : ∀ v, EulerDartChain layout memory (EulerBuildIncident edges darts v)
  records : ∀ d ∈ darts, EulerBuiltDart layout memory d

def EulerBuildPrepend {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) (d : EulerDart edges.length) :
    ℕ → ℕ :=
  let t := eulerTraversalOf edges d
  insertEulerDartMemory memory (layout.heads + (start G t).val) (layout.dartAddress d)
    (start G t).val (finish G t).val (layout.active + d.1.val) t.1.val (if t.2 then 1 else 0)

theorem EulerBuiltDarts.prepend {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {memory : ℕ → ℕ} {ds : List (EulerDart edges.length)}
    (prior : EulerBuiltDarts layout memory ds) (d : EulerDart edges.length) (fresh : d ∉ ds) :
    EulerBuiltDarts layout (EulerBuildPrepend layout memory d) (d :: ds) := by
  let t := eulerTraversalOf edges d
  let source := start G t
  let head := layout.heads + source.val
  let address := layout.dartAddress d
  let after := EulerBuildPrepend layout memory d
  have headLimit (v : Fin G.n) : layout.heads + v.val < address := by
    have boundary := layout.headEnd
    have index := v.isLt
    unfold address EulerLayout.dartAddress
    omega
  have data := insertEulerDartMemory_record memory head address source.val (finish G t).val
    (layout.active + d.1.val) t.1.val (if t.2 then 1 else 0) (headLimit source)
  have otherHead (v : Fin G.n) (different : v ≠ source) :
      after (layout.heads + v.val) = memory (layout.heads + v.val) := by
    have differentValue : v.val ≠ source.val := fun h => different (Fin.ext h)
    exact insertEulerDartMemory_elsewhere _ _ _ _ _ _ _ _ _
      (by change layout.heads + v.val ≠ layout.heads + source.val; omega)
      (Or.inl (headLimit v))
  have otherRecord (e : EulerDart edges.length) (different : e ≠ d) (i : ℕ) (within : i < 6) :
      EulerBuildPrepend layout memory d (layout.dartAddress e + i) =
        memory (layout.dartAddress e + i) := by
    have boundary := layout.headEnd
    have index := source.isLt
    exact insertEulerDartMemory_elsewhere _ _ _ _ _ _ _ _ _
      (by
        change layout.dartAddress e + i ≠ layout.heads + source.val
        unfold EulerLayout.dartAddress
        omega)
      (layout.dartRecords_disjoint different within)
  have oldChain (v : Fin G.n) : EulerDartChain layout after (EulerBuildIncident edges ds v) :=
    (prior.chains v).of_same_records fun e inRow => by
      have old := (List.mem_filter.mp inRow).1
      simpa using otherRecord e (fun h => fresh (h ▸ old)) 0 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases equal : v = source
    · subst v
      simp only [EulerBuildIncident, List.filter_cons, show
        decide (start G (eulerTraversalOf edges d) = source) = true by simp [source, t],
        if_true, EulerLayout.firstDart]
      exact data.1
    · have miss : start G (eulerTraversalOf edges d) ≠ v := fun h => equal h.symm
      simpa [EulerBuildIncident, miss] using (otherHead v equal).trans (prior.heads v)
  · intro v
    by_cases equal : v = source
    · subst v
      have leg : after address = layout.firstDart (EulerBuildIncident edges ds source) :=
        data.2.1.trans (prior.heads source)
      simpa only [EulerBuildIncident, List.filter_cons, show
        decide (start G (eulerTraversalOf edges d) = source) = true by simp [source, t],
        if_true, EulerDartChain] using And.intro leg (oldChain source)
    · have miss : start G (eulerTraversalOf edges d) ≠ v := fun h => equal h.symm
      simpa [EulerBuildIncident, miss] using oldChain v
  · intro e present
    rcases List.mem_cons.mp present with rfl | old
    · exact data.2.2
    · have different : e ≠ d := fun h => fresh (h ▸ old)
      have slots (i : ℕ) (hi : i < 6) := otherRecord e different i hi
      simpa only [EulerBuiltDart, slots 1 (by decide), slots 2 (by decide), slots 3 (by decide),
        slots 4 (by decide), slots 5 (by decide)] using prior.records e old


end VehicleRoutingSurvey.Routing
end RppSource_EulerBuildTable

/-! runtime/EulerBuildCorrect.lean -/
section RppSource_EulerBuildCorrect
namespace VehicleRoutingSurvey.Routing

def eulerDartSuffix (m remaining : ℕ) : List (EulerDart m) :=
  ((List.finRange m).drop remaining).flatMap fun i => [(i, true), (i, false)]

theorem eulerDartSuffix_step {m i : ℕ} (hi : i < m) :
    eulerDartSuffix m i = (⟨i, hi⟩, true) :: (⟨i, hi⟩, false) :: eulerDartSuffix m (i + 1) := by
  unfold eulerDartSuffix
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

theorem eulerDartSuffix_lower {m i : ℕ} {d : EulerDart m} (used : d ∈ eulerDartSuffix m i) :
    i ≤ d.1.val := by
  obtain ⟨e, ed, member⟩ := List.mem_flatMap.mp used
  have fromOccurrence : d.1 = e := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    exact member.elim (congrArg Prod.fst) (congrArg Prod.fst)
  obtain ⟨j, hj, equality⟩ := List.mem_iff_getElem.mp ed
  have offset := congrArg Fin.val equality
  simp at offset
  rw [fromOccurrence]
  omega

private theorem eulerBuildPrepend_below_heads {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) (d : EulerDart edges.length)
    {a : ℕ} (before : a < layout.heads) :
    EulerBuildPrepend layout memory d a = memory a := by
  have boundary := layout.headEnd
  unfold EulerBuildPrepend
  apply insertEulerDartMemory_elsewhere
  · omega
  · left
    unfold EulerLayout.dartAddress
    omega

def EulerBuildInsertOccurrence {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (memory : ℕ → ℕ) (i : Fin edges.length) : ℕ → ℕ :=
  EulerBuildPrepend layout
    (EulerBuildPrepend layout (Function.update memory (layout.active + i.val) 1) (i, false)) (i, true)

structure EulerOccurrenceInput {G : Network} (edges : List (Fin G.q)) (input : ℕ)
    (memory : ℕ → ℕ) : Prop where
  ids : ∀ i : Fin edges.length, memory (input + i.val) = (edges.get i).val
  tails : ∀ e : Fin G.q, memory (e.val + e.val + e.val + 2) = (G.tail e).val
  heads : ∀ e : Fin G.q, memory (e.val + e.val + e.val + 3) = (G.head e).val

structure EulerBuildInvariant {G : Network} {edges : List (Fin G.q)}
    (layout : EulerLayout G.n edges.length) (input : ℕ) (remaining : ℕ) (view : EulerBuildView) :
    Prop where
  count : view.remaining = remaining
  cursor : view.dartCursor = layout.darts + 12 * remaining
  readInput : EulerOccurrenceInput edges input view.memory
  built : EulerBuiltDarts layout view.memory (eulerDartSuffix edges.length remaining)
  live : ∀ i : Fin edges.length, remaining ≤ i.val → view.memory (layout.active + i.val) = 1

theorem EulerBuildInvariant.initial {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {input : ℕ} {view : EulerBuildView}
    (count : view.remaining = edges.length) (cursor : view.dartCursor = layout.darts + 12 * edges.length)
    (encoded : EulerOccurrenceInput edges input view.memory)
    (empty : ∀ v : Fin G.n, view.memory (layout.heads + v.val) = 0) :
    EulerBuildInvariant layout input edges.length view := by
  have suffix : eulerDartSuffix edges.length edges.length = [] := by
    simp [eulerDartSuffix, List.drop_of_length_le]
  refine ⟨count, cursor, encoded, ?_, ?_⟩
  · rw [suffix]
    exact ⟨empty, fun _ => trivial, fun _ h => (List.not_mem_nil h).elim⟩
  · exact fun i h => (Nat.not_le_of_lt i.isLt h).elim

theorem EulerBuildInvariant.toEulerMemory {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {input : ℕ} {view : EulerBuildView}
    (rep : EulerBuildInvariant layout input 0 view) (root : Fin G.n) :
    EulerMemory layout ⟨root.val, layout.stack, 2 + 2 * edges.length, view.memory⟩
      (EulerTraversalState.initial edges root) := by
  refine ⟨rfl, rfl, by simp [EulerTraversalState.initial, EulerCursor.initial], ?_, ?_, ?_, ?_,
    trivial, trivial⟩
  · exact rep.built.heads
  · exact rep.built.chains
  · intro d
    apply rep.built.records d
    rcases d with ⟨i, direction⟩
    exact List.mem_flatMap.mpr ⟨i, by simp, by cases direction <;> simp⟩
  · intro i
    simpa [EulerTraversalState.initial, EulerOccurrences.initial] using rep.live i (Nat.zero_le _)

theorem EulerBuildInvariant.step {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {input i : ℕ} {view : EulerBuildView}
    (rep : EulerBuildInvariant layout input (i + 1) view) (hi : i < edges.length)
    (inputBound : input + edges.length ≤ layout.active) (rawBound : 2 + 3 * G.q ≤ layout.active) :
    EulerBuildInvariant layout input i (view.next layout.heads input layout.active) := by
  let index : Fin edges.length := ⟨i, hi⟩
  let edge := edges.get index
  let flagged := Function.update view.memory (layout.active + i) 1
  let written := EulerBuildInsertOccurrence layout view.memory index
  have dartCursor : view.dartCursor - 12 = layout.darts + 12 * i := by
    rw [rep.cursor, Nat.mul_succ]
    omega
  have linkRead : view.memory (input + i) = edge.val := rep.readInput.ids index
  have tailRead := rep.readInput.tails edge
  have headRead : view.memory (edge.val + edge.val + edge.val + 2 + 1) = (G.head edge).val :=
    rep.readInput.heads edge
  simp [index, edge] at tailRead headRead
  have next : view.next layout.heads input layout.active =
      ⟨i, layout.darts + 12 * i, written⟩ := by
    simp [EulerBuildView.next, rep.count, dartCursor, linkRead, tailRead, headRead,
      EulerOccurrenceOperands.write, written, EulerBuildInsertOccurrence, EulerBuildPrepend,
      EulerLayout.dartAddress, eulerTraversalOf, start, finish, index, edge]
  rw [next]
  have activityEnd := layout.activeEnd
  have headEnd := layout.headEnd
  have flagBelow : layout.active + i < layout.heads := by omega
  have flagWritePast (a : ℕ) (later : layout.heads ≤ a) :
      flagged a = view.memory a :=
    Function.update_of_ne (by omega) _ _
  have dartWritePast (d : EulerDart edges.length) (j : ℕ) :
      flagged (layout.dartAddress d + j) = view.memory (layout.dartAddress d + j) :=
    flagWritePast _ (by unfold EulerLayout.dartAddress; omega)
  have prior : EulerBuiltDarts layout flagged (eulerDartSuffix edges.length (i + 1)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      exact (flagWritePast _ (by omega)).trans (rep.built.heads v)
    · intro v
      exact (rep.built.chains v).of_memory (fun d => by simpa using dartWritePast d 0)
    · intro d used
      simpa only [EulerBuiltDart, dartWritePast] using rep.built.records d used
  have reverseFresh : (index, false) ∉ eulerDartSuffix edges.length (i + 1) :=
    fun h => Nat.not_succ_le_self i (eulerDartSuffix_lower h)
  have forwardFresh : (index, true) ∉ (index, false) :: eulerDartSuffix edges.length (i + 1) := by
    intro h
    rcases List.mem_cons.mp h with mismatch | old
    · cases mismatch
    · exact Nat.not_succ_le_self i (eulerDartSuffix_lower old)
  have readUnchanged (addr : ℕ) (early : addr < layout.active) : written addr = view.memory addr := by
    have beforeHeads : addr < layout.heads := by omega
    simp only [written, EulerBuildInsertOccurrence, eulerBuildPrepend_below_heads _ _ _ beforeHeads,
      Function.update_of_ne (show addr ≠ layout.active + index.val by omega)]
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    have := j.isLt
    exact (readUnchanged _ (by omega)).trans (rep.readInput.ids j)
  · intro e
    have := e.isLt
    exact (readUnchanged _ (by omega)).trans (rep.readInput.tails e)
  · intro e
    have := e.isLt
    exact (readUnchanged _ (by omega)).trans (rep.readInput.heads e)
  · rw [eulerDartSuffix_step hi]
    exact (prior.prepend (index, false) reverseFresh).prepend (index, true) forwardFresh
  · intro j bound
    have jLt := j.isLt
    have beforeHeads : layout.active + j.val < layout.heads := by omega
    simp only [written, EulerBuildInsertOccurrence,
      eulerBuildPrepend_below_heads _ _ _ beforeHeads]
    by_cases equal : j.val = i
    · simp [index, equal]
    · rw [Function.update_of_ne (by change layout.active + j.val ≠ layout.active + i; omega)]
      exact rep.live j (by omega)

theorem EulerBuildInvariant.iterate {G : Network} {edges : List (Fin G.q)}
    {layout : EulerLayout G.n edges.length} {input : ℕ} {view : EulerBuildView}
    (rep : EulerBuildInvariant layout input edges.length view)
    (inputBound : input + edges.length ≤ layout.active) (rawBound : 2 + 3 * G.q ≤ layout.active) :
    EulerBuildInvariant layout input 0
      ((EulerBuildView.next layout.heads input layout.active)^[edges.length] view) := by
  have loop (k : ℕ) (within : k ≤ edges.length) :
      EulerBuildInvariant layout input (edges.length - k)
        ((EulerBuildView.next layout.heads input layout.active)^[k] view) := by
    induction k with
    | zero => exact rep
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have position : edges.length - k = (edges.length - (k + 1)) + 1 := by omega
      have before := ih (by omega)
      rw [position] at before
      exact before.step (by omega) inputBound rawBound
  simpa using loop edges.length le_rfl


end VehicleRoutingSurvey.Routing
end RppSource_EulerBuildCorrect

/-! runtime/DegreeParity.lean -/
section RppSource_DegreeParity
namespace VehicleRoutingSurvey.Routing

/-- Registers 7 and 8 hold the edge endpoints, register 9 holds the base
of the parity array, and register 6 supplies one. A loop flips one cell twice. -/
def degreeParityCell : List ArithmeticInstruction :=
  [.natAdd 0 9 7, .natLoad 2 0, .natSub 2 6 2, .natStore 0 2,
   .natAdd 0 9 8, .natLoad 2 0, .natSub 2 6 2, .natStore 0 2]

def flipParity (m : ℕ → ℕ) (address : ℕ) : ℕ → ℕ :=
  Function.update m address (1 - m address)

theorem degreeParityCell_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns degreeParityCell 8 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 0 → r ≠ 2 → t.nr r = s.nr r) ∧
      t.nm = flipParity (flipParity s.nm (s.nr 9 + s.nr 7)) (s.nr 9 + s.nr 8) := by
  let a := s.nr 9 + s.nr 7
  let b := s.nr 9 + s.nr 8
  let midway := flipParity s.nm a
  let t := {s with
    pc := 8
    nr := Function.update (Function.update s.nr 0 b) 2 (1 - midway b)
    nm := flipParity midway b}
  have finish : (arithmeticStep degreeParityCell)^[8] s = t := by
    simp [degreeParityCell, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      t, midway, flipParity, a, b, Function.update_idem,
      Function.update_comm (show (0 : ℕ) ≠ 2 by decide)]
  refine ⟨t, ⟨?_, finish, rfl⟩, running, rfl, ?_, rfl⟩
  · intro i bound
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [degreeParityCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r other0 other2
    simp [t, Function.update_of_ne other0, Function.update_of_ne other2]

private theorem flipParity_eq (m : ℕ → ℕ) (address query : ℕ) {d : ℕ}
    (old : m query = d % 2) :
    flipParity m address query = (d + if query = address then 1 else 0) % 2 := by
  by_cases equal : query = address
  · subst query
    simp only [flipParity, Function.update_self, if_true, old]
    omega
  · simp [flipParity, equal, old]

theorem flipDegreeParity_cons (G : Network) (es : List (Fin G.q)) (e : Fin G.q)
    (base : ℕ) (m : ℕ → ℕ) (initial : ∀ v, m (base + v.val) = degree G es v % 2) :
    ∀ v : Fin G.n,
      flipParity (flipParity m (base + (G.tail e).val)) (base + (G.head e).val)
        (base + v.val) = degree G (e :: es) v % 2 := by
  intro v
  rw [flipParity_eq _ _ _ (flipParity_eq _ _ _ (initial v))]
  have eqTail : base + v.val = base + (G.tail e).val ↔ G.tail e = v := by
    simp [Fin.ext_iff, eq_comm]
  have eqHead : base + v.val = base + (G.head e).val ↔ G.head e = v := by
    simp [Fin.ext_iff, eq_comm]
  simp only [eqTail, eqHead]
  simp only [degree, List.filter_cons, decide_eq_true_eq]
  split <;> split <;> simp_all <;> omega


end VehicleRoutingSurvey.Routing
end RppSource_DegreeParity

/-! runtime/DegreeParityScan.lean -/
section RppSource_DegreeParityScan
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

private def readParityEdgeBlock : List ArithmeticInstruction :=
  [.natAdd 0 23 17, .natLoad 13 0,
   .natAdd 0 13 13, .natAdd 0 0 13, .natAdd 0 0 24,
   .natLoad 7 0, .natAdd 0 0 6, .natLoad 8 0]

private def parityEdgePreserved : List ℕ := [3, 4, 5, 6, 9, 10, 17, 18, 20, 21, 23, 24, 26, 28, 29, 31, 33]

private theorem readParityEdgeBlock_correct {G : Network} {edges : List (Fin G.q)}
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (two : s.nr 24 = 2) (encoded : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (i : Fin edges.length) (position : s.nr 17 = i.val) :
    ∃ t, BlockRuns readParityEdgeBlock 8 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ r ∈ parityEdgePreserved, t.nr r = s.nr r) ∧
      t.nr 7 = (G.tail (edges.get i)).val ∧ t.nr 8 = (G.head (edges.get i)).val := by
  let t := (arithmeticStep readParityEdgeBlock)^[8] s
  have ready : t.halted = false := by
    simp [t, readParityEdgeBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = readParityEdgeBlock.length := by
    simp [t, readParityEdgeBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have head : s.nm ((edges.get i).val + (edges.get i).val + (edges.get i).val + 2 + 1) =
      (G.head (edges.get i)).val := encoded.heads (edges.get i)
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, readParityEdgeBlock, parityEdgePreserved, arithmeticStep, entry, running, one, two,
    position, encoded.ids i, Function.iterate_succ_apply', or_imp, forall_and]
  exact ⟨encoded.tails (edges.get i), head⟩

private def parityOccurrenceBlock : List ArithmeticInstruction :=
  appendBlock readParityEdgeBlock degreeParityCell

private theorem parityOccurrenceBlock_correct {G : Network} {edges : List (Fin G.q)}
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (two : s.nr 24 = 2) (encoded : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (i : Fin edges.length) (position : s.nr 17 = i.val) :
    ∃ t, BlockRuns parityOccurrenceBlock 16 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      (∀ r ∈ parityEdgePreserved, t.nr r = s.nr r) ∧
      t.nm = flipParity (flipParity s.nm (s.nr 9 + (G.tail (edges.get i)).val))
        (s.nr 9 + (G.head (edges.get i)).val) := by
  obtain ⟨read, loads, readReady, unchanged, realMemory, fixed, tail, head⟩ :=
    readParityEdgeBlock_correct entry running one two encoded i position
  obtain ⟨t, flips, ready, rm, keep, memory⟩ :=
    degreeParityCell_correct (s := {read with pc := 0}) rfl readReady
      ((fixed 6 (by decide)).trans one)
  refine ⟨_, loads.append flips, ready, rm.trans realMemory, ?_, ?_⟩
  · intro r member
    have not0 : r ≠ 0 := by rintro rfl; simp [parityEdgePreserved] at member
    have not2 : r ≠ 2 := by rintro rfl; simp [parityEdgePreserved] at member
    exact (keep r not0 not2).trans (fixed r member)
  · change t.nm = _
    simpa only [unchanged, fixed 9 (by decide), tail, head] using memory

def degreeParityScanBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 17 18 parityOccurrenceBlock

def parityScanPreserved : List ℕ := [3, 4, 5, 6, 9, 10, 18, 20, 21, 23, 24, 26, 28, 29, 31, 33]

private structure DegreeParityScanInvariant {G : Network} (edges : List (Fin G.q))
    (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 17 = i
  stable : ∀ r ∈ parityScanPreserved, m.nr r = s.nr r
  input : ∀ addr < s.nr 9, m.nm addr = s.nm addr
  realMemory : m.rm = s.rm
  flags : ∀ v : Fin G.n, m.nm (s.nr 9 + v.val) = degree G (edges.take i).reverse v % 2

theorem degreeParityScanBlock_correct {G : Network} {edges : List (Fin G.q)}
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (two : s.nr 24 = 2) (count : s.nr 18 = edges.length)
    (inputBound : s.nr 23 + edges.length ≤ s.nr 9) (rawBound : 2 + 3 * G.q ≤ s.nr 9)
    (encoded : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (zeroes : ∀ v : Fin G.n, s.nm (s.nr 9 + v.val) = 0) :
    ∃ t, BlockRuns degreeParityScanBlock (19 * edges.length + 2) s t ∧ t.halted = false ∧
      (∀ r ∈ parityScanPreserved, t.nr r = s.nr r) ∧
      (∀ addr < s.nr 9, t.nm addr = s.nm addr) ∧ t.rm = s.rm ∧
      ∀ v : Fin G.n, t.nm (s.nr 9 + v.val) = degree G edges v % 2 := by
  have initial : DegreeParityScanInvariant edges s 0
      {s with pc := 0, nr := Function.update s.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, rfl, ?_⟩
    · intro r member
      have different : r ≠ 17 := by rintro rfl; simp [parityScanPreserved] at member
      exact Function.update_of_ne different _ _
    · intro v
      simp [zeroes, degree]
  have control (i : ℕ) (m : ArithmeticState) (inv : DegreeParityScanInvariant edges s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 18 = edges.length :=
    ⟨inv.entry, inv.running, inv.index, (inv.stable 18 (by decide)).trans count⟩
  have iterate (i : ℕ) (inside : i < edges.length) (m : ArithmeticState)
      (inv : DegreeParityScanInvariant edges s i m) :
      ∃ t, BlockRuns parityOccurrenceBlock 16 m t ∧ t.halted = false ∧
        DegreeParityScanInvariant edges s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    have base := inv.stable 9 (by decide)
    have occurs := inv.stable 23 (by decide)
    have mOne := (inv.stable 6 (by decide)).trans one
    have mTwo := (inv.stable 24 (by decide)).trans two
    have read : EulerOccurrenceInput edges (m.nr 23) m.nm := by
      rw [occurs]
      refine ⟨?_, ?_, ?_⟩
      · intro j
        have := j.isLt
        exact (inv.input _ (by omega)).trans (encoded.ids j)
      · intro e
        have := e.isLt
        exact (inv.input _ (by omega)).trans (encoded.tails e)
      · intro e
        have := e.isLt
        exact (inv.input _ (by omega)).trans (encoded.heads e)
    let j : Fin edges.length := ⟨i, inside⟩
    obtain ⟨t, run, ready, realMemory, fixed, memory⟩ :=
      parityOccurrenceBlock_correct inv.entry inv.running mOne mTwo read j inv.index
    have tIndex := (fixed 17 (by decide)).trans inv.index
    have tOne := (fixed 6 (by decide)).trans mOne
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [tIndex, tOne], ?_, ?_,
      realMemory.trans inv.realMemory, ?_⟩⟩
    · intro r member
      have different : r ≠ 17 := by rintro rfl; simp [parityScanPreserved] at member
      exact (Function.update_of_ne different _ _).trans
        ((fixed r (by simp [parityEdgePreserved, parityScanPreserved] at member ⊢; tauto)).trans
          (inv.stable r member))
    · intro addr below
      change t.nm addr = _
      rw [memory, base]
      unfold flipParity
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact inv.input _ below
    · intro v
      change t.nm (s.nr 9 + v.val) = _
      rw [memory, base, List.take_succ_eq_append_getElem inside, List.reverse_append]
      exact flipDegreeParity_cons G _ (edges.get j) (s.nr 9) m.nm inv.flags v
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 17 18 edges.length 16
    parityOccurrenceBlock (DegreeParityScanInvariant edges s) entry running initial control iterate
  have elapsed : 1 + (edges.length * (16 + 3) + 1) = 19 * edges.length + 2 := by omega
  rw [elapsed] at run
  refine ⟨_, run, inv.running, inv.stable, inv.input, inv.realMemory, ?_⟩
  intro v
  change last.nm (s.nr 9 + v.val) = degree G edges v % 2
  have degreeEq := degree_eq_of_perm (List.reverse_perm edges) v
  simpa only [List.take_length, degreeEq] using inv.flags v


end VehicleRoutingSurvey.Routing
end RppSource_DegreeParityScan

/-! runtime/OddVertexArray.lean -/
section RppSource_OddVertexArray
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Append the current vertex when its parity bit is set. Register 17 is
the original vertex index. Registers 31 and 32 are the compact array's
base and current length. -/
def appendOddVertexCell : List ArithmeticInstruction :=
  [.natAdd 0 9 17, .natLoad 2 0, .natBranch 2 10 7 3,
   .natAdd 0 31 32, .natStore 0 17, .natAdd 32 32 6, .jump 11,
   .jump 8, .jump 9, .jump 10, .jump 11]

theorem appendOddVertexCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 10 = 0) :
    let flag := s.nm (s.nr 9 + s.nr 17)
    ∃ t, BlockRuns appendOddVertexCell 7 s t ∧ t.halted = false ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ [3, 4, 5, 6, 9, 10, 17, 20, 21, 23, 26, 28, 29, 31, 33], t.nr r = s.nr r) ∧
      t.nr 32 = (if flag = 0 then s.nr 32 else s.nr 32 + 1) ∧
      t.nm = (if flag = 0 then s.nm else Function.update s.nm (s.nr 31 + s.nr 32) (s.nr 17)) := by
  let t := (arithmeticStep appendOddVertexCell)^[7] s
  have output : t.halted = false ∧ t.pc = appendOddVertexCell.length ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ [3, 4, 5, 6, 9, 10, 17, 20, 21, 23, 26, 28, 29, 31, 33], t.nr r = s.nr r) ∧
      t.nr 32 = (if s.nm (s.nr 9 + s.nr 17) = 0 then s.nr 32 else s.nr 32 + 1) ∧
      t.nm = (if s.nm (s.nr 9 + s.nr 17) = 0 then s.nm
        else Function.update s.nm (s.nr 31 + s.nr 32) (s.nr 17)) := by
    by_cases empty : s.nm (s.nr 9 + s.nr 17) = 0 <;>
      simp [t, appendOddVertexCell, arithmeticStep, entry, running, one, zero, empty,
        Function.iterate_succ_apply', or_imp, forall_and]
  exact ⟨t, BlockRuns.of_running_exit rfl output.1 output.2.1, output.1, output.2.2⟩

def compactOddVerticesBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 32 0] (countedLoopFromZero 6 17 29 appendOddVertexCell)

def oddVertexPrefix (s : ArithmeticState) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun v => decide (s.nm (s.nr 9 + v) ≠ 0))

private theorem oddVertexPrefix_succ (s : ArithmeticState) (i : ℕ) :
    oddVertexPrefix s (i + 1) =
      if s.nm (s.nr 9 + i) = 0 then oddVertexPrefix s i else oddVertexPrefix s i ++ [i] := by
  unfold oddVertexPrefix
  rw [List.range_succ, List.filter_append]
  by_cases h : s.nm (s.nr 9 + i) = 0 <;> simp [h]

def oddVertexFixed : List ℕ := [3, 4, 5, 6, 9, 10, 20, 21, 23, 26, 28, 29, 31, 33]

private structure OddArrayInvariant (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  ready : m.halted = false
  index : m.nr 17 = i
  fixed : ∀ r ∈ oddVertexFixed, m.nr r = s.nr r
  size : m.nr 32 = (oddVertexPrefix s i).length
  below : ∀ k < s.nr 31, m.nm k = s.nm k
  realMemory : m.rm = s.rm
  stored : ∀ j, m.nm (s.nr 31 + j) =
    if j < (oddVertexPrefix s i).length then ((oddVertexPrefix s i)[j]?).getD 0
    else s.nm (s.nr 31 + j)

theorem compactOddVerticesBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 10 = 0)
    (arrays : s.nr 9 + s.nr 29 ≤ s.nr 31) :
    ∃ t, BlockRuns compactOddVerticesBlock (10 * s.nr 29 + 3) s t ∧ t.halted = false ∧
      (∀ r ∈ oddVertexFixed, t.nr r = s.nr r) ∧
      t.nr 32 = (oddVertexPrefix s (s.nr 29)).length ∧
      t.rm = s.rm ∧
      (∀ j, t.nm (s.nr 31 + j) =
        if j < (oddVertexPrefix s (s.nr 29)).length then ((oddVertexPrefix s (s.nr 29))[j]?).getD 0
        else s.nm (s.nr 31 + j)) ∧
      (∀ k < s.nr 31, t.nm k = s.nm k) := by
  let initialized := {s with pc := 0, nr := Function.update s.nr 32 0}
  have initial : OddArrayInvariant s 0 {initialized with pc := 0, nr := Function.update initialized.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [initialized, oddVertexPrefix], fun _ _ => rfl, rfl, ?_⟩
    · intro r hr
      have not17 : r ≠ 17 := by rintro rfl; simp [oddVertexFixed] at hr
      have not32 : r ≠ 32 := by rintro rfl; simp [oddVertexFixed] at hr
      simp [initialized, Function.update_of_ne not17, Function.update_of_ne not32]
    · intro j
      simp [initialized, oddVertexPrefix]
  have control (i : ℕ) (m : ArithmeticState) (inv : OddArrayInvariant s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 29 = s.nr 29 :=
    ⟨inv.entry, inv.ready, inv.index, inv.fixed 29 (by decide)⟩
  have iterate (i : ℕ) (inside : i < s.nr 29) (m : ArithmeticState) (inv : OddArrayInvariant s i m) :
      ∃ t, BlockRuns appendOddVertexCell 7 m t ∧ t.halted = false ∧
        OddArrayInvariant s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    have mOne := (inv.fixed 6 (by decide)).trans one
    have mZero := (inv.fixed 10 (by decide)).trans zero
    have array := inv.fixed 31 (by decide)
    have flag : m.nm (m.nr 9 + m.nr 17) = s.nm (s.nr 9 + i) := by
      rw [inv.fixed 9 (by decide), inv.index]
      exact inv.below _ (by omega)
    obtain ⟨t, run, ready, rm, _, stable, size, memory⟩ :=
      appendOddVertexCell_correct inv.entry inv.ready mOne mZero
    have index := (stable 17 (by decide)).trans inv.index
    have oneAfter := (stable 6 (by decide)).trans mOne
    rw [flag, inv.size] at size
    rw [flag, array, inv.size, inv.index] at memory
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [index, oneAfter], ?_, ?_, ?_,
      rm.trans inv.realMemory, ?_⟩⟩
    · intro r hr
      have not17 : r ≠ 17 := by rintro rfl; simp [oddVertexFixed] at hr
      exact (Function.update_of_ne not17 _ _).trans
        ((stable r (by simp [oddVertexFixed] at hr ⊢; tauto)).trans (inv.fixed r hr))
    · change t.nr 32 = _
      rw [size, oddVertexPrefix_succ]
      split <;> simp
    · intro k early
      change t.nm k = _
      rw [memory]
      split
      · exact inv.below _ early
      · rw [Function.update_of_ne (by omega)]
        exact inv.below _ early
    · intro j
      change t.nm (s.nr 31 + j) = _
      rw [memory, oddVertexPrefix_succ]
      by_cases absent : s.nm (s.nr 9 + i) = 0
      · simpa only [if_pos absent] using inv.stored j
      · simp only [if_neg absent]
        by_cases slot : j = (oddVertexPrefix s i).length
        · rw [slot, Function.update_self]
          have inNew : (oddVertexPrefix s i).length < (oddVertexPrefix s i ++ [i]).length := by simp
          rw [if_pos inNew, List.getElem?_append_right (by omega)]
          simp
        · have away : s.nr 31 + j ≠ s.nr 31 + (oddVertexPrefix s i).length := by omega
          rw [Function.update_of_ne away, inv.stored]
          by_cases old : j < (oddVertexPrefix s i).length
          · have new : j < (oddVertexPrefix s i ++ [i]).length := by simp; omega
            rw [if_pos old, if_pos new, List.getElem?_append_left old]
          · have new : ¬ j < (oddVertexPrefix s i ++ [i]).length := by simp; omega
            rw [if_neg old, if_neg new]
  obtain ⟨last, inv, loop⟩ := countedLoopFromZero_correct 6 17 29 (s.nr 29) 7
    appendOddVertexCell (OddArrayInvariant s) (s := initialized) rfl running initial control iterate
  have run := (zeroRegister_runs 32 s entry running).append loop
  have elapsed : 1 + (1 + (s.nr 29 * (7 + 3) + 1)) = 10 * s.nr 29 + 3 := by omega
  rw [elapsed] at run
  exact ⟨_, run, inv.ready, inv.fixed, inv.size, inv.realMemory, inv.stored, inv.below⟩


end VehicleRoutingSurvey.Routing
end RppSource_OddVertexArray

/-! runtime/OddMatchingInput.lean -/
section RppSource_OddMatchingInput
namespace VehicleRoutingSurvey.Routing

def oddVertexOrder (G : Network) (edges : List (Fin G.q)) : List (Fin G.n) :=
  (List.finRange G.n).filter fun v => decide (v ∈ oddVertices G edges)

theorem mem_oddVertexOrder (G : Network) (edges : List (Fin G.q)) (v : Fin G.n) :
    v ∈ oddVertexOrder G edges ↔ v ∈ oddVertices G edges := by
  simp [oddVertexOrder]

theorem oddVertexOrder_nodup (G : Network) (edges : List (Fin G.q)) :
    (oddVertexOrder G edges).Nodup :=
  (List.nodup_finRange _).filter _

theorem oddVertexOrder_length (G : Network) (edges : List (Fin G.q)) :
    (oddVertexOrder G edges).length = (oddVertices G edges).card := by
  have vertices : (oddVertexOrder G edges).toFinset = oddVertices G edges := by
    ext v
    simpa only [List.mem_toFinset] using mem_oddVertexOrder G edges v
  rw [← vertices]
  exact (List.toFinset_card_of_nodup (oddVertexOrder_nodup G edges)).symm

theorem oddVertexOrder_even (G : Network) (edges : List (Fin G.q)) :
    (oddVertexOrder G edges).length % 2 = 0 := by
  rw [oddVertexOrder_length]
  exact oddVertices_card_mod_two G edges

def oddVertexAt (G : Network) (edges : List (Fin G.q))
    (i : Fin (oddVertexOrder G edges).length) : Fin G.n :=
  (oddVertexOrder G edges).get i

theorem oddVertexAt_injective (G : Network) (edges : List (Fin G.q)) :
    Function.Injective (oddVertexAt G edges) := by
  intro i j equal
  apply Fin.ext
  exact (List.getElem_inj (oddVertexOrder_nodup G edges)).mp equal

theorem oddVertexAt_range (G : Network) (edges : List (Fin G.q)) (v : Fin G.n) :
    v ∈ oddVertices G edges ↔ ∃ i, oddVertexAt G edges i = v := by
  rw [← mem_oddVertexOrder]
  exact ⟨fun h => List.get_of_mem h, fun ⟨i, eq⟩ => eq ▸ List.get_mem _ i⟩

private theorem natIndicesOfFinRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem oddVertexPrefix_graph {G : Network} {edges : List (Fin G.q)} {s : ArithmeticState}
    (flags : ∀ v : Fin G.n, s.nm (s.nr 9 + v.val) = degree G edges v % 2) :
    oddVertexPrefix s G.n = (oddVertexOrder G edges).map Fin.val := by
  unfold oddVertexPrefix oddVertexOrder
  rw [← natIndicesOfFinRange, List.filter_map]
  apply congrArg (List.map Fin.val)
  have agree (v : Fin G.n) :
      decide (s.nm (s.nr 9 + v.val) ≠ 0) = decide (v ∈ oddVertices G edges) := by
    have modBound := Nat.mod_lt (degree G edges v) (by decide : 0 < 2)
    have odd : degree G edges v % 2 ≠ 0 ↔ degree G edges v % 2 = 1 := by omega
    simp [flags v, oddVertices, Nat.odd_iff, odd]
  exact congrArg (fun predicate => (List.finRange G.n).filter predicate) (funext agree)

theorem compactOddVerticesBlock_graph {G : Network} {edges : List (Fin G.q)} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 10 = 0)
    (n : s.nr 29 = G.n) (arrays : s.nr 9 + s.nr 29 ≤ s.nr 31)
    (flags : ∀ v : Fin G.n, s.nm (s.nr 9 + v.val) = degree G edges v % 2) :
    ∃ t, BlockRuns compactOddVerticesBlock (10 * G.n + 3) s t ∧ t.halted = false ∧
      t.nr 32 = (oddVertexOrder G edges).length ∧
      (∀ r ∈ oddVertexFixed, t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      (∀ i : Fin (oddVertexOrder G edges).length,
        t.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val) ∧
      ∀ addr < s.nr 31, t.nm addr = s.nm addr := by
  obtain ⟨t, run, ready, stable, count, rm, table, below⟩ :=
    compactOddVerticesBlock_correct entry running one zero arrays
  rw [n] at run count table
  rw [oddVertexPrefix_graph flags, List.length_map] at count
  refine ⟨t, run, ready, count, stable, rm, ?_, below⟩
  intro i
  simp [table, oddVertexPrefix_graph flags, i.isLt, oddVertexAt]


end VehicleRoutingSurvey.Routing
end RppSource_OddMatchingInput

/-! runtime/CompactMetric.lean -/
section RppSource_CompactMetric
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Copy one shortest distance to the compact odd-vertex matrix. Registers
17 and 18 are compact row and column indices, 31 is the vertex list base,
and 20 and 21 are the new distance and row-offset bases. -/
def copyCompactMetricCell : List ArithmeticInstruction :=
  [.natAdd 0 31 17, .natLoad 1 0, .natAdd 0 31 18, .natLoad 2 0,
   .natAdd 0 3 1, .natLoad 1 0, .natAdd 1 4 1, .natAdd 0 1 2, .realLoad 0 0,
   .natAdd 0 21 17, .natLoad 1 0, .natAdd 1 20 1, .natAdd 0 1 18, .realStore 0 0]

theorem copyCompactMetricCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let u := s.nm (s.nr 31 + s.nr 17)
    let v := s.nm (s.nr 31 + s.nr 18)
    let source := s.nr 4 + s.nm (s.nr 3 + u) + v
    let destination := s.nr 20 + s.nm (s.nr 21 + s.nr 17) + s.nr 18
    ∃ t, BlockRuns copyCompactMetricCell 14 s t ∧ t.halted = false ∧ t.nm = s.nm ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → t.nr r = s.nr r) ∧
      t.rm = Function.update s.rm destination (s.rm source) := by
  let t := (arithmeticStep copyCompactMetricCell)^[14] s
  have ready : t.halted = false := by
    simp [t, copyCompactMetricCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = copyCompactMetricCell.length := by
    simp [t, copyCompactMetricCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_⟩
  · simp [t, copyCompactMetricCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r not0 not1 not2
    simp [t, copyCompactMetricCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne not0, Function.update_of_ne not1, Function.update_of_ne not2]
  · simp [t, copyCompactMetricCell, arithmeticStep, entry, running, Function.iterate_succ_apply']

def copyCompactMetricRow : List ArithmeticInstruction :=
  countedLoopFromZero 6 18 32 copyCompactMetricCell

def copyCompactMetricBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 17 32 copyCompactMetricRow

/-- The larger matrix and its lookup table stay live while the compact
matrix is filled in a disjoint part of real memory. -/
structure CompactMetricFrame {n k : ℕ} (vertices : Fin k → Fin n) (s : ArithmeticState) : Prop where
  floyd : FloydFrame n (s.nr 3) (s.nr 4) s
  count : s.nr 32 = k
  oddList : ∀ i, s.nm (s.nr 31 + i.val) = (vertices i).val
  offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i
  separate : s.nr 4 + n * n ≤ s.nr 20

def metricStable (s t : ArithmeticState) : Prop :=
  ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 17 → r ≠ 18 → t.nr r = s.nr r

private theorem metricKeep (s t : ArithmeticState) (fixed : metricStable s t)
    {r : ℕ} (safe : r ∈ [3, 4, 6, 20, 21, 31, 32]) : t.nr r = s.nr r := by
  rcases (by simpa using safe : r = 3 ∨ r = 4 ∨ r = 6 ∨ r = 20 ∨ r = 21 ∨ r = 31 ∨ r = 32)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fixed _ (by decide) (by decide)
      (by decide) (by decide) (by decide)

private structure CompactMetricProgress {n k : ℕ} (vertices : Fin k → Fin n)
    (initial : ArithmeticState) (row col : ℕ) (current : ArithmeticState) : Prop where
  naturalMemory : current.nm = initial.nm
  registers : metricStable initial current
  source : ∀ a < initial.nr 20, current.rm a = initial.rm a
  done : ∀ a b : Fin k, a.val < row ∨ (a.val = row ∧ b.val < col) →
    current.rm (initial.nr 20 + k * a.val + b.val) =
      initial.rm (initial.nr 4 + n * (vertices a).val + (vertices b).val)

private theorem CompactMetricProgress.cell {n k : ℕ} {vertices : Fin k → Fin n}
    {initial current : ArithmeticState} (input : CompactMetricFrame vertices initial)
    (i j : Fin k) (prior : CompactMetricProgress vertices initial i.val j.val current)
    (entry : current.pc = 0) (running : current.halted = false)
    (row : current.nr 17 = i.val) (col : current.nr 18 = j.val) :
    ∃ t, BlockRuns copyCompactMetricCell 14 current t ∧ t.halted = false ∧
      t.nr 17 = i.val ∧ t.nr 18 = j.val ∧ CompactMetricProgress vertices initial i.val (j.val + 1) t := by
  obtain ⟨t, run, ready, nm, fixed, memory⟩ := copyCompactMetricCell_correct entry running
  let source := initial.nr 4 + n * (vertices i).val + (vertices j).val
  let destination := initial.nr 20 + k * i.val + j.val
  have rowIndex := input.oddList i
  have colIndex := input.oddList j
  have rowOffset := input.floyd.rows (vertices i).val (vertices i).isLt
  have compactOffset := input.offsets i.val i.isLt
  have written : t.rm = Function.update current.rm destination (current.rm source) := by
    simpa only [prior.naturalMemory, metricKeep _ _ prior.registers (by decide : 3 ∈ _),
      metricKeep _ _ prior.registers (by decide : 4 ∈ _), metricKeep _ _ prior.registers (by decide : 20 ∈ _),
      metricKeep _ _ prior.registers (by decide : 21 ∈ _), metricKeep _ _ prior.registers (by decide : 31 ∈ _),
      row, col, rowIndex, colIndex, rowOffset, compactOffset, source, destination] using memory
  have indexBound : n * (vertices i).val + (vertices j).val < n * n := by
    calc
      _ < n * (vertices i).val + n := Nat.add_lt_add_left (vertices j).isLt _
      _ = n * ((vertices i).val + 1) := by rw [Nat.mul_succ]
      _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (vertices i).isLt)
  have below : source < initial.nr 20 := by
    have boundary := input.separate
    unfold source
    omega
  have registers : metricStable initial t := by
    intro r p0 p1 p2 p17 p18
    exact (fixed r p0 p1 p2).trans (prior.registers r p0 p1 p2 p17 p18)
  refine ⟨t, run, ready, (fixed 17 (by decide) (by decide) (by decide)).trans row,
    (fixed 18 (by decide) (by decide) (by decide)).trans col,
    ⟨nm.trans prior.naturalMemory, registers, ?_, ?_⟩⟩
  · intro a early
    rw [written, Function.update_of_ne (by unfold destination; omega)]
    exact prior.source a early
  · intro a b processed
    by_cases same : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := same
      change t.rm destination = initial.rm source
      rw [written, Function.update_self]
      exact prior.source source below
    · have different : initial.nr 20 + k * a.val + b.val ≠ destination := by
        intro equal
        have offset : k * a.val + b.val = k * i.val + j.val := by
          unfold destination at equal
          omega
        obtain ⟨left, right⟩ := (denseMatrixOffset_eq_iff b.isLt j.isLt).mp offset
        exact same ⟨Fin.ext left, Fin.ext right⟩
      rw [written, Function.update_of_ne different]
      apply prior.done
      have earlier : ¬(a.val = i.val ∧ b.val = j.val) :=
        fun h => same ⟨Fin.ext h.1, Fin.ext h.2⟩
      omega

private structure CompactRowInvariant {n k : ℕ} (vertices : Fin k → Fin n)
    (initial : ArithmeticState) (row col : ℕ) (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  index : current.nr 18 = col
  rowIndex : current.nr 17 = row
  progress : CompactMetricProgress vertices initial row col current

private theorem compactMetricRow_correct {n k : ℕ} {vertices : Fin k → Fin n}
    {initial current : ArithmeticState} (input : CompactMetricFrame vertices initial) (i : Fin k)
    (prior : CompactMetricProgress vertices initial i.val 0 current)
    (entry : current.pc = 0) (running : current.halted = false) (row : current.nr 17 = i.val) :
    ∃ t, BlockRuns copyCompactMetricRow (1 + (k * 17 + 1)) current t ∧ t.halted = false ∧
      t.nr 17 = i.val ∧ CompactMetricProgress vertices initial (i.val + 1) 0 t := by
  have seed : CompactRowInvariant vertices initial i.val 0
      {current with pc := 0, nr := Function.update current.nr 18 0} := by
    refine ⟨rfl, running, by simp, by simp [row],
      ⟨prior.naturalMemory, ?_, prior.source, prior.done⟩⟩
    intro r p0 p1 p2 p17 p18
    exact (Function.update_of_ne p18 _ _).trans (prior.registers r p0 p1 p2 p17 p18)
  have control (j : ℕ) (m : ArithmeticState) (inv : CompactRowInvariant vertices initial i.val j m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 18 = j ∧ m.nr 32 = k :=
    ⟨inv.entry, inv.running, inv.index, (metricKeep _ _ inv.progress.registers (by decide)).trans input.count⟩
  have iterate (j : ℕ) (below : j < k) (m : ArithmeticState)
      (inv : CompactRowInvariant vertices initial i.val j m) :
      ∃ t, BlockRuns copyCompactMetricCell 14 m t ∧ t.halted = false ∧
        CompactRowInvariant vertices initial i.val (j + 1)
          {t with pc := 0, nr := Function.update t.nr 18 (t.nr 18 + t.nr 6)} := by
    obtain ⟨t, run, ready, row, col, progress⟩ :=
      inv.progress.cell input i ⟨j, below⟩ inv.entry inv.running inv.rowIndex inv.index
    have one : t.nr 6 = 1 := (metricKeep _ _ progress.registers (by decide)).trans input.floyd.one
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [col, one], by simp [row],
      ⟨progress.naturalMemory, ?_, progress.source, progress.done⟩⟩⟩
    intro r p0 p1 p2 p17 p18
    exact (Function.update_of_ne p18 _ _).trans (progress.registers r p0 p1 p2 p17 p18)
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 18 32 k 14 copyCompactMetricCell
    (CompactRowInvariant vertices initial i.val) entry running seed control iterate
  refine ⟨_, run, inv.running, inv.rowIndex,
    ⟨inv.progress.naturalMemory, inv.progress.registers, inv.progress.source, ?_⟩⟩
  intro a b processed
  apply inv.progress.done
  have valid := b.isLt
  omega

private structure CompactRowsInvariant {n k : ℕ} (vertices : Fin k → Fin n)
    (initial : ArithmeticState) (i : ℕ) (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  index : current.nr 17 = i
  progress : CompactMetricProgress vertices initial i 0 current

theorem copyCompactMetricBlock_correct {n k : ℕ} {vertices : Fin k → Fin n}
    {s : ArithmeticState} (input : CompactMetricFrame vertices s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns copyCompactMetricBlock (1 + (k * (17 * k + 5) + 1)) s t ∧
      t.halted = false ∧ t.nm = s.nm ∧ metricStable s t ∧
      (∀ addr < s.nr 20, t.rm addr = s.rm addr) ∧
      (∀ i j : Fin k, t.rm (s.nr 20 + k * i.val + j.val) =
        s.rm (s.nr 4 + n * (vertices i).val + (vertices j).val)) := by
  have seed : CompactRowsInvariant vertices s 0 {s with pc := 0, nr := Function.update s.nr 17 0} := by
    refine ⟨rfl, running, by simp, ⟨rfl, ?_, fun _ _ => rfl, ?_⟩⟩
    · intro r _ _ _ p17 _
      exact Function.update_of_ne p17 _ _
    · intro i j invalid
      omega
  have control (i : ℕ) (m : ArithmeticState) (inv : CompactRowsInvariant vertices s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 32 = k :=
    ⟨inv.entry, inv.running, inv.index, (metricKeep _ _ inv.progress.registers (by decide)).trans input.count⟩
  have iterate (i : ℕ) (below : i < k) (m : ArithmeticState) (inv : CompactRowsInvariant vertices s i m) :
      ∃ t, BlockRuns copyCompactMetricRow (1 + (k * 17 + 1)) m t ∧ t.halted = false ∧
        CompactRowsInvariant vertices s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    obtain ⟨t, run, ready, row, progress⟩ :=
      compactMetricRow_correct input ⟨i, below⟩ inv.progress inv.entry inv.running inv.index
    have one : t.nr 6 = 1 := (metricKeep _ _ progress.registers (by decide)).trans input.floyd.one
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [row, one],
      ⟨progress.naturalMemory, ?_, progress.source, progress.done⟩⟩⟩
    intro r p0 p1 p2 p17 p18
    exact (Function.update_of_ne p17 _ _).trans (progress.registers r p0 p1 p2 p17 p18)
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 17 32 k (1 + (k * 17 + 1))
    copyCompactMetricRow (CompactRowsInvariant vertices s) entry running seed control iterate
  have elapsed : 1 + (k * ((1 + (k * 17 + 1)) + 3) + 1) = 1 + (k * (17 * k + 5) + 1) := by ring
  rw [elapsed] at run
  exact ⟨_, run, inv.running, inv.progress.naturalMemory, inv.progress.registers, inv.progress.source,
    fun i j => inv.progress.done i j (Or.inl i.isLt)⟩


end VehicleRoutingSurvey.Routing
end RppSource_CompactMetric

/-! runtime/CompactMetricOffsets.lean -/
section RppSource_CompactMetricOffsets
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

private def compactOffsetCell : List ArithmeticInstruction :=
  [.natAdd 0 21 17, .natStore 0 22, .natAdd 22 22 32]

def compactMetricOffsetsBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 22 0] (countedLoopFromZero 6 17 32 compactOffsetCell)

private def compactOffsetFixed (s t : ArithmeticState) : Prop :=
  ∀ r, r ≠ 0 → r ≠ 17 → r ≠ 22 → t.nr r = s.nr r

private structure CompactOffsetInvariant (s : ArithmeticState) (i : ℕ) (t : ArithmeticState) :
    Prop where
  entry : t.pc = 0
  running : t.halted = false
  cursor : t.nr 17 = i
  offset : t.nr 22 = s.nr 32 * i
  fixed : compactOffsetFixed s t
  realMemory : t.rm = s.rm
  slots : ∀ a, t.nm a =
    if s.nr 21 ≤ a ∧ a < s.nr 21 + i then s.nr 32 * (a - s.nr 21) else s.nm a

theorem compactMetricOffsetsBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns compactMetricOffsetsBlock (6 * s.nr 32 + 3) s t ∧ t.halted = false ∧
      compactOffsetFixed s t ∧ t.rm = s.rm ∧
      (∀ i < s.nr 32, t.nm (s.nr 21 + i) = s.nr 32 * i) ∧
      (∀ a < s.nr 21, t.nm a = s.nm a) := by
  let first := {s with pc := 0, nr := Function.update s.nr 22 0}
  have seed : CompactOffsetInvariant s 0 {first with pc := 0, nr := Function.update first.nr 17 0} := by
    refine ⟨rfl, running, by simp, by simp [first], ?_, rfl, ?_⟩
    · intro r _ not17 not22
      simp [first, Function.update_of_ne not17, Function.update_of_ne not22]
    · intro a
      simp only [Nat.add_zero, if_neg (show ¬(s.nr 21 ≤ a ∧ a < s.nr 21) by omega)]
      rfl
  have control (i : ℕ) (m : ArithmeticState) (inv : CompactOffsetInvariant s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 32 = s.nr 32 :=
    ⟨inv.entry, inv.running, inv.cursor, inv.fixed 32 (by decide) (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 32) (m : ArithmeticState) (inv : CompactOffsetInvariant s i m) :
      ∃ t, BlockRuns compactOffsetCell 3 m t ∧ t.halted = false ∧
        CompactOffsetInvariant s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    let address := s.nr 21 + i
    let t := {m with
      pc := 3
      nr := Function.update (Function.update m.nr 0 address) 22 (s.nr 32 * i + s.nr 32)
      nm := Function.update m.nm address (s.nr 32 * i)}
    have table := inv.fixed 21 (by decide) (by decide) (by decide)
    have size := inv.fixed 32 (by decide) (by decide) (by decide)
    have oneAt := (inv.fixed 6 (by decide) (by decide) (by decide)).trans one
    have run : (arithmeticStep compactOffsetCell)^[3] m = t := by
      simp [compactOffsetCell, arithmeticStep, inv.entry, inv.running, table, size,
        inv.cursor, inv.offset, t, address, Function.iterate_succ_apply']
    refine ⟨t, BlockRuns.of_running_exit run inv.running rfl, inv.running,
      ⟨rfl, inv.running, by simp [t, inv.cursor, oneAt], by simp [t, Nat.mul_succ], ?_,
        inv.realMemory, ?_⟩⟩
    · intro r not0 not17 not22
      simp [t, Function.update_of_ne not0, Function.update_of_ne not17, Function.update_of_ne not22,
        inv.fixed r not0 not17 not22]
    · intro a
      change Function.update m.nm address (s.nr 32 * i) a = _
      by_cases same : a = address
      · subst a
        rw [Function.update_self, if_pos (by unfold address; omega)]
        simp [address]
      · rw [Function.update_of_ne same, inv.slots]
        have before : (s.nr 21 ≤ a ∧ a < s.nr 21 + i) ↔
            (s.nr 21 ≤ a ∧ a < s.nr 21 + (i + 1)) := by unfold address at same; omega
        simp only [before]
  obtain ⟨last, inv, loop⟩ := countedLoopFromZero_correct 6 17 32 (s.nr 32) 3
    compactOffsetCell (CompactOffsetInvariant s) (s := first) rfl running seed control iterate
  have run := (zeroRegister_runs 22 s entry running).append loop
  have elapsed : 1 + (1 + (s.nr 32 * (3 + 3) + 1)) = 6 * s.nr 32 + 3 := by omega
  rw [elapsed] at run
  refine ⟨_, run, inv.running, inv.fixed, inv.realMemory, ?_, ?_⟩
  · intro i inside
    change last.nm (s.nr 21 + i) = _
    rw [inv.slots, if_pos (by omega)]
    simp
  · intro a early
    change last.nm a = _
    rw [inv.slots, if_neg (by omega)]


end VehicleRoutingSurvey.Routing
end RppSource_CompactMetricOffsets

/-! runtime/OddMetricInput.lean -/
section RppSource_OddMetricInput
namespace VehicleRoutingSurvey.Routing

def prepareOddMetricBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock compactOddVerticesBlock compactMetricOffsetsBlock) copyCompactMetricBlock

/-- Compact the odd vertices and copy their exact distance submatrix.
Register 32 holds the new dimension. Natural registers 20, 21 and 31
address the real matrix, its natural row offsets, and the vertex map. -/
theorem prepareOddMetricBlock_correct {G : Network} {edges : List (Fin G.q)}
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (floyd : FloydFrame G.n (s.nr 3) (s.nr 4) s)
    (zero : s.nr 10 = 0) (dimension : s.nr 29 = G.n)
    (tableBefore : s.nr 3 + G.n ≤ s.nr 31) (parityBefore : s.nr 9 + G.n ≤ s.nr 31)
    (verticesBefore : s.nr 31 + G.n ≤ s.nr 21) (matrixBefore : s.nr 4 + G.n * G.n ≤ s.nr 20)
    (flags : ∀ v : Fin G.n, s.nm (s.nr 9 + v.val) = degree G edges v % 2)
    (costs : ∀ u v : Fin G.n, s.rm (s.nr 4 + G.n * u.val + v.val) = distance G u v) :
    let k := (oddVertexOrder G edges).length
    ∃ t, BlockRuns prepareOddMetricBlock (10 * G.n + 3 + (6 * k + 3) + (1 + (k * (17 * k + 5) + 1))) s t ∧
      t.halted = false ∧ t.nr 32 = k ∧ t.nr 20 = s.nr 20 ∧ t.nr 21 = s.nr 21 ∧
      t.nr 31 = s.nr 31 ∧ (∀ r ∈ oddVertexFixed, t.nr r = s.nr r) ∧
      (∀ i : Fin k, t.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val) ∧
      (∀ i < k, t.nm (s.nr 21 + i) = k * i) ∧
      (∀ i j : Fin k, t.rm (s.nr 20 + k * i.val + j.val) =
        distance G (oddVertexAt G edges i) (oddVertexAt G edges j)) ∧
      (∀ a < s.nr 31, t.nm a = s.nm a) ∧ (∀ a < s.nr 20, t.rm a = s.rm a) := by
  let k := (oddVertexOrder G edges).length
  have kBound : k ≤ G.n := by
    simpa [k, oddVertexOrder] using
      (List.length_filter_le (fun v => decide (v ∈ oddVertices G edges)) (List.finRange G.n))
  obtain ⟨verts, verticesRun, verticesReady, count, vf, vReal, oddMap, vBelow⟩ :=
    compactOddVerticesBlock_graph entry running floyd.one zero dimension
      (by rw [dimension]; exact parityBefore) flags
  obtain ⟨rows, rowsRun, rowsReady, rf, rReal, offsets, rBelow⟩ :=
    compactMetricOffsetsBlock_correct (s := {verts with pc := 0}) rfl verticesReady
      ((vf 6 (by decide)).trans floyd.one)
  have keep (r : ℕ) (member : r ∈ oddVertexFixed) : rows.nr r = s.nr r := by
    have not0 : r ≠ 0 := by rintro rfl; simp [oddVertexFixed] at member
    have not17 : r ≠ 17 := by rintro rfl; simp [oddVertexFixed] at member
    have not22 : r ≠ 22 := by rintro rfl; simp [oddVertexFixed] at member
    exact (rf r not0 not17 not22).trans (vf r member)
  have sameReal : rows.rm = s.rm := rReal.trans vReal
  have rowCount : rows.nr 32 = k := (rf 32 (by decide) (by decide) (by decide)).trans count
  have mapExact (i : Fin k) : rows.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val := by
    have h := i.isLt
    have small : s.nr 31 + i.val < verts.nr 21 := by rw [vf 21 (by decide)]; omega
    exact (rBelow _ small).trans (oddMap i)
  have rawExact (a : ℕ) (small : a < s.nr 31) : rows.nm a = s.nm a := by
    have earlier : a < verts.nr 21 := by rw [vf 21 (by decide)]; omega
    exact (rBelow a earlier).trans (vBelow a small)
  have offsetExact (i : ℕ) (valid : i < k) : rows.nm (s.nr 21 + i) = k * i := by
    have atRow := offsets i (by rw [show verts.nr 32 = k from count]; exact valid)
    simpa only [vf 21 (by decide), count] using atRow
  have sourceRows : ∀ i < G.n, rows.nm (rows.nr 3 + i) = G.n * i := by
    intro i valid
    rw [keep 3 (by decide), rawExact _ (by omega)]
    exact floyd.rows i valid
  have fullFrame : FloydFrame G.n (rows.nr 3) (rows.nr 4) {rows with pc := 0} :=
    ⟨rfl, rfl, (keep 5 (by decide)).trans floyd.dimension, (keep 6 (by decide)).trans floyd.one, sourceRows⟩
  have metricInput : CompactMetricFrame (oddVertexAt G edges) {rows with pc := 0} := by
    refine ⟨fullFrame, rowCount, ?_, ?_, ?_⟩
    · intro i
      change rows.nm (rows.nr 31 + i.val) = _
      rw [keep 31 (by decide)]
      exact mapExact i
    · intro i valid
      change rows.nm (rows.nr 21 + i) = _
      rw [keep 21 (by decide)]
      exact offsetExact i valid
    · change rows.nr 4 + G.n * G.n ≤ rows.nr 20
      rw [keep 4 (by decide), keep 20 (by decide)]
      exact matrixBefore
  obtain ⟨result, copied, resultReady, noNaturalWrites, rfCopy, belowCopy, values⟩ :=
    copyCompactMetricBlock_correct metricInput rfl rowsReady
  have combined := (verticesRun.append rowsRun).append copied
  have time : 6 * ({verts with pc := 0} : ArithmeticState).nr 32 + 3 = 6 * k + 3 := by
    change 6 * verts.nr 32 + 3 = _
    rw [count]
  rw [time] at combined
  have regs (r : ℕ) (p0 : r ≠ 0) (p1 : r ≠ 1) (p2 : r ≠ 2) (p17 : r ≠ 17) (p18 : r ≠ 18) :
      result.nr r = rows.nr r := rfCopy r p0 p1 p2 p17 p18
  have fullFixed (r : ℕ) (member : r ∈ oddVertexFixed) : result.nr r = s.nr r := by
    have safe : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 17 ∧ r ≠ 18 := by
      simp [oddVertexFixed] at member
      omega
    exact (regs r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2).trans (keep r member)
  refine ⟨_, combined, resultReady, (regs 32 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans rowCount,
    (regs 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (keep 20 (by decide)),
    (regs 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (keep 21 (by decide)),
    (regs 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (keep 31 (by decide)),
    fullFixed, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change result.nm (s.nr 31 + i.val) = _
    exact (congrFun noNaturalWrites _).trans (mapExact i)
  · intro i valid
    change result.nm (s.nr 21 + i) = _
    exact (congrFun noNaturalWrites _).trans (offsetExact i valid)
  · intro i j
    change result.rm (s.nr 20 + k * i.val + j.val) = _
    have copy := values i j
    change result.rm (rows.nr 20 + k * i.val + j.val) =
      rows.rm (rows.nr 4 + G.n * (oddVertexAt G edges i).val + (oddVertexAt G edges j).val) at copy
    rw [keep 20 (by decide), keep 4 (by decide), sameReal] at copy
    exact copy.trans (costs _ _)
  · intro a small
    change result.nm a = _
    exact (congrFun noNaturalWrites a).trans (rawExact a small)
  · intro a small
    change result.rm a = _
    have prior : a < rows.nr 20 := by rwa [keep 20 (by decide)]
    exact (belowCopy a prior).trans (congrFun sameReal a)


end VehicleRoutingSurvey.Routing
end RppSource_OddMetricInput

/-! runtime/EulerTour.lean -/
section RppSource_EulerTour
namespace VehicleRoutingSurvey.Routing

theorem EulerOutputCells.code {G : Network} {memory : ℕ → ℕ} {base : ℕ}
    {ts : List (Traversal G)} (cells : EulerOutputCells memory base ts) :
    ((List.range (2 * ts.length)).map fun i => memory (base + i)) =
      ts.flatMap (fun t => [t.1.val, if t.2 then 1 else 0]) := by
  induction ts generalizing base with
  | nil => rfl
  | cons t rest ih =>
    have length : 2 * (t :: rest).length = 2 + 2 * rest.length := by
      simp [Nat.mul_succ, Nat.add_comm]
    rw [length, List.range_add, List.map_append, List.map_map, show List.range 2 = [0, 1] by decide]
    simp [Function.comp_def, ← Nat.add_assoc, cells.1, cells.2.1, ih cells.2.2]

/-- Once the occurrence arrays are initialized, one linear-cost RAM
block emits the complete Euler circuit. Its first traversal starts at cell 2. -/
theorem eulerTraversalBlock_tour {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (two : s.nr 14 = 2)
    (three : s.nr 15 = 3) (four : s.nr 16 = 4)
    (heads : s.nr 7 = layout.heads) (stack : s.nr 12 = layout.stack)
    (bound : s.nr 18 = 4 * edges.length + 1)
    (rep : EulerMemory layout (EulerTickView.read s) (EulerTraversalState.initial edges root))
    (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (connected : EdgeSupportConnected G edges) (supported : EdgeSupport G edges root) :
    ∃ t ts, BlockRuns eulerTraversalBlock (80 * edges.length + 22) s t ∧
      t.halted = false ∧ (∀ r ∈ [6, 10, 19, 28], t.nr r = s.nr r) ∧
      IsPath G root ts root ∧ (ts.map Prod.fst).Perm edges ∧
      ((List.range (2 * edges.length)).map fun i => t.nm (2 + i)) =
        ts.flatMap (fun r => [r.1.val, if r.2 then 1 else 0]) := by
  obtain ⟨t, run, ready, _, _, fixed, projection⟩ :=
    eulerTraversalBlock_correct entry running one zero two three four
  let final := (EulerTraversalState.step undirected even)^[4 * edges.length + 1]
    (EulerTraversalState.initial edges root)
  have correct : IsPath G root final.cursor.output root ∧ (final.cursor.output.map Prod.fst).Perm edges :=
    EulerTraversalState.output_correct undirected even connected supported
  have encoded : EulerMemory layout (EulerTickView.read t) final := by
    rw [projection, heads, stack, bound]
    exact rep.iterate undirected even (4 * edges.length + 1)
  have length : final.cursor.output.length = edges.length := by simpa using correct.2.length_eq
  have index : (EulerTickView.read t).outputCursor = 2 := by
    rw [encoded.outputCursor, length]
    omega
  have code := encoded.outputCells.code
  rw [index, length] at code
  have outputRegs (r : ℕ) (used : r ∈ [6, 10, 19, 28]) : t.nr r = s.nr r :=
    fixed r (by simp at used ⊢; tauto)
  exact ⟨t, final.cursor.output, by convert run using 1 <;> omega, ready, outputRegs,
    correct.1, correct.2, code⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerTour

/-! runtime/EulerOutput.lean -/
section RppSource_EulerOutput
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Prepare the traversal from the occurrence count in register 18,
stack base in register 27 and root in register 28. -/
def prepareEulerTraversalBlock : List ArithmeticInstruction :=
  [.natAdd 8 28 10, .natAdd 12 27 10, .natAdd 11 12 10,
   .natAdd 13 18 18, .natAdd 13 13 24,
   .natAdd 14 24 10, .natAdd 15 14 6, .natAdd 16 15 6,
   .natAdd 19 18 18, .natAdd 19 19 6,
   .natAdd 18 18 18, .natAdd 18 18 18, .natAdd 18 18 6]

theorem prepareEulerTraversalBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (two : s.nr 24 = 2) :
    ∃ t, BlockRuns prepareEulerTraversalBlock 13 s t ∧ t.halted = false ∧ t.nm = s.nm ∧
      (∀ r ∈ [6, 7, 10, 27, 28], t.nr r = s.nr r) ∧
      t.nr 8 = s.nr 28 ∧ t.nr 12 = s.nr 27 ∧ t.nr 11 = s.nr 27 ∧
      t.nr 13 = 2 + 2 * s.nr 18 ∧ t.nr 14 = 2 ∧ t.nr 15 = 3 ∧ t.nr 16 = 4 ∧
      t.nr 19 = 2 * s.nr 18 + 1 ∧ t.nr 18 = 4 * s.nr 18 + 1 := by
  let t := (arithmeticStep prepareEulerTraversalBlock)^[13] s
  have ready : t.halted = false := by
    simp [t, prepareEulerTraversalBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = prepareEulerTraversalBlock.length := by
    simp [t, prepareEulerTraversalBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, prepareEulerTraversalBlock, arithmeticStep, entry, running, one, zero, two,
    Function.iterate_succ_apply', or_imp, forall_and] <;> omega

def storeEulerOutputHeader : List ArithmeticInstruction :=
  [.natStore 10 19, .natStore 6 28]

theorem storeEulerOutputHeader_correct {G : Network} {root : Fin G.n}
    {ts : List (Traversal G)} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0)
    (length : s.nr 19 = 2 * ts.length + 1) (vertex : s.nr 28 = root.val)
    (tail : ((List.range (2 * ts.length)).map fun i => s.nm (2 + i)) =
      ts.flatMap (fun r => [r.1.val, if r.2 then 1 else 0])) :
    ∃ t, BlockRuns storeEulerOutputHeader 2 s t ∧ t.halted = false ∧
      arithmeticOutput t = tourCode G root ts := by
  let memory := Function.update (Function.update s.nm 0 (2 * ts.length + 1)) 1 root.val
  let t := {s with pc := 2, nm := memory}
  have execute : (arithmeticStep storeEulerOutputHeader)^[2] s = t := by
    simp [t, memory, storeEulerOutputHeader, arithmeticStep, entry, running,
      Function.iterate_succ_apply', one, zero, length, vertex]
  have storedLength : t.nm 0 = 2 * ts.length + 1 := by simp [t, memory]
  have storedRoot : t.nm 1 = root.val := by simp [t, memory]
  have rest (i : ℕ) : t.nm (i.succ + 1) = s.nm (2 + i) := by
    have notZero : i.succ + 1 ≠ 0 := by omega
    have notOne : i.succ + 1 ≠ 1 := by omega
    rw [show i.succ + 1 = 2 + i by omega] at notZero notOne ⊢
    simp [t, memory, Function.update_of_ne notZero, Function.update_of_ne notOne]
  refine ⟨t, BlockRuns.of_running_exit execute running rfl, running, ?_⟩
  simp only [arithmeticOutput, storedLength, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.zero_add, storedRoot, tourCode, Function.comp_def, rest, tail]


end VehicleRoutingSurvey.Routing
end RppSource_EulerOutput

/-! runtime/EulerBuildTour.lean -/
section RppSource_EulerBuildTour
namespace VehicleRoutingSurvey.Routing

def buildAndWriteEulerTourBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock buildEulerOccurrencesBlock prepareEulerTraversalBlock)
    eulerTraversalBlock) storeEulerOutputHeader

/-- A linear-cost block from the array of augmented link occurrences to
the mission's output encoding. Its workspace starts with empty head cells. -/
theorem buildAndWriteEulerTourBlock_correct
    {G : Network} {edges : List (Fin G.q)} {root : Fin G.n}
    {layout : EulerLayout G.n edges.length} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (two : s.nr 24 = 2)
    (width : s.nr 22 = 12) (halfWidth : s.nr 26 = 6)
    (heads : s.nr 7 = layout.heads) (flags : s.nr 25 = layout.active)
    (stack : s.nr 27 = layout.stack) (vertex : s.nr 28 = root.val)
    (count : s.nr 18 = edges.length) (remaining : s.nr 20 = edges.length)
    (dartEnd : s.nr 21 = layout.darts + 12 * edges.length)
    (inputBound : s.nr 23 + edges.length ≤ layout.active) (rawBound : 2 + 3 * G.q ≤ layout.active)
    (encoded : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (emptyHeads : ∀ v : Fin G.n, s.nm (layout.heads + v.val) = 0)
    (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (connected : EdgeSupportConnected G edges) (supported : EdgeSupport G edges root) :
    ∃ t ts, BlockRuns buildAndWriteEulerTourBlock (130 * edges.length + 39) s t ∧
      t.halted = false ∧ IsPath G root ts root ∧ (ts.map Prod.fst).Perm edges ∧
      arithmeticOutput t = tourCode G root ts := by
  have seed : EulerBuildInvariant layout (s.nr 23) edges.length (EulerBuildView.read s) :=
    EulerBuildInvariant.initial remaining dartEnd encoded emptyHeads
  obtain ⟨built, builtExecutes, builtReady, _, _, buildRegs, projected⟩ :=
    buildEulerOccurrencesBlock_correct entry running one zero width two halfWidth
  have incidence : EulerBuildInvariant layout (s.nr 23) 0 (EulerBuildView.read built) := by
    rw [projected, heads, flags, count]
    exact seed.iterate inputBound rawBound
  have builtOne := (buildRegs 6 (by decide)).trans one
  have builtZero := (buildRegs 10 (by decide)).trans zero
  have builtTwo := (buildRegs 24 (by decide)).trans two
  have builtCount := (buildRegs 18 (by decide)).trans count
  have builtStack := (buildRegs 27 (by decide)).trans stack
  have builtRoot := (buildRegs 28 (by decide)).trans vertex
  obtain ⟨prepared, preparedExecutes, preparedReady, preparedMemory, setupRegs, initialVertex,
    stackBase, stackCursor, outputCursor, finalTwo, finalThree, finalFour, outputSize, iterations⟩ :=
    prepareEulerTraversalBlock_correct (s := {built with pc := 0}) rfl builtReady
      builtOne builtZero builtTwo
  have preparedOne := (setupRegs 6 (by decide)).trans builtOne
  have preparedZero := (setupRegs 10 (by decide)).trans builtZero
  have preparedHeads := (setupRegs 7 (by decide)).trans ((buildRegs 7 (by decide)).trans heads)
  have preparedRoot := (setupRegs 28 (by decide)).trans builtRoot
  have preparedStack := stackBase.trans builtStack
  have preparedCount : prepared.nr 18 = 4 * edges.length + 1 := by rwa [builtCount] at iterations
  have traversalRep :
      EulerMemory layout (EulerTickView.read {prepared with pc := 0})
        (EulerTraversalState.initial edges root) := by
    have view : EulerTickView.read {prepared with pc := 0} =
        ⟨root.val, layout.stack, 2 + 2 * edges.length, built.nm⟩ := by
      simp [EulerTickView.read, initialVertex, builtRoot, stackCursor, builtStack,
        outputCursor, builtCount, preparedMemory]
    rw [view]
    exact incidence.toEulerMemory root
  obtain ⟨walk, ts, traverses, walkReady, walkRegs, closed, uses, tail⟩ :=
    eulerTraversalBlock_tour (s := {prepared with pc := 0}) rfl preparedReady
      preparedOne preparedZero finalTwo finalThree finalFour preparedHeads preparedStack preparedCount
      traversalRep undirected even connected supported
  have length : ts.length = edges.length := by simpa using uses.length_eq
  have encodedLength : walk.nr 19 = 2 * ts.length + 1 := by
    rw [walkRegs 19 (by decide), outputSize, builtCount, length]
  obtain ⟨finished, writeExecutes, finishReady, output⟩ :=
    storeEulerOutputHeader_correct (s := {walk with pc := 0}) rfl walkReady
      ((walkRegs 6 (by decide)).trans preparedOne) ((walkRegs 10 (by decide)).trans preparedZero)
      encodedLength ((walkRegs 28 (by decide)).trans preparedRoot) (by simpa only [length] using tail)
  have total := ((builtExecutes.append preparedExecutes).append traverses).append writeExecutes
  have time :
      1 + (s.nr 18 * 50 + 1) + 13 + (80 * edges.length + 22) + 2 = 130 * edges.length + 39 := by
    rw [count]
    omega
  rw [time] at total
  exact ⟨_, ts, total, finishReady, closed, uses, output⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerBuildTour

/-! runtime/EulerWorkspace.lean -/
section RppSource_EulerWorkspace
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Reserve the new working arrays above both the input arrays and the
output cells, using only addition to compute addresses. -/
def EulerLayout.afterInput (n m inputLimit : ℕ) : EulerLayout n m :=
  let stack := 2 + 2 * m + inputLimit
  let active := stack + m
  let heads := active + m
  ⟨stack, active, heads, heads + n + 1,
    Nat.le_add_right _ _, le_rfl, le_rfl, Nat.lt_succ_self _⟩

def allocateEulerWorkspaceBlock : List ArithmeticInstruction :=
  [.natConst 6 1, .natConst 10 0, .natConst 22 12, .natConst 24 2, .natConst 26 6,
   .natAdd 27 18 18, .natAdd 27 27 24, .natAdd 27 27 30,
   .natAdd 25 27 18, .natAdd 7 25 18, .natAdd 21 7 29, .natAdd 21 21 6,
   .natAdd 20 18 18, .natAdd 0 20 20, .natAdd 20 0 20, .natAdd 20 20 20,
   .natAdd 21 21 20, .natAdd 20 18 10]

theorem allocateEulerWorkspaceBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let layout := EulerLayout.afterInput (s.nr 29) (s.nr 18) (s.nr 30)
    ∃ t, BlockRuns allocateEulerWorkspaceBlock 18 s t ∧ t.halted = false ∧ t.nm = s.nm ∧
      (∀ r ∈ [18, 23, 28, 29, 30], t.nr r = s.nr r) ∧
      t.nr 6 = 1 ∧ t.nr 10 = 0 ∧ t.nr 22 = 12 ∧ t.nr 24 = 2 ∧ t.nr 26 = 6 ∧
      t.nr 7 = layout.heads ∧ t.nr 25 = layout.active ∧ t.nr 27 = layout.stack ∧
      t.nr 20 = s.nr 18 ∧ t.nr 21 = layout.darts + 12 * s.nr 18 := by
  let t := (arithmeticStep allocateEulerWorkspaceBlock)^[18] s
  have ready : t.halted = false := by
    simp [t, allocateEulerWorkspaceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = allocateEulerWorkspaceBlock.length := by
    simp [t, allocateEulerWorkspaceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, allocateEulerWorkspaceBlock, arithmeticStep, entry, running, EulerLayout.afterInput,
    Function.iterate_succ_apply', or_imp, forall_and] <;> omega

private def clearEulerHeadCell : List ArithmeticInstruction :=
  [.natAdd 0 7 17, .natStore 0 10]

def clearEulerHeadsBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 17 29 clearEulerHeadCell

private structure EulerClearInvariant (s : ArithmeticState) (i : ℕ) (t : ArithmeticState) : Prop where
  entry : t.pc = 0
  ready : t.halted = false
  index : t.nr 17 = i
  registers : ∀ r, r ≠ 0 → r ≠ 17 → t.nr r = s.nr r
  realMemory : t.rm = s.rm
  memory : ∀ k, t.nm k = if s.nr 7 ≤ k ∧ k < s.nr 7 + i then 0 else s.nm k

theorem clearEulerHeadsBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 10 = 0) :
    ∃ t, BlockRuns clearEulerHeadsBlock (1 + (s.nr 29 * 5 + 1)) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 0 → r ≠ 17 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ k, t.nm k = if s.nr 7 ≤ k ∧ k < s.nr 7 + s.nr 29 then 0 else s.nm k := by
  have initial : EulerClearInvariant s 0 {s with pc := 0, nr := Function.update s.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ?_⟩
    · intro r _ different
      exact Function.update_of_ne different _ _
    · intro k
      simp only [Nat.add_zero, if_neg (show ¬ (s.nr 7 ≤ k ∧ k < s.nr 7) by omega)]
  have control (i : ℕ) (t : ArithmeticState) (inv : EulerClearInvariant s i t) :
      t.pc = 0 ∧ t.halted = false ∧ t.nr 17 = i ∧ t.nr 29 = s.nr 29 :=
    ⟨inv.entry, inv.ready, inv.index, inv.registers 29 (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 29) (t : ArithmeticState) (inv : EulerClearInvariant s i t) :
      ∃ u, BlockRuns clearEulerHeadCell 2 t u ∧ u.halted = false ∧
        EulerClearInvariant s (i + 1)
          {u with pc := 0, nr := Function.update u.nr 17 (u.nr 17 + u.nr 6)} := by
    let address := s.nr 7 + i
    let u := {t with
      pc := 2
      nr := Function.update t.nr 0 address
      nm := Function.update t.nm address 0}
    have table := inv.registers 7 (by decide) (by decide)
    have tZero := (inv.registers 10 (by decide) (by decide)).trans zero
    have tOne := (inv.registers 6 (by decide) (by decide)).trans one
    have executed : (arithmeticStep clearEulerHeadCell)^[2] t = u := by
      simp [u, address, clearEulerHeadCell, arithmeticStep, inv.entry, inv.ready,
        inv.index, table, tZero, Function.iterate_succ_apply']
    refine ⟨u, BlockRuns.of_running_exit executed inv.ready rfl, inv.ready,
      ⟨rfl, inv.ready, by simp [u, tOne, inv.index], ?_, inv.realMemory, ?_⟩⟩
    · intro r not0 notIndex
      simp [u, Function.update_of_ne not0, Function.update_of_ne notIndex,
        inv.registers r not0 notIndex]
    · intro k
      change Function.update t.nm address 0 k =
        if s.nr 7 ≤ k ∧ k < s.nr 7 + (i + 1) then 0 else s.nm k
      by_cases written : k = address
      · subst k
        rw [Function.update_self, if_pos (by unfold address; omega)]
      · rw [Function.update_of_ne written, inv.memory]
        have ranges : (s.nr 7 ≤ k ∧ k < s.nr 7 + i) ↔ (s.nr 7 ≤ k ∧ k < s.nr 7 + (i + 1)) := by
          unfold address at written
          omega
        simp [ranges]
  obtain ⟨_, last, run⟩ := countedLoopFromZero_correct 6 17 29 (s.nr 29) 2
    clearEulerHeadCell (EulerClearInvariant s) entry running initial control iterate
  exact ⟨_, run, last.ready, last.registers, last.realMemory, last.memory⟩

def eulerFromOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock allocateEulerWorkspaceBlock clearEulerHeadsBlock) buildAndWriteEulerTourBlock

/-- From an occurrence array and the mission's original input links, allocate
the workspace and emit the encoded tour. Register 30 bounds the occupied
natural-memory prefix. -/
theorem eulerFromOccurrencesBlock_correct
    {G : Network} {edges : List (Fin G.q)} {root : Fin G.n} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (count : s.nr 18 = edges.length) (vertices : s.nr 29 = G.n)
    (vertex : s.nr 28 = root.val)
    (inputBound : s.nr 23 + edges.length ≤ s.nr 30)
    (rawBound : 2 + 3 * G.q ≤ s.nr 30)
    (encoded : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G edges v % 2 = 0)
    (connected : EdgeSupportConnected G edges) (supported : EdgeSupport G edges root) :
    ∃ t ts, BlockRuns eulerFromOccurrencesBlock (130 * edges.length + 5 * G.n + 59) s t ∧
      t.halted = false ∧ IsPath G root ts root ∧ (ts.map Prod.fst).Perm edges ∧
      arithmeticOutput t = tourCode G root ts := by
  let layout := EulerLayout.afterInput G.n edges.length (s.nr 30)
  obtain ⟨allocated, allocation, allocatedReady, initialMemory, fixed,
    one, zero, width, two, halfWidth, headBase, flagBase, stackBase, remaining, dartEnd⟩ :=
    allocateEulerWorkspaceBlock_correct entry running
  rw [vertices, count] at headBase flagBase stackBase dartEnd
  obtain ⟨cleared, clearing, clearedReady, sameRegs, _, readMemory⟩ :=
    clearEulerHeadsBlock_correct (s := {allocated with pc := 0}) rfl allocatedReady one zero
  have preserves (r : ℕ) (noScratch : r ≠ 0) (noCounter : r ≠ 17) :
      cleared.nr r = allocated.nr r := sameRegs r noScratch noCounter
  have headEq : allocated.nr 7 = layout.heads := headBase
  have nEq := (fixed 29 (by decide)).trans vertices
  have inputEq := (preserves 23 (by decide) (by decide)).trans (fixed 23 (by decide))
  have available : s.nr 30 ≤ layout.active := by simp [layout, EulerLayout.afterInput] <;> omega
  have endActive := layout.activeEnd
  have untouched (a : ℕ) (below : a < layout.active) : cleared.nm a = s.nm a := by
    have early : a < layout.heads := by omega
    rw [readMemory]
    change (if allocated.nr 7 ≤ a ∧ a < allocated.nr 7 + allocated.nr 29 then 0
      else allocated.nm a) = s.nm a
    rw [headEq, if_neg (by omega), initialMemory]
  have inputs : EulerOccurrenceInput edges (cleared.nr 23) cleared.nm := by
    rw [inputEq]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have bound := i.isLt
      exact (untouched _ (by omega)).trans (encoded.ids i)
    · intro e
      have bound := e.isLt
      exact (untouched _ (by omega)).trans (encoded.tails e)
    · intro e
      have bound := e.isLt
      exact (untouched _ (by omega)).trans (encoded.heads e)
  have labels : ∀ v : Fin G.n, cleared.nm (layout.heads + v.val) = 0 := by
    intro v
    have bound := v.isLt
    rw [readMemory]
    change (if allocated.nr 7 ≤ layout.heads + v.val ∧
        layout.heads + v.val < allocated.nr 7 + allocated.nr 29 then 0
        else allocated.nm (layout.heads + v.val)) = 0
    rw [headEq, nEq, if_pos (by omega)]
  obtain ⟨walk, ts, traversed, ready, closes, covers, output⟩ :=
    buildAndWriteEulerTourBlock_correct (layout := layout) (s := {cleared with pc := 0})
      rfl clearedReady
      ((preserves 6 (by decide) (by decide)).trans one)
      ((preserves 10 (by decide) (by decide)).trans zero)
      ((preserves 24 (by decide) (by decide)).trans two)
      ((preserves 22 (by decide) (by decide)).trans width)
      ((preserves 26 (by decide) (by decide)).trans halfWidth)
      ((preserves 7 (by decide) (by decide)).trans headEq)
      ((preserves 25 (by decide) (by decide)).trans flagBase)
      ((preserves 27 (by decide) (by decide)).trans stackBase)
      ((preserves 28 (by decide) (by decide)).trans ((fixed 28 (by decide)).trans vertex))
      ((preserves 18 (by decide) (by decide)).trans ((fixed 18 (by decide)).trans count))
      ((preserves 20 (by decide) (by decide)).trans (remaining.trans count))
      ((preserves 21 (by decide) (by decide)).trans dartEnd)
      (by change cleared.nr 23 + edges.length ≤ layout.active; omega) (rawBound.trans available)
      inputs labels undirected even connected supported
  have executes := (allocation.append clearing).append traversed
  have elapsed :
      18 + (1 + (({allocated with pc := 0} : ArithmeticState).nr 29 * 5 + 1)) +
        (130 * edges.length + 39) = 130 * edges.length + 5 * G.n + 59 := by
    change 18 + (1 + (allocated.nr 29 * 5 + 1)) + (130 * edges.length + 39) = _
    rw [nEq]
    omega
  rw [elapsed] at executes
  exact ⟨_, ts, executes, ready, closes, covers, output⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerWorkspace

/-! runtime/MatchingInputBlock.lean -/
section RppSource_MatchingInputBlock
namespace VehicleRoutingSurvey.Routing

private def setParityClearBase : List ArithmeticInstruction := [.natAdd 7 9 10]

def prepareMatchingInputBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock setParityClearBase clearEulerHeadsBlock)
    degreeParityScanBlock) prepareOddMetricBlock

/-- Start from the required and connector occurrences, initialize parity,
and produce the exact compact input to weighted perfect matching. -/
theorem prepareMatchingInputBlock_correct {G : Network} {edges : List (Fin G.q)} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (floyd : FloydFrame G.n (s.nr 3) (s.nr 4) s) (zero : s.nr 10 = 0) (two : s.nr 24 = 2)
    (dimension : s.nr 29 = G.n) (occurrences : s.nr 18 = edges.length)
    (offsetsBefore : s.nr 3 + G.n ≤ s.nr 9)
    (inputBefore : s.nr 23 + edges.length ≤ s.nr 9) (rawBefore : 2 + 3 * G.q ≤ s.nr 9)
    (parityBefore : s.nr 9 + G.n ≤ s.nr 31) (verticesBefore : s.nr 31 + G.n ≤ s.nr 21)
    (matrixBefore : s.nr 4 + G.n * G.n ≤ s.nr 20)
    (input : EulerOccurrenceInput edges (s.nr 23) s.nm)
    (costs : ∀ u v : Fin G.n, s.rm (s.nr 4 + G.n * u.val + v.val) = distance G u v) :
    let k := (oddVertexOrder G edges).length
    ∃ t, BlockRuns prepareMatchingInputBlock
        (1 + (1 + (G.n * 5 + 1)) + (19 * edges.length + 2) +
          (10 * G.n + 3 + (6 * k + 3) + (1 + (k * (17 * k + 5) + 1)))) s t ∧
      t.halted = false ∧ t.nr 32 = k ∧ k % 2 = 0 ∧
      (∀ r ∈ oddVertexFixed, t.nr r = s.nr r) ∧
      (∀ i : Fin k, t.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val) ∧
      (∀ i < k, t.nm (s.nr 21 + i) = k * i) ∧
      (∀ i j : Fin k, t.rm (s.nr 20 + k * i.val + j.val) =
        distance G (oddVertexAt G edges i) (oddVertexAt G edges j)) ∧
      (∀ a < s.nr 9, t.nm a = s.nm a) ∧ (∀ a < s.nr 20, t.rm a = s.rm a) := by
  let start := {s with pc := 1, nr := Function.update s.nr 7 (s.nr 9)}
  have setup : BlockRuns setParityClearBase 1 s start := by
    have execute : (arithmeticStep setParityClearBase)^[1] s = start := by
      simp [setParityClearBase, arithmeticStep, entry, running, zero, start]
    exact BlockRuns.of_running_exit execute running rfl
  have startFixed (r : ℕ) (other : r ≠ 7) : start.nr r = s.nr r :=
    Function.update_of_ne other _ _
  obtain ⟨cleared, clears, clearedReady, clearFixed, clearReal, clearSlots⟩ :=
    clearEulerHeadsBlock_correct (s := {start with pc := 0}) rfl running
      ((startFixed 6 (by decide)).trans floyd.one) ((startFixed 10 (by decide)).trans zero)
  have clearReg (r : ℕ) (scratch : r ≠ 0) (base : r ≠ 7) (cursor : r ≠ 17) :
      cleared.nr r = s.nr r :=
    (clearFixed r scratch cursor).trans (startFixed r base)
  have clearN := (clearReg 29 (by decide) (by decide) (by decide)).trans dimension
  have startN := (startFixed 29 (by decide)).trans dimension
  have clearTable (a : ℕ) :
      cleared.nm a = if s.nr 9 ≤ a ∧ a < s.nr 9 + G.n then 0 else s.nm a := by
    simpa [start, dimension] using clearSlots a
  have clearRaw (a : ℕ) (before : a < s.nr 9) : cleared.nm a = s.nm a := by
    rw [clearTable, if_neg (by omega)]
  have clearInput : EulerOccurrenceInput edges (cleared.nr 23) cleared.nm := by
    rw [clearReg 23 (by decide) (by decide) (by decide)]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have := i.isLt
      exact (clearRaw _ (by omega)).trans (input.ids i)
    · intro e
      have := e.isLt
      exact (clearRaw _ (by omega)).trans (input.tails e)
    · intro e
      have := e.isLt
      exact (clearRaw _ (by omega)).trans (input.heads e)
  have allZero (v : Fin G.n) : cleared.nm (cleared.nr 9 + v.val) = 0 := by
    have bound := v.isLt
    rw [clearReg 9 (by decide) (by decide) (by decide), clearTable, if_pos (by omega)]
  obtain ⟨parity, scans, parityReady, parityFixed, parityRaw, parityReal, bits⟩ :=
    degreeParityScanBlock_correct (s := {cleared with pc := 0}) rfl clearedReady
      ((clearReg 6 (by decide) (by decide) (by decide)).trans floyd.one)
      ((clearReg 24 (by decide) (by decide) (by decide)).trans two)
      ((clearReg 18 (by decide) (by decide) (by decide)).trans occurrences)
      (by simpa only [clearReg 23 (by decide) (by decide) (by decide),
        clearReg 9 (by decide) (by decide) (by decide)] using inputBefore)
      (by simpa only [clearReg 9 (by decide) (by decide) (by decide)] using rawBefore)
      clearInput allZero
  have safe (r : ℕ) (member : r ∈ oddVertexFixed) : parity.nr r = s.nr r := by
    have same : r ∈ parityScanPreserved := by
      simp [oddVertexFixed, parityScanPreserved] at member ⊢
      tauto
    have allowed : r ≠ 0 ∧ r ≠ 7 ∧ r ≠ 17 := by simp [oddVertexFixed] at member; omega
    exact (parityFixed r same).trans (clearReg r allowed.1 allowed.2.1 allowed.2.2)
  have savedReal : parity.rm = s.rm := parityReal.trans clearReal
  have savedInput (a : ℕ) (before : a < s.nr 9) : parity.nm a = s.nm a := by
    have earlier : a < cleared.nr 9 := by rwa [clearReg 9 (by decide) (by decide) (by decide)]
    exact (parityRaw a earlier).trans (clearRaw a before)
  have parityFrame : FloydFrame G.n (parity.nr 3) (parity.nr 4) {parity with pc := 0} := by
    refine ⟨rfl, rfl, (safe 5 (by decide)).trans floyd.dimension, (safe 6 (by decide)).trans floyd.one, ?_⟩
    intro i bound
    change parity.nm (parity.nr 3 + i) = _
    rw [safe 3 (by decide), savedInput _ (by omega)]
    exact floyd.rows i bound
  have flags (v : Fin G.n) : parity.nm (parity.nr 9 + v.val) = degree G edges v % 2 := by
    rw [safe 9 (by decide), ← clearReg 9 (by decide) (by decide) (by decide)]
    exact bits v
  have parityCosts (u v : Fin G.n) :
      parity.rm (parity.nr 4 + G.n * u.val + v.val) = distance G u v := by
    rw [savedReal, safe 4 (by decide)]
    exact costs u v
  obtain ⟨result, matrix, ready, count, _, _, _, reg, vertices, offsets, values, earlier, realEarlier⟩ :=
    prepareOddMetricBlock_correct (s := {parity with pc := 0}) rfl parityReady
      parityFrame ((safe 10 (by decide)).trans zero) ((safe 29 (by decide)).trans dimension)
      (by change parity.nr 3 + G.n ≤ parity.nr 31; rw [safe 3 (by decide), safe 31 (by decide)]; omega)
      (by change parity.nr 9 + G.n ≤ parity.nr 31; rw [safe 9 (by decide), safe 31 (by decide)]; exact parityBefore)
      (by change parity.nr 31 + G.n ≤ parity.nr 21; rw [safe 31 (by decide), safe 21 (by decide)]; exact verticesBefore)
      (by change parity.nr 4 + G.n * G.n ≤ parity.nr 20; rw [safe 4 (by decide), safe 20 (by decide)]; exact matrixBefore)
      flags parityCosts
  have total := ((setup.append clears).append scans).append matrix
  have clearTime : 1 + (({start with pc := 0} : ArithmeticState).nr 29 * 5 + 1) = 1 + (G.n * 5 + 1) := by
    change 1 + (start.nr 29 * 5 + 1) = _
    rw [startN]
  rw [clearTime] at total
  refine ⟨_, total, ready, count, oddVertexOrder_even G edges,
    fun r keep => (reg r keep).trans (safe r keep), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change result.nm (s.nr 31 + i.val) = _
    simpa only [safe 31 (by decide)] using vertices i
  · intro i valid
    change result.nm (s.nr 21 + i) = _
    simpa only [safe 21 (by decide)] using offsets i valid
  · intro i j
    change result.rm (s.nr 20 + (oddVertexOrder G edges).length * i.val + j.val) = _
    simpa only [safe 20 (by decide)] using values i j
  · intro a bound
    have before : a < parity.nr 31 := by rw [safe 31 (by decide)]; omega
    exact (earlier a before).trans (savedInput a bound)
  · intro a bound
    have before : a < parity.nr 20 := by rwa [safe 20 (by decide)]
    exact (realEarlier a before).trans (congrFun savedReal a)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInputBlock

/-! runtime/OccurrenceInterface.lean -/
section RppSource_OccurrenceInterface
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Publish the accumulated occurrence length and buffer base for degree
parity, retaining the prefix and the next write cursor. -/
def publishOccurrenceBlock : List ArithmeticInstruction :=
  [.natSub 18 29 33, .natAdd 23 33 28, .natConst 24 2]

theorem publishOccurrenceBlock_correct {s : ArithmeticState} {edges : List (Fin G.q)}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 28 = 0)
    (cursor : s.nr 29 = s.nr 33 + edges.length)
    (encoded : OccurrenceArray s.nm (s.nr 33) edges) :
    ∃ t, BlockRuns publishOccurrenceBlock 3 s t ∧ t.halted = false ∧
      t.nr 18 = edges.length ∧ t.nr 23 = s.nr 33 ∧ t.nr 24 = 2 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ OccurrenceArray t.nm (t.nr 23) edges ∧
      ∀ r, r ≠ 18 → r ≠ 23 → r ≠ 24 → t.nr r = s.nr r := by
  let t := (arithmeticStep publishOccurrenceBlock)^[3] s
  have ready : t.halted = false := by
    simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = publishOccurrenceBlock.length := by
    simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have mem : t.nm = s.nm := by
    simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have base : t.nr 23 = s.nr 33 := by
    simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, base, ?_, mem, ?_, ?_, ?_⟩
  · simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, cursor, Function.iterate_succ_apply']
  · simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · rwa [base, mem]
  · intro r countReg baseReg twoReg
    simp [t, publishOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne countReg, Function.update_of_ne baseReg, Function.update_of_ne twoReg]

private def prepareEulerRegisters : List ArithmeticInstruction :=
  [.natAdd 30 29 28, .natAdd 29 5 28, .natAdd 28 31 28]

private theorem prepareEulerRegisters_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 28 = 0) :
    ∃ t, BlockRuns prepareEulerRegisters 3 s t ∧ t.halted = false ∧
      t.nr 30 = s.nr 29 ∧ t.nr 29 = s.nr 5 ∧ t.nr 28 = s.nr 31 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.nr 18 = s.nr 18 ∧ t.nr 23 = s.nr 23 := by
  let t := (arithmeticStep prepareEulerRegisters)^[3] s
  have ready : t.halted = false := by
    simp [t, prepareEulerRegisters, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = prepareEulerRegisters.length := by
    simp [t, prepareEulerRegisters, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, prepareEulerRegisters, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']

/-- Finish the occurrence phase and allocate subsequent Euler work above
the complete occurrence buffer. The chosen start vertex is register 31. -/
def configureEulerOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock publishOccurrenceBlock prepareEulerRegisters

theorem configureEulerOccurrencesBlock_correct {s : ArithmeticState} {edges : List (Fin G.q)}
    {root : Fin G.n} (entry : s.pc = 0) (running : s.halted = false)
    (zero : s.nr 28 = 0) (dimension : s.nr 5 = G.n) (rootReg : s.nr 31 = root.val)
    (cursor : s.nr 29 = s.nr 33 + edges.length)
    (rawBound : 2 + 3 * G.q ≤ s.nr 29)
    (encoded : OccurrenceArray s.nm (s.nr 33) edges)
    (tailCells : ∀ e : Fin G.q, s.nm (2 + 3 * e.val) = (G.tail e).val)
    (headCells : ∀ e : Fin G.q, s.nm (3 + 3 * e.val) = (G.head e).val) :
    ∃ t, BlockRuns configureEulerOccurrencesBlock 6 s t ∧ t.halted = false ∧
      t.nr 18 = edges.length ∧ t.nr 29 = G.n ∧ t.nr 28 = root.val ∧
      t.nr 23 + edges.length ≤ t.nr 30 ∧ 2 + 3 * G.q ≤ t.nr 30 ∧
      EulerOccurrenceInput edges (t.nr 23) t.nm := by
  obtain ⟨p, publishes, pReady, count, base, _, natural, _, occurrence, fixed⟩ :=
    publishOccurrenceBlock_correct entry running zero cursor encoded
  obtain ⟨f, configures, ready, free, vertices, vertex, fNatural, _, fCount, fBase⟩ :=
    prepareEulerRegisters_correct {p with pc := 0} rfl pReady
      ((fixed 28 (by decide) (by decide) (by decide)).trans zero)
  have rfree : f.nr 30 = s.nr 29 :=
    free.trans (fixed 29 (by decide) (by decide) (by decide))
  have nBound : f.nr 23 + edges.length ≤ f.nr 30 := by
    rw [fBase, base, rfree, cursor]
  refine ⟨relocateState publishOccurrenceBlock.length f, publishes.append configures, ready,
    fCount.trans count, vertices.trans ((fixed 5 (by decide) (by decide) (by decide)).trans dimension),
    vertex.trans ((fixed 31 (by decide) (by decide) (by decide)).trans rootReg),
    nBound, rfree.symm ▸ rawBound, ?_⟩
  change EulerOccurrenceInput edges (f.nr 23) f.nm
  rw [fBase, fNatural]
  refine ⟨fun i => occurrence i.val i.isLt, ?_, ?_⟩
  · intro e
    rw [natural, show e.val + e.val + e.val + 2 = 2 + 3 * e.val by omega]
    exact tailCells e
  · intro e
    rw [natural, show e.val + e.val + e.val + 3 = 3 + 3 * e.val by omega]
    exact headCells e

/-- Read a supported vertex from the first original link occurrence. -/
def chooseOccurrenceRootBlock : List ArithmeticInstruction :=
  [.natLoad 31 33, .natAdd 32 31 31, .natAdd 32 32 31,
    .natAdd 32 32 6, .natAdd 32 32 6, .natLoad 31 32]

theorem chooseOccurrenceRootBlock_correct {s : ArithmeticState}
    {edge : Fin G.q} {other : List (Fin G.q)}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (encoded : OccurrenceArray s.nm (s.nr 33) (edge :: other))
    (tail : s.nm (2 + 3 * edge.val) = (G.tail edge).val) :
    ∃ t, BlockRuns chooseOccurrenceRootBlock 6 s t ∧ t.halted = false ∧
      t.nr 31 = (G.tail edge).val ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ≠ 31 → r ≠ 32 → t.nr r = s.nr r := by
  let t := (arithmeticStep chooseOccurrenceRootBlock)^[6] s
  have ready : t.halted = false := by
    simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = chooseOccurrenceRootBlock.length := by
    simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have first : s.nm (s.nr 33) = edge.val := by
    have value := encoded 0 (by simp)
    change s.nm (s.nr 33 + 0) = edge.val at value
    rwa [Nat.add_zero] at value
  have address : edge.val + edge.val + edge.val + 1 + 1 = 2 + 3 * edge.val := by omega
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_⟩
  · simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, one,
      Function.iterate_succ_apply', first, address, tail]
  · simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r left right
    simp [t, chooseOccurrenceRootBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne left, Function.update_of_ne right]

def configureEulerNonemptyOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock chooseOccurrenceRootBlock configureEulerOccurrencesBlock

theorem configureEulerNonemptyOccurrencesBlock_correct {s : ArithmeticState}
    {edge : Fin G.q} {other : List (Fin G.q)}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (zero : s.nr 28 = 0) (dimension : s.nr 5 = G.n)
    (cursor : s.nr 29 = s.nr 33 + (edge :: other).length)
    (rawBound : 2 + 3 * G.q ≤ s.nr 29)
    (encoded : OccurrenceArray s.nm (s.nr 33) (edge :: other))
    (tailCells : ∀ e : Fin G.q, s.nm (2 + 3 * e.val) = (G.tail e).val)
    (headCells : ∀ e : Fin G.q, s.nm (3 + 3 * e.val) = (G.head e).val) :
    ∃ t root, BlockRuns configureEulerNonemptyOccurrencesBlock 12 s t ∧ t.halted = false ∧
      EdgeSupport G (edge :: other) root ∧
      t.nr 18 = (edge :: other).length ∧ t.nr 29 = G.n ∧ t.nr 28 = root.val ∧
      t.nr 23 + (edge :: other).length ≤ t.nr 30 ∧ 2 + 3 * G.q ≤ t.nr 30 ∧
      EulerOccurrenceInput (edge :: other) (t.nr 23) t.nm := by
  obtain ⟨r, chooses, rReady, value, nat, real, fixed⟩ :=
    chooseOccurrenceRootBlock_correct entry running one encoded (tailCells edge)
  let start := {r with pc := 0}
  have preparedCursor : r.nr 29 = r.nr 33 + (edge :: other).length := by
    rw [fixed 29 (by decide) (by decide), fixed 33 (by decide) (by decide)]
    exact cursor
  have unchangedRaw : 2 + 3 * G.q ≤ r.nr 29 := by rwa [fixed 29 (by decide) (by decide)]
  have unchangedList : OccurrenceArray r.nm (r.nr 33) (edge :: other) := by
    rwa [nat, fixed 33 (by decide) (by decide)]
  obtain ⟨t, prepares, ready, count, vertices, root, free, protectedRaw, encoding⟩ :=
    configureEulerOccurrencesBlock_correct (s := start) rfl rReady
      ((fixed 28 (by decide) (by decide)).trans zero)
      ((fixed 5 (by decide) (by decide)).trans dimension)
      value preparedCursor unchangedRaw unchangedList
      (fun e => (congrFun nat _).trans (tailCells e))
      (fun e => (congrFun nat _).trans (headCells e))
  exact ⟨_, G.tail edge, chooses.append prepares, ready, ⟨edge, List.mem_cons_self, .inl rfl⟩,
    count, vertices, root, free, protectedRaw, encoding⟩

end VehicleRoutingSurvey.Routing
end RppSource_OccurrenceInterface

/-! runtime/OccurrenceRegisters.lean -/
section RppSource_OccurrenceRegisters
namespace VehicleRoutingSurvey.Routing

/-- Values shared by the connector expansion and the matching expansion.
The matching stage uses lower registers for its own state. -/
structure SavedOccurrenceRegisters (original saved : ArithmeticState) : Prop where
  rows : saved.nr 100 = original.nr 3
  distances : saved.nr 101 = original.nr 4
  vertices : saved.nr 102 = original.nr 5
  nextEdges : saved.nr 103 = original.nr 26
  occurrenceEnd : saved.nr 104 = original.nr 29
  occurrenceBase : saved.nr 105 = original.nr 33

def saveOccurrenceRegistersBlock : List ArithmeticInstruction :=
  [.natAdd 100 3 28, .natAdd 101 4 28, .natAdd 102 5 28,
    .natAdd 103 26 28, .natAdd 104 29 28, .natAdd 105 33 28]

theorem saveOccurrenceRegistersBlock_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 28 = 0) :
    ∃ t, BlockRuns saveOccurrenceRegistersBlock 6 s t ∧ t.halted = false ∧
      SavedOccurrenceRegisters s t ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r < 100, t.nr r = s.nr r := by
  let t := (arithmeticStep saveOccurrenceRegistersBlock)^[6] s
  have ready : t.halted = false := by
    simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = saveOccurrenceRegistersBlock.length := by
    simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have saved : SavedOccurrenceRegisters s t := by
    constructor <;>
      simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running, zero,
        Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, saved, ?_, ?_, ?_⟩
  · simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r small
    simp [t, saveOccurrenceRegistersBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_of_ne (show r ≠ 100 by omega),
      Function.update_of_ne (show r ≠ 101 by omega), Function.update_of_ne (show r ≠ 102 by omega),
      Function.update_of_ne (show r ≠ 103 by omega), Function.update_of_ne (show r ≠ 104 by omega),
      Function.update_of_ne (show r ≠ 105 by omega)]

theorem SavedOccurrenceRegisters.preserved {original s t : ArithmeticState}
    (initial : SavedOccurrenceRegisters original s)
    (keeps : ∀ r ≥ 100, t.nr r = s.nr r) : SavedOccurrenceRegisters original t :=
  ⟨(keeps 100 (by decide)).trans initial.rows, (keeps 101 (by decide)).trans initial.distances,
    (keeps 102 (by decide)).trans initial.vertices, (keeps 103 (by decide)).trans initial.nextEdges,
    (keeps 104 (by decide)).trans initial.occurrenceEnd,
    (keeps 105 (by decide)).trans initial.occurrenceBase⟩

def restoreOccurrenceRegistersBlock : List ArithmeticInstruction :=
  [.natConst 28 0, .natConst 6 1,
    .natAdd 3 100 28, .natAdd 4 101 28, .natAdd 5 102 28,
    .natAdd 26 103 28, .natAdd 29 104 28, .natAdd 33 105 28]

theorem restoreOccurrenceRegistersBlock_correct {original s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (saved : SavedOccurrenceRegisters original s) :
    ∃ t, BlockRuns restoreOccurrenceRegistersBlock 8 s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 3 = original.nr 3 ∧ t.nr 4 = original.nr 4 ∧ t.nr 5 = original.nr 5 ∧
      t.nr 26 = original.nr 26 ∧ t.nr 29 = original.nr 29 ∧ t.nr 33 = original.nr 33 ∧
      t.nr 6 = 1 ∧ t.nr 28 = 0 ∧ t.nr 34 = s.nr 34 ∧ t.nr 35 = s.nr 35 := by
  let t := (arithmeticStep restoreOccurrenceRegistersBlock)^[8] s
  have ready : t.halted = false := by
    simp [t, restoreOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = restoreOccurrenceRegistersBlock.length := by
    simp [t, restoreOccurrenceRegistersBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, restoreOccurrenceRegistersBlock, arithmeticStep, entry, running,
    Function.iterate_succ_apply', saved.rows, saved.distances, saved.vertices,
    saved.nextEdges, saved.occurrenceEnd, saved.occurrenceBase]

end VehicleRoutingSurvey.Routing
end RppSource_OccurrenceRegisters


