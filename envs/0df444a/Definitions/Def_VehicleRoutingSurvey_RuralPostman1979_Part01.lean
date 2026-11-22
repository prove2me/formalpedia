-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part01
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:43.256175+00:00
-- url     : https://prove2.me/theorems/99b18d2e-db81-41d0-9213-1deb3812cbe9
-- title:
--   Rural postman algorithm — Existence, approximation, and a family approaching the three-halves bound
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for existence, approximation, and a family approaching the three-halves bound in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_SupplyChainTheory_tsp
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_VehicleRoutingSurvey_Routing_Network
import Mathlib.Algebra.Order.BigOperators.Group.List
import Definitions.Def_VehicleRoutingSurvey_Routing_RuralAlgorithm
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_VehicleRoutingSurvey_Routing_RuralRuntime
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.FinRange

/-! matching/CycleMatching.lean -/
section RppSource_CycleMatching
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The length of a route through specified intermediate vertices. -/
def routeVia {α : Type*} (cost : α → α → ℝ) (u : α) : List α → α → ℝ
  | [], v => cost u v
  | w :: rest, v => cost u w + routeVia cost w rest v

/-- The length of a cyclic visiting order. -/
def routeCycleCost {α : Type*} (cost : α → α → ℝ) : List α → ℝ
  | [] => 0
  | a :: rest => routeVia cost a rest a

/-- Pair consecutive vertices in the listed order. -/
def alternatingEdges {α : Type*} : List α → List (Sym2 α)
  | a :: b :: rest => s(a, b) :: alternatingEdges rest
  | _ => []

theorem alternatingEdges_perfect {n : ℕ} (l : List (Fin n))
    (distinct : l.Nodup) (even : l.length % 2 = 0) :
    (alternatingEdges l).Nodup ∧ IsPerfectMatchingOn l.toFinset (alternatingEdges l).toFinset := by
  induction l using List.twoStepInduction
  case nil => simp [alternatingEdges, IsPerfectMatchingOn]
  case singleton => simp at even
  case cons_cons a b tail ih _ =>
    obtain ⟨oldDistinct, oldPerfect⟩ := ih distinct.of_cons.of_cons
      (by simpa [Nat.add_assoc, Nat.add_mod] using even)
    obtain ⟨⟨different, aFresh⟩, bFresh, _⟩ : (a ≠ b ∧ a ∉ tail) ∧ b ∉ tail ∧ tail.Nodup :=
      by simpa only [List.nodup_cons, List.mem_cons, not_or] using distinct
    have exclusive (e : Sym2 (Fin n)) (old : e ∈ (alternatingEdges tail).toFinset)
        (v : Fin n) (inNew : v ∈ s(a, b)) (inOld : v ∈ e) : False :=
      let seen := List.mem_toFinset.mp ((oldPerfect.1 e old).2 v inOld)
      (Sym2.mem_iff.mp inNew).elim (fun h => aFresh (h ▸ seen)) (fun h => bFresh (h ▸ seen))
    refine ⟨List.nodup_cons.mpr ⟨fun h => exclusive _ (List.mem_toFinset.mpr h) a
      (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a b), oldDistinct⟩, ?_⟩
    simp only [alternatingEdges, List.toFinset_cons, IsPerfectMatchingOn, Finset.mem_insert]
    refine ⟨fun e support => support.elim
      (fun eq => eq.symm ▸ ⟨mt Sym2.mk_isDiag_iff.mp different,
        fun _ hv => (Sym2.mem_iff.mp hv).imp_right Or.inl⟩)
      (fun old => ⟨(oldPerfect.1 e old).1, fun v hv => Or.inr (Or.inr ((oldPerfect.1 e old).2 v hv))⟩), ?_⟩
    exact fun v hv => if new : v ∈ s(a, b) then
      ⟨s(a, b), ⟨Or.inl rfl, new⟩, fun e he =>
        he.1.resolve_right (fun old => exclusive e old v new he.2)⟩
    else
      let old := hv.resolve_left (fun h => new (Sym2.mem_iff.mpr (Or.inl h)))
      let old := old.resolve_left (fun h => new (Sym2.mem_iff.mpr (Or.inr h)))
      match oldPerfect.2 v old with
      | ⟨e, he, unique⟩ => ⟨e, ⟨Or.inr he.1, he.2⟩, fun f hf =>
        unique f ⟨hf.1.resolve_left (fun eq => new (eq ▸ hf.2)), hf.2⟩⟩

theorem edgeCost_eq_of_symmetric {n : ℕ} (c : Fin n → Fin n → ℝ)
    (symmetric : ∀ u v, c u v = c v u) (u v : Fin n) : edgeCost c s(u, v) = c u v := by
  simpa only [edgeCost, Sym2.lift_mk, symmetric v u] using (show (c u v + c u v) / 2 = c u v by linarith)

private theorem alternatingEdges_routeVia {n : ℕ} (c : Fin n → Fin n → ℝ)
    (symmetric : ∀ u v, c u v = c v u) (l : List (Fin n))
    (even : l.length % 2 = 0) (u v : Fin n) :
    ((alternatingEdges l).map (edgeCost c)).sum +
      ((alternatingEdges (u :: l ++ [v])).map (edgeCost c)).sum = routeVia c u l v := by
  induction l using List.twoStepInduction generalizing u
  case nil => simp [alternatingEdges, routeVia, edgeCost_eq_of_symmetric c symmetric]
  case singleton => simp at even
  case cons_cons a b tail ih _ =>
    simpa only [List.cons_append, alternatingEdges, List.map_cons, List.sum_cons, routeVia,
      edgeCost_eq_of_symmetric c symmetric, add_assoc, add_left_comm, add_comm] using
      congrArg (fun z : ℝ => c u a + c a b + z)
        (ih (by simpa [Nat.add_assoc, Nat.add_mod] using even) b)

/-- In a cyclic visiting order of an even vertex set, alternate edges give two matchings. -/
theorem two_matchings_of_even_cycle {n : ℕ} (c : Fin n → Fin n → ℝ)
    (symmetric : ∀ u v, c u v = c v u) (l : List (Fin n))
    (distinct : l.Nodup) (even : l.length % 2 = 0) :
    ∃ M₁ M₂, IsPerfectMatchingOn l.toFinset M₁ ∧ IsPerfectMatchingOn l.toFinset M₂ ∧
      edgeSetWeight c M₁ + edgeSetWeight c M₂ = routeCycleCost c l := by
  cases l with
  | nil => exact ⟨∅, ∅, by simp [IsPerfectMatchingOn], by simp [IsPerfectMatchingOn],
      by simp [edgeSetWeight, routeCycleCost]⟩
  | cons a rest =>
    cases rest with
    | nil => simp at even
    | cons b tail =>
      have rotated : List.Perm (b :: tail ++ [a]) (a :: b :: tail) :=
        List.perm_append_singleton a (b :: tail)
      obtain ⟨distinct₁, matching₁⟩ := alternatingEdges_perfect (a :: b :: tail) distinct even
      obtain ⟨distinct₂, matching₂⟩ := alternatingEdges_perfect (b :: tail ++ [a])
        (rotated.nodup_iff.mpr distinct) (rotated.length_eq ▸ even)
      have sameSet : (b :: tail ++ [a]).toFinset = (a :: b :: tail).toFinset :=
        Finset.ext fun w => List.mem_toFinset.trans ((rotated.mem_iff (a := w)).trans List.mem_toFinset.symm)
      refine ⟨_, _, matching₁, sameSet ▸ matching₂, ?_⟩
      rw [edgeSetWeight, edgeSetWeight, List.sum_toFinset _ distinct₁, List.sum_toFinset _ distinct₂]
      simpa only [alternatingEdges, List.map_cons, List.sum_cons, routeCycleCost, routeVia, add_assoc,
        edgeCost_eq_of_symmetric c symmetric] using
        congrArg (c a b + ·) (alternatingEdges_routeVia c symmetric tail
          (by simpa [Nat.add_assoc, Nat.add_mod] using even) b a)

/-- Every finite even vertex set admits a perfect matching in its complete graph. -/
theorem exists_perfectMatching_on_even {n : ℕ} (O : Finset (Fin n))
    (even : O.card % 2 = 0) : ∃ M, IsPerfectMatchingOn O M := by
  simpa only [Finset.toList_toFinset] using
    (show ∃ M, IsPerfectMatchingOn O.toList.toFinset M from
      ⟨_, (alternatingEdges_perfect O.toList O.nodup_toList (by simpa using even)).2⟩)

end VehicleRoutingSurvey.Routing
end RppSource_CycleMatching

/-! PathCosts.lean -/
section RppSource_PathCosts
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

def pathVertices (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : List (Fin G.n) :=
  u :: ts.map (finish G)

theorem pathCost_append (xs ys : List (Traversal G)) :
    pathCost G (xs ++ ys) = pathCost G xs + pathCost G ys := by
  simp [pathCost]

theorem isPath_append {u v w : Fin G.n} {xs ys : List (Traversal G)}
    (first : IsPath G u xs v) (second : IsPath G v ys w) : IsPath G u (xs ++ ys) w := by
  induction xs generalizing u <;> simp_all [IsPath]

theorem pathCost_nonnegative (nonnegative : Nonnegative G) (ts : List (Traversal G)) :
    0 ≤ pathCost G ts :=
  List.sum_nonneg (fun _ member => (List.mem_map.mp member).elim
    (fun t result => result.2 ▸ nonnegative t.1))

theorem pathCost_mono_sublist (nonnegative : Nonnegative G) {xs ys : List (Traversal G)}
    (included : xs.Sublist ys) : pathCost G xs ≤ pathCost G ys :=
  (included.map (fun t => G.weight t.1)).sum_le_sum
    (fun _ member => (List.mem_map.mp member).elim (fun t result => result.2 ▸ nonnegative t.1))

theorem distance_eq_of_shortestPath {u v : Fin G.n} {ts : List (Traversal G)}
    (shortest : ShortestPath G u v ts) : distance G u v = pathCost G ts :=
  IsLeast.csInf_eq ⟨⟨ts, shortest.1, rfl⟩,
    fun _ ⟨ss, path, cost⟩ => cost.symm ▸ shortest.2 ss path⟩

theorem distance_le_pathCost (nonnegative : Nonnegative G) {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) : distance G u v ≤ pathCost G ts :=
  csInf_le ⟨0, fun _ ⟨ss, _, cost⟩ => cost.symm ▸ pathCost_nonnegative nonnegative ss⟩
    ⟨ts, path, rfl⟩

def reverseTraversal (t : Traversal G) : Traversal G := (t.1, !t.2)

def reverseTraversals (ts : List (Traversal G)) : List (Traversal G) :=
  ts.reverse.map reverseTraversal

theorem start_reverseTraversal (t : Traversal G) :
    start G (reverseTraversal t) = finish G t := by
  cases direction : t.2 <;> simp [start, finish, reverseTraversal, direction]

theorem finish_reverseTraversal (t : Traversal G) :
    finish G (reverseTraversal t) = start G t := by
  cases direction : t.2 <;> simp [start, finish, reverseTraversal, direction]

theorem pathCost_reverseTraversals (ts : List (Traversal G)) :
    pathCost G (reverseTraversals ts) = pathCost G ts := by
  simp [reverseTraversals, pathCost, List.map_map, Function.comp_def, reverseTraversal]

theorem isPath_reverse (undirected : Undirected G) {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) : IsPath G v (reverseTraversals ts) u := by
  induction ts generalizing u with
  | nil => exact (show u = v from path).symm
  | cons t rest ih =>
    have back : IsPath G (finish G t) [reverseTraversal t] u :=
      ⟨(start_reverseTraversal t).symm, Or.inl (undirected t.1),
        (finish_reverseTraversal t).trans path.1.symm⟩
    have joined := isPath_append (ih path.2.2) back
    simpa only [reverseTraversals, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      using joined

theorem distance_self (nonnegative : Nonnegative G) (u : Fin G.n) : distance G u u = 0 :=
  distance_eq_of_shortestPath (ts := [])
    ⟨rfl, fun ss _ => pathCost_nonnegative nonnegative ss⟩

theorem distance_symm (undirected : Undirected G) (u v : Fin G.n) :
    distance G u v = distance G v u := by
  have transfer (x y : Fin G.n) :
      {c | ∃ ts, IsPath G x ts y ∧ c = pathCost G ts} ⊆
        {c | ∃ ts, IsPath G y ts x ∧ c = pathCost G ts} :=
    fun _ ⟨ts, path, cost⟩ => ⟨reverseTraversals ts, isPath_reverse undirected path,
      cost.trans (pathCost_reverseTraversals ts).symm⟩
  exact congrArg sInf (Set.Subset.antisymm (transfer u v) (transfer v u))

theorem distance_nonnegative (connected : Connected G) (nonnegative : Nonnegative G) (u v : Fin G.n) :
    0 ≤ distance G u v :=
  le_csInf ((connected.2 u v).elim fun ts path => ⟨pathCost G ts, ts, path, rfl⟩)
    (fun _ ⟨ts, _, cost⟩ => cost.symm ▸ pathCost_nonnegative nonnegative ts)

end VehicleRoutingSurvey.Routing
end RppSource_PathCosts

/-! matching/MatchingComparison.lean -/
section RppSource_MatchingComparison
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem routeVia_insert_left {α : Type*} (c : α → α → ℝ)
    (triangle : ∀ a b d, c a d ≤ c a b + c b d) (u w v : α) (xs : List α) :
    routeVia c u xs v ≤ c u w + routeVia c w xs v := by
  cases xs with
  | nil => exact triangle u w v
  | cons a tail => simpa only [routeVia, add_assoc] using
      (add_le_add (triangle u w a) (le_refl (routeVia c a tail v)))

private theorem routeVia_insert_right {α : Type*} (c : α → α → ℝ)
    (triangle : ∀ a b d, c a d ≤ c a b + c b d) (u w v : α) (xs : List α) :
    routeVia c u xs v ≤ routeVia c u xs w + c w v := by
  induction xs generalizing u with
  | nil => exact triangle u w v
  | cons a tail ih => simpa only [routeVia, add_assoc] using
      (add_le_add (le_refl (c u a)) (ih a))

theorem routeVia_le_of_sublist {α : Type*} (c : α → α → ℝ)
    (triangle : ∀ a b d, c a d ≤ c a b + c b d) {xs ys : List α} (keep : xs.Sublist ys)
    (u v : α) : routeVia c u xs v ≤ routeVia c u ys v := by
  induction keep generalizing u
  case slnil => exact le_rfl
  case cons a _ ih => exact (ih u).trans (routeVia_insert_left c triangle u a v _)
  case cons_cons a _ ih => exact add_le_add (le_refl (c u a)) (ih a)

theorem routeCycleCost_le_routeVia {α : Type*} (c : α → α → ℝ) (self : ∀ u, c u u = 0)
    (triangle : ∀ a b d, c a d ≤ c a b + c b d) (u : α) (xs : List α) :
    routeCycleCost c xs ≤ routeVia c u xs u := by
  cases xs with
  | nil => exact (self u).ge
  | cons a tail => simpa only [routeCycleCost, routeVia, add_comm] using
      (routeVia_insert_right c triangle a u a tail)

theorem pathVertices_toFinset {G : Network} (u : Fin G.n) (ts : List (Traversal G)) :
    (pathVertices G u ts).toFinset = Visited G u ts := by
  simp only [pathVertices, List.toFinset_cons, Visited, Finset.singleton_union]

theorem traversal_start_visited {G : Network} {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) (t : Traversal G) (member : t ∈ ts) : start G t ∈ Visited G u ts := by
  rw [← pathVertices_toFinset, List.mem_toFinset]
  induction ts generalizing u
  case nil => cases member
  case cons a _ ih =>
    exact (List.mem_cons.mp member).elim
      (fun eq => List.mem_cons.mpr (Or.inl ((congrArg (start G) eq).trans path.1.symm)))
      (fun rest => List.mem_cons_of_mem u (ih path.2.2 rest))

theorem requiredVertices_subset_visited {I : Service} {u : Fin I.graph.n}
    {ts : List (Traversal I.graph)} (tour : Feasible I u ts) : requiredVertices I ⊆ Visited I.graph u ts := by
  have endpoints (e : Fin I.graph.q) (required : e ∈ I.links) :
      I.graph.tail e ∈ Visited I.graph u ts ∧ I.graph.head e ∈ Visited I.graph u ts := by
    obtain ⟨t, used, equal⟩ := tour.2.2 e required
    have starts := traversal_start_visited tour.1 t used
    have finishes : finish I.graph t ∈ Visited I.graph u ts :=
      Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem used))
    cases dir : t.2 with
    | false => exact ⟨by simpa [finish, dir, equal] using finishes,
        by simpa [start, dir, equal] using starts⟩
    | true => exact ⟨by simpa [start, dir, equal] using starts,
        by simpa [finish, dir, equal] using finishes⟩
  exact fun v hv => (Finset.mem_union.mp hv).elim
    (fun h => (Finset.mem_image.mp h).elim fun e he => he.2 ▸ (endpoints e he.1).1)
    (fun h => (Finset.mem_image.mp h).elim fun e he => he.2 ▸ (endpoints e he.1).2)

private theorem routeVia_finish_le_pathCost {G : Network} (nonnegative : Nonnegative G)
    {u v : Fin G.n} {ts : List (Traversal G)} (path : IsPath G u ts v) :
    routeVia (distance G) u (ts.map (finish G)) v ≤ pathCost G ts := by
  induction ts generalizing u
  case nil => simpa only [show u = v from path, List.map_nil, routeVia, distance_self nonnegative,
      pathCost, List.sum_nil] using (le_refl (0 : ℝ))
  case cons t tail ih =>
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, routeVia, pathCost, add_zero] using
      (add_le_add (distance_le_pathCost nonnegative
        (show IsPath G u [t] (finish G t) from ⟨path.1, path.2.1, rfl⟩)) (ih path.2.2))

theorem pairCost_eq_edgeSetWeight {G : Network} (undirected : Undirected G)
    {ps : List (Fin G.n × Fin G.n)} (distinct : (ps.map (fun p => s(p.1, p.2))).Nodup) :
    pairCost G ps = edgeSetWeight (distance G) (matchingEdges G ps) := by
  simpa [pairCost, edgeSetWeight, matchingEdges, List.map_map, Function.comp_def,
    edgeCost_eq_of_symmetric _ (distance_symm undirected)] using
    (List.sum_toFinset (edgeCost (distance G)) distinct).symm

/-- The minimum matching weighs at most half of any closed tour through all odd vertices. -/
theorem minimumMatching_le_half_path {G : Network} (nonnegative : Nonnegative G)
    (undirected : Undirected G) (triangle : ∀ u v w, distance G u w ≤ distance G u v + distance G v w)
    {es : List (Fin G.q)} {matching : List (Fin G.n × Fin G.n)}
    (minimum : MinimumMatching G es matching) (even : (oddVertices G es).card % 2 = 0)
    {u : Fin G.n} {ts : List (Traversal G)} (path : IsPath G u ts u)
    (visits : oddVertices G es ⊆ Visited G u ts) :
    2 * pairCost G matching ≤ pathCost G ts := by
  classical
  let chosen := ((pathVertices G u ts).filter fun v => decide (v ∈ oddVertices G es)).dedup
  have chosenSet : chosen.toFinset = oddVertices G es := Finset.ext fun v => by
    simp only [chosen, List.mem_toFinset, List.mem_dedup, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hv => ⟨List.mem_toFinset.mp (pathVertices_toFinset u ts ▸ visits hv), hv⟩⟩
  have chosenDistinct : chosen.Nodup := List.nodup_dedup _
  have chosenEven : chosen.length % 2 = 0 := by
    simpa only [List.toFinset_card_of_nodup chosenDistinct] using
      (show chosen.toFinset.card % 2 = 0 from chosenSet ▸ even)
  obtain ⟨a, b, aPerfect, bPerfect, cost⟩ :=
    two_matchings_of_even_cycle _ (distance_symm undirected) chosen chosenDistinct chosenEven
  have kept : chosen.Sublist (pathVertices G u ts) :=
    (List.dedup_sublist _).trans List.filter_sublist
  have cap : routeCycleCost (distance G) chosen ≤ pathCost G ts :=
    (routeCycleCost_le_routeVia _ (distance_self nonnegative) triangle u chosen).trans
      ((routeVia_le_of_sublist _ triangle kept u u).trans (by
        simpa only [pathVertices, routeVia, distance_self nonnegative, zero_add] using
          routeVia_finish_le_pathCost nonnegative path))
  calc
    2 * pairCost G matching = edgeSetWeight (distance G) (matchingEdges G matching) +
        edgeSetWeight (distance G) (matchingEdges G matching) := by
      rw [pairCost_eq_edgeSetWeight undirected minimum.1, two_mul]
    _ ≤ edgeSetWeight (distance G) a + edgeSetWeight (distance G) b :=
      add_le_add (minimum.2.2 a (chosenSet ▸ aPerfect)) (minimum.2.2 b (chosenSet ▸ bPerfect))
    _ = routeCycleCost (distance G) chosen := cost
    _ ≤ pathCost G ts := cap

end VehicleRoutingSurvey.Routing
end RppSource_MatchingComparison

/-! matching/OddSupport.lean -/
section RppSource_OddSupport
namespace VehicleRoutingSurvey.Routing

private def mark {α : Type*} [DecidableEq α] (v u : α) : ℕ := if u = v then 1 else 0

theorem degree_append (G : Network) (es fs : List (Fin G.q)) (v : Fin G.n) :
    degree G (es ++ fs) v = degree G es v + degree G fs v := by
  simp [degree, List.filter_append, add_assoc, add_left_comm]

private theorem degree_cons_traversal (G : Network) (t : Traversal G) (es : List (Fin G.q))
    (v : Fin G.n) : degree G (t.1 :: es) v =
    mark v (start G t) + mark v (finish G t) + degree G es v := by
  cases orientation : t.2
  all_goals
    by_cases head : G.head t.1 = v <;> by_cases tail : G.tail t.1 = v <;>
      simp [degree, mark, start, finish, orientation, head, tail,
        add_assoc, add_left_comm, add_comm]
  all_goals omega

private theorem degree_cons_eq (G : Network) (e : Fin G.q) (es : List (Fin G.q)) (v : Fin G.n) :
    degree G (e :: es) v = mark v (G.tail e) + mark v (G.head e) + degree G es v := by
  simpa [start, finish] using degree_cons_traversal G (e, true) es v

/-- A path contributes even degree except at its two distinct endpoints. -/
theorem degree_path_mod_two {G : Network} {u w : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts w) (v : Fin G.n) :
    degree G (ts.map Prod.fst) v % 2 = (mark v u + mark v w) % 2 := by
  induction ts generalizing u
  case nil => simp [degree, show u = w from path, ← two_mul, Nat.mul_mod_right]
  case cons t rest ih =>
    rw [List.map_cons, degree_cons_traversal, ← path.1]
    have remaining := ih path.2.2
    omega

theorem degree_path_even_of_not_endpoints {G : Network} {u w v : Fin G.n}
    {ts : List (Traversal G)} (path : IsPath G u ts w) (hu : u ≠ v) (hw : w ≠ v) :
    degree G (ts.map Prod.fst) v % 2 = 0 := by
  simpa [mark, hu, hw] using degree_path_mod_two path v

theorem degree_eq_zero_of_no_incident {G : Network} (es : List (Fin G.q))
    (v : Fin G.n) (avoid : ∀ e ∈ es, G.tail e ≠ v ∧ G.head e ≠ v) : degree G es v = 0 := by
  induction es with
  | nil => simp [degree]
  | cons e rest ih =>
    simpa [degree_cons_eq, mark, (avoid e List.mem_cons_self).1, (avoid e List.mem_cons_self).2] using
      (ih (fun f h => avoid f (List.mem_cons_of_mem e h)))

theorem degree_eq_of_perm {G : Network} {es fs : List (Fin G.q)} (perm : es.Perm fs)
    (v : Fin G.n) : degree G es v = degree G fs v :=
  congrArg₂ Nat.add ((perm.filter fun e => decide (G.tail e = v)).length_eq)
    ((perm.filter fun e => decide (G.head e = v)).length_eq)

theorem degree_closedPath_mod_two {G : Network} {u : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts u) (v : Fin G.n) : degree G (ts.map Prod.fst) v % 2 = 0 := by
  simpa [← two_mul, Nat.mul_mod_right] using degree_path_mod_two path v

theorem degree_openPath_mod_two_at_finish {G : Network} {u w : Fin G.n}
    {ts : List (Traversal G)} (path : IsPath G u ts w) (openPath : u ≠ w) :
    degree G (ts.map Prod.fst) w % 2 = 1 := by
  simpa [mark, openPath] using degree_path_mod_two path w

private theorem expanded_degree_mod_two {G : Network} {v : Fin G.n}
    {tree : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (expansion : Expands G tree paths) (avoid : ∀ p ∈ tree, p.1 ≠ v ∧ p.2 ≠ v) :
    degree G (paths.flatten.map Prod.fst) v % 2 = 0 := by
  induction expansion
  case nil => simp [degree]
  case cons p ts restTree restPaths shortest _ ih =>
    simp only [List.flatten_cons, List.map_append, degree_append, Nat.add_mod,
      degree_path_even_of_not_endpoints shortest.1 (avoid p List.mem_cons_self).1
        (avoid p List.mem_cons_self).2,
      ih (fun pair hp => avoid pair (List.mem_cons_of_mem p hp)), Nat.add_zero, Nat.zero_mod]

/-- The odd vertices after adding component paths belong to the required support. -/
theorem oddVertices_subset_required {I : Service} {base : List (Fin I.graph.q)}
    {tree : List (Fin I.graph.n × Fin I.graph.n)} {paths : List (List (Traversal I.graph))}
    (baseLinks : base.toFinset = I.links) (expansion : Expands I.graph tree paths)
    (endpoints : ∀ p ∈ tree, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I) :
    oddVertices I.graph (base ++ paths.flatten.map Prod.fst) ⊆ requiredVertices I := by
  intro v odd
  by_contra excluded
  have baseZero : degree I.graph base v = 0 := degree_eq_zero_of_no_incident base v fun e he =>
    let needed : e ∈ I.links := baseLinks ▸ List.mem_toFinset.mpr he
    ⟨fun h => excluded (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, needed, h⟩)),
      fun h => excluded (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, needed, h⟩))⟩
  have treeEven := expanded_degree_mod_two expansion (v := v) fun p hp =>
    ⟨fun h => excluded (h ▸ (endpoints p hp).1), fun h => excluded (h ▸ (endpoints p hp).2)⟩
  exact Nat.zero_ne_one (by
    simpa only [degree_append, baseZero, zero_add, treeEven] using
      (Nat.odd_iff.mp (Finset.mem_filter.mp odd).2))

/-- The handshake lemma, counting both incidences of a loop. -/
theorem degree_sum (G : Network) (es : List (Fin G.q)) :
    (∑ v : Fin G.n, degree G es v) = 2 * es.length := by
  induction es
  case nil => simp [degree]
  case cons e rest ih =>
    simp [degree_cons_eq, mark, Finset.sum_add_distrib, ih, Nat.mul_succ,
      Finset.sum_ite_eq, add_comm]

theorem oddVertices_card_mod_two (G : Network) (es : List (Fin G.q)) :
    (oddVertices G es).card % 2 = 0 := by
  have step (v : Fin G.n) : (if Odd (degree G es v) then 1 else 0 : ℕ) ≡ degree G es v [MOD 2] := by
    simp only [Nat.ModEq, Nat.odd_iff]
    split <;> omega
  simpa [Nat.ModEq, oddVertices, degree_sum] using
    (Nat.ModEq.sum (s := Finset.univ) (fun v _ => step v))

private def pairDegree {α : Type*} [DecidableEq α] (pairs : List (α × α)) (v : α) : ℕ :=
  (pairs.map (fun p => mark v p.1 + mark v p.2)).sum

private theorem expanded_degree_mod_two_eq_pairDegree {G : Network} (v : Fin G.n)
    {pairs : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (expansion : Expands G pairs paths) :
    degree G (paths.flatten.map Prod.fst) v % 2 = pairDegree pairs v % 2 := by
  induction expansion
  case nil => simp [degree, pairDegree]
  case cons p ts rest paths shortest _ ih =>
    simp only [List.flatten_cons, List.map_append, degree_append, pairDegree, List.map_cons,
      List.sum_cons]
    exact Nat.ModEq.add (degree_path_mod_two shortest.1 v) ih

private theorem matching_pairDegree_eq {G : Network} {es : List (Fin G.q)}
    {pairs : List (Fin G.n × Fin G.n)} (matching : PerfectMatching G es pairs) (v : Fin G.n) :
    pairDegree pairs v = if v ∈ oddVertices G es then 1 else 0 := by
  have each (p : Fin G.n × Fin G.n) (uses : p ∈ pairs) :
      mark v p.1 + mark v p.2 = if v ∈ s(p.1, p.2) then 1 else 0 := by
    have distinct : p.1 ≠ p.2 := mt Sym2.mk_isDiag_iff.mpr (matching.2.1 _
      (List.mem_toFinset.mpr (List.mem_map_of_mem uses))).1
    by_cases first : p.1 = v <;> by_cases second : p.2 = v <;> simp_all [mark]
    exact ⟨Ne.symm first, Ne.symm second⟩
  have incidence : pairDegree pairs v = ((matchingEdges G pairs).filter fun e => v ∈ e).card := by
    calc
      _ = (pairs.map fun p => if v ∈ s(p.1, p.2) then 1 else 0).sum :=
        congrArg List.sum (List.map_congr_left each)
      _ = ∑ e ∈ matchingEdges G pairs, (if v ∈ e then 1 else 0 : ℕ) := by
        rw [matchingEdges, List.sum_toFinset _ matching.1, List.map_map]
        rfl
      _ = _ := by simp
  by_cases present : v ∈ oddVertices G es
  case pos =>
    obtain ⟨e, covers, unique⟩ := matching.2.2 v present
    have singleton : ((matchingEdges G pairs).filter fun f => v ∈ f) = {e} :=
      Finset.ext fun f =>
        ⟨fun hf => Finset.mem_singleton.mpr (unique f (Finset.mem_filter.mp hf)),
          fun hf => Finset.mem_filter.mpr ((Finset.mem_singleton.mp hf).symm ▸ covers)⟩
    simp [incidence, singleton, present]
  case neg =>
    have empty : ((matchingEdges G pairs).filter fun e => v ∈ e) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
        let ⟨inMatching, hasV⟩ := Finset.mem_filter.mp he
        present ((matching.2.1 e inMatching).2 v hasV)
    simp [incidence, empty, present]

/-- Adding the chosen matching paths corrects the parity of every vertex degree. -/
theorem degree_matching_augmentation_even {G : Network} {es : List (Fin G.q)}
    {pairs : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (matching : PerfectMatching G es pairs) (expansion : Expands G pairs paths) (v : Fin G.n) :
    degree G (es ++ paths.flatten.map Prod.fst) v % 2 = 0 := by
  rw [degree_append, Nat.add_mod, expanded_degree_mod_two_eq_pairDegree v expansion,
    matching_pairDegree_eq matching v]
  simp only [oddVertices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.odd_iff]
  split <;> omega

end VehicleRoutingSurvey.Routing
end RppSource_OddSupport

/-! matching/EulerSupport.lean -/
section RppSource_EulerSupport
namespace VehicleRoutingSurvey.Routing

/-- A vertex incident to at least one edge occurrence in the list. -/
def EdgeSupport (G : Network) (es : List (Fin G.q)) (v : Fin G.n) : Prop :=
  ∃ e ∈ es, G.tail e = v ∨ G.head e = v

/-- Undirected adjacency using a link present in the occurrence list. -/
def EdgeAdjacent (G : Network) (es : List (Fin G.q)) (u v : Fin G.n) : Prop :=
  ∃ e ∈ es, (G.tail e = u ∧ G.head e = v) ∨ (G.head e = u ∧ G.tail e = v)

def EdgeSupportConnected (G : Network) (es : List (Fin G.q)) : Prop :=
  ∀ u, EdgeSupport G es u → ∀ v, EdgeSupport G es v →
    Relation.ReflTransGen (EdgeAdjacent G es) u v

theorem edgeAdjacent_of_traversal {G : Network} {es : List (Fin G.q)} (t : Traversal G)
    (used : t.1 ∈ es) : EdgeAdjacent G es (start G t) (finish G t) := by
  refine ⟨t.1, used, ?_⟩
  cases dir : t.2 <;> simp [start, finish, dir]

theorem edgeReachable_of_path {G : Network} {es : List (Fin G.q)} {u v : Fin G.n}
    {ts : List (Traversal G)} (path : IsPath G u ts v) (supported : ∀ t ∈ ts, t.1 ∈ es) :
    Relation.ReflTransGen (EdgeAdjacent G es) u v := by
  induction ts generalizing u with
  | nil => exact (show u = v from path) ▸ Relation.ReflTransGen.refl
  | cons t rest ih =>
    exact path.1 ▸ Relation.ReflTransGen.head (edgeAdjacent_of_traversal t (supported t List.mem_cons_self))
      (ih path.2.2 (fun s hs => supported s (List.mem_cons_of_mem _ hs)))

end VehicleRoutingSurvey.Routing
end RppSource_EulerSupport

/-! matching/EulerRun.lean -/
section RppSource_EulerRun
namespace VehicleRoutingSurvey.Routing

private structure PartialTraversal {G : Network} (es : List (Fin G.q)) (u v : Fin G.n) where
  steps : List (Traversal G)
  remaining : List (Fin G.q)
  path : IsPath G u steps v
  uses : (steps.map Prod.fst ++ remaining).Perm es

private def PartialTraversal.empty {G : Network} (es : List (Fin G.q)) (u : Fin G.n) :
    PartialTraversal es u u := ⟨[], es, rfl, .refl _⟩

private def PartialTraversal.appendLink {G : Network} {es : List (Fin G.q)} {u v : Fin G.n}
    (trail : PartialTraversal es u v) (t : Traversal G) (used : t.1 ∈ trail.remaining)
    (path : IsPath G v [t] (finish G t)) : PartialTraversal es u (finish G t) where
  steps := trail.steps ++ [t]
  remaining := trail.remaining.erase t.1
  path := isPath_append trail.path path
  uses := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] using
      (((List.perm_cons_erase used).symm.append_left (trail.steps.map Prod.fst)).trans trail.uses)

private theorem exists_longest_partial {G : Network} (es : List (Fin G.q)) (u : Fin G.n)
    (acceptEnd : Fin G.n → Prop) (trivialEnd : acceptEnd u) :
    ∃ (w : Fin G.n) (trail : PartialTraversal es u w), acceptEnd w ∧
      ∀ v (other : PartialTraversal es u v), acceptEnd v → other.steps.length ≤ trail.steps.length := by
  classical
  let feasible (k : ℕ) : Prop :=
    ∃ (w : Fin G.n) (trail : PartialTraversal es u w), acceptEnd w ∧ trail.steps.length = k
  obtain ⟨w, trail, accepted, lengthEq⟩ := Nat.findGreatest_spec (P := feasible) (Nat.zero_le es.length)
    ⟨u, PartialTraversal.empty es u, trivialEnd, rfl⟩
  exact ⟨w, trail, accepted, fun v other admissible => by
    have length := other.uses.length_eq
    have bounded : other.steps.length ≤ es.length := by
      simp only [List.length_append, List.length_map] at length
      omega
    rw [lengthEq]
    exact Nat.le_findGreatest (P := feasible) bounded ⟨v, other, admissible, rfl⟩⟩

private theorem orient_incident {G : Network} (undirected : Undirected G) {e : Fin G.q}
    {u : Fin G.n} (incident : G.tail e = u ∨ G.head e = u) :
    ∃ t : Traversal G, t.1 = e ∧ IsPath G u [t] (finish G t) := by
  exact incident.elim
    (fun h => ⟨(e, true), rfl, by simp [IsPath, start, h.symm]⟩)
    (fun h => ⟨(e, false), rfl, by simp [IsPath, start, h.symm, undirected e]⟩)

private theorem degree_zero_of_not_support {G : Network} {es : List (Fin G.q)} {u : Fin G.n}
    (isolated : ¬EdgeSupport G es u) : degree G es u = 0 := by
  exact degree_eq_zero_of_no_incident es u fun e he =>
    ⟨fun h => isolated ⟨e, he, Or.inl h⟩, fun h => isolated ⟨e, he, Or.inr h⟩⟩

private theorem nonempty_circuit {G : Network} {es : List (Fin G.q)} (undirected : Undirected G)
    (even : ∀ v : Fin G.n, degree G es v % 2 = 0) {u : Fin G.n} (support : EdgeSupport G es u) :
    ∃ trail : PartialTraversal es u u, 0 < trail.steps.length := by
  obtain ⟨w, trail, _, longest⟩ := exists_longest_partial es u (fun _ => True) trivial
  have positive : 0 < trail.steps.length := by
    obtain ⟨e, he, direction⟩ := support
    obtain ⟨t, rfl, step⟩ := orient_incident undirected direction
    let first := (PartialTraversal.empty es u).appendLink t he step
    exact (show 0 < first.steps.length from Nat.zero_lt_one).trans_le (longest _ first trivial)
  have closed : w = u := by
    by_contra ne
    have available : EdgeSupport G trail.remaining w := by
      by_contra none
      have same := degree_eq_of_perm trail.uses w
      rw [degree_append, degree_zero_of_not_support none, Nat.add_zero] at same
      have odd := degree_openPath_mod_two_at_finish trail.path (Ne.symm ne)
      rw [same, even w] at odd
      exact Nat.zero_ne_one odd
    obtain ⟨e, he, direction⟩ := available
    obtain ⟨t, rfl, step⟩ := orient_incident undirected direction
    exact Nat.not_succ_le_self trail.steps.length (by
      simpa [PartialTraversal.appendLink] using longest _ (trail.appendLink t he step) trivial)
  subst w
  exact ⟨trail, positive⟩

private theorem exists_split_at_visited {G : Network} {u w v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) (visited : w ∈ pathVertices G u ts) :
    ∃ pre post, ts = pre ++ post ∧ IsPath G u pre w ∧ IsPath G w post v := by
  induction ts generalizing u
  case nil =>
    exact let same : w = u := by simpa [pathVertices] using visited
      ⟨[], [], rfl, same.symm, same.trans path⟩
  case cons a rest ih =>
    rcases List.mem_cons.mp visited with rfl | tailSeen
    · exact ⟨[], a :: rest, rfl, rfl, path⟩
    · obtain ⟨pre, post, split, beforePath, afterPath⟩ := ih path.2.2 tailSeen
      exact ⟨a :: pre, post, congrArg (List.cons a) split, ⟨path.1, path.2.1, beforePath⟩, afterPath⟩

private theorem used_edge_ends_visited {G : Network} {u : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts u) {e : Fin G.q} (used : e ∈ ts.map Prod.fst) :
    G.tail e ∈ pathVertices G u ts ∧ G.head e ∈ pathVertices G u ts := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp used
  have seenStart : start G t ∈ pathVertices G u ts := List.mem_toFinset.mp
    ((pathVertices_toFinset u ts).symm ▸ traversal_start_visited path t ht)
  have seenFinish : finish G t ∈ pathVertices G u ts :=
    List.mem_cons_of_mem u (List.mem_map_of_mem ht)
  cases direction : t.2 with
  | false => exact ⟨by simpa [finish, direction] using seenFinish,
      by simpa [start, direction] using seenStart⟩
  | true => exact ⟨by simpa [start, direction] using seenStart,
      by simpa [finish, direction] using seenFinish⟩

private theorem leftover_incident_at_visited {G : Network} {es : List (Fin G.q)} {u : Fin G.n}
    (connected : EdgeSupportConnected G es) (support : EdgeSupport G es u)
    (trail : PartialTraversal es u u) (leftover : trail.remaining ≠ []) :
    ∃ v ∈ pathVertices G u trail.steps, EdgeSupport G trail.remaining v := by
  by_contra disjoint
  have keeps (a b : Fin G.n) (step : EdgeAdjacent G es a b)
      (seen : a ∈ pathVertices G u trail.steps) : b ∈ pathVertices G u trail.steps := by
    obtain ⟨e, he, orientation⟩ := step
    have notLeft : e ∉ trail.remaining := fun h => disjoint ⟨a, seen, e, h,
      orientation.elim (fun dir => Or.inl dir.1) (fun dir => Or.inr dir.1)⟩
    have used := used_edge_ends_visited trail.path
      ((List.mem_append.mp (trail.uses.mem_iff.mpr he)).resolve_right notLeft)
    exact orientation.elim (fun dir => dir.2 ▸ used.2) (fun dir => dir.2 ▸ used.1)
  have reachable_seen {v : Fin G.n} (reach : Relation.ReflTransGen (EdgeAdjacent G es) u v) :
      v ∈ pathVertices G u trail.steps := by
    induction reach with
    | refl => exact List.mem_cons_self
    | tail _ step ih => exact keeps _ _ step ih
  exact (List.exists_mem_of_ne_nil _ leftover).elim fun e he =>
    let original := trail.uses.mem_iff.mp (List.mem_append.mpr (Or.inr he))
    let reached := connected u support (G.tail e) ⟨e, original, Or.inl rfl⟩
    disjoint ⟨G.tail e, reachable_seen reached, e, he, Or.inl rfl⟩

private theorem splice_circuit {G : Network} {es : List (Fin G.q)} {u v : Fin G.n}
    (trail : PartialTraversal es u u) (revisit : v ∈ pathVertices G u trail.steps)
    (more : PartialTraversal trail.remaining v v) :
    ∃ longer : PartialTraversal es u u, longer.steps.length = trail.steps.length + more.steps.length := by
  obtain ⟨pre, post, split, beforePath, afterPath⟩ := exists_split_at_visited trail.path revisit
  have reorder : ((pre ++ more.steps ++ post).map Prod.fst ++ more.remaining).Perm
      ((pre ++ post).map Prod.fst ++ (more.steps.map Prod.fst ++ more.remaining)) := by
    simpa only [List.map_append, List.append_assoc] using
      ((List.perm_append_comm_assoc (more.steps.map Prod.fst) (post.map Prod.fst)
        more.remaining).append_left (pre.map Prod.fst))
  have conserved := reorder.trans ((more.uses.append_left ((pre ++ post).map Prod.fst)).trans
    (split ▸ trail.uses))
  exact ⟨⟨pre ++ more.steps ++ post, more.remaining,
    isPath_append (isPath_append beforePath more.path) afterPath, conserved⟩,
    by simp [split, Nat.add_assoc, Nat.add_comm]⟩

/-- Euler circuit rooted at any vertex incident to an occurrence in the edge list. -/
theorem exists_euler_traversal {G : Network} {es : List (Fin G.q)} (undirected : Undirected G)
    (even : ∀ v : Fin G.n, degree G es v % 2 = 0)
    (connected : EdgeSupportConnected G es) (u : Fin G.n) (support : EdgeSupport G es u) :
    ∃ ts, IsPath G u ts u ∧ (ts.map Prod.fst).Perm es := by
  obtain ⟨w, trail, closed, longest⟩ := exists_longest_partial es u (fun v => v = u) rfl
  subst w
  refine ⟨trail.steps, trail.path, ?_⟩
  by_cases none : trail.remaining = []
  · simpa [none] using trail.uses
  · exfalso
    have remainingEven (v : Fin G.n) : degree G trail.remaining v % 2 = 0 := by
      have conserved := degree_eq_of_perm trail.uses v
      rw [degree_append] at conserved
      have usedEven := degree_closedPath_mod_two trail.path v
      have allEven := even v
      omega
    exact (leftover_incident_at_visited connected support trail none).elim fun _ hv =>
      (nonempty_circuit undirected remainingEven hv.2).elim fun more positive =>
        (splice_circuit trail hv.1 more).elim fun extended length =>
          (not_lt_of_ge (longest u extended rfl)) (by omega)

/-- Euler circuit existence with an idle circuit for an empty list. -/
theorem exists_euler_circuit {G : Network} {es : List (Fin G.q)} (nonempty : 0 < G.n)
    (undirected : Undirected G) (even : ∀ v : Fin G.n, degree G es v % 2 = 0)
    (connected : EdgeSupportConnected G es) :
    ∃ u ts, IsPath G u ts u ∧ (ts.map Prod.fst).Perm es := by
  cases es with
  | nil => exact ⟨⟨0, nonempty⟩, [], rfl, .refl _⟩
  | cons e rest => exact ⟨G.tail e, exists_euler_traversal undirected even connected (G.tail e)
      ⟨e, List.mem_cons_self, Or.inl rfl⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_EulerRun

/-! RunCost.lean -/
section RppSource_RunCost
namespace VehicleRoutingSurvey.Routing

variable {G : Network} {I : Service}

def linkListCost (G : Network) (es : List (Fin G.q)) : ℝ :=
  (es.map G.weight).sum

theorem linkListCost_append (es fs : List (Fin G.q)) :
    linkListCost G (es ++ fs) = linkListCost G es + linkListCost G fs := by
  simp [linkListCost]

theorem pathCost_eq_linkListCost (ts : List (Traversal G)) :
    pathCost G ts = linkListCost G (ts.map Prod.fst) := by
  simp [pathCost, linkListCost, List.map_map, Function.comp_def]

theorem linkListCost_perm {es fs : List (Fin G.q)} (permutation : es.Perm fs) :
    linkListCost G es = linkListCost G fs :=
  (permutation.map G.weight).sum_eq

noncomputable def requiredCost (I : Service) : ℝ :=
  ∑ e ∈ I.links, I.graph.weight e

theorem linkListCost_required {es : List (Fin I.graph.q)}
    (distinct : es.Nodup) (covers : es.toFinset = I.links) :
    linkListCost I.graph es = requiredCost I := by
  rw [requiredCost, ← covers, List.sum_toFinset I.graph.weight distinct, linkListCost]

theorem expands_cost {pairs : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (expansion : Expands G pairs paths) : pathCost G paths.flatten = pairCost G pairs := by
  induction expansion with
  | nil => rfl
  | @cons pair ts pairs paths shortest _ ih =>
    exact (pathCost_append ts paths.flatten).trans
      (congrArg₂ (· + ·) (distance_eq_of_shortestPath shortest).symm ih)

theorem ruralRun_cost_of_witnesses {ts : List (Traversal I.graph)}
    {base : List (Fin I.graph.q)} {tree matching : List (Fin I.graph.n × Fin I.graph.n)}
    {tp mp : List (List (Traversal I.graph))}
    (distinct : base.Nodup) (covers : base.toFinset = I.links)
    (treePaths : Expands I.graph tree tp) (matchingPaths : Expands I.graph matching mp)
    (edges : (ts.map Prod.fst).Perm (base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst)) :
    pathCost I.graph ts = requiredCost I + pairCost I.graph tree + pairCost I.graph matching := by
  rw [pathCost_eq_linkListCost, linkListCost_perm edges, linkListCost_append, linkListCost_append,
    linkListCost_required distinct covers, ← pathCost_eq_linkListCost, ← pathCost_eq_linkListCost,
    expands_cost treePaths, expands_cost matchingPaths]

theorem ruralRun_feasible {u : Fin I.graph.n} {ts : List (Traversal I.graph)}
    (rural : Rural I) (run : RuralRun I u ts) : Feasible I u ts := by
  classical
  have noVertices := rural.2.2.2
  by_cases empty : I.links = ∅
  · have noSteps : ts = [] := by simpa [RuralRun, empty] using run
    subst ts
    simp [Feasible, IsPath, noVertices, empty]
  · rw [RuralRun, if_neg empty] at run
    obtain ⟨base, _, _, _, _, _, covers, _, _, _, _, path, edges⟩ := run
    refine ⟨path, by simp [noVertices], ?_⟩
    intro e he
    have baseMem : e ∈ base := List.mem_toFinset.mp (covers.symm ▸ he)
    have used : e ∈ ts.map Prod.fst := edges.mem_iff.mpr (by simp [baseMem])
    exact (List.mem_map.mp used).elim (fun t ht => ⟨t, ht.1, ht.2⟩)

/-- The two comparison inequalities give the approximation for every admitted run. -/
theorem ruralRun_le_of_comparison_bounds {u : Fin I.graph.n} {ts comparison : List (Traversal I.graph)}
    (rural : Rural I) (run : RuralRun I u ts)
    (connectorBound : ∀ tree, MinimumComponentTree I tree →
      requiredCost I + pairCost I.graph tree ≤ pathCost I.graph comparison)
    (matchingBound : ∀ (base : List (Fin I.graph.q)) tree paths matching,
      base.Nodup → base.toFinset = I.links → MinimumComponentTree I tree →
      Expands I.graph tree paths →
      MinimumMatching I.graph (base ++ paths.flatten.map Prod.fst) matching →
      2 * pairCost I.graph matching ≤ pathCost I.graph comparison) :
    pathCost I.graph ts ≤ (3 / 2 : ℝ) * pathCost I.graph comparison := by
  classical
  by_cases empty : I.links = ∅
  · have noSteps : ts = [] := by simpa [RuralRun, empty] using run
    simpa [noSteps, pathCost] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (pathCost_nonnegative rural.2.1 comparison)
  · rw [RuralRun, if_neg empty] at run
    obtain ⟨base, tree, matching, tp, mp, distinct, covers, minimumTree, expandsTree,
      minimumMatching, expandsMatching, _, edges⟩ := run
    rw [ruralRun_cost_of_witnesses distinct covers expandsTree expandsMatching edges]
    linarith only [connectorBound tree minimumTree,
      matchingBound base tree tp matching distinct covers minimumTree expandsTree minimumMatching]

end VehicleRoutingSurvey.Routing
end RppSource_RunCost

/-! Optimum.lean -/
section RppSource_Optimum
namespace VehicleRoutingSurvey.Routing

variable {I : Service}

theorem optimum_le_feasible (nonnegative : Nonnegative I.graph) {u : Fin I.graph.n}
    {ts : List (Traversal I.graph)} (tour : Feasible I u ts) :
    optimum I ≤ pathCost I.graph ts :=
  csInf_le ⟨0, fun _ ⟨_, ss, _, cost⟩ => cost.symm ▸ pathCost_nonnegative nonnegative ss⟩
    ⟨u, ts, tour, rfl⟩

theorem empty_rural_run_and_optimum (rural : Rural I) (empty : I.links = ∅) :
    ∃ u : Fin I.graph.n, RuralRun I u [] ∧ Feasible I u [] ∧ optimum I = 0 := by
  classical
  let u : Fin I.graph.n := ⟨0, rural.1.1⟩
  have run : RuralRun I u [] := by simp [RuralRun, empty]
  have feasible := ruralRun_feasible rural run
  exact ⟨u, run, feasible, IsLeast.csInf_eq ⟨⟨u, [], feasible, rfl⟩,
    fun _ ⟨_, ts, _, cost⟩ => cost.symm ▸ pathCost_nonnegative rural.2.1 ts⟩⟩

private theorem isPath_flatMap_closed {G : Network} {u : Fin G.n} {α : Type*}
    (items : List α) (excursion : α → List (Traversal G)) (closed : ∀ a, IsPath G u (excursion a) u) :
    IsPath G u (items.flatMap excursion) u := by
  induction items with
  | nil => rfl
  | cons a _ ih => exact isPath_append (closed a) ih

/-- Concatenating one round trip through each required link gives a feasible tour. -/
theorem exists_rural_feasible (rural : Rural I) : ∃ u ts, Feasible I u ts := by
  classical
  let u : Fin I.graph.n := ⟨0, rural.1.1⟩
  let outbound (e : Fin I.graph.q) := (rural.1.2 u (I.graph.tail e)).choose
  let inbound (e : Fin I.graph.q) := (rural.1.2 (I.graph.head e) u).choose
  let excursion (e : Fin I.graph.q) := outbound e ++ (e, true) :: inbound e
  have closed (e : Fin I.graph.q) : IsPath I.graph u (excursion e) u := by
    refine isPath_append (rural.1.2 u (I.graph.tail e)).choose_spec ?_
    exact ⟨rfl, Or.inr rfl, (rural.1.2 (I.graph.head e) u).choose_spec⟩
  refine ⟨u, I.links.toList.flatMap excursion, isPath_flatMap_closed _ excursion closed,
    by simp [rural.2.2.2], ?_⟩
  intro e required
  exact ⟨(e, true), List.mem_flatMap.mpr ⟨e, Finset.mem_toList.mpr required,
    List.mem_append_right _ List.mem_cons_self⟩, rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_Optimum

/-! Multiplicity.lean -/
section RppSource_Multiplicity
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Remove pairs of repeated links while retaining support and degree parity.
This reduction preserves loops and parallel link identifiers. -/
theorem reduce_link_multiplicities (es : List (Fin G.q)) :
    ∃ rs : List (Fin G.q), rs.Sublist es ∧
      (∀ e, e ∈ rs ↔ e ∈ es) ∧ (∀ e, rs.count e ≤ 2) ∧
      (∀ v, degree G rs v % 2 = degree G es v % 2) := by
  by_cases bounded : ∀ e, es.count e ≤ 2
  · exact ⟨es, List.Sublist.refl _, fun _ => Iff.rfl, bounded, fun _ => rfl⟩
  · push Not at bounded
    obtain ⟨e, excess⟩ := bounded
    let fewer := (es.erase e).erase e
    have mem : e ∈ es := List.count_pos_iff.mp (by omega)
    have twiceMem : e ∈ es.erase e := List.count_pos_iff.mp (by simp; omega)
    have permutation : es.Perm (e :: e :: fewer) :=
      (List.perm_cons_erase mem).trans ((List.perm_cons_erase twiceMem).cons e)
    have support (f : Fin G.q) : f ∈ fewer ↔ f ∈ es := by
      simp only [← List.count_pos_iff]
      by_cases equal : f = e
      · subst f
        simp only [fewer, List.count_erase_self]
        omega
      · simp only [fewer, List.count_erase_of_ne equal]
    have parity (v : Fin G.n) : degree G fewer v % 2 = degree G es v % 2 := by
      rw [degree_eq_of_perm permutation]
      by_cases tail : G.tail e = v <;> by_cases head : G.head e = v <;>
        simp [degree, tail, head] <;> omega
    obtain ⟨rs, subset, sameSupport, count, sameParity⟩ := reduce_link_multiplicities fewer
    have first : (es.erase e).Sublist es := List.erase_sublist
    have second : fewer.Sublist (es.erase e) := List.erase_sublist
    exact ⟨rs, subset.trans (second.trans first),
      fun f => (sameSupport f).trans (support f), count, fun v => (sameParity v).trans (parity v)⟩
termination_by es.length
decreasing_by
  change fewer.length < es.length
  have length := permutation.length_eq
  simp only [List.length_cons] at length
  omega

theorem length_le_twice_links {es : List (Fin G.q)} (count : ∀ e, es.count e ≤ 2) :
    es.length ≤ 2 * G.q := by
  rw [← List.sum_toFinset_count_eq_length]
  calc
    _ ≤ ∑ _ ∈ es.toFinset, (2 : ℕ) := Finset.sum_le_sum (fun e _ => count e)
    _ ≤ _ := by
      have card := Finset.card_le_univ es.toFinset
      simp only [Fintype.card_fin] at card
      simpa [mul_comm] using Nat.mul_le_mul_left 2 card

end VehicleRoutingSurvey.Routing
end RppSource_Multiplicity

/-! RequiredComponents.lean -/
section RppSource_RequiredComponents
namespace VehicleRoutingSurvey.Routing

variable {I : Service}

theorem requiredAdjacent_of_traversal (t : Traversal I.graph) (required : t.1 ∈ I.links) :
    requiredAdjacent I (start I.graph t) (finish I.graph t) := by
  cases direction : t.2 <;> simp [requiredAdjacent, start, finish, direction]; all_goals
    exact ⟨t.1, required, by simp⟩

theorem requiredAdjacent_comm {u v : Fin I.graph.n} (adjacent : requiredAdjacent I u v) :
    requiredAdjacent I v u :=
  adjacent.elim fun edge ⟨required, direction⟩ => ⟨edge, required, direction.symm⟩

theorem requiredAdjacent_mem_requiredVertices {u v : Fin I.graph.n}
    (adjacent : requiredAdjacent I u v) : u ∈ requiredVertices I ∧ v ∈ requiredVertices I := by
  obtain ⟨e, required, forward | backward⟩ := adjacent
  · exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, required, forward.1⟩),
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, required, forward.2⟩)⟩
  · exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, required, backward.2⟩),
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, required, backward.1⟩)⟩

/-- Quotient labels keep required components distinct while allowing arbitrary representatives. -/
def requiredComponentSetoid (I : Service) : Setoid (Fin I.graph.n) where
  r := sameComponent I
  iseqv := ⟨fun _ => .refl, fun h =>
    @Std.Symm.symm _ _ (@Relation.ReflTransGen.stdSymm _ _ ⟨fun _ _ => requiredAdjacent_comm⟩) _ _ h,
    fun h k => h.trans k⟩

abbrev RequiredComponent (I : Service) := Quotient (requiredComponentSetoid I)

def requiredComponent (I : Service) (u : Fin I.graph.n) : RequiredComponent I := Quotient.mk _ u

theorem requiredComponent_eq_iff {u v : Fin I.graph.n} :
    requiredComponent I u = requiredComponent I v ↔ sameComponent I u v :=
  ⟨Quotient.exact, fun same => Quotient.sound (s := requiredComponentSetoid I) same⟩

noncomputable def activeRequiredComponents (I : Service) : Finset (RequiredComponent I) := by
  classical
  exact (requiredVertices I).image (requiredComponent I)

noncomputable def requiredRepresentative (I : Service) (c : ↥(activeRequiredComponents I)) :
    Fin I.graph.n := by
  classical
  exact (Finset.mem_image.mp c.property).choose

theorem requiredRepresentative_spec (c : ↥(activeRequiredComponents I)) :
    requiredRepresentative I c ∈ requiredVertices I ∧
      requiredComponent I (requiredRepresentative I c) = c.val := by
  classical
  exact (Finset.mem_image.mp c.property).choose_spec

noncomputable def requiredRepresentatives (I : Service) : List (Fin I.graph.n) :=
  (activeRequiredComponents I).attach.toList.map (requiredRepresentative I)

theorem requiredRepresentatives_length (I : Service) :
    (requiredRepresentatives I).length = (activeRequiredComponents I).card := by
  simp [requiredRepresentatives]

theorem requiredRepresentatives_valid (I : Service) :
    ComponentRepresentatives I (requiredRepresentatives I) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u member
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
    exact (requiredRepresentative_spec c).1
  · exact List.pairwise_map.mpr ((Finset.nodup_toList _).imp (fun different same =>
      different (Subtype.ext ((requiredRepresentative_spec _).2.symm.trans
        (requiredComponent_eq_iff.mpr same |>.trans (requiredRepresentative_spec _).2)))))
  · intro u member
    let c : ↥(activeRequiredComponents I) := ⟨requiredComponent I u, Finset.mem_image_of_mem _ member⟩
    exact ⟨requiredRepresentative I c, List.mem_map.mpr ⟨c, by simp, rfl⟩,
      requiredComponent_eq_iff.mp (requiredRepresentative_spec c).2.symm⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredComponents

/-! ExpansionConnectivity.lean -/
section RppSource_ExpansionConnectivity
namespace VehicleRoutingSurvey.Routing

variable {I : Service} {G : Network}

theorem edgeAdjacent_comm {es : List (Fin G.q)} {u v : Fin G.n}
    (adjacent : EdgeAdjacent G es u v) : EdgeAdjacent G es v u :=
  adjacent.elim fun e ⟨included, oriented⟩ =>
    ⟨e, included, oriented.elim (fun h => .inr h.symm) (fun h => .inl h.symm)⟩

theorem edgeReachable_comm {es : List (Fin G.q)} {u v : Fin G.n}
    (reaches : Relation.ReflTransGen (EdgeAdjacent G es) u v) :
    Relation.ReflTransGen (EdgeAdjacent G es) v u := by
  let _ : Std.Symm (EdgeAdjacent G es) := ⟨fun _ _ => edgeAdjacent_comm⟩
  exact @Std.Symm.symm _ _ Relation.ReflTransGen.stdSymm u v reaches

theorem reaches_traversal_endpoints {es : List (Fin G.q)} {u v : Fin G.n}
    {ts : List (Traversal G)} (path : IsPath G u ts v) (supported : ∀ t ∈ ts, t.1 ∈ es)
    (t : Traversal G) (hit : t ∈ ts) :
    Relation.ReflTransGen (EdgeAdjacent G es) u (start G t) ∧
    Relation.ReflTransGen (EdgeAdjacent G es) u (finish G t) := by
  induction ts generalizing u with
  | nil => simp at hit
  | cons initial rest ih =>
    have first : Relation.ReflTransGen (EdgeAdjacent G es) u (finish G initial) := by
      rw [path.1]
      exact .single (edgeAdjacent_of_traversal initial (supported initial List.mem_cons_self))
    rcases List.mem_cons.mp hit with rfl | later
    · exact ⟨path.1 ▸ .refl, first⟩
    · obtain ⟨toStart, toEnd⟩ := ih path.2.2 (fun s hs => supported s (List.mem_cons_of_mem _ hs)) later
      exact ⟨first.trans toStart, first.trans toEnd⟩

theorem path_of_mem_expansion {pairs : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (expands : Expands G pairs paths) {pair : Fin G.n × Fin G.n} (member : pair ∈ pairs) :
    ∃ path ∈ paths, ShortestPath G pair.1 pair.2 path := by
  induction expands with
  | nil => simp at member
  | @cons first segment rest remaining shortest _ ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨segment, List.mem_cons_self, shortest⟩
    · obtain ⟨path, included, walk⟩ := ih later
      exact ⟨path, List.mem_cons_of_mem _ included, walk⟩

theorem pair_of_mem_expansion {pairs : List (Fin G.n × Fin G.n)} {paths : List (List (Traversal G))}
    (expands : Expands G pairs paths) {path : List (Traversal G)} (member : path ∈ paths) :
    ∃ pair ∈ pairs, ShortestPath G pair.1 pair.2 path := by
  induction expands with
  | nil => simp at member
  | @cons first segment rest remaining shortest _ ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨first, List.mem_cons_self, shortest⟩
    · obtain ⟨pair, included, walk⟩ := ih later
      exact ⟨pair, List.mem_cons_of_mem _ included, walk⟩

theorem edgeSupport_base_iff_required {base : List (Fin I.graph.q)}
    (covers : base.toFinset = I.links) (v : Fin I.graph.n) :
    EdgeSupport I.graph base v ↔ v ∈ requiredVertices I := by
  have required (e : Fin I.graph.q) : e ∈ base ↔ e ∈ I.links := by
    rw [← covers, List.mem_toFinset]
  constructor
  · rintro ⟨e, used, tail | head⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, (required e).mp used, tail⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, (required e).mp used, head⟩)
  · intro visited
    rcases Finset.mem_union.mp visited with tail | head
    · obtain ⟨e, used, equal⟩ := Finset.mem_image.mp tail
      exact ⟨e, (required e).mpr used, .inl equal⟩
    · obtain ⟨e, used, equal⟩ := Finset.mem_image.mp head
      exact ⟨e, (required e).mpr used, .inr equal⟩

private theorem expansion_reaches_incident {all : List (Fin I.graph.q)}
    {pairs : List (Fin I.graph.n × Fin I.graph.n)} {paths : List (List (Traversal I.graph))}
    (expands : Expands I.graph pairs paths)
    (origins : ∀ p ∈ pairs, p.1 ∈ requiredVertices I)
    (supported : ∀ t ∈ paths.flatten, t.1 ∈ all)
    {v : Fin I.graph.n} (incident : EdgeSupport I.graph (paths.flatten.map Prod.fst) v) :
    ∃ u ∈ requiredVertices I, Relation.ReflTransGen (EdgeAdjacent I.graph all) u v := by
  obtain ⟨e, used, endpoint⟩ := incident
  obtain ⟨t, tIn, label⟩ := List.mem_map.mp used
  obtain ⟨ls, lsIn, member⟩ := List.mem_flatten.mp tIn
  obtain ⟨p, pIn, shortest⟩ := pair_of_mem_expansion expands lsIn
  have reached := reaches_traversal_endpoints shortest.1
    (fun d h => supported d (List.mem_flatten.mpr ⟨ls, lsIn, h⟩)) t member
  have atEndpoint : start I.graph t = v ∨ finish I.graph t = v := by
    cases direction : t.2
    · simpa [start, finish, direction, label, or_comm] using endpoint
    · simpa [start, finish, direction, label] using endpoint
  exact ⟨p.1, origins p pIn, atEndpoint.elim (fun eq => eq ▸ reached.1) (fun eq => eq ▸ reached.2)⟩

/-- Service links and expanded connectors are connected. Expanding further
paths whose origins lie in the service support preserves connected support. -/
theorem expandedSupport_connected {base : List (Fin I.graph.q)}
    {tree extra : List (Fin I.graph.n × Fin I.graph.n)}
    {tp mp : List (List (Traversal I.graph))} (covers : base.toFinset = I.links)
    (component : ComponentTree I tree) (treePaths : Expands I.graph tree tp)
    (extraPaths : Expands I.graph extra mp) (origins : ∀ p ∈ extra, p.1 ∈ requiredVertices I) :
    EdgeSupportConnected I.graph (base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst) := by
  let all := base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst
  have inBase {e : Fin I.graph.q} (he : e ∈ base) : e ∈ all := by simp [all, he]
  have inTree {t : Traversal I.graph} (ht : t ∈ tp.flatten) : t.1 ∈ all :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ht))
  have inExtra {t : Traversal I.graph} (ht : t ∈ mp.flatten) : t.1 ∈ all :=
    List.mem_append_right _ (List.mem_map_of_mem ht)
  have treeEdge {p : Fin I.graph.n × Fin I.graph.n} (member : p ∈ tree) :
      Relation.ReflTransGen (EdgeAdjacent I.graph all) p.1 p.2 := by
    obtain ⟨ls, lsIn, shortest⟩ := path_of_mem_expansion treePaths member
    exact edgeReachable_of_path shortest.1 (fun t ht => inTree (List.mem_flatten.mpr ⟨ls, lsIn, ht⟩))
  have betweenRequired (x : Fin I.graph.n) (hx : x ∈ requiredVertices I)
      (y : Fin I.graph.n) (hy : y ∈ requiredVertices I) :
      Relation.ReflTransGen (EdgeAdjacent I.graph all) x y := by
    have connected := component.2.2 x hx y hy
    clear hx hy
    induction connected with
    | refl => exact .refl
    | tail _ step ih =>
      rcases step with required | pair | reversed
      · obtain ⟨e, he, direction⟩ := required
        have used := inBase (List.mem_toFinset.mp (covers.symm ▸ he))
        exact ih.tail ⟨e, used, direction.imp id And.symm⟩
      · exact ih.trans (treeEdge pair)
      · exact ih.trans (edgeReachable_comm (treeEdge reversed))
  have fromRequired (v : Fin I.graph.n) (support : EdgeSupport I.graph all v) :
      ∃ u ∈ requiredVertices I, Relation.ReflTransGen (EdgeAdjacent I.graph all) u v := by
    obtain ⟨e, used, endpoint⟩ := support
    simp only [all, List.mem_append] at used
    rcases used with (baseEdge | treeEdge) | extraEdge
    · exact ⟨v, (edgeSupport_base_iff_required covers v).mp ⟨e, baseEdge, endpoint⟩, .refl⟩
    · exact expansion_reaches_incident treePaths (fun p hp => (component.2.1 p hp).1)
        (fun _ ht => inTree ht) ⟨e, treeEdge, endpoint⟩
    · exact expansion_reaches_incident extraPaths origins (fun _ ht => inExtra ht) ⟨e, extraEdge, endpoint⟩
  intro x hx y hy
  obtain ⟨u, hu, pathX⟩ := fromRequired x hx
  obtain ⟨v, hv, pathY⟩ := fromRequired y hy
  exact ((edgeReachable_comm pathX).trans (betweenRequired u hu v hv)).trans pathY

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionConnectivity

/-! sharpness/OptimumAttainment.lean -/
section RppSource_OptimumAttainment
namespace VehicleRoutingSurvey.Routing

private theorem least_cost_of_bounded_tours {I : Service} (nonnegative : Nonnegative I.graph)
    (bounded : ∀ u ts, Feasible I u ts → ∃ v ss, Feasible I v ss ∧
      ss.length ≤ 2 * I.graph.q ∧ pathCost I.graph ss ≤ pathCost I.graph ts)
    (feasible : ∃ u ts, Feasible I u ts) :
    ∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I := by
  classical
  let Code := Fin I.graph.n × (Σ k : Fin (2 * I.graph.q + 1),
    Fin k.val → Traversal I.graph)
  let decode (s : Code) : List (Traversal I.graph) := List.ofFn s.2.2
  let encode (u : Fin I.graph.n) (ts : List (Traversal I.graph))
      (len : ts.length ≤ 2 * I.graph.q) : Code :=
    ⟨u, ⟨⟨ts.length, Nat.lt_succ_of_le len⟩, ts.get⟩⟩
  have decode_encode (u : Fin I.graph.n) (ts : List (Traversal I.graph))
      (len : ts.length ≤ 2 * I.graph.q) : decode (encode u ts len) = ts :=
    List.ofFn_get ts
  let candidates : Finset Code := Finset.univ.filter (fun s => Feasible I s.1 (decode s))
  have admissible {u : Fin I.graph.n} {ts : List (Traversal I.graph)}
      (tour : Feasible I u ts) (len : ts.length ≤ 2 * I.graph.q) :
      encode u ts len ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [decode_encode] using tour⟩
  have nonempty : candidates.Nonempty := by
    obtain ⟨u, ts, tour⟩ := feasible
    obtain ⟨v, ss, shorter, len, _⟩ := bounded u ts tour
    exact ⟨encode v ss len, admissible shorter len⟩
  obtain ⟨s, selected, minimum⟩ :=
    Finset.exists_min_image candidates (fun s => pathCost I.graph (decode s)) nonempty
  have tour : Feasible I s.1 (decode s) := (Finset.mem_filter.mp selected).2
  refine ⟨s.1, decode s, tour, ?_⟩
  apply le_antisymm _ (optimum_le_feasible nonnegative tour)
  refine le_csInf ⟨pathCost I.graph (decode s), s.1, decode s, tour, rfl⟩ ?_
  rintro _ ⟨u, ts, comparison, rfl⟩
  obtain ⟨v, ss, shorter, len, cheaper⟩ := bounded u ts comparison
  have least := minimum (encode v ss len) (admissible shorter len)
  exact least.trans (by simpa only [decode_encode] using cheaper)

private theorem tour_support_connected {G : Network} {u v : Fin G.n}
    {ts : List (Traversal G)} (path : IsPath G u ts v) :
    EdgeSupportConnected G (ts.map Prod.fst) := by
  have reaches (w : Fin G.n) (support : EdgeSupport G (ts.map Prod.fst) w) :
      Relation.ReflTransGen (EdgeAdjacent G (ts.map Prod.fst)) u w := by
    obtain ⟨e, used, incident⟩ := support
    obtain ⟨t, visited, rfl⟩ := List.mem_map.mp used
    obtain ⟨atStart, atFinish⟩ :=
      reaches_traversal_endpoints path (fun _ ht => List.mem_map_of_mem ht) t visited
    cases direction : t.2 <;> rcases incident with rfl | rfl
    · simpa [finish, direction] using atFinish
    · simpa [start, direction] using atStart
    · simpa [start, direction] using atStart
    · simpa [finish, direction] using atFinish
  exact fun a ha b hb => (edgeReachable_comm (reaches a ha)).trans (reaches b hb)

private theorem bounded_feasible_tour {I : Service} (rural : Rural I)
    {u : Fin I.graph.n} {ts : List (Traversal I.graph)} (tour : Feasible I u ts) :
    ∃ v ss, Feasible I v ss ∧ ss.length ≤ 2 * I.graph.q ∧
      pathCost I.graph ss ≤ pathCost I.graph ts := by
  obtain ⟨rs, sublist, support, bounded, parity⟩ :=
    reduce_link_multiplicities (ts.map Prod.fst)
  have sameSupport (v : Fin I.graph.n) :
      EdgeSupport I.graph rs v ↔ EdgeSupport I.graph (ts.map Prod.fst) v := by
    simp only [EdgeSupport, support]
  have takesStep (a b : Fin I.graph.n) (adjacent : EdgeAdjacent I.graph (ts.map Prod.fst) a b) :
      EdgeAdjacent I.graph rs a b := by
    obtain ⟨e, used, orientation⟩ := adjacent
    exact ⟨e, (support e).mpr used, orientation⟩
  have connected : EdgeSupportConnected I.graph rs := fun a ha b hb =>
    Relation.ReflTransGen.mono takesStep _ _ (tour_support_connected tour.1 a
      ((sameSupport a).mp ha) b ((sameSupport b).mp hb))
  obtain ⟨v, ss, path, permutation⟩ := exists_euler_circuit rural.1.1 rural.2.2.1
    (fun v => (parity v).trans (degree_closedPath_mod_two tour.1 v))
    connected
  have len : ss.length ≤ 2 * I.graph.q := calc
    ss.length = rs.length := by simpa only [List.length_map] using permutation.length_eq
    _ ≤ _ := length_le_twice_links bounded
  have cost : pathCost I.graph ss ≤ pathCost I.graph ts := by
    rw [pathCost_eq_linkListCost ss, pathCost_eq_linkListCost ts, linkListCost_perm permutation]
    exact (sublist.map I.graph.weight).sum_le_sum (fun _ member => (List.mem_map.mp member).elim
      (fun e entry => entry.2 ▸ rural.2.1 e))
  refine ⟨v, ss, ⟨path, by simp [rural.2.2.2], fun e required => ?_⟩, len, cost⟩
  obtain ⟨t, visited, same⟩ := tour.2.2 e required
  exact List.mem_map.mp (permutation.mem_iff.mpr
    ((support e).mpr (List.mem_map.mpr ⟨t, visited, same⟩)))

/-- An optimum rural tour exists by reducing each link multiplicity to at most two. -/
theorem exists_rural_optimum {I : Service} (rural : Rural I) :
    ∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I :=
  least_cost_of_bounded_tours rural.2.1
    (fun _ _ => bounded_feasible_tour rural)
    (exists_rural_feasible rural)

end VehicleRoutingSurvey.Routing
end RppSource_OptimumAttainment

/-! runtime/ShortestPath.lean -/
section RppSource_ShortestPath
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Every visited vertex begins a suffix of the walk, also at the vertex-list level. -/
theorem path_suffix_of_vertex_mem {u v x : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) (seen : x ∈ u :: ts.map (finish G)) :
    ∃ ss, ss <:+ ts ∧ IsPath G x ss v ∧
      (x :: ss.map (finish G)) <:+ (u :: ts.map (finish G)) := by
  induction ts generalizing u with
  | nil =>
    have eq : x = u := List.mem_singleton.mp seen
    subst x
    exact ⟨[], ⟨[], rfl⟩, path, ⟨[], rfl⟩⟩
  | cons t ts ih =>
    rw [List.mem_cons] at seen
    rcases seen with rfl | seen
    · exact ⟨t :: ts, ⟨[], rfl⟩, path, ⟨[], rfl⟩⟩
    · obtain ⟨ss, hss, walk, hvertices⟩ :=
        ih path.2.2 (by simpa only [List.map_cons] using seen)
      exact ⟨ss, hss.trans ⟨[t], rfl⟩, walk,
        hvertices.trans ⟨[u], rfl⟩⟩

/-- Remove cycles by deleting traversals, without changing either endpoint. -/
theorem exists_simple_subpath {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) :
    ∃ ss, ss.Sublist ts ∧ IsPath G u ss v ∧ (u :: ss.map (finish G)).Nodup := by
  induction ts generalizing u with
  | nil => exact ⟨[], List.Sublist.refl [], path, by simp⟩
  | cons t ts ih =>
    obtain ⟨ss, sub, walk, unique⟩ := ih path.2.2
    by_cases visits : u ∈ finish G t :: ss.map (finish G)
    · obtain ⟨tail, suffix, walkTail, vertices⟩ := path_suffix_of_vertex_mem walk visits
      exact ⟨tail, suffix.sublist.trans (sub.trans (List.sublist_cons_self t ts)),
        walkTail, List.Nodup.sublist vertices.sublist unique⟩
    · exact ⟨t :: ss, sub.cons_cons t, ⟨path.1, path.2.1, walk⟩,
        List.nodup_cons.mpr ⟨visits, unique⟩⟩

private theorem length_lt_of_simple {u : Fin G.n} {ts : List (Traversal G)}
    (simple : (u :: ts.map (finish G)).Nodup) : ts.length < G.n := by
  exact Nat.lt_of_succ_le (by simpa using simple.length_le_card)

/-- Nonnegative connected networks have shortest walks with no repeated vertex.
In particular, witnesses need fewer traversals than vertices, even at zero-weight ties. -/
theorem exists_shortest_path (connected : Connected G) (nonnegative : Nonnegative G)
    (u v : Fin G.n) :
    ∃ ts, ShortestPath G u v ts ∧ ts.length < G.n ∧ (u :: ts.map (finish G)).Nodup := by
  classical
  let Code := Σ k : Fin G.n, Fin k.val → Traversal G
  let decode (p : Code) := List.ofFn p.2
  let valid := (Finset.univ : Finset Code).filter
    (fun p => IsPath G u (decode p) v ∧ (u :: (decode p).map (finish G)).Nodup)
  have encode (ts : List (Traversal G)) (path : IsPath G u ts v) :
      ∃ p ∈ valid, pathCost G (decode p) ≤ pathCost G ts := by
    obtain ⟨ss, inclusion, walk, simple⟩ := exists_simple_subpath path
    let k : Fin G.n := ⟨ss.length, length_lt_of_simple simple⟩
    let p : Code := ⟨k, ss.get⟩
    have exactDecode : decode p = ss := List.ofFn_get ss
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [exactDecode]
      exact ⟨walk, simple⟩
    · rw [exactDecode]
      exact pathCost_mono_sublist nonnegative inclusion
  obtain ⟨ts, path⟩ := connected.2 u v
  obtain ⟨p, member, _⟩ := encode ts path
  obtain ⟨best, bestMem, bestCost⟩ :=
    Finset.exists_min_image valid (fun p => pathCost G (decode p)) ⟨p, member⟩
  have bestOK := (Finset.mem_filter.mp bestMem).2
  refine ⟨decode best, ⟨bestOK.1, ?_⟩, length_lt_of_simple bestOK.2, bestOK.2⟩
  intro zs walk
  obtain ⟨other, otherMem, otherCost⟩ := encode zs walk
  exact (bestCost other otherMem).trans otherCost

private theorem start_mem_visited_of_traversal_mem {u v : Fin G.n}
    {ts : List (Traversal G)} {t : Traversal G}
    (path : IsPath G u ts v) (seen : t ∈ ts) :
    start G t ∈ u :: ts.map (finish G) := by
  induction ts generalizing u with
  | nil => cases seen
  | cons e ts ih =>
    rcases List.mem_cons.mp seen with rfl | tail
    · exact List.mem_cons.mpr (Or.inl path.1.symm)
    · exact List.mem_cons_of_mem _ (ih path.2.2 tail)

/-- A walk with no repeated vertex uses each link at most once, even in a multigraph. -/
theorem simple_path_link_ids_nodup {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) (simple : (u :: ts.map (finish G)).Nodup) :
    (ts.map Prod.fst).Nodup := by
  induction ts generalizing u with
  | nil => exact List.nodup_nil
  | cons t ts ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp simple
    apply List.nodup_cons.mpr
    refine ⟨?_, ih path.2.2 tail⟩
    intro repeatLink
    obtain ⟨other, occurs, linkEq⟩ := List.mem_map.mp repeatLink
    have startSeen := start_mem_visited_of_traversal_mem path.2.2 occurs
    have finishSeen : finish G other ∈ finish G t :: ts.map (finish G) :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem occurs)
    have both : u = start G other ∨ u = finish G other := by
      rw [path.1]
      cases dt : t.2 <;> cases dother : other.2 <;>
        simp [start, finish, dt, dother, linkEq]
    exact fresh (both.elim (fun eq => eq.symm ▸ startSeen) (fun eq => eq.symm ▸ finishSeen))

/-- One plus the sum of input weights is a strict finite sentinel for shortest distances. -/
theorem distance_lt_weight_sentinel (connected : Connected G) (nonnegative : Nonnegative G)
    (u v : Fin G.n) : distance G u v < 1 + ∑ e, G.weight e := by
  classical
  obtain ⟨ts, shortest, _, simple⟩ := exists_shortest_path connected nonnegative u v
  have linkIds := simple_path_link_ids_nodup shortest.1 simple
  have cost_eq : pathCost G ts = ∑ e ∈ (ts.map Prod.fst).toFinset, G.weight e := by
    simpa [pathCost, List.map_map, Function.comp_def] using
      (List.sum_toFinset G.weight linkIds).symm
  have bounded : distance G u v ≤ ∑ e, G.weight e := by
    rw [distance_eq_of_shortestPath shortest, cost_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => nonnegative e)
  exact bounded.trans_lt (lt_add_of_pos_left _ zero_lt_one)

end VehicleRoutingSurvey.Routing
end RppSource_ShortestPath

/-! runtime/ExpansionSize.lean -/
section RppSource_ExpansionSize
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- A list of endpoint pairs admits shortest expansions whose individual
lengths are bounded by the number of vertices. -/
theorem exists_bounded_expands (connected : Connected G) (nonnegative : Nonnegative G)
    (pairs : List (Fin G.n × Fin G.n)) :
    ∃ paths, Expands G pairs paths ∧ ∀ ts ∈ paths, ts.length < G.n := by
  induction pairs with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons p pairs ih =>
    obtain ⟨ts, shortest, length, _⟩ := exists_shortest_path connected nonnegative p.1 p.2
    obtain ⟨other, expands, bounded⟩ := ih
    exact ⟨ts :: other, .cons shortest expands, fun ss member =>
      (List.mem_cons.mp member).elim (fun h => h ▸ length) (bounded ss)⟩

theorem expands_traversal_count_le {pairs : List (Fin G.n × Fin G.n)}
    {paths : List (List (Traversal G))} (expands : Expands G pairs paths)
    (bounded : ∀ ts ∈ paths, ts.length < G.n) :
    paths.flatten.length ≤ pairs.length * G.n := by
  rw [List.Forall₂.length_eq expands]
  clear expands
  induction paths with
  | nil => simp
  | cons ts paths ih =>
    have head := bounded ts List.mem_cons_self
    have tail := ih (fun ss seen => bounded ss (List.mem_cons_of_mem _ seen))
    simpa [List.flatten_cons, Nat.succ_mul, Nat.add_comm] using add_le_add head.le tail

theorem componentTree_length_lt {I : Service}
    {tree : List (Fin I.graph.n × Fin I.graph.n)} (h : ComponentTree I tree) :
    tree.length < I.graph.n := by
  obtain ⟨cs, reps, length⟩ := h.1
  have unique : cs.Nodup := reps.2.1.imp (fun different same => by
    cases same
    exact different .refl)
  exact Nat.lt_of_succ_le (by simpa [← length] using unique.length_le_card)

theorem minimumMatching_length_le_square {es : List (Fin G.q)}
    {matching : List (Fin G.n × Fin G.n)} (h : MinimumMatching G es matching) :
    matching.length ≤ G.n ^ 2 := by
  have unique : matching.Nodup := List.Nodup.of_map _ h.1
  simpa [Fintype.card_prod, pow_two] using unique.length_le_card

/-- Bounded shortest-path witnesses also bound the Euler output length. -/
theorem expanded_traversal_count_le {I : Service} {base : List (Fin I.graph.q)}
    {tree matching : List (Fin I.graph.n × Fin I.graph.n)}
    {tp mp : List (List (Traversal I.graph))} {ts : List (Traversal I.graph)}
    (baseUnique : base.Nodup) (treeOK : ComponentTree I tree)
    (treePaths : Expands I.graph tree tp) (treeBound : ∀ walk ∈ tp, walk.length < I.graph.n)
    (matchOK : MinimumMatching I.graph (base ++ tp.flatten.map Prod.fst) matching)
    (matchPaths : Expands I.graph matching mp) (matchBound : ∀ walk ∈ mp, walk.length < I.graph.n)
    (tour : (ts.map Prod.fst).Perm (base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst)) :
    ts.length ≤ I.graph.q + I.graph.n ^ 2 + I.graph.n ^ 3 := by
  have baseLen : base.length ≤ I.graph.q := by simpa using baseUnique.length_le_card
  have treeLen : tp.flatten.length ≤ I.graph.n ^ 2 :=
    (expands_traversal_count_le treePaths treeBound).trans (by
      simpa [pow_two] using Nat.mul_le_mul_right I.graph.n (componentTree_length_lt treeOK).le)
  have matchLen : mp.flatten.length ≤ I.graph.n ^ 3 :=
    (expands_traversal_count_le matchPaths matchBound).trans (by
      simpa [pow_succ] using Nat.mul_le_mul_right I.graph.n (minimumMatching_length_le_square matchOK))
  have count : ts.length = base.length + tp.flatten.length + mp.flatten.length := by
    simpa only [List.length_map, List.length_append, Nat.add_assoc] using tour.length_eq
  rw [count]
  exact Nat.add_le_add (Nat.add_le_add baseLen treeLen) matchLen

theorem tourCode_length (u : Fin G.n) (ts : List (Traversal G)) :
    (tourCode G u ts).length = 1 + 2 * ts.length := by
  simp [tourCode, Nat.mul_comm]
  omega

theorem tourCode_size_le_cubic (positive : 0 < G.n) (u : Fin G.n) (ts : List (Traversal G))
    (bounded : ts.length ≤ G.q + G.n ^ 2 + G.n ^ 3) :
    (tourCode G u ts).length ≤ 5 * (G.n ^ 3 + G.q) := by
  rw [tourCode_length]
  have square : G.n ^ 2 ≤ G.n ^ 3 := by
    calc
      G.n ^ 2 = G.n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ G.n ^ 2 * G.n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt positive)
      _ = G.n ^ 3 := (pow_succ _ 2).symm
  have cube : 0 < G.n ^ 3 := pow_pos positive _
  omega

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionSize

/-! ConnectorCosts.lean -/
section RppSource_ConnectorCosts
namespace VehicleRoutingSurvey.Routing

variable {I : Service}

def requiredTraversals (I : Service) (ts : List (Traversal I.graph)) : List (Traversal I.graph) :=
  ts.filter (fun t => decide (t.1 ∈ I.links))

def connectorTraversals (I : Service) (ts : List (Traversal I.graph)) : List (Traversal I.graph) :=
  ts.filter (fun t => !decide (t.1 ∈ I.links))

theorem pathCost_required_add_connector (ts : List (Traversal I.graph)) :
    pathCost I.graph ts = pathCost I.graph (requiredTraversals I ts) +
      pathCost I.graph (connectorTraversals I ts) :=
  calc
    _ = pathCost I.graph (requiredTraversals I ts ++ connectorTraversals I ts) :=
      ((List.filter_append_perm (fun t : Traversal I.graph => decide (t.1 ∈ I.links)) ts).symm.map
        (fun t : Traversal I.graph => I.graph.weight t.1)).sum_eq
    _ = _ := pathCost_append (G := I.graph) (requiredTraversals I ts) (connectorTraversals I ts)

private theorem dedup_requiredTraversals_covers {u : Fin I.graph.n} {ts : List (Traversal I.graph)}
    (feasible : Feasible I u ts) :
    ((requiredTraversals I ts).map Prod.fst).dedup.toFinset = I.links := by
  ext e
  simp only [List.mem_toFinset, List.mem_dedup, List.mem_map, requiredTraversals,
    List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨_, inList, equal⟩ => equal ▸ inList.2,
    fun required => (feasible.2.2 e required).elim fun t ht => ⟨t, ⟨ht.1, ht.2.symm ▸ required⟩, ht.2⟩⟩

/-- Reserve one occurrence of each required link before charging any connector paths. -/
theorem requiredCost_le_requiredTraversals {u : Fin I.graph.n} {ts : List (Traversal I.graph)}
    (nonnegative : Nonnegative I.graph) (feasible : Feasible I u ts) :
    requiredCost I ≤ pathCost I.graph (requiredTraversals I ts) := by
  rw [← linkListCost_required (List.nodup_dedup _) (dedup_requiredTraversals_covers feasible),
    pathCost_eq_linkListCost]
  exact ((List.dedup_sublist _).map I.graph.weight).sum_le_sum
    (fun _ member => (List.mem_map.mp member).elim fun edge h => h.2 ▸ nonnegative edge)

end VehicleRoutingSurvey.Routing
end RppSource_ConnectorCosts

/-! ComparisonConnectors.lean -/
section RppSource_ComparisonConnectors
namespace VehicleRoutingSurvey.Routing

variable {I : Service} {G : Network}

abbrev VertexPair (G : Network) := Fin G.n × Fin G.n

def componentJoin (I : Service) (pairs : List (VertexPair I.graph)) (u v : Fin I.graph.n) : Prop :=
  requiredAdjacent I u v ∨ (u, v) ∈ pairs ∨ (v, u) ∈ pairs

theorem componentJoin_comm {pairs : List (VertexPair I.graph)} {u v : Fin I.graph.n} :
    componentJoin I pairs u v → componentJoin I pairs v u :=
  fun h => h.elim (Or.inl ∘ requiredAdjacent_comm) (Or.inr ∘ Or.symm)

private theorem isPath_split_append {u v : Fin G.n} {xs ys : List (Traversal G)}
    (path : IsPath G u (xs ++ ys) v) : ∃ w, IsPath G u xs w ∧ IsPath G w ys v := by
  induction xs generalizing u with
  | nil => exact ⟨u, rfl, path⟩
  | cons t rest ih =>
    obtain ⟨w, first, second⟩ := ih path.2.2
    exact ⟨w, ⟨path.1, path.2.1, first⟩, second⟩

private theorem exists_first_required_split (ts : List (Traversal I.graph))
    (hit : ∃ t ∈ ts, t.1 ∈ I.links) :
    ∃ (before : List (Traversal I.graph)) (t : Traversal I.graph) (rest : List (Traversal I.graph)),
      ts = before ++ t :: rest ∧ (∀ d ∈ before, d.1 ∉ I.links) ∧ t.1 ∈ I.links := by
  induction ts with
  | nil => simp at hit
  | cons d ts ih =>
    by_cases required : d.1 ∈ I.links
    · exact ⟨[], d, ts, rfl, by simp, required⟩
    · have next : ∃ t ∈ ts, t.1 ∈ I.links := by
        obtain ⟨t, present, serves⟩ := hit
        exact ⟨t, (List.mem_cons.mp present).resolve_left (fun eq => required (eq ▸ serves)), serves⟩
      obtain ⟨before, t, rest, split, noService, serves⟩ := ih next
      exact ⟨d :: before, t, rest, congrArg (List.cons d) split,
        fun e mem => (List.mem_cons.mp mem).elim (fun eq => eq.symm ▸ required) (noService e), serves⟩

private theorem connectorTraversals_split {before rest : List (Traversal I.graph)}
    {t : Traversal I.graph} (noService : ∀ d ∈ before, d.1 ∉ I.links) (serves : t.1 ∈ I.links) :
    connectorTraversals I (before ++ t :: rest) = before ++ connectorTraversals I rest := by
  have beforeFiltered : connectorTraversals I before = before :=
    List.filter_eq_self.mpr fun d mem => by simp [noService d mem]
  unfold connectorTraversals at *
  rw [List.filter_append, beforeFiltered]
  simp [serves]

private theorem componentJoin_mono {pairs larger : List (VertexPair I.graph)}
    (included : pairs ⊆ larger) : componentJoin I pairs ≤ componentJoin I larger :=
  fun _ _ h => h.elim Or.inl (fun edge => .inr (edge.imp (fun mem => included mem) (fun mem => included mem)))

/-- Each gap before a required traversal contributes one link between required vertices.
The rest of the comparison path supplies the subsequent links, with disjoint cost. -/
private theorem collect_component_pairs (ts : List (Traversal I.graph)) (u v : Fin I.graph.n)
    (nonnegative : Nonnegative I.graph) (anchor : u ∈ requiredVertices I)
    (path : IsPath I.graph u ts v) :
    ∃ pairs : List (VertexPair I.graph),
      (∀ p ∈ pairs, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I) ∧
      pairCost I.graph pairs ≤ pathCost I.graph (connectorTraversals I ts) ∧
      ∀ t ∈ ts, t.1 ∈ I.links →
        Relation.ReflTransGen (componentJoin I pairs) u (start I.graph t) ∧
        Relation.ReflTransGen (componentJoin I pairs) u (finish I.graph t) := by
  by_cases hit : ∃ t ∈ ts, t.1 ∈ I.links
  · obtain ⟨before, t, rest, split, noService, required⟩ := exists_first_required_split ts hit
    obtain ⟨w, entrance, after⟩ := isPath_split_append (split ▸ path)
    have toStart : IsPath I.graph u before (start I.graph t) := after.1 ▸ entrance
    have adjacent := requiredAdjacent_of_traversal t required
    obtain ⟨atStart, atEnd⟩ := requiredAdjacent_mem_requiredVertices adjacent
    obtain ⟨pairs, inside, cost, connected⟩ :=
      collect_component_pairs rest (finish I.graph t) v nonnegative atEnd after.2.2
    let link : VertexPair I.graph := (u, start I.graph t)
    refine ⟨link :: pairs, ?_, ?_, ?_⟩
    · intro p present
      exact (List.mem_cons.mp present).elim (fun eq => eq.symm ▸ And.intro anchor atStart) (inside p)
    · calc
        pairCost I.graph (link :: pairs) = distance I.graph u (start I.graph t) +
            pairCost I.graph pairs := rfl
        _ ≤ pathCost I.graph before + pathCost I.graph (connectorTraversals I rest) :=
          add_le_add (distance_le_pathCost nonnegative toStart) cost
        _ = _ := by rw [split, connectorTraversals_split noService required, pathCost_append]
    · have reachesStart : Relation.ReflTransGen (componentJoin I (link :: pairs)) u (start I.graph t) :=
        .single (.inr (.inl List.mem_cons_self))
      have reachesEnd := reachesStart.tail (.inl adjacent)
      intro s member served
      have atOrAfter := (List.mem_append.mp (split ▸ member)).resolve_left (fun h => noService s h served)
      rcases List.mem_cons.mp atOrAfter with rfl | later
      · exact ⟨reachesStart, reachesEnd⟩
      · obtain ⟨restStart, restEnd⟩ := connected s later served
        have incl : componentJoin I pairs ≤ componentJoin I (link :: pairs) :=
          componentJoin_mono (fun _ => List.mem_cons_of_mem _)
        exact ⟨reachesEnd.trans (Relation.ReflTransGen.mono incl _ _ restStart),
          reachesEnd.trans (Relation.ReflTransGen.mono incl _ _ restEnd)⟩
  · exact ⟨[], by simp, pathCost_nonnegative nonnegative _, fun t h r => (hit ⟨t, h, r⟩).elim⟩
termination_by ts.length
decreasing_by
  rw [split, List.length_append, List.length_cons]
  omega

noncomputable def interComponentPairs (I : Service) (pairs : List (VertexPair I.graph)) :
    List (VertexPair I.graph) := by
  classical
  exact pairs.filter (fun p => !decide (sameComponent I p.1 p.2))

theorem mem_interComponentPairs {pairs : List (VertexPair I.graph)} {p : VertexPair I.graph} :
    p ∈ interComponentPairs I pairs ↔ p ∈ pairs ∧ ¬sameComponent I p.1 p.2 := by
  classical
  simp [interComponentPairs]

theorem pairCost_mono_sublist (connected : Connected G) (nonnegative : Nonnegative G)
    {ps qs : List (VertexPair G)} (included : ps.Sublist qs) : pairCost G ps ≤ pairCost G qs :=
  (included.map (fun p => distance G p.1 p.2)).sum_le_sum fun _ mem =>
    (List.mem_map.mp mem).elim fun p h => h.2 ▸ distance_nonnegative connected nonnegative p.1 p.2

private theorem interComponentPairs_reaches {pairs : List (VertexPair I.graph)} {u v : Fin I.graph.n}
    (path : Relation.ReflTransGen (componentJoin I pairs) u v) :
    Relation.ReflTransGen (componentJoin I (interComponentPairs I pairs)) u v := by
  let _ : Std.Symm (componentJoin I (interComponentPairs I pairs)) := ⟨fun _ _ => componentJoin_comm⟩
  have forward (x y : Fin I.graph.n) (member : (x, y) ∈ pairs) :
      Relation.ReflTransGen (componentJoin I (interComponentPairs I pairs)) x y := by
    by_cases same : sameComponent I x y
    · exact Relation.ReflTransGen.mono (fun _ _ => Or.inl) _ _ same
    · exact .single (.inr (.inl (mem_interComponentPairs.mpr ⟨member, same⟩)))
  induction path with
  | refl => exact .refl
  | tail _ step ih =>
    rcases step with required | edge | reverse
    · exact ih.tail (.inl required)
    · exact ih.trans (forward _ _ edge)
    · exact ih.trans (@Std.Symm.symm _ _ Relation.ReflTransGen.stdSymm _ _ (forward _ _ reverse))

private theorem required_vertex_is_served_endpoint {u v : Fin I.graph.n} {ts : List (Traversal I.graph)}
    (tour : Feasible I u ts) (required : v ∈ requiredVertices I) :
    ∃ t ∈ ts, t.1 ∈ I.links ∧ (start I.graph t = v ∨ finish I.graph t = v) := by
  have edgeExists : ∃ e ∈ I.links, I.graph.tail e = v ∨ I.graph.head e = v := by
    rcases Finset.mem_union.mp required with tail | head
    · obtain ⟨e, serves, same⟩ := Finset.mem_image.mp tail
      exact ⟨e, serves, .inl same⟩
    · obtain ⟨e, serves, same⟩ := Finset.mem_image.mp head
      exact ⟨e, serves, .inr same⟩
  obtain ⟨e, serves, endpoint⟩ := edgeExists
  obtain ⟨t, hit, edge⟩ := tour.2.2 e serves
  refine ⟨t, hit, edge.symm ▸ serves, ?_⟩
  cases direction : t.2
  · simpa [start, finish, direction, edge, or_comm] using endpoint
  · simpa [start, finish, direction, edge] using endpoint

/-- Compress a comparison tour between consecutive visits to required links.
The resulting connections span the required components and charge only travel
along nonrequired traversals. Component distances need no triangle inequality. -/
theorem exists_comparison_pairs {u : Fin I.graph.n} {ts : List (Traversal I.graph)}
    (connected : Connected I.graph) (nonnegative : Nonnegative I.graph)
    (hasRequired : I.links.Nonempty) (tour : Feasible I u ts) :
    ∃ pairs : List (VertexPair I.graph),
      (∀ p ∈ pairs, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2) ∧
      (∀ x ∈ requiredVertices I, ∀ y ∈ requiredVertices I,
        Relation.ReflTransGen (componentJoin I pairs) x y) ∧
      pairCost I.graph pairs ≤ pathCost I.graph (connectorTraversals I ts) := by
  obtain ⟨e, serves⟩ := hasRequired
  obtain ⟨t, present, edge⟩ := tour.2.2 e serves
  obtain ⟨before, first, rest, split, noService, firstRequired⟩ :=
    exists_first_required_split ts ⟨t, present, edge.symm ▸ serves⟩
  obtain ⟨v, _, after⟩ := isPath_split_append (split ▸ tour.1)
  let root := start I.graph first
  have rootIncluded := (requiredAdjacent_mem_requiredVertices
    (requiredAdjacent_of_traversal first firstRequired)).1
  have usefulPath : IsPath I.graph root (first :: rest) u := by
    change IsPath I.graph (start I.graph first) (first :: rest) u
    exact after.1 ▸ after
  obtain ⟨pairs, inside, cost, reachable⟩ := collect_component_pairs (first :: rest) root u
    nonnegative rootIncluded usefulPath
  let output := interComponentPairs I pairs
  have connectedToRoot (x : Fin I.graph.n) (hx : x ∈ requiredVertices I) :
      Relation.ReflTransGen (componentJoin I output) root x := by
    obtain ⟨w, wIn, wRequired, isEndpoint⟩ := required_vertex_is_served_endpoint tour hx
    have valid := (List.mem_append.mp (split ▸ wIn)).resolve_left (fun h => noService w h wRequired)
    obtain ⟨atStart, atEnd⟩ := reachable w valid wRequired
    exact isEndpoint.elim (fun eq => eq ▸ interComponentPairs_reaches atStart)
      (fun eq => eq ▸ interComponentPairs_reaches atEnd)
  refine ⟨output, ?_, ?_, ?_⟩
  · intro p mem
    have both := mem_interComponentPairs.mp mem
    exact ⟨(inside p both.1).1, (inside p both.1).2, both.2⟩
  · intro x hx y hy
    let _ : Std.Symm (componentJoin I output) := ⟨fun _ _ => componentJoin_comm⟩
    exact (@Std.Symm.symm _ _ Relation.ReflTransGen.stdSymm _ _ (connectedToRoot x hx)).trans
      (connectedToRoot y hy)
  · have kept : output.Sublist pairs := by
      unfold output interComponentPairs
      exact List.filter_sublist
    have suffix : (first :: rest).Sublist ts := split.symm ▸ List.sublist_append_right before _
    exact (pairCost_mono_sublist connected nonnegative kept).trans (cost.trans
      (pathCost_mono_sublist nonnegative (suffix.filter _)))

end VehicleRoutingSurvey.Routing
end RppSource_ComparisonConnectors

/-! runtime/GreedyComponentTree.lean -/
section RppSource_GreedyComponentTree
namespace VehicleRoutingSurvey.Routing

/-- A crossing edge can replace a crossing edge of a connected graph.
The final union keeps the added edge when it has the same endpoints as
the removed edge. -/
theorem exists_crossing_connected_swap {V : Type*} {G : SimpleGraph V}
    (connected : G.Connected) (cut : Set V) {x y : V}
    (inside : x ∈ cut) (outside : y ∉ cut) :
    ∃ a ∈ cut, ∃ b ∉ cut, G.Adj a b ∧
      (((G ⊔ SimpleGraph.edge x y).deleteEdges {s(a, b)}) ⊔ SimpleGraph.edge x y).Connected := by
  classical
  let added := SimpleGraph.edge x y
  let augmented := G ⊔ added
  have distinct : x ≠ y := fun same => outside (same ▸ inside)
  have addedAdj : added.Adj x y :=
    (SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, distinct⟩
  by_cases existing : G.Adj x y
  · refine ⟨x, inside, y, outside, existing, connected.mono ?_⟩
    intro u v old
    by_cases removed : s(u, v) = s(x, y)
    · exact Or.inr ((SimpleGraph.adj_edge x y).mpr ⟨removed.symm, old.ne⟩)
    · exact Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨Or.inl old,
        fun inSet => removed (Set.mem_singleton_iff.mp inSet)⟩)
  · obtain ⟨path, simple⟩ := connected.exists_isPath x y
    obtain ⟨dart, onPath, sourceSide, targetSide⟩ := path.exists_boundary_dart cut inside outside
    let lifted := path.mapLe (show G ≤ augmented from le_sup_left)
    have liftedSimple : lifted.IsPath := simple.mapLe _
    have absent : s(y, x) ∉ lifted.edges := by
      intro used
      rw [show lifted.edges = path.edges from path.edges_mapLe_eq_edges _] at used
      exact existing (path.adj_of_mem_edges used).symm
    have closes : augmented.Adj y x := Or.inr addedAdj.symm
    have cycle := SimpleGraph.Path.cons_isCycle ⟨lifted, liftedSimple⟩ closes absent
    have onCycle : dart.edge ∈ (SimpleGraph.Walk.cons closes lifted).edges := by
      have original : dart.edge ∈ path.edges := List.mem_map_of_mem onPath
      have liftedMember : dart.edge ∈ lifted.edges :=
        (path.edges_mapLe_eq_edges _).symm ▸ original
      exact List.mem_cons_of_mem _ liftedMember
    have removable : ¬ augmented.IsBridge s(dart.fst, dart.snd) := by
      intro bridge
      exact bridge.notMem_edges_of_isCycle cycle onCycle
    refine ⟨dart.fst, sourceSide, dart.snd, targetSide, dart.adj, ?_⟩
    have augmentedConnected := connected.mono (show G ≤ augmented from le_sup_left)
    exact (augmentedConnected.connected_delete_edge_of_not_isBridge removable).mono le_sup_left

end VehicleRoutingSurvey.Routing
end RppSource_GreedyComponentTree

/-! sharpness/ComponentTreeExtraction.lean -/
section RppSource_ComponentTreeExtraction
namespace VehicleRoutingSurvey.Routing

private abbrev ActiveComponent (I : Service) := ↥(activeRequiredComponents I)

private abbrev EndpointPair (I : Service) := Fin I.graph.n × Fin I.graph.n

private abbrev ComponentStep (I : Service) (ps : List (EndpointPair I))
    (u v : Fin I.graph.n) : Prop :=
  requiredAdjacent I u v ∨ (u, v) ∈ ps ∨ (v, u) ∈ ps

/-- A total quotient projection, whose fallback is never used on the required support. -/
private noncomputable def componentOf {I : Service} (fallback : ActiveComponent I)
    (u : Fin I.graph.n) : ActiveComponent I := by
  classical
  exact if member : u ∈ requiredVertices I then
    ⟨requiredComponent I u, Finset.mem_image_of_mem _ member⟩
  else fallback

private theorem componentOf_val {I : Service} (fallback : ActiveComponent I) {u : Fin I.graph.n}
    (member : u ∈ requiredVertices I) : (componentOf fallback u).val = requiredComponent I u := by
  simp [componentOf, member]

private theorem componentOf_eq_iff {I : Service} (fallback : ActiveComponent I) {u v : Fin I.graph.n}
    (hu : u ∈ requiredVertices I) (hv : v ∈ requiredVertices I) :
    componentOf fallback u = componentOf fallback v ↔ sameComponent I u v :=
  Subtype.ext_iff.trans (by rw [componentOf_val fallback hu, componentOf_val fallback hv,
    requiredComponent_eq_iff])

private noncomputable def componentEdge {I : Service} (fallback : ActiveComponent I)
    (p : EndpointPair I) : Sym2 (ActiveComponent I) := s(componentOf fallback p.1, componentOf fallback p.2)

private def componentGraph {I : Service} (fallback : ActiveComponent I)
    (ps : List (EndpointPair I)) : SimpleGraph (ActiveComponent I) where
  Adj c d := c ≠ d ∧ ∃ p ∈ ps, componentEdge fallback p = s(c, d)
  symm := ⟨fun _ _ ⟨distinct, p, present, endpoints⟩ =>
    ⟨distinct.symm, p, present, endpoints.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem componentStep_project {I : Service} (fallback : ActiveComponent I)
    {ps : List (EndpointPair I)}
    (valid : ∀ p ∈ ps, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2)
    {u v : Fin I.graph.n} (step : ComponentStep I ps u v) :
    (componentGraph fallback ps).Reachable (componentOf fallback u) (componentOf fallback v) := by
  rcases step with required | forward | backward
  · have support := requiredAdjacent_mem_requiredVertices required
    exact ((componentOf_eq_iff fallback support.1 support.2).mpr
      (Relation.ReflTransGen.single required)).symm ▸ SimpleGraph.Reachable.refl _
  · obtain ⟨hu, hv, distinct⟩ := valid (u, v) forward
    exact SimpleGraph.Adj.reachable ⟨(componentOf_eq_iff fallback hu hv).not.mpr distinct, _, forward, rfl⟩
  · obtain ⟨hv, hu, distinct⟩ := valid (v, u) backward
    exact SimpleGraph.Reachable.symm (SimpleGraph.Adj.reachable
      ⟨(componentOf_eq_iff fallback hv hu).not.mpr distinct, _, backward, rfl⟩)

private theorem project_componentWalk {I : Service} (fallback : ActiveComponent I)
    {ps : List (EndpointPair I)}
    (valid : ∀ p ∈ ps, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2)
    {u v : Fin I.graph.n} (walk : Relation.ReflTransGen (ComponentStep I ps) u v) :
    (componentGraph fallback ps).Reachable (componentOf fallback u) (componentOf fallback v) := by
  induction walk with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ step ih => exact ih.trans (componentStep_project fallback valid step)

private theorem class_representative {I : Service} (fallback c : ActiveComponent I) :
    componentOf fallback (requiredRepresentative I c) = c :=
  Subtype.ext ((componentOf_val fallback (requiredRepresentative_spec c).1).trans
    (requiredRepresentative_spec c).2)

private theorem componentGraph_connected {I : Service} (fallback : ActiveComponent I)
    {ps : List (EndpointPair I)}
    (valid : ∀ p ∈ ps, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2)
    (connects : ∀ u ∈ requiredVertices I, ∀ v ∈ requiredVertices I,
      Relation.ReflTransGen (ComponentStep I ps) u v) : (componentGraph fallback ps).Connected := by
  let nonempty : Nonempty (ActiveComponent I) := ⟨fallback⟩
  exact @SimpleGraph.Connected.mk _ _ (fun u v => (class_representative fallback u) ▸ (class_representative fallback v) ▸
    project_componentWalk fallback valid (connects _ (requiredRepresentative_spec u).1 _
      (requiredRepresentative_spec v).1)) nonempty

private theorem componentWalk_within {I : Service} (fallback : ActiveComponent I)
    (qs : List (EndpointPair I)) {u v : Fin I.graph.n} {hu : u ∈ requiredVertices I}
    {hv : v ∈ requiredVertices I} (equal : componentOf fallback u = componentOf fallback v) :
    Relation.ReflTransGen (ComponentStep I qs) u v :=
  Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _
    ((componentOf_eq_iff fallback hu hv).mp equal)

private theorem lift_selectedPair {I : Service} (fallback : ActiveComponent I)
    {qs : List (EndpointPair I)} {p : EndpointPair I} (present : p ∈ qs)
    (support : p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I) {c d : ActiveComponent I}
    (profile : componentEdge fallback p = s(c, d)) :
    Relation.ReflTransGen (ComponentStep I qs) (requiredRepresentative I c) (requiredRepresentative I d) := by
  have join {x y : Fin I.graph.n} (hx : x ∈ requiredVertices I) (hy : y ∈ requiredVertices I)
      (left : componentOf fallback x = c) (right : componentOf fallback y = d)
      (across : ComponentStep I qs x y) :
      Relation.ReflTransGen (ComponentStep I qs) (requiredRepresentative I c) (requiredRepresentative I d) :=
    ((componentWalk_within fallback qs (hu := (requiredRepresentative_spec c).1) (hv := hx)
      ((class_representative fallback c).trans left.symm)).tail across).trans
      (componentWalk_within fallback qs (hu := hy) (hv := (requiredRepresentative_spec d).1)
        (right.trans (class_representative fallback d).symm))
  rcases Sym2.eq_iff.mp profile with forward | backward
  · exact join support.1 support.2 forward.1 forward.2 (Or.inr (Or.inl present))
  · exact join support.2 support.1 backward.2 backward.1 (Or.inr (Or.inr present))

private theorem lift_componentWalk {I : Service} (fallback : ActiveComponent I)
    {qs : List (EndpointPair I)} {T : SimpleGraph (ActiveComponent I)}
    (support : ∀ p ∈ qs, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I)
    (represented : ∀ c d, T.Adj c d → ∃ p ∈ qs, componentEdge fallback p = s(c, d))
    {c d : ActiveComponent I} (walk : Relation.ReflTransGen T.Adj c d) :
    Relation.ReflTransGen (ComponentStep I qs) (requiredRepresentative I c) (requiredRepresentative I d) := by
  induction walk with
  | refl => exact .refl
  | tail _ step ih =>
    obtain ⟨p, present, profile⟩ := represented _ _ step
    exact ih.trans (lift_selectedPair fallback present (support p present) profile)

/-- Select endpoint pairs forming a spanning tree on the required components.
The selected pairs retain their order in the original list. -/
theorem exists_componentTree_sublist {I : Service} (nonempty : (requiredVertices I).Nonempty)
    {ps : List (Fin I.graph.n × Fin I.graph.n)}
    (valid : ∀ p ∈ ps, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2)
    (connects : ∀ u ∈ requiredVertices I, ∀ v ∈ requiredVertices I,
      Relation.ReflTransGen (fun x y => requiredAdjacent I x y ∨ (x, y) ∈ ps ∨ (y, x) ∈ ps) u v) :
    ∃ qs, qs.Sublist ps ∧ ComponentTree I qs := by
  classical
  obtain ⟨initial, member⟩ := nonempty
  let fallback : ActiveComponent I := ⟨requiredComponent I initial, Finset.mem_image_of_mem _ member⟩
  obtain ⟨T, subgraph, tree⟩ := (componentGraph_connected fallback valid connects).exists_isTree_le
  have edgeWitness {e : Sym2 (ActiveComponent I)} (member : e ∈ T.edgeFinset) :
      ∃ p ∈ ps, componentEdge fallback p = e := by
    induction e using Sym2.inductionOn with
    | hf c d => exact (subgraph (show T.Adj c d from SimpleGraph.mem_edgeFinset.mp member)).2
  let pick (e : ↥T.edgeFinset) : EndpointPair I := (edgeWitness e.property).choose
  have pick_spec (e : ↥T.edgeFinset) : pick e ∈ ps ∧ componentEdge fallback (pick e) = e.val :=
    (edgeWitness e.property).choose_spec
  let selected : Finset (EndpointPair I) := T.edgeFinset.attach.image pick
  let qs := ps.dedup.filter (fun p => decide (p ∈ selected))
  have sublist : qs.Sublist ps := (List.filter_sublist : qs.Sublist ps.dedup).trans (List.dedup_sublist _)
  have selected_sound {p : EndpointPair I} (member : p ∈ selected) : p ∈ ps := by
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp member
    exact (pick_spec e).1
  have member_iff (p : EndpointPair I) : p ∈ qs ↔ p ∈ selected := by
    simp only [qs, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
    exact and_iff_right_of_imp selected_sound
  have nodup : qs.Nodup := (List.nodup_dedup _).filter _
  have selection : qs.toFinset = selected := Finset.ext fun p => List.mem_toFinset.trans (member_iff p)
  have injective : Function.Injective pick := fun a b equal => Subtype.ext
    ((pick_spec a).2.symm.trans ((congrArg (componentEdge fallback) equal).trans (pick_spec b).2))
  have count : qs.length + 1 = (requiredRepresentatives I).length := by
    rw [← List.toFinset_card_of_nodup nodup, selection]
    change (T.edgeFinset.attach.image pick).card + 1 = (requiredRepresentatives I).length
    rw [Finset.card_image_of_injective _ injective,
      Finset.card_attach, tree.card_edgeFinset, requiredRepresentatives_length, Fintype.card_coe]
  have witnesses (c d : ActiveComponent I) (adj : T.Adj c d) :
      ∃ p ∈ qs, componentEdge fallback p = s(c, d) := by
    let e : ↥T.edgeFinset := ⟨s(c, d), SimpleGraph.mem_edgeFinset.mpr (show s(c, d) ∈ T.edgeSet from adj)⟩
    exact ⟨pick e, (member_iff _).mpr (Finset.mem_image_of_mem pick (Finset.mem_attach T.edgeFinset e)),
      (pick_spec e).2⟩
  have eligible (p : EndpointPair I) (member : p ∈ qs) := valid p (sublist.subset member)
  refine ⟨qs, sublist, ⟨_, requiredRepresentatives_valid I, count⟩, eligible, fun u hu v hv => ?_⟩
  have walk := (T.reachable_iff_reflTransGen _ _).mp (tree.connected (componentOf fallback u)
    (componentOf fallback v))
  have middle := lift_componentWalk fallback (fun p mem => ⟨(eligible p mem).1, (eligible p mem).2.1⟩)
    witnesses walk
  exact ((componentWalk_within fallback qs (hu := hu) (hv := (requiredRepresentative_spec _).1)
    (class_representative fallback _).symm).trans middle).trans
    (componentWalk_within fallback qs (hu := (requiredRepresentative_spec _).1) (hv := hv)
      (class_representative fallback _))

theorem componentRepresentatives_length {I : Service} {cs : List (Fin I.graph.n)}
    (reps : ComponentRepresentatives I cs) :
    cs.length = (activeRequiredComponents I).card := by
  classical
  have nodup : (cs.map (requiredComponent I)).Nodup :=
    List.pairwise_map.mpr (reps.2.1.imp (fun distinct equal =>
      distinct (requiredComponent_eq_iff.mp equal)))
  have cover : (cs.map (requiredComponent I)).toFinset = activeRequiredComponents I := by
    ext c
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact Finset.mem_image_of_mem _ (reps.1 v hv)
    · intro member
      obtain ⟨u, hu, equal⟩ := Finset.mem_image.mp member
      obtain ⟨v, hv, connected⟩ := reps.2.2 u hu
      exact ⟨v, hv, (requiredComponent_eq_iff.mpr connected).symm.trans equal⟩
  have count := List.toFinset_card_of_nodup nodup
  rw [cover, List.length_map] at count
  exact count.symm

theorem exists_minimumComponentTree_of_tree {I : Service}
    {ps : List (Fin I.graph.n × Fin I.graph.n)} (witness : ComponentTree I ps) :
    ∃ qs, MinimumComponentTree I qs := by
  classical
  have cardinality {qs : List (EndpointPair I)} (tree : ComponentTree I qs) :
      qs.length + 1 = (activeRequiredComponents I).card := by
    obtain ⟨cs, reps, count⟩ := tree.1
    exact count.trans (componentRepresentatives_length reps)
  let candidates : Finset (Fin ps.length → EndpointPair I) :=
    Finset.univ.filter (fun f => ComponentTree I (List.ofFn f))
  have nonempty : candidates.Nonempty :=
    ⟨ps.get, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [List.ofFn_get] using witness⟩⟩
  obtain ⟨f, member, least⟩ := Finset.exists_min_image candidates
    (fun f => pairCost I.graph (List.ofFn f)) nonempty
  refine ⟨List.ofFn f, (Finset.mem_filter.mp member).2, ?_⟩
  intro qs tree
  have len := Nat.add_right_cancel ((cardinality tree).trans (cardinality witness).symm)
  obtain ⟨g, rfl⟩ : ∃ g : Fin ps.length → EndpointPair I, List.ofFn g = qs :=
    len ▸ ⟨qs.get, List.ofFn_get qs⟩
  exact least g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, tree⟩)

theorem exists_minimumComponentTree {I : Service} (nonempty : (requiredVertices I).Nonempty) :
    ∃ qs, MinimumComponentTree I qs := by
  classical
  let pairs := (requiredVertices I ×ˢ requiredVertices I).filter
    (fun p => ¬sameComponent I p.1 p.2)
  have member_iff (p : EndpointPair I) :
      p ∈ pairs.toList ↔ p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧
        ¬sameComponent I p.1 p.2 := by
    rw [Finset.mem_toList, Finset.mem_filter, Finset.mem_product, and_assoc]
  have connects : ∀ u ∈ requiredVertices I, ∀ v ∈ requiredVertices I,
      Relation.ReflTransGen (ComponentStep I pairs.toList) u v := by
    intro u hu v hv
    by_cases same : sameComponent I u v
    · exact Relation.ReflTransGen.mono (fun _ _ step => Or.inl step) _ _ same
    · exact .single (Or.inr (Or.inl ((member_iff (u, v)).mpr ⟨hu, hv, same⟩)))
  obtain ⟨qs, _, witness⟩ :=
    exists_componentTree_sublist nonempty (fun p => (member_iff p).mp) connects
  exact exists_minimumComponentTree_of_tree witness

/-- A retained endpoint pair crosses a cut of the required components. -/
def CrossesRequiredCut {I : Service} (cut : Set (RequiredComponent I))
    (p : Fin I.graph.n × Fin I.graph.n) : Prop :=
  (requiredComponent I p.1 ∈ cut ∧ requiredComponent I p.2 ∉ cut) ∨
    (requiredComponent I p.2 ∈ cut ∧ requiredComponent I p.1 ∉ cut)

/-- A least-cost crossing pair extends the chosen pairs contained in a minimum
component tree whenever the previous choices stay within the two sides. -/
theorem extend_minimumComponentTree_across_cut {I : Service} (cut : Set (RequiredComponent I))
    (edge : Fin I.graph.n × Fin I.graph.n)
    (left : edge.1 ∈ requiredVertices I) (right : edge.2 ∈ requiredVertices I)
    (inside : requiredComponent I edge.1 ∈ cut) (outside : requiredComponent I edge.2 ∉ cut)
    (cheapest : ∀ p : Fin I.graph.n × Fin I.graph.n,
      p.1 ∈ requiredVertices I → p.2 ∈ requiredVertices I → CrossesRequiredCut cut p →
      distance I.graph edge.1 edge.2 ≤ distance I.graph p.1 p.2)
    {tree chosen : List (Fin I.graph.n × Fin I.graph.n)} (minimum : MinimumComponentTree I tree)
    (keeps : ∀ p ∈ chosen, p ∈ tree ∧ ¬CrossesRequiredCut cut p) :
    ∃ next, MinimumComponentTree I next ∧ ∀ p ∈ edge :: chosen, p ∈ next := by
  classical
  by_cases chosenPresent : edge ∈ tree
  · exact ⟨tree, minimum, fun p member =>
      (List.mem_cons.mp member).elim (fun same => same.symm ▸ chosenPresent)
        (fun m => (keeps p m).1)⟩
  let fallback : ActiveComponent I := ⟨requiredComponent I edge.1, Finset.mem_image_of_mem _ left⟩
  let G := componentGraph fallback tree
  let side : Set (ActiveComponent I) := Subtype.val ⁻¹' cut
  let x := componentOf fallback edge.1
  let y := componentOf fallback edge.2
  have connected : G.Connected := componentGraph_connected fallback minimum.1.2.1 minimum.1.2.2
  have xIn : x ∈ side := by
    change x.val ∈ cut
    simpa [x, componentOf_val fallback left] using inside
  have yOut : y ∉ side := by
    change y.val ∉ cut
    simpa [y, componentOf_val fallback right] using outside
  obtain ⟨a, aIn, b, bOut, present, swapped⟩ := exists_crossing_connected_swap connected side xIn yOut
  change a ≠ b ∧ ∃ p ∈ tree, componentEdge fallback p = s(a, b) at present
  obtain ⟨_, removed, used, removedEdge⟩ := present
  have validRemoved := minimum.1.2.1 removed used
  have crosses : CrossesRequiredCut cut removed := by
    change a.val ∈ cut at aIn
    change b.val ∉ cut at bOut
    unfold CrossesRequiredCut
    rw [← componentOf_val fallback validRemoved.1, ← componentOf_val fallback validRemoved.2.1]
    rcases Sym2.eq_iff.mp removedEdge with aligned | reversed
    · rw [aligned.1, aligned.2]
      exact Or.inl ⟨aIn, bOut⟩
    · rw [reversed.1, reversed.2]
      exact Or.inr ⟨aIn, bOut⟩
  let next := edge :: tree.erase removed
  let H := componentGraph fallback next
  have adds : SimpleGraph.edge x y ≤ H := by
    intro c d adj
    obtain ⟨equivalent, different⟩ := (SimpleGraph.adj_edge x y).mp adj
    exact ⟨different, edge, List.mem_cons_self, equivalent⟩
  have remains : (G ⊔ SimpleGraph.edge x y).deleteEdges {s(a, b)} ≤ H := by
    intro c d adj
    obtain ⟨previous, notRemoved⟩ := SimpleGraph.deleteEdges_adj.mp adj
    rcases previous with fromG | fromEdge
    · have wasAdj : c ≠ d ∧ ∃ p ∈ tree, componentEdge fallback p = s(c, d) := fromG
      obtain ⟨different, p, member, equivalent⟩ := wasAdj
      have survives : p ≠ removed := fun equal => notRemoved (Set.mem_singleton_iff.mpr
        (equivalent.symm.trans (equal.symm ▸ removedEdge)))
      exact ⟨different, p, List.mem_cons_of_mem _ ((List.mem_erase_of_ne survives).mpr member), equivalent⟩
    · exact adds fromEdge
  have newConnected : H.Connected := swapped.mono (sup_le remains adds)
  have distinct : ¬sameComponent I edge.1 edge.2 :=
    fun same => outside (requiredComponent_eq_iff.mpr same ▸ inside)
  have eligible (p : EndpointPair I) (member : p ∈ next) :
      p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧ ¬sameComponent I p.1 p.2 := by
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨left, right, distinct⟩
    · exact minimum.1.2.1 p (List.mem_of_mem_erase old)
  have newTree : ComponentTree I next := by
    obtain ⟨cs, reps, count⟩ := minimum.1.1
    have oldLength := (List.perm_cons_erase used).length_eq
    have newCount : next.length + 1 = cs.length := calc
      _ = (removed :: tree.erase removed).length + 1 := rfl
      _ = tree.length + 1 := congrArg (· + 1) oldLength.symm
      _ = cs.length := count
    refine ⟨⟨cs, reps, newCount⟩, eligible, fun u hu v hv => ?_⟩
    have walk := (H.reachable_iff_reflTransGen _ _).mp
      (newConnected (componentOf fallback u) (componentOf fallback v))
    have middle := lift_componentWalk fallback (qs := next) (T := H)
      (fun p mem => ⟨(eligible p mem).1, (eligible p mem).2.1⟩) (fun _ _ adj => adj.2) walk
    exact ((componentWalk_within fallback next (hu := hu) (hv := (requiredRepresentative_spec _).1)
      (class_representative fallback _).symm).trans middle).trans
      (componentWalk_within fallback next (hu := (requiredRepresentative_spec _).1) (hv := hv)
        (class_representative fallback _))
  have oldCost : pairCost I.graph tree =
      distance I.graph removed.1 removed.2 + pairCost I.graph (tree.erase removed) := by
    simpa only [pairCost, List.map_cons, List.sum_cons] using
      ((List.perm_cons_erase used).map (fun p => distance I.graph p.1 p.2)).sum_eq
  have noWorse : pairCost I.graph next ≤ pairCost I.graph tree := by
    rw [oldCost]
    change distance I.graph edge.1 edge.2 + pairCost I.graph (tree.erase removed) ≤ _
    exact add_le_add (cheapest removed validRemoved.1 validRemoved.2.1 crosses) le_rfl
  refine ⟨next, ⟨newTree, fun ps ht => noWorse.trans (minimum.2 ps ht)⟩, fun p member => ?_⟩
  rcases List.mem_cons.mp member with rfl | earlier
  · exact List.mem_cons_self
  · obtain ⟨wasIn, stable⟩ := keeps p earlier
    have survives : p ≠ removed := fun same => stable (same.symm ▸ crosses)
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne survives).mpr wasIn)

end VehicleRoutingSurvey.Routing
end RppSource_ComponentTreeExtraction

/-! DistanceMetric.lean -/
section RppSource_DistanceMetric
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

theorem distance_triangle (connected : Connected G) (nonnegative : Nonnegative G)
    (u v w : Fin G.n) : distance G u w ≤ distance G u v + distance G v w := by
  obtain ⟨xs, shortestXs, _⟩ := exists_shortest_path connected nonnegative u v
  obtain ⟨ys, shortestYs, _⟩ := exists_shortest_path connected nonnegative v w
  simpa only [pathCost_append, ← distance_eq_of_shortestPath shortestXs,
    ← distance_eq_of_shortestPath shortestYs] using
    distance_le_pathCost nonnegative (isPath_append shortestXs.1 shortestYs.1)

theorem distance_isMetric (connected : Connected G) (nonnegative : Nonnegative G)
    (undirected : Undirected G) : SupplyChainTheory.IsMetric (distance G) :=
  ⟨distance_symm undirected, distance_nonnegative connected nonnegative,
    distance_self nonnegative, fun u w v => distance_triangle connected nonnegative u v w⟩

end VehicleRoutingSurvey.Routing
end RppSource_DistanceMetric

/-! matching/MatchingApplication.lean -/
section RppSource_MatchingApplication
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem expanded_pathCost_eq_pairCost {G : Network} {pairs : List (Fin G.n × Fin G.n)}
    {paths : List (List (Traversal G))} (expansion : Expands G pairs paths) :
    pathCost G paths.flatten = pairCost G pairs := by
  induction expansion with
  | nil => rfl
  | @cons p ts rest ps shortest _ ih =>
    calc
      pathCost G (ts :: ps).flatten = pathCost G ts + pathCost G ps.flatten := pathCost_append _ _
      _ = pairCost G (p :: rest) := by rw [ih, ← distance_eq_of_shortestPath shortest]; rfl

/-- The matching stage costs at most half of any feasible rural-postman tour. -/
theorem minimumMatching_le_half_feasible {I : Service} (rural : Rural I)
    {base : List (Fin I.graph.q)} {tree matching : List (Fin I.graph.n × Fin I.graph.n)}
    {tp : List (List (Traversal I.graph))} (baseLinks : base.toFinset = I.links)
    (componentTree : ComponentTree I tree) (expansion : Expands I.graph tree tp)
    (minimum : MinimumMatching I.graph (base ++ tp.flatten.map Prod.fst) matching)
    {u : Fin I.graph.n} {ts : List (Traversal I.graph)} (tour : Feasible I u ts) :
    2 * pairCost I.graph matching ≤ pathCost I.graph ts :=
  minimumMatching_le_half_path rural.2.1 rural.2.2.1 (distance_triangle rural.1 rural.2.1)
    minimum (oddVertices_card_mod_two _ _) tour.1
    ((oddVertices_subset_required baseLinks expansion
      (fun p hp => ⟨(componentTree.2.1 p hp).1, (componentTree.2.1 p hp).2.1⟩)).trans
      (requiredVertices_subset_visited tour))

/-- A least-cost perfect matching of the odd vertices exists in the complete metric graph. -/
theorem exists_minimumMatching (G : Network) (es : List (Fin G.q)) :
    ∃ ms, MinimumMatching G es ms := by
  classical
  let candidates := (Finset.univ : Finset (Finset (Sym2 (Fin G.n)))).filter
    (IsPerfectMatchingOn (oddVertices G es))
  obtain ⟨m, inCandidates, least⟩ := Finset.exists_min_image candidates (edgeSetWeight (distance G))
    ((exists_perfectMatching_on_even _ (oddVertices_card_mod_two G es)).imp fun m perfect =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ m, perfect⟩)
  let ms := m.toList.map fun e => e.out
  have restore : (ms.map fun p => s(p.1, p.2)) = m.toList := by
    simp [ms, List.map_map, Function.comp_def, Sym2.mk, Quot.out_eq]
  exact ⟨ms, by
    simp only [MinimumMatching, matchingEdges, restore, Finset.toList_toFinset]
    exact ⟨m.nodup_toList, (Finset.mem_filter.mp inCandidates).2,
      fun other perfect => least other (Finset.mem_filter.mpr ⟨Finset.mem_univ other, perfect⟩)⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingApplication

/-! RuralApproximation.lean -/
section RppSource_RuralApproximation
namespace VehicleRoutingSurvey.Routing

variable {I : Service}

theorem requiredVertices_nonempty_of_links_nonempty (nonempty : I.links.Nonempty) :
    (requiredVertices I).Nonempty :=
  nonempty.elim fun e he => ⟨I.graph.tail e,
    Finset.mem_union_left _ (Finset.mem_image_of_mem I.graph.tail he)⟩

/-- The required links and the minimum connector tree cost no more than any feasible tour. -/
theorem minimumComponentTree_le_feasible (rural : Rural I) (nonempty : I.links.Nonempty)
    {tree : List (VertexPair I.graph)} (minimum : MinimumComponentTree I tree)
    {u : Fin I.graph.n} {ts : List (Traversal I.graph)} (comparison : Feasible I u ts) :
    requiredCost I + pairCost I.graph tree ≤ pathCost I.graph ts := by
  obtain ⟨pairs, valid, connected, pathBudget⟩ := exists_comparison_pairs rural.1 rural.2.1 nonempty comparison
  obtain ⟨selected, sublist, spanning⟩ :=
    exists_componentTree_sublist (requiredVertices_nonempty_of_links_nonempty nonempty) valid connected
  have treeBound := (minimum.2 selected spanning).trans
    ((pairCost_mono_sublist rural.1 rural.2.1 sublist).trans pathBudget)
  exact (add_le_add (requiredCost_le_requiredTraversals rural.2.1 comparison) treeBound).trans_eq
    (pathCost_required_add_connector ts).symm

/-- Every admitted run costs at most three halves of every feasible comparison tour. -/
theorem ruralRun_le_three_halves_feasible (rural : Rural I)
    {u v : Fin I.graph.n} {runSteps comparisonSteps : List (Traversal I.graph)}
    (run : RuralRun I u runSteps) (comparison : Feasible I v comparisonSteps) :
    pathCost I.graph runSteps ≤ (3 / 2 : ℝ) * pathCost I.graph comparisonSteps := by
  classical
  by_cases empty : I.links = ∅
  · have noSteps : runSteps = [] := by simpa [RuralRun, empty] using run
    simpa [noSteps, pathCost] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (pathCost_nonnegative rural.2.1 comparisonSteps)
  · apply ruralRun_le_of_comparison_bounds rural run
    · intro tree minimum
      exact minimumComponentTree_le_feasible rural (Finset.nonempty_iff_ne_empty.mpr empty) minimum comparison
    · intro base tree tp matching _ covers minimumTree expandsTree minimumMatching
      exact minimumMatching_le_half_feasible rural covers minimumTree.1 expandsTree minimumMatching comparison

theorem ruralRun_feasible_and_le_optimum (rural : Rural I)
    (attains : ∃ v ts, Feasible I v ts ∧ pathCost I.graph ts = optimum I)
    {u : Fin I.graph.n} {ts : List (Traversal I.graph)} (run : RuralRun I u ts) :
    Feasible I u ts ∧ pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I := by
  obtain ⟨v, comparison, feasible, exactCost⟩ := attains
  exact ⟨ruralRun_feasible rural run,
    exactCost ▸ ruralRun_le_three_halves_feasible rural run feasible⟩

end VehicleRoutingSurvey.Routing
end RppSource_RuralApproximation

/-! RuralExistence.lean -/
section RppSource_RuralExistence
namespace VehicleRoutingSurvey.Routing

variable {I : Service}

/-- The minimum component tree and matching admit a run once the even
expanded multigraph is traversed by an Euler circuit. -/
theorem exists_ruralRun_of_euler (rural : Rural I)
    (euler : ∀ es : List (Fin I.graph.q), (∀ v, degree I.graph es v % 2 = 0) →
      EdgeSupportConnected I.graph es → ∀ u, EdgeSupport I.graph es u →
      ∃ ts, IsPath I.graph u ts u ∧ (ts.map Prod.fst).Perm es) :
    ∃ u ts, RuralRun I u ts := by
  classical
  by_cases empty : I.links = ∅
  · obtain ⟨u, run, _, _⟩ := empty_rural_run_and_optimum rural empty
    exact ⟨u, [], run⟩
  have nonempty : I.links.Nonempty := Finset.nonempty_iff_ne_empty.mpr empty
  obtain ⟨tree, minimumTree⟩ := exists_minimumComponentTree
    (requiredVertices_nonempty_of_links_nonempty nonempty)
  obtain ⟨tp, treePaths, _⟩ := exists_bounded_expands rural.1 rural.2.1 tree
  let base := I.links.toList
  have distinct : base.Nodup := I.links.nodup_toList
  have covers : base.toFinset = I.links := I.links.toList_toFinset
  obtain ⟨matching, minimumMatching⟩ := exists_minimumMatching I.graph
    (base ++ tp.flatten.map Prod.fst)
  obtain ⟨mp, matchingPaths, _⟩ := exists_bounded_expands rural.1 rural.2.1 matching
  have treeEnds (p : Fin I.graph.n × Fin I.graph.n) (member : p ∈ tree) :
      p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I :=
    let both := minimumTree.1.2.1 p member
    ⟨both.1, both.2.1⟩
  have oddRequired := oddVertices_subset_required covers treePaths treeEnds
  have matchingStarts (p : Fin I.graph.n × Fin I.graph.n) (member : p ∈ matching) :
      p.1 ∈ requiredVertices I := by
    have matched : s(p.1, p.2) ∈ matchingEdges I.graph matching :=
      List.mem_toFinset.mpr (List.mem_map_of_mem member)
    exact oddRequired ((minimumMatching.2.1.1 _ matched).2 _ (by simp))
  let all := base ++ tp.flatten.map Prod.fst ++ mp.flatten.map Prod.fst
  have connected : EdgeSupportConnected I.graph all :=
    expandedSupport_connected covers minimumTree.1 treePaths matchingPaths matchingStarts
  have perfect : PerfectMatching I.graph (base ++ tp.flatten.map Prod.fst) matching :=
    ⟨minimumMatching.1, minimumMatching.2.1⟩
  have even (v : Fin I.graph.n) : degree I.graph all v % 2 = 0 :=
    degree_matching_augmentation_even perfect matchingPaths v
  obtain ⟨edge, serves⟩ := nonempty
  let u := I.graph.tail edge
  have used : edge ∈ base := List.mem_toFinset.mp (covers.symm ▸ serves)
  have support : EdgeSupport I.graph all u := ⟨edge, by simp [all, used], .inl rfl⟩
  obtain ⟨ts, path, permutation⟩ := euler all even connected u support
  exact ⟨u, ts, by rw [RuralRun, if_neg empty]; exact ⟨base, tree, matching, tp, mp,
    distinct, covers, minimumTree, treePaths, minimumMatching, matchingPaths, path, permutation⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_RuralExistence

/-! sharpness/SharpnessArithmetic.lean -/
section RppSource_SharpnessArithmetic
namespace VehicleRoutingSurvey.Routing.Sharpness

/-- Parameters for a path of length `2*m`, with additional links jumping two places. -/
theorem choose_halfSpan (ε : ℝ) (positive : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ N ≤ 2 * m + 1 ∧
      (3 / 2 - ε) * (2 * (m : ℝ) + 1) < 3 * (m : ℝ) := by
  obtain ⟨m, large⟩ := exists_nat_gt (max (N : ℝ) (1 / ε))
  have below : N < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left (N : ℝ) (1 / ε)) large)
  refine ⟨m, ?_, ?_, ?_⟩
  all_goals try omega
  have gain : 1 < (m : ℝ) * ε := (div_lt_iff₀ positive).mp ((le_max_right _ _).trans_lt large)
  nlinarith

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessArithmetic

/-! sharpness/SharpnessFamily.lean -/
section RppSource_SharpnessFamily
namespace VehicleRoutingSurvey.Routing.Sharpness

abbrev Vertex (k : ℕ) := Fin (k + 1)
abbrev Edge (k : ℕ) := Fin ((k + 1) + ((k + 1) + (k + 1)))

def loop {k : ℕ} (i : Vertex k) : Edge k := i.castAdd ((k + 1) + (k + 1))
def step {k : ℕ} (i : Vertex k) : Edge k := (i.castAdd (k + 1)).natAdd (k + 1)
def jump {k : ℕ} (i : Vertex k) : Edge k := (i.natAdd (k + 1)).natAdd (k + 1)

def shift {k : ℕ} (d : ℕ) (i : Vertex k) : Vertex k :=
  ⟨min (i.val + d) k, Nat.lt_succ_of_le (min_le_right _ _)⟩

def edgeTail (k : ℕ) : Edge k → Vertex k := Fin.addCases id (Fin.addCases id id)

def edgeHead (k : ℕ) : Edge k → Vertex k :=
  Fin.addCases id (Fin.addCases (shift 1) (shift 2))

def edgeWeight (k : ℕ) : Edge k → ℝ := Fin.addCases (fun _ => 0) (fun _ => 1)

/-- Each vertex has a free required loop. Consecutive and two-step links cost one.
Near the right endpoint the clipped links are harmless additional links. -/
abbrev network (k : ℕ) : Network where
  n := k + 1
  q := (k + 1) + ((k + 1) + (k + 1))
  tail := edgeTail k
  head := edgeHead k
  directed := fun _ => false
  weight := edgeWeight k

abbrev instanceAt (k : ℕ) : Service where
  graph := network k
  vertices := ∅
  links := Finset.univ.image loop

@[simp] theorem directed_network {k : ℕ} (e : Edge k) : (network k).directed e = false := rfl

@[simp] theorem tail_loop {k : ℕ} (i : Vertex k) : edgeTail k (loop i) = i := by
  simp [edgeTail, loop]

@[simp] theorem head_loop {k : ℕ} (i : Vertex k) : edgeHead k (loop i) = i := by
  simp [edgeHead, loop]

@[simp] theorem tail_step {k : ℕ} (i : Vertex k) : edgeTail k (step i) = i := by
  simp [edgeTail, step, Fin.addCases_right]

@[simp] theorem head_step {k : ℕ} (i : Vertex k) : edgeHead k (step i) = shift 1 i := by
  simp [edgeHead, step, Fin.addCases_right]

@[simp] theorem tail_jump {k : ℕ} (i : Vertex k) : edgeTail k (jump i) = i := by
  simp only [edgeTail, jump, Fin.addCases_right, id]

@[simp] theorem head_jump {k : ℕ} (i : Vertex k) : edgeHead k (jump i) = shift 2 i := by
  simp only [edgeHead, jump, Fin.addCases_right]

@[simp] theorem weight_loop {k : ℕ} (i : Vertex k) : edgeWeight k (loop i) = 0 := by
  simp [edgeWeight, loop]

@[simp] theorem weight_step {k : ℕ} (i : Vertex k) : edgeWeight k (step i) = 1 := by
  simp [edgeWeight, step, Fin.addCases_right]

@[simp] theorem weight_jump {k : ℕ} (i : Vertex k) : edgeWeight k (jump i) = 1 := by
  simp [edgeWeight, jump, Fin.addCases_right]

theorem edge_cases {k : ℕ} (e : Edge k) :
    (∃ i, e = loop i) ∨ (∃ i, e = step i) ∨ ∃ i, e = jump i := by
  induction e using Fin.addCases
  case left i => exact .inl ⟨i, rfl⟩
  case right i => exact Fin.addCases (fun j => .inr (.inl ⟨j, rfl⟩)) (fun j => .inr (.inr ⟨j, rfl⟩)) i

theorem loop_required {k : ℕ} (i : Vertex k) : loop i ∈ (instanceAt k).links :=
  Finset.mem_image_of_mem loop (Finset.mem_univ i)

theorem required_is_loop {k : ℕ} {e : Edge k} (required : e ∈ (instanceAt k).links) :
    ∃ i : Vertex k, loop i = e :=
  (Finset.mem_image.mp required).imp fun _ h => h.2

theorem requiredVertices_eq_univ (k : ℕ) : requiredVertices (instanceAt k) = Finset.univ :=
  Finset.eq_univ_of_forall fun i => Finset.mem_union_left _ <|
    Finset.mem_image.mpr ⟨loop i, loop_required i, tail_loop i⟩

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessFamily

/-! sharpness/SharpnessRoutes.lean -/
section RppSource_SharpnessRoutes
namespace VehicleRoutingSurvey.Routing.Sharpness

/-- An evenly spaced sequence of vertices with `count` moves. -/
def point {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (i : Fin (count + 1)) : Vertex k :=
  ⟨lo + stride * i, Nat.lt_succ_of_le <| le_trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left stride (Nat.le_of_lt_succ i.isLt)) lo) fit⟩

def risingEdge {k : ℕ} (stride : ℕ) (i : Vertex k) : Edge k :=
  if stride = 1 then step i else jump i

def risingBlock {k : ℕ} (stride : ℕ) (withLoop : Bool) (i : Vertex k) :
    List (Traversal (network k)) :=
  (if withLoop then [(loop i, true)] else []) ++ [(risingEdge stride i, true)]

def risingPath {k lo stride count : ℕ} (fit : lo + stride * count ≤ k) (withLoops : Bool) :
    List (Traversal (network k)) :=
  (List.ofFn fun i : Fin count => risingBlock stride withLoops (point fit i.castSucc)).flatten

theorem isPath_of_blocks {G : Network} {count : ℕ} (points : Fin (count + 1) → Fin G.n)
    (blocks : Fin count → List (Traversal G))
    (linked : ∀ i, IsPath G (points i.castSucc) (blocks i) (points i.succ)) :
    IsPath G (points 0) (List.ofFn blocks).flatten (points (Fin.last count)) := by
  induction count with
  | zero => exact (show IsPath G (points 0) [] (points (Fin.last 0)) from rfl)
  | succ count ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    exact isPath_append (linked 0) (ih (fun i => points i.succ) (fun i => blocks i.succ)
      (fun i => linked i.succ))

theorem shift_point {k lo stride count : ℕ} (fit : lo + stride * count ≤ k) (i : Fin count) :
    shift stride (point fit i.castSucc) = point fit i.succ := by
  apply Fin.ext
  change min (lo + stride * i.val + stride) k = lo + stride * (i.val + 1)
  simpa only [Nat.mul_succ, ← Nat.add_assoc] using
    (min_eq_left ((Nat.add_le_add_left (Nat.mul_le_mul_left stride (Nat.succ_le_of_lt i.isLt)) lo).trans fit))

theorem risingBlock_isPath {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (allowed : stride = 1 ∨ stride = 2) (withLoop : Bool) (i : Fin count) :
    IsPath (network k) (point fit i.castSucc) (risingBlock stride withLoop (point fit i.castSucc))
      (point fit i.succ) := by
  cases withLoop <;> rcases allowed with rfl | rfl
  all_goals simp [risingBlock, risingEdge, IsPath, start, finish, shift_point]

theorem risingPath_isPath {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (allowed : stride = 1 ∨ stride = 2) (withLoops : Bool) :
    IsPath (network k) (point fit 0) (risingPath fit withLoops) (point fit (Fin.last count)) :=
  isPath_of_blocks (G := network k) (count := count) (point fit)
    (fun i => risingBlock stride withLoops (point fit i.castSucc)) (risingBlock_isPath fit allowed withLoops)

@[simp] theorem point_zero_val {k lo stride count : ℕ} (fit : lo + stride * count ≤ k) :
    (point fit 0).val = lo := by
  simp [point]

@[simp] theorem point_last_val {k lo stride count : ℕ} (fit : lo + stride * count ≤ k) :
    (point fit (Fin.last count)).val = lo + stride * count := rfl

@[simp] theorem risingBlock_cost {k : ℕ} (stride : ℕ) (withLoop : Bool) (i : Vertex k) :
    pathCost (network k) (risingBlock stride withLoop i) = 1 := by
  cases withLoop <;> by_cases stepLength : stride = 1 <;>
    simp [risingBlock, risingEdge, pathCost, stepLength]

theorem risingPath_cost {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (withLoops : Bool) : pathCost (network k) (risingPath fit withLoops) = count := by
  rw [risingPath, pathCost, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn]
  change (List.ofFn (fun i : Fin count =>
    pathCost (network k) (risingBlock stride withLoops (point fit i.castSucc)))).sum = count
  simp [List.ofFn_const]

theorem risingPath_with_endpoints {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (allowed : stride = 1 ∨ stride = 2) (withLoops : Bool) (a b : Vertex k)
    (ha : a.val = lo) (hb : b.val = lo + stride * count) :
    IsPath (network k) a (risingPath fit withLoops) b :=
  (Fin.ext ((point_zero_val fit).trans ha.symm) : point fit 0 = a) ▸
    (Fin.ext ((point_last_val fit).trans hb.symm) : point fit (Fin.last count) = b) ▸
    risingPath_isPath fit allowed withLoops

theorem risingPath_contains_loop {k lo stride count : ℕ} (fit : lo + stride * count ≤ k)
    (i : Fin count) : (loop (point fit i.castSucc), true) ∈ risingPath fit true :=
  List.mem_flatten.mpr ⟨risingBlock stride true (point fit i.castSucc),
    List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [risingBlock]⟩

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessRoutes

/-! sharpness/SharpnessMetric.lean -/
section RppSource_SharpnessMetric
namespace VehicleRoutingSurvey.Routing.Sharpness

theorem weight_zero_or_one {k : ℕ} (e : Edge k) :
    (network k).weight e = 0 ∨ (network k).weight e = 1 := by
  rcases edge_cases e with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp

theorem undirected_network (k : ℕ) : Undirected (network k) := fun _ => rfl

theorem nonnegative_network (k : ℕ) : Nonnegative (network k) := by
  intro e
  rcases weight_zero_or_one e with h | h
  · exact h.symm ▸ (le_rfl : (0 : ℝ) ≤ 0)
  · exact h.symm ▸ (zero_le_one : (0 : ℝ) ≤ 1)

private theorem shift_backward_le {k : ℕ} (i : Vertex k) (d : ℕ) :
    (i.val : ℝ) ≤ ((shift d i).val : ℝ) + 2 :=
  (show (i.val : ℝ) ≤ ((shift d i).val : ℝ) from by
    exact_mod_cast (le_min (Nat.le_add_right i.val d) (Nat.le_of_lt_succ i.isLt)))
    |>.trans (le_add_of_nonneg_right (by norm_num))

private theorem shift_forward_le {k : ℕ} (i : Vertex k) (d : ℕ) (hd : d ≤ 2) :
    ((shift d i).val : ℝ) ≤ (i.val : ℝ) + 2 := by
  exact_mod_cast (min_le_left (i.val + d) k |>.trans (Nat.add_le_add_left hd i.val))

theorem traversal_displacement {k : ℕ} (t : Traversal (network k)) :
    ((finish (network k) t).val : ℝ) ≤
      ((start (network k) t).val : ℝ) + 2 * (network k).weight t.1 := by
  rcases t with ⟨e, orientation⟩
  rcases edge_cases e with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> cases orientation
  all_goals norm_num [finish, start]
  all_goals first
    | exact shift_backward_le i 1
    | exact shift_forward_le i 1 (by decide)
    | exact shift_backward_le i 2
    | exact shift_forward_le i 2 (by decide)

theorem path_displacement {k : ℕ} {u v : Vertex k} {ts : List (Traversal (network k))}
    (path : IsPath (network k) u ts v) :
    (v.val : ℝ) ≤ (u.val : ℝ) + 2 * pathCost (network k) ts := by
  induction ts generalizing u
  case nil => simp [pathCost, show u = v from path]
  case cons t ts ih =>
    rcases path with ⟨rfl, _, tail⟩
    change (v.val : ℝ) ≤ ((start (network k) t).val : ℝ) +
      2 * ((network k).weight t.1 + pathCost (network k) ts)
    linarith only [traversal_displacement t, ih tail]

private theorem loop_of_zero {k : ℕ} {e : Edge k} (free : edgeWeight k e = 0) :
    ∃ i, e = loop i := by
  rcases edge_cases e with h | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp_all

theorem cheap_path_constant {k : ℕ} {u v : Vertex k} {ts : List (Traversal (network k))}
    (path : IsPath (network k) u ts v) (cheap : pathCost (network k) ts < 1) :
    u = v ∧ ∀ t ∈ ts, start (network k) t = u := by
  induction ts generalizing u
  case nil => exact ⟨path, by simp⟩
  case cons t rest ih =>
    rcases path with ⟨rfl, _, restPath⟩
    change edgeWeight k t.1 + pathCost (network k) rest < 1 at cheap
    have free : edgeWeight k t.1 = 0 := (weight_zero_or_one t.1).resolve_right
      (fun paid => by linarith only [cheap, paid, pathCost_nonnegative (nonnegative_network k) rest])
    obtain ⟨i, index⟩ := loop_of_zero free
    have same : start (network k) t = finish (network k) t := by
      cases direction : t.2 <;> simp [start, finish, direction, index]
    exact let result := ih restPath (by simpa only [free, zero_add] using cheap)
      ⟨same.trans result.1, fun s member => (List.mem_cons.mp member).elim
        (congrArg (start (network k))) (fun inside => (result.2 s inside).trans same.symm)⟩

theorem pathCost_ge_one_of_ne {k : ℕ} {u v : Vertex k} {ts : List (Traversal (network k))}
    (path : IsPath (network k) u ts v) (distinct : u ≠ v) : 1 ≤ pathCost (network k) ts :=
  le_of_not_gt fun cheap => distinct (cheap_path_constant path cheap).1

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessMetric

/-! sharpness/SharpnessTree.lean -/
section RppSource_SharpnessTree
namespace VehicleRoutingSurvey.Routing.Sharpness

def baseLinks (k : ℕ) : List (Edge k) := (List.finRange (k + 1)).map loop

def consecutivePairs (k : ℕ) : List (Vertex k × Vertex k) :=
  (List.finRange k).map fun i => (i.castSucc, i.succ)

def consecutivePaths (k : ℕ) : List (List (Traversal (network k))) :=
  (List.finRange k).map fun i => [(step i.castSucc, true)]

theorem loop_injective {k : ℕ} : Function.Injective (@loop k) :=
  fun _ _ equal => Fin.ext (congrArg (fun e : Edge k => e.val) equal)

theorem baseLinks_nodup (k : ℕ) : (baseLinks k).Nodup :=
  (List.nodup_finRange _).map loop_injective

theorem baseLinks_toFinset (k : ℕ) : (baseLinks k).toFinset = (instanceAt k).links := by
  ext e
  simp [baseLinks, List.mem_map]

theorem requiredAdjacent_eq {k : ℕ} {u v : Vertex k}
    (adj : requiredAdjacent (instanceAt k) u v) : u = v := by
  obtain ⟨e, needed, endpoints⟩ := adj
  obtain ⟨i, rfl⟩ := required_is_loop needed
  simp only [instanceAt, head_loop, tail_loop] at endpoints
  exact endpoints.elim (fun h => h.1.symm.trans h.2) (fun h => h.2.symm.trans h.1)

theorem sameComponent_iff_eq {k : ℕ} {u v : Vertex k} :
    sameComponent (instanceAt k) u v ↔ u = v := by
  constructor
  · intro chain
    induction chain with
    | refl => rfl
    | tail _ adj ih => exact ih.trans (requiredAdjacent_eq adj)
  · intro equal
    exact equal ▸ Relation.ReflTransGen.refl

private theorem path_of_order {k : ℕ} (u v : Vertex k) (order : u.val ≤ v.val) :
    ∃ ts, IsPath (network k) u ts v :=
  let fit : u.val + 1 * (v.val - u.val) ≤ k := by have := v.isLt; omega
  ⟨risingPath fit false, risingPath_with_endpoints fit (Or.inl rfl) false u v rfl (by omega)⟩

theorem rural_instance (k : ℕ) : Rural (instanceAt k) := by
  refine ⟨⟨Nat.succ_pos _, fun u v => ?_⟩, nonnegative_network k, undirected_network k, rfl⟩
  rcases le_total u.val v.val with forward | backward
  · exact path_of_order u v forward
  · exact (path_of_order v u backward).elim fun ts path =>
      ⟨reverseTraversals ts, isPath_reverse (undirected_network k) path⟩

def consecutiveAdjacent (k : ℕ) (u v : Vertex k) : Prop :=
  requiredAdjacent (instanceAt k) u v ∨
    (u, v) ∈ consecutivePairs k ∨ (v, u) ∈ consecutivePairs k

theorem consecutive_reaches_from_zero {k : ℕ} (v : Vertex k) :
    Relation.ReflTransGen (consecutiveAdjacent k) 0 v :=
  Fin.induction .refl (fun i walk => walk.tail
    (Or.inr (Or.inl (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))) v

theorem consecutive_connected {k : ℕ} (u v : Vertex k) :
    Relation.ReflTransGen (consecutiveAdjacent k) u v := by
  let symmAdj : Std.Symm (consecutiveAdjacent k) :=
    ⟨fun _ _ h => h.elim (fun r => Or.inl (requiredAdjacent_comm r)) (fun links => Or.inr links.symm)⟩
  exact (@Std.Symm.symm _ _ (@Relation.ReflTransGen.stdSymm _ _ symmAdj) _ _
    (consecutive_reaches_from_zero u)).trans (consecutive_reaches_from_zero v)

theorem consecutive_componentTree (k : ℕ) : ComponentTree (instanceAt k) (consecutivePairs k) := by
  refine ⟨⟨List.finRange (k + 1), ?_, by rw [consecutivePairs, List.length_map, List.length_finRange, List.length_finRange]⟩, ?_, ?_⟩
  · exact ⟨fun _ _ => requiredVertices_eq_univ k ▸ Finset.mem_univ _,
      (List.nodup_finRange _).imp (fun distinct same => distinct (sameComponent_iff_eq.mp same)),
      fun u _ => ⟨u, List.mem_finRange u, Relation.ReflTransGen.refl⟩⟩
  · intro p member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    refine ⟨requiredVertices_eq_univ k ▸ Finset.mem_univ _, requiredVertices_eq_univ k ▸ Finset.mem_univ _, ?_⟩
    exact fun same => by
      have impossible := congrArg (fun u : Vertex k => u.val) (sameComponent_iff_eq.mp same)
      change i.val = i.val + 1 at impossible
      omega
  · exact fun u _ v _ => consecutive_connected u v

theorem consecutive_distinct {k : ℕ} (i : Fin k) : i.castSucc ≠ i.succ := by
  intro impossible
  exact (show i.val ≠ i.val + 1 by omega) (congrArg (fun v : Vertex k => v.val) impossible)

@[simp] theorem shift_consecutive {k : ℕ} (i : Fin k) : shift 1 i.castSucc = i.succ :=
  Fin.ext (min_eq_left (Nat.succ_le_of_lt i.isLt))

theorem consecutive_shortest {k : ℕ} (i : Fin k) :
    ShortestPath (network k) i.castSucc i.succ [(step i.castSucc, true)] := by
  refine ⟨by simp [IsPath, start, finish], fun ts path => ?_⟩
  simpa [pathCost] using pathCost_ge_one_of_ne path (consecutive_distinct i)

private theorem all_consecutivePaths_expand {k : ℕ} (indices : List (Fin k)) :
    Expands (network k) (indices.map fun i => (i.castSucc, i.succ))
      (indices.map fun i => [(step i.castSucc, true)]) := by
  induction indices with
  | nil => exact .nil
  | cons i _ ih => exact .cons (consecutive_shortest i) ih

theorem consecutive_expands (k : ℕ) : Expands (network k) (consecutivePairs k) (consecutivePaths k) :=
  all_consecutivePaths_expand (List.finRange k)

theorem consecutive_distance {k : ℕ} (i : Fin k) :
    distance (network k) i.castSucc i.succ = 1 :=
  (distance_eq_of_shortestPath (consecutive_shortest i)).trans (by simp [pathCost])

theorem distance_ge_one {k : ℕ} {u v : Vertex k} (h : u ≠ v) :
    1 ≤ distance (network k) u v :=
  le_csInf (((rural_instance k).1.2 u v).elim fun ts path => ⟨_, ts, path, rfl⟩)
    (fun _ ⟨_, path, eq⟩ => eq.symm ▸ pathCost_ge_one_of_ne path h)

theorem reps_length {k : ℕ} {cs : List (Vertex k)}
    (reps : ComponentRepresentatives (instanceAt k) cs) : cs.length = k + 1 := by
  have nodup : cs.Nodup := reps.2.1.imp (fun blocked equal => blocked (sameComponent_iff_eq.mpr equal))
  have all : cs.toFinset = Finset.univ := Finset.eq_univ_of_forall fun u =>
    (reps.2.2 u (requiredVertices_eq_univ k ▸ Finset.mem_univ _)).elim fun v ⟨member, same⟩ =>
      List.mem_toFinset.mpr ((sameComponent_iff_eq.mp same).symm ▸ member)
  rw [← List.toFinset_card_of_nodup nodup, all, Finset.card_univ, Fintype.card_fin]

theorem pairCost_ge_length {k : ℕ} (ps : List (Vertex k × Vertex k))
    (distinct : ∀ p ∈ ps, p.1 ≠ p.2) : (ps.length : ℝ) ≤ pairCost (network k) ps := by
  induction ps with
  | nil => simp [pairCost]
  | cons p rest ih =>
    have first := distance_ge_one (distinct p List.mem_cons_self)
    have remaining := ih (fun q member => distinct q (List.mem_cons_of_mem p member))
    simpa only [pairCost, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_comm] using
      add_le_add first remaining

theorem consecutive_pairCost (k : ℕ) : pairCost (network k) (consecutivePairs k) = k := by
  simp [pairCost, consecutivePairs, List.map_map, Function.comp_def, consecutive_distance]

theorem consecutive_minimum (k : ℕ) : MinimumComponentTree (instanceAt k) (consecutivePairs k) := by
  refine ⟨consecutive_componentTree k, fun qs qtree => ?_⟩
  obtain ⟨cs, reps, size⟩ := qtree.1
  calc
    _ = (k : ℝ) := consecutive_pairCost k
    _ = (qs.length : ℝ) := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.add_right_cancel (size.trans (reps_length reps))).symm
    _ ≤ _ := pairCost_ge_length qs (fun p member equal =>
      (qtree.2.1 p member).2.2 (sameComponent_iff_eq.mpr equal))

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessTree

/-! sharpness/SharpnessTours.lean -/
section RppSource_SharpnessTours
namespace VehicleRoutingSurvey.Routing.Sharpness

def lastOdd (m : ℕ) : Vertex (2 * m) := ⟨2 * m - 1, by omega⟩

def firstOdd (m : ℕ) (hm : 0 < m) : Vertex (2 * m) := ⟨1, by omega⟩

def riseOne (k : ℕ) (withLoops : Bool) : List (Traversal (network k)) :=
  risingPath (k := k) (lo := 0) (stride := 1) (count := k) (by simp) withLoops

def riseEven (m : ℕ) (withLoops : Bool) : List (Traversal (network (2 * m))) :=
  risingPath (k := 2 * m) (lo := 0) (stride := 2) (count := m) (by simp) withLoops

def riseOdd (m : ℕ) (hm : 0 < m) : List (Traversal (network (2 * m))) :=
  risingPath (k := 2 * m) (lo := 1) (stride := 2) (count := m - 1) (by omega) true

/-- Go forward along the chosen consecutive tree and return using the two-step links. -/
def greedyTour (m : ℕ) : List (Traversal (network (2 * m))) :=
  (riseOne (2 * m) true ++ [(loop (Fin.last (2 * m)), true)]) ++ reverseTraversals (riseEven m false)

/-- Visit even vertices in increasing order and odd vertices in decreasing order. -/
def comparisonTour (m : ℕ) (hm : 0 < m) : List (Traversal (network (2 * m))) :=
  riseEven m true ++ ([(loop (Fin.last (2 * m)), true), (step (lastOdd m), false)] ++
    (reverseTraversals (riseOdd m hm ++ [(loop (lastOdd m), true)]) ++ [(step 0, false)]))

theorem riseOne_path (k : ℕ) (withLoops : Bool) :
    IsPath (network k) 0 (riseOne k withLoops) (Fin.last k) :=
  risingPath_with_endpoints (lo := 0) (stride := 1) (count := k) (by simp) (Or.inl rfl)
    withLoops 0 (Fin.last k) (by simp) (by simp)

theorem riseEven_path (m : ℕ) (withLoops : Bool) :
    IsPath (network (2 * m)) 0 (riseEven m withLoops) (Fin.last (2 * m)) :=
  risingPath_with_endpoints (lo := 0) (stride := 2) (count := m) (by simp) (Or.inr rfl)
    withLoops 0 (Fin.last (2 * m)) (by simp) (by simp)

theorem riseOdd_path (m : ℕ) (hm : 0 < m) :
    IsPath (network (2 * m)) (firstOdd m hm) (riseOdd m hm) (lastOdd m) :=
  risingPath_with_endpoints (lo := 1) (stride := 2) (count := m - 1) (by omega) (Or.inr rfl)
    true (firstOdd m hm) (lastOdd m) rfl (by change 2 * m - 1 = 1 + 2 * (m - 1); omega)

theorem loop_path {k : ℕ} (i : Vertex k) : IsPath (network k) i [(loop i, true)] i := by
  simp [IsPath, start, finish]

theorem step_back_path {k : ℕ} (i : Vertex k) :
    IsPath (network k) (shift 1 i) [(step i, false)] i := by
  simp [IsPath, start, finish]

theorem greedyTour_path (m : ℕ) :
    IsPath (network (2 * m)) 0 (greedyTour m) 0 :=
  isPath_append (isPath_append (riseOne_path (2 * m) true) (loop_path (Fin.last (2 * m))))
    (isPath_reverse (undirected_network (2 * m)) (riseEven_path m false))

private theorem lastOdd_step {m : ℕ} (hm : 0 < m) : shift 1 (lastOdd m) = Fin.last (2 * m) :=
  Fin.ext (by dsimp [shift, lastOdd]; omega)

private theorem firstOdd_step {m : ℕ} (hm : 0 < m) : shift 1 (0 : Vertex (2 * m)) = firstOdd m hm :=
  Fin.ext (by simp [shift, firstOdd]; omega)

theorem comparisonTour_path (m : ℕ) (hm : 0 < m) :
    IsPath (network (2 * m)) 0 (comparisonTour m hm) 0 :=
  isPath_append (riseEven_path m true)
    (isPath_append (isPath_append (loop_path (Fin.last (2 * m)))
      (lastOdd_step hm ▸ step_back_path (lastOdd m)))
      (isPath_append (isPath_reverse (undirected_network (2 * m))
        (isPath_append (riseOdd_path m hm) (loop_path (lastOdd m))))
        (firstOdd_step hm ▸ step_back_path 0)))

@[simp] theorem loop_price {k : ℕ} (i : Vertex k) :
    pathCost (network k) [(loop i, true)] = 0 := by
  simp [pathCost]

@[simp] theorem step_reverse_price {k : ℕ} (i : Vertex k) :
    pathCost (network k) [(step i, false)] = 1 := by
  simp [pathCost]

@[simp] theorem loop_and_step_price {k : ℕ} (i j : Vertex k) :
    pathCost (network k) [(loop i, true), (step j, false)] = 1 := by
  simp [pathCost]

theorem greedyTour_cost (m : ℕ) : pathCost (network (2 * m)) (greedyTour m) = 3 * (m : ℝ) := by
  rw [greedyTour, pathCost_append, pathCost_append, pathCost_reverseTraversals]
  rw [riseOne, riseEven, risingPath_cost, risingPath_cost, loop_price]
  norm_num [Nat.cast_mul]; linarith

theorem comparisonTour_cost (m : ℕ) (hm : 0 < m) :
    pathCost (network (2 * m)) (comparisonTour m hm) = 2 * (m : ℝ) + 1 := by
  rw [comparisonTour, pathCost_append, pathCost_append, pathCost_append, pathCost_reverseTraversals,
    pathCost_append]
  rw [riseEven, riseOdd, risingPath_cost, risingPath_cost, loop_and_step_price, loop_price, step_reverse_price]
  norm_num [Nat.cast_sub (show 1 ≤ m from hm)]; linarith

theorem reverse_contains_loop {k : ℕ} {ts : List (Traversal (network k))} (v : Vertex k)
    (member : (loop v, true) ∈ ts) : (loop v, false) ∈ reverseTraversals ts :=
  List.mem_map_of_mem (List.mem_reverse.mpr member)

theorem comparisonTour_contains_loop (m : ℕ) (hm : 0 < m) (v : Vertex (2 * m)) :
    ∃ direction : Bool, (loop v, direction) ∈ comparisonTour m hm := by
  rcases Nat.mod_two_eq_zero_or_one v.val with even | odd
  case inl =>
    by_cases last : v = Fin.last (2 * m)
    · exact ⟨true, by simp [comparisonTour, last]⟩
    · let i : Fin m := ⟨v.val / 2, by have := v.isLt; have h : v.val ≠ 2 * m := fun eq => last (Fin.ext eq); omega⟩
      let fit : 0 + 2 * m ≤ 2 * m := by omega
      have atV : point fit i.castSucc = v := Fin.ext (by dsimp [point, i]; omega)
      exact ⟨true, List.mem_append_left _ (atV ▸ risingPath_contains_loop fit i)⟩
  case inr =>
    by_cases last : v = lastOdd m
    · exact ⟨false, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (last.symm ▸ reverse_contains_loop (lastOdd m) (List.mem_append_right _ (by simp)))))⟩
    · let i : Fin (m - 1) := ⟨(v.val - 1) / 2, by
        have := v.isLt
        have h : v.val ≠ 2 * m - 1 := fun eq => last (Fin.ext eq)
        omega⟩
      let fit : 1 + 2 * (m - 1) ≤ 2 * m := by omega
      have atV : point fit i.castSucc = v := Fin.ext (by dsimp [point, i]; omega)
      exact ⟨false, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (reverse_contains_loop v (List.mem_append_left _ (atV ▸ risingPath_contains_loop fit i)))))⟩

theorem comparisonTour_feasible (m : ℕ) (hm : 0 < m) :
    Feasible (instanceAt (2 * m)) (0 : Vertex (2 * m)) (comparisonTour m hm) :=
  ⟨comparisonTour_path m hm, Finset.empty_subset _, fun _ required =>
    (required_is_loop required).elim fun v equal =>
      (comparisonTour_contains_loop m hm v).elim fun b present => ⟨(loop v, b), present, equal⟩⟩

theorem comparison_optimum_upper (m : ℕ) (hm : 0 < m) :
    optimum (instanceAt (2 * m)) ≤ 2 * (m : ℝ) + 1 :=
  (optimum_le_feasible (nonnegative_network (2 * m)) (comparisonTour_feasible m hm)).trans_eq
    (comparisonTour_cost m hm)

theorem riseEven_shortest (m : ℕ) :
    ShortestPath (network (2 * m)) 0 (Fin.last (2 * m)) (riseEven m false) := by
  refine ⟨riseEven_path m false, fun ts path => ?_⟩
  have spread := path_displacement path
  rw [riseEven, risingPath_cost]
  norm_num [Fin.val_zero, Fin.val_last, Nat.cast_mul] at spread
  linarith

private theorem start_at_loop {k : ℕ} (t : Traversal (network k)) (i : Vertex k)
    (index : t.1 = loop i) : start (network k) t = i := by
  cases direction : t.2 <;> simp [start, direction, index]

theorem feasibleCost_ge_one {k : ℕ} (positive : 0 < k) {u : Vertex k}
    {ts : List (Traversal (network k))} (tour : Feasible (instanceAt k) u ts) :
    1 ≤ pathCost (network k) ts := by
  by_contra! cheap
  have fixed (v : Vertex k) : v = u := (tour.2.2 (loop v) (loop_required v)).elim fun t hit =>
    (start_at_loop t v hit.2).symm.trans ((cheap_path_constant tour.1 cheap).2 t hit.1)
  exact (Nat.ne_of_gt positive) (by simpa using (congrArg (fun v : Vertex k => v.val)
    ((fixed (Fin.last k)).trans (fixed 0).symm)))

theorem comparison_optimum_lower (m : ℕ) (hm : 0 < m) :
    1 ≤ optimum (instanceAt (2 * m)) :=
  le_csInf ⟨_, 0, comparisonTour m hm, comparisonTour_feasible m hm, rfl⟩
    (fun _ ⟨_, _, tour, cost⟩ => cost.symm ▸ feasibleCost_ge_one (by omega) tour)

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessTours

/-! sharpness/SharpnessMatching.lean -/
section RppSource_SharpnessMatching
namespace VehicleRoutingSurvey.Routing.Sharpness

theorem consecutivePaths_flatten (k : ℕ) : (consecutivePaths k).flatten = riseOne k false := by
  rw [consecutivePaths, List.finRange, List.map_ofFn, riseOne, risingPath]
  simp [Function.comp_def, risingBlock, risingEdge, point, Fin.castSucc]
  rfl

private theorem loop_degree_even {k : ℕ} (v : Vertex k) (vertices : List (Vertex k)) :
    degree (network k) (vertices.map loop) v % 2 = 0 := by
  induction vertices with
  | nil => rfl
  | cons i tail ih =>
    have together : (i :: tail).map loop = [loop i] ++ tail.map loop := rfl
    rw [together, degree_append]
    have singleton : degree (network k) [loop i] v % 2 = 0 := by
      by_cases incident : i = v <;> simp [degree, incident]
    omega

theorem endpoints_distinct {k : ℕ} (positive : 0 < k) : (0 : Vertex k) ≠ Fin.last k := by
  intro equal
  exact (Nat.ne_of_gt positive) (by simpa using congrArg (fun v : Vertex k => v.val) equal.symm)

theorem odd_consecutive {k : ℕ} (positive : 0 < k) :
    oddVertices (network k) (baseLinks k ++ (consecutivePaths k).flatten.map Prod.fst) =
      {0, Fin.last k} := by
  ext v
  rw [oddVertices, Finset.mem_filter, consecutivePaths_flatten, degree_append, Nat.odd_iff]
  have parity := degree_path_mod_two (riseOne_path k false) v
  change _ = ((if (0 : Vertex k) = v then 1 else 0) +
    (if Fin.last k = v then 1 else 0)) % 2 at parity
  have base : degree (network k) (baseLinks k) v % 2 = 0 := loop_degree_even v (List.finRange (k + 1))
  rw [Nat.add_mod, base, parity]
  by_cases left : (0 : Vertex k) = v <;> by_cases right : Fin.last k = v <;> simp [left, right]
  · exact endpoints_distinct positive (left.trans right.symm)
  · exact ⟨Ne.symm left, Ne.symm right⟩

private theorem singleton_perfect {n : ℕ} (a b : Fin n) (distinct : a ≠ b) :
    SupplyChainTheory.IsPerfectMatchingOn {a, b} {s(a, b)} := by
  refine ⟨?_, ?_⟩
  · simp [Sym2.mk_isDiag_iff, distinct, Sym2.mem_iff]
  · intro v member
    exact ⟨s(a, b), ⟨Finset.mem_singleton_self _, Sym2.mem_iff.mpr
      ((Finset.mem_insert.mp member).imp_right Finset.mem_singleton.mp)⟩,
      fun e present => Finset.mem_singleton.mp present.1⟩

private theorem perfect_on_pair_eq_singleton {n : ℕ} (a b : Fin n)
    (M : Finset (Sym2 (Fin n))) (perfect : SupplyChainTheory.IsPerfectMatchingOn {a, b} M) :
    M = {s(a, b)} := by
  have subset : M ⊆ {s(a, b)} := by
    intro e member
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨nonloop, support⟩ := perfect.1 _ member
      have ends : (x = a ∨ x = b) ∧ (y = a ∨ y = b) :=
        ⟨(Finset.mem_insert.mp (support x (Sym2.mem_mk_left x y))).imp_right Finset.mem_singleton.mp,
         (Finset.mem_insert.mp (support y (Sym2.mem_mk_right x y))).imp_right Finset.mem_singleton.mp⟩
      rcases ends with ⟨rfl | rfl, rfl | rfl⟩ <;>
        simp_all [Sym2.mk_isDiag_iff, Sym2.eq_swap]
  exact Finset.Subset.antisymm subset <| (perfect.2 a (by simp)).elim fun e hit _ =>
    Finset.singleton_subset_iff.mpr (Finset.mem_singleton.mp (subset hit.1) ▸ hit.1)

theorem endpoint_matching_minimum {k : ℕ} (positive : 0 < k) :
    MinimumMatching (network k) (baseLinks k ++ (consecutivePaths k).flatten.map Prod.fst)
      [(0, Fin.last k)] := by
  refine ⟨by simp, ?_⟩
  rw [odd_consecutive positive]
  change SupplyChainTheory.IsMinMatchingOn (distance (network k))
    {0, Fin.last k} {s(0, Fin.last k)}
  exact ⟨singleton_perfect 0 (Fin.last k) (endpoints_distinct positive),
    fun M perfect => by rw [perfect_on_pair_eq_singleton 0 (Fin.last k) M perfect]⟩

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessMatching

/-! sharpness/SharpnessPermutation.lean -/
section RppSource_SharpnessPermutation
namespace VehicleRoutingSurvey.Routing.Sharpness

private theorem interleave_perm {α β : Type*} (items : List α) (f g : α → β) :
    (items.flatMap fun a => [f a, g a]).Perm (items.map f ++ items.map g) := by
  induction items with
  | nil => exact .nil
  | cons a rest ih =>
    exact ((ih.cons (g a)).cons (f a)).trans
      ((List.perm_middle (a := g a) (l₁ := rest.map f) (l₂ := rest.map g)).symm.cons (f a))

theorem riseOne_links (k : ℕ) :
    (riseOne k true).map Prod.fst = (List.finRange k).flatMap fun i =>
      [loop i.castSucc, step i.castSucc] := by
  rw [riseOne, risingPath, List.map_flatten, List.map_ofFn, List.flatMap_def, List.finRange, List.map_ofFn]
  simp [Function.comp_def, risingBlock, risingEdge, point, Fin.castSucc]
  rfl

theorem consecutivePaths_links (k : ℕ) :
    (consecutivePaths k).flatten.map Prod.fst = (List.finRange k).map (step ∘ Fin.castSucc) := by
  rw [consecutivePaths, List.map_flatten, List.map_map]
  simp [Function.comp_def, ← List.flatMap_def]
  exact List.flatMap_pure_eq_map _ _

theorem baseLinks_split (k : ℕ) :
    baseLinks k = (List.finRange k).map (loop ∘ Fin.castSucc) ++ [loop (Fin.last k)] := by
  rw [baseLinks, List.finRange_succ_last, List.map_append, List.map_map, List.map_singleton]

theorem reverseLinks_perm {G : Network} (ts : List (Traversal G)) :
    ((reverseTraversals ts).map Prod.fst).Perm (ts.map Prod.fst) := by
  rw [reverseTraversals, List.map_map]
  exact (List.reverse_perm ts).map Prod.fst

theorem beginning_perm (k : ℕ) :
    ((riseOne k true ++ [(loop (Fin.last k), true)]).map Prod.fst).Perm
      (baseLinks k ++ (consecutivePaths k).flatten.map Prod.fst) := by
  rw [List.map_append, List.map_singleton, riseOne_links, baseLinks_split, consecutivePaths_links]
  have grouped := interleave_perm (List.finRange k) (loop ∘ Fin.castSucc) (step ∘ Fin.castSucc)
  exact (grouped.append_right [loop (Fin.last k)]).trans (by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := (List.finRange k).map (step ∘ Fin.castSucc))
        (l₂ := [loop (Fin.last k)])).append_left ((List.finRange k).map (loop ∘ Fin.castSucc)))

theorem greedyTour_perm (m : ℕ) : ((greedyTour m).map Prod.fst).Perm
    (baseLinks (2 * m) ++ (consecutivePaths (2 * m)).flatten.map Prod.fst ++
      (riseEven m false).map Prod.fst) := by
  rw [greedyTour, List.map_append]
  exact (beginning_perm (2 * m)).append (reverseLinks_perm (riseEven m false))

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessPermutation

/-! sharpness/SharpnessRun.lean -/
section RppSource_SharpnessRun
namespace VehicleRoutingSurvey.Routing.Sharpness

theorem greedyTour_run (m : ℕ) (hm : 0 < m) :
    RuralRun (instanceAt (2 * m)) (0 : Vertex (2 * m)) (greedyTour m) := by
  have nonempty : (instanceAt (2 * m)).links ≠ ∅ := fun empty =>
    Finset.notMem_empty (loop (0 : Vertex (2 * m))) (empty ▸ loop_required (0 : Vertex (2 * m)))
  rw [RuralRun, if_neg nonempty]
  exact ⟨baseLinks (2 * m), consecutivePairs (2 * m), [(0, Fin.last (2 * m))],
    consecutivePaths (2 * m), [riseEven m false], baseLinks_nodup _, baseLinks_toFinset _,
    consecutive_minimum _, consecutive_expands _, endpoint_matching_minimum (by omega),
    List.Forall₂.cons (riseEven_shortest m) List.Forall₂.nil, greedyTour_path m,
    by simpa only [List.flatten_singleton] using greedyTour_perm m⟩

/-- Sharpness for the exact run relation, with unbounded vertex count and positive optimum. -/
theorem rpp_sharpness :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
        Rural I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ RuralRun I u ts ∧
        (3 / 2 - ε) * optimum I < pathCost I.graph ts := by
  intro ε positive N
  obtain ⟨m, hm, size, ratio⟩ := choose_halfSpan ε positive N
  refine ⟨instanceAt (2 * m), (0 : Vertex (2 * m)), greedyTour m, rural_instance _, size,
    lt_of_lt_of_le zero_lt_one (comparison_optimum_lower m hm), greedyTour_run m hm, ?_⟩
  rw [greedyTour_cost]
  rcases le_or_gt (3 / 2 - ε : ℝ) 0 with small | large
  · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg small
      (zero_le_one.trans (comparison_optimum_lower m hm))) (by positivity)
  · exact (mul_le_mul_of_nonneg_left (comparison_optimum_upper m hm) large.le).trans_lt ratio

end VehicleRoutingSurvey.Routing.Sharpness
end RppSource_SharpnessRun

/-! RuralGuarantees.lean -/
section RppSource_RuralGuarantees
namespace VehicleRoutingSurvey.Routing

theorem rpp_tree_matching_guarantees (I : Service) (rural : Rural I) :
    (∃ u ts, RuralRun I u ts) ∧
    (∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I) ∧
    (∀ u ts, RuralRun I u ts → Feasible I u ts ∧
      pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I) := by
  have euler (es : List (Fin I.graph.q)) (even : ∀ v, degree I.graph es v % 2 = 0)
      (connected : EdgeSupportConnected I.graph es) (u : Fin I.graph.n)
      (support : EdgeSupport I.graph es u) :
      ∃ ts, IsPath I.graph u ts u ∧ (ts.map Prod.fst).Perm es :=
    exists_euler_traversal rural.2.2.1 even connected u support
  have attained := exists_rural_optimum rural
  exact ⟨exists_ruralRun_of_euler rural euler, attained,
    fun _ _ run => ruralRun_feasible_and_le_optimum rural attained run⟩

/-- The approximation, existence, and sharpness arguments are independent of
the arithmetic-RAM proof for this algorithm. -/
theorem rpp_tree_matching_sharp_of_implementation
    (implementation : ∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N) :
    (∀ I : Service, Rural I →
      (∃ u ts, RuralRun I u ts) ∧
      (∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I) ∧
      (∀ u ts, RuralRun I u ts → Feasible I u ts ∧
        pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
        Rural I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ RuralRun I u ts ∧
        (3 / 2 - ε) * optimum I < pathCost I.graph ts) ∧
    (∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N) :=
  ⟨rpp_tree_matching_guarantees, Sharpness.rpp_sharpness, implementation⟩

end VehicleRoutingSurvey.Routing
end RppSource_RuralGuarantees


