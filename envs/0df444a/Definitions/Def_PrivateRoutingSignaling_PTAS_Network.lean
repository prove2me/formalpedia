-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Network
-- name    : PrivateRoutingSignaling_PTAS_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:51:21.817775+00:00
-- url     : https://prove2.me/theorems/9765aed5-62e6-4631-a8c7-8b13fb770ee4
-- title:
--   Directed routing paths, real simplex flows, and uniform grids
-- statement:
--   A routing network has finitely many labelled directed arcs, a source, a sink, and an integer path-length bound $d$. Its graph carrier is the published directed multigraph, with parallel arcs and cycles permitted. The path family is generated from the graph: composable arc lists with no repeated vertex and length at most $d$. Network validity requires a path to exist and every simple source-sink path to have length at most $d$, so the enumeration includes all the paper's paths, and it is the same list for every valid bound. The maximum enumerated path length is also defined; it is the paper's $d$ of Theorem 1.1. Coincident terminals admit the empty path.
--
--   A real unit-demand flow is a vector $s_p\ge0$ with
--
--   $$\sum_{p\in P}s_p=1,\qquad x_i(s)=\sum_{p\ni i}s_p.$$
--
--   The simplex inherits its Borel structure from the finite real coordinate space. For integer $k$, grid points are integer path-count vectors of total $k$; their real traffic is the count divided by $k$. The grid-to-flow construction requires $k>0$ and proves its domain condition. Finite distributions use arbitrary real nonnegative weights summing to one.
--
--   These definitions provide one shared graph and flow layer for the two rounding lemmas and the signaling algorithm. The published routing functions supply arc loads; the graph's incidence is exactly zero or one.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), §2.1, p. 5 (PDF p. 5); §3.1, pp. 9–10 (PDF pp. 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_SelfishRouting_Bicriteria_Model

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS

/-- Raw graph input, with labelled arcs (parallel arcs and cycles are allowed).
`d` is a supplied upper bound, not an explicitly supplied list of paths. -/
structure RoutingNetwork where
  vertices : ℕ
  arcs : ℕ
  graph : AtomicDynRouting.ResidenceTime.Network (Fin vertices) (Fin arcs)
  source : Fin vertices
  sink : Fin vertices
  d : ℕ

/-- Vertices of a walk, including its initial vertex. -/
def visited (N : RoutingNetwork) (p : List (Fin N.arcs)) : List (Fin N.vertices) :=
  N.source :: p.map N.graph.head

/-- All vertex-simple directed source-sink paths, including [] when the terminals coincide. -/
def SimplePath (N : RoutingNetwork) (p : List (Fin N.arcs)) : Prop :=
  N.graph.IsPathFrom N.source N.sink p ∧ (visited N p).Nodup

/-- Executable enumeration of all words of length at most b over the arc alphabet. -/
def arcWords (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | b + 1 => [] :: (List.finRange n).flatMap (fun e => (arcWords n b).map (e :: ·))

instance simplePathDecidable (N : RoutingNetwork) (p : List (Fin N.arcs)) :
    Decidable (SimplePath N p) := by
  unfold SimplePath
  have decWalk : ∀ (u w : Fin N.vertices) (q : List (Fin N.arcs)),
      Decidable (N.graph.IsPathFrom u w q) := by
    intro u w q
    induction q generalizing u with
    | nil => exact inferInstanceAs (Decidable (u = w))
    | cons e q ih =>
      unfold AtomicDynRouting.ResidenceTime.Network.IsPathFrom
      exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (N.graph.tail e = u)))
        (ih (N.graph.head e))
  exact @instDecidableAnd _ _ (decWalk _ _ _) inferInstance

/-- Enumeration comes from the graph. No path list is input data. -/
def pathList (N : RoutingNetwork) : List (List (Fin N.arcs)) :=
  (arcWords N.arcs N.d).filter (fun p => decide (SimplePath N p))

abbrev Path (N : RoutingNetwork) := Fin (pathList N).length

/-- The maximum number of arcs on an enumerated simple source-sink path (Theorem 1.1's `d`),
computed from the graph. On a valid network it is at most the bound `N.d`, and the enumeration
`pathList N` does not depend on which valid bound is used. -/
def maxPathLength (N : RoutingNetwork) : ℕ :=
  ((pathList N).map List.length).foldr max 0

def pathArcs (N : RoutingNetwork) (p : Path N) : List (Fin N.arcs) :=
  (pathList N).get p

def NetworkValid (N : RoutingNetwork) : Prop :=
  (∃ p, SimplePath N p) ∧ ∀ p, SimplePath N p → p.length ≤ N.d

def incidence (N : RoutingNetwork) (i : Fin N.arcs) (p : Path N) : ℝ :=
  if i ∈ pathArcs N p then 1 else 0

/-- Unit demand with arbitrary real coordinates. -/
def IsFlow (N : RoutingNetwork) (s : Path N → ℝ) : Prop :=
  (∀ p, 0 ≤ s p) ∧ ∑ p, s p = 1

abbrev Flow (N : RoutingNetwork) := {s : Path N → ℝ // IsFlow N s}

/-- Inherited Borel space of the actual simplex, rather than a discrete topology. -/
instance flowMeasurable (N : RoutingNetwork) : MeasurableSpace (Flow N) := borel (Flow N)
instance flowBorel (N : RoutingNetwork) : BorelSpace (Flow N) := ⟨rfl⟩

def arcLoad (N : RoutingNetwork) (s : Path N → ℝ) (i : Fin N.arcs) : ℝ :=
  KellyStochasticNetworks.linkFlow (incidence N) s i

/-- All k-uniform flows, indexed injectively by their integer path counts. -/
abbrev Grid (N : RoutingNetwork) (k : ℕ) :=
  {a : Path N → Fin (k + 1) // ∑ p, (a p).val = k}

instance gridFintype (N : RoutingNetwork) (k : ℕ) : Fintype (Grid N k) :=
  inferInstanceAs (Fintype {a : Path N → Fin (k + 1) // ∑ p, (a p).val = k})

noncomputable def gridVector (N : RoutingNetwork) (k : ℕ) (a : Grid N k) (p : Path N) : ℝ :=
  ((a.val p).val : ℝ) / k

/-- A real-valued probability mass function on a finite carrier. -/
def FiniteLaw {α : Type} [Fintype α] (w : α → ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1

/-- Structural domain fact: a grid point is a unit-demand real flow when k > 0. -/
theorem grid_isFlow (N : RoutingNetwork) (k : ℕ) (hk : 0 < k) (a : Grid N k) :
    IsFlow N (gridVector N k a) := by
  constructor
  · intro p
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · unfold gridVector
    rw [← Finset.sum_div]
    have hs : (∑ p, ((a.val p).val : ℝ)) = (k : ℝ) := by
      exact_mod_cast a.property
    rw [hs, div_self (by exact_mod_cast (Nat.ne_of_gt hk))]

noncomputable def gridFlow (N : RoutingNetwork) (k : ℕ) (hk : 0 < k) (a : Grid N k) : Flow N :=
  ⟨gridVector N k a, grid_isFlow N k hk a⟩

end PrivateRoutingSignaling.PTAS


