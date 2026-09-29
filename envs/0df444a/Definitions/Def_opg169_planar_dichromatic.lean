-- Prove2me | Definitions.Def_opg169_planar_dichromatic
-- name    : opg169_planar_dichromatic
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-08T05:04:52.911152+00:00
-- url     : https://prove2.me/theorems/9a392f52-f2de-40b9-91c2-1d4164458bfe
-- title:
--   Planar orientations, directed cycles, and acyclic two-colorings
-- statement:
--   This module couples a binary directed relation to an underlying finite simple graph by requiring exactly one direction on every edge and no arcs on nonedges. Planarity is represented by an injective crossing-free straight-line drawing of the underlying graph.
--
--   A directed cycle is a cyclic list of at least three distinct vertices following directed arcs. A two-coloring is valid when neither full induced color class contains such a cycle; colors may be unused. Strong connectivity uses nonempty reflexive-transitive directed reachability.
--
--   A least-order counterexample is planar, uncolorable, and smaller than every other uncolorable planar orientation in the same universe. The module also defines the underlying minimum-degree-three condition.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-169, https://www.unsolvedmath.com/problems/OPG-169; critical-digraph comparison: Mohar, Eigenvalues and colorings of digraphs, Section 2, https://www.sfu.ca/~mohar/Reprints/Inprint/BM09_LAA09_Mohar_EigenvaluesandColorings.pdf

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card

namespace OPG169

universe u

abbrev Digraph (V : Type u) := V → V → Prop
abbrev Point := ℝ × ℝ

def pointOnSegment (a b : Point) (t : ℝ) : Point :=
  ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)

def closedSegment (a b : Point) : Set Point :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = pointOnSegment a b t}

/-- A straight-line planar embedding of the underlying simple graph. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ p : V → Point,
    Function.Injective p ∧
    (∀ ⦃a b v : V⦄, G.Adj a b → v ≠ a → v ≠ b → p v ∉ closedSegment (p a) (p b)) ∧
    (∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d →
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Disjoint (closedSegment (p a) (p b)) (closedSegment (p c) (p d)))

/-- `D` chooses exactly one direction for every edge of `G` and no arcs for
nonedges. -/
def IsOrientationOf {V : Type u} (D : Digraph V) (G : SimpleGraph V) : Prop :=
  (∀ v : V, ¬ D v v) ∧
  (∀ ⦃u v : V⦄, D u v → G.Adj u v) ∧
  ∀ ⦃u v : V⦄, G.Adj u v →
    (D u v ∨ D v u) ∧ ¬ (D u v ∧ D v u)

/-- A list of at least two distinct vertices joined cyclically by directed
arcs. In an orientation of a simple graph such a cycle necessarily has at
least three vertices. -/
def IsDirectedCycle {V : Type u} (D : Digraph V) (vs : List V) : Prop :=
  ∃ x y : V, ∃ middle : List V,
    vs = x :: (middle ++ [y]) ∧ 3 ≤ vs.length ∧
    vs.Nodup ∧ vs.Chain' D ∧ D y x

/-- The vertices of one color induce an acyclic digraph. -/
def ColorClassAcyclic {V : Type u} (D : Digraph V)
    (color : V → Fin 2) (k : Fin 2) : Prop :=
  ¬ ∃ vs : List V,
    IsDirectedCycle D vs ∧ ∀ v ∈ vs, color v = k

/-- A two-coloring in which both full induced color classes are acyclic.
Either color may be unused. -/
def IsAcyclicTwoColoring {V : Type u} (D : Digraph V)
    (color : V → Fin 2) : Prop :=
  ∀ k : Fin 2, ColorClassAcyclic D color k

def HasAcyclicTwoColoring {V : Type u} (D : Digraph V) : Prop :=
  ∃ color : V → Fin 2, IsAcyclicTwoColoring D color

/-- Nonempty strong connectivity under directed reachability. -/
def IsStronglyConnected {V : Type u} (D : Digraph V) : Prop :=
  Nonempty V ∧ ∀ u v : V, Relation.ReflTransGen D u v

/-- A counterexample of least vertex order among all finite planar
orientations in the same universe. -/
def IsLeastOrderCounterexample {V : Type u} [Fintype V]
    (G : SimpleGraph V) (D : Digraph V) : Prop :=
  IsPlanar G ∧ IsOrientationOf D G ∧ ¬ HasAcyclicTwoColoring D ∧
  ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (E : Digraph W),
    IsPlanar H → IsOrientationOf E H →
    Fintype.card W < Fintype.card V → HasAcyclicTwoColoring E

/-- Every vertex of the underlying graph has degree at least three. -/
def HasMinimumDegreeThree {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ v : V, 3 ≤ (G.neighborSet v).encard

end OPG169


