-- Prove2me | Definitions.Def_opg401_circular_coloring
-- name    : opg401_circular_coloring
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-07T07:13:37.57771+00:00
-- url     : https://prove2.me/theorems/11e5bd7b-80e3-4a66-b74a-ce450b9791ea
-- title:
--   Circular colorings and straight-line planarity for OPG-401
-- statement:
--   This module fixes the finite graph model for OPG-401. A planar graph is supplied with an injective straight-line drawing in the real plane: no third vertex lies on an edge segment, and segments for nonincident edges are disjoint. Triangle-free and subcubic predicates are literal graph conditions.
--
--   For residues modulo $p$, the circular distance is the shorter of the two directed modular differences. Two colors are $(p,q)$-compatible when their circular distance lies between $q$ and $p-q$, inclusive. A $(p,q)$-coloring assigns compatible residues to every adjacent pair. The module also defines the exact allowed-color set next to a residue for the palette $(20,7)$.
--
--   The definitions include disconnected and empty finite graphs. Values are represented by `Fin p`, and natural subtraction is used only in formulas where the residue representatives make the modular differences well-defined.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-401, https://www.unsolvedmath.com/problems/OPG-401; circular-coloring convention cross-checked with X. Zhu, https://doi.org/10.1016/j.ejc.2011.03.004

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

namespace OPG401

universe u

abbrev Point := ℝ × ℝ

def pointOnSegment (a b : Point) (t : ℝ) : Point :=
  ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)

def closedSegment (a b : Point) : Set Point :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = pointOnSegment a b t}

def openSegment (a b : Point) : Set Point :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = pointOnSegment a b t}

/-- A finite graph is represented as planar by an injective straight-line drawing:
no third vertex lies on an edge, and nonincident edges are disjoint. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ p : V → Point,
    Function.Injective p ∧
    (∀ ⦃a b v : V⦄, G.Adj a b → v ≠ a → v ≠ b → p v ∉ closedSegment (p a) (p b)) ∧
    (∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d →
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Disjoint (closedSegment (p a) (p b)) (closedSegment (p c) (p d)))

/-- The graph contains no triangle. -/
def IsTriangleFree {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj c a

/-- Every vertex has at most three neighbors. -/
def IsSubcubic {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).encard ≤ 3

/-- Shortest cyclic distance between two residues modulo `p`. -/
def circularDistance {p : ℕ} (a b : Fin p) : ℕ :=
  min ((a.val + p - b.val) % p) ((b.val + p - a.val) % p)

/-- The edge constraint for a `(p,q)`-coloring, using shortest cyclic distance. -/
def PQCompatible (p q : ℕ) (a b : Fin p) : Prop :=
  q ≤ circularDistance a b ∧ circularDistance a b ≤ p - q

/-- A `(p,q)`-coloring of a simple graph. -/
def IsPQColoring {V : Type u} (G : SimpleGraph V) (p q : ℕ)
    (color : V → Fin p) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → PQCompatible p q (color u) (color v)

/-- The colors that may be assigned next to a vertex of color `a` in a
`(20,7)`-coloring. -/
noncomputable def allowedColors (a : Fin 20) : Finset (Fin 20) := by
  classical
  exact Finset.univ.filter fun z => PQCompatible 20 7 z a

end OPG401


