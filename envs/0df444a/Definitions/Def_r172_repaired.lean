-- Prove2me | Definitions.Def_r172_repaired
-- name    : r172_repaired
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T01:56:34.836423+00:00
-- url     : https://prove2.me/theorems/8b0075fd-cba1-4b6d-bddf-0e7cffc63df9
-- title:
--   R172 conditional transition packet
-- statement:
--   Defines the explicit conditional R170–R171 packet data for one actual graph, its support and zero-support common-neighbor counts, graph-owned core-connector predicate, and induced-square predicate. Packet construction from the uniform-empty branch remains a separate open obligation.
-- source:
--   Conway99/results/R172_uniform_empty_active_transition_squares.md (SHA-256 983d75aa77e82152d4eb32655c8e05a6f00e81d082877fa69d80b668f529ef85); formalization/2026-10-03/r172-repaired/R172Repaired.lean at a45708acebe3f397faccb1b646be906f24f23ee5 (Git blob 581e8b0a310649acd6868745deb8cabcbc55026c). Finite replay: replays/odd-cross-lift/UNIFORM_EMPTY_ACTIVE_TRANSITION_SQUARE_CHECK.py. The result is conditional on an explicit R170–R171 Transition packet.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.R172Repaired

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices outside the fixed triangle and its signed support. -/
def zeroSupport (S T : Finset V) : Finset V := Finset.univ \ (S ∪ T)

/-- Common graph neighbors of the two selected outer vertices. -/
def common (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : Finset V :=
  (G.commonNeighbors a b).toFinset

/-- Conditional R170–R171 packet data for one moved point in one actual graph. -/
structure Transition (G : SimpleGraph V) [DecidableRel G.Adj] where
  support : Finset V
  triangle : Finset V
  support_card : support.card = 36
  triangle_card : triangle.card = 3
  zero_card : (zeroSupport support triangle).card = 60
  support_triangle_disjoint : Disjoint support triangle
  triangle_clique : ∀ x ∈ triangle, ∀ y ∈ triangle, x ≠ y → G.Adj x y
  centre : V
  left : V
  right : V
  centre_support : centre ∈ support
  centre_left : G.Adj centre left
  centre_right : G.Adj centre right
  outer_nonadj : ¬ G.Adj left right
  outer_distinct : left ≠ right
  left_zero : left ∈ zeroSupport support triangle
  right_zero : right ∈ zeroSupport support triangle
  row_codegree_cap : ∀ x ∈ support, x ≠ centre →
    ((zeroSupport support triangle).filter
      (fun w => G.Adj centre w ∧ G.Adj x w)).card ≤ 2
  no_triangle_common : ∀ x ∈ triangle, x ∉ common G left right
  zero_transport : ∀ x ∈ common G left right,
    x ∈ zeroSupport support triangle → ¬ G.Adj centre x
  second_support_nonadj : ∀ x ∈ common G left right,
    x ∈ support → x ≠ centre → ¬ G.Adj centre x

namespace Transition

variable {G : SimpleGraph V} [DecidableRel G.Adj] (p : Transition G)

/-- Number of common neighbors in the support. -/
def q : ℕ := ((common G p.left p.right) ∩ p.support).card

/-- Common neighbors outside the support. -/
def wCommon : Finset V := common G p.left p.right \ p.support

/-- The support column of a zero-support vertex in the same graph. -/
def supportColumn (x : V) : Finset V := p.support.filter (G.Adj x)

/-- A graph-owned two-edge connector with disjoint support columns. -/
def coreConnector (x : V) : Prop :=
  x ∈ zeroSupport p.support p.triangle ∧
  G.Adj p.left x ∧ G.Adj p.right x ∧
  Disjoint (p.supportColumn p.left) (p.supportColumn x) ∧
  Disjoint (p.supportColumn p.right) (p.supportColumn x)

/-- The ordered four vertices form an induced square. -/
def inducedSquare (x : V) : Prop :=
  p.centre ≠ p.left ∧ p.left ≠ x ∧ x ≠ p.right ∧ p.right ≠ p.centre ∧
  p.centre ≠ x ∧ p.left ≠ p.right ∧
  G.Adj p.centre p.left ∧ G.Adj p.left x ∧
  G.Adj x p.right ∧ G.Adj p.right p.centre ∧
  ¬ G.Adj p.centre x ∧ ¬ G.Adj p.left p.right

end Transition
end Conway99Formal.R172Repaired


