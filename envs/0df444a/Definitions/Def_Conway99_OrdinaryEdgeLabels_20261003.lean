-- Prove2me | Definitions.Def_Conway99_OrdinaryEdgeLabels_20261003
-- name    : Conway99_OrdinaryEdgeLabels_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T02:07:37.329426+00:00
-- url     : https://prove2.me/theorems/eae33b09-24e9-4746-8777-84db569ba9f3
-- title:
--   Graph-owned ordinary edge-label interfaces
-- statement:
--   Definitions for conditional ordinary-edge arguments over one hypothetical SRG(99,14,1,2): literal graph triangles, one common cubic and its operators, point and lattice data, and explicit unproved minimum/coset bridge fields. No ordinary vertex or graph existence follows from these definitions.
-- source:
--   archive/clean-start/proof-library.zip members proofs/ROOTLESS_MINIMUM_DYADS.md and proofs/MINIMUM_EDGE_LABEL_COMPATIBILITY.md; exact member hashes and open bridges in claims.json.

import Mathlib

set_option autoImplicit false

/-! Graph-owned interfaces for the ordinary edge-discrepancy argument. -/

namespace Conway99Formal.OrdinaryEdgeLabels

abbrev Space := EuclideanSpace ℝ (Fin 44)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual point pairing, expressed in the graph's vertex coordinates. -/
def pointPair (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℤ :=
  if a = b then 28 else if G.Adj a b then -8 else 1

/-- The literal three-cliques of the same graph. -/
def IsTriangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b

noncomputable def triangles (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter (IsTriangle G)

noncomputable def triangleVector (point : V → Space) (T : Finset V) : Space :=
  (1 / 3 : ℝ) • T.sum point

/-- Data from one graph, one point frame, and one common cubic. The fields after
`owned` are the still-unformalized lattice and minimum-frame bridges. -/
structure OrdinaryData (G : SimpleGraph V) [DecidableRel G.Adj] where
  srg : G.IsSRGWith 99 14 1 2
  point : V → Space
  cubic : Space → Space → Space → ℝ
  cubic_graph_owned : ∀ x y z,
    cubic x y z = (triangles G).sum (fun T =>
      inner ℝ x (triangleVector point T) *
      inner ℝ y (triangleVector point T) *
      inner ℝ z (triangleVector point T))
  op : V → Space →ₗ[ℝ] Space
  owned : ∀ u x y, inner ℝ (op u x) y = -(cubic (point u) x y) / 3
  ordinary : V
  ordinary_trace_sq :
    LinearMap.trace ℝ Space ((op ordinary).comp (op ordinary)) = 44
  point_gram : ∀ a b, inner ℝ (point a) (point b) = (pointPair G a b : ℝ)
  triangleLattice : AddSubgroup Space
  startingLattice : AddSubgroup Space
  triangle_le_starting : triangleLattice ≤ startingLattice
  point_in_triangle_lattice : ∀ v, point v ∈ triangleLattice
  op_preserves_triangle_lattice : ∀ u x,
    x ∈ triangleLattice → op u x ∈ triangleLattice
  divided_point_difference_in_starting : ∀ a b,
    (1 / 3 : ℝ) • (point a - point b) ∈ startingLattice
  image_norm : ∀ v,
    inner ℝ (op ordinary (point v)) (op ordinary (point v)) = 28
  discrepancy : V → V → ℤ
  discrepancy_symm : ∀ a b, discrepancy a b = discrepancy b a
  image_edge_pairing : ∀ a b, G.Adj a b →
    inner ℝ (op ordinary (point a)) (op ordinary (point b)) =
      -8 + 9 * (discrepancy a b : ℝ)
  triangle_balance : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
    discrepancy a b + discrepancy b c + discrepancy c a = 0
  edge_lower : ∀ a b, G.Adj a b → -1 ≤ discrepancy a b
  vertex_balance : ∀ a,
    (Finset.univ.filter (G.Adj a)).sum (discrepancy a) = 0
  labelPair : V → V → V → ℤ
  label_pairing : ∀ a b v, G.Adj a b → discrepancy a b = -1 →
    inner ℝ (-(op ordinary (point a) + op ordinary (point b))) (point v) =
      (labelPair a b v : ℝ)
  label_values : ∀ a b v, G.Adj a b → discrepancy a b = -1 →
    labelPair a b v = -2 ∨ labelPair a b v = 7
  label_independent : ∀ a b v w, G.Adj a b → discrepancy a b = -1 →
    G.Adj v w → labelPair a b v = 7 → labelPair a b w = 7 → False
  label_at_ordinary : ∀ a b, G.Adj a b → discrepancy a b = -1 →
    labelPair a b ordinary =
      -(pointPair G ordinary a + pointPair G ordinary b)
  endpoint_pairings : ∀ a b, G.Adj a b → discrepancy a b = -1 →
    ∃ κ : ℤ,
      labelPair a b a = -pointPair G ordinary a - κ ∧
      labelPair a b b = -pointPair G ordinary b - κ

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The image of an original point under the one ordinary operator. -/
def image (d : OrdinaryData G) (v : V) : Space := d.op d.ordinary (d.point v)

/-- The actual vector attached to a negative edge. -/
def labelVector (d : OrdinaryData G) (a b : V) : Space :=
  -(image d a + image d b)

/-- The divided difference used by the repeated-label argument. -/
noncomputable def repeatedKernelVector (d : OrdinaryData G) (a b c e : V) : Space :=
  (1 / 3 : ℝ) • (d.point a + d.point b - d.point c - d.point e)

end Conway99Formal.OrdinaryEdgeLabels


