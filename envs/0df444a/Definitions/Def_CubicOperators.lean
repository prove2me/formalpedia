-- Prove2me | Definitions.Def_CubicOperators
-- name    : CubicOperators
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T04:49:48.848979+00:00
-- url     : https://prove2.me/theorems/7906cfea-1856-4574-bcc4-91bb57f8b8e6
-- title:
--   44-coordinate point frame and triangle tightness
-- statement:
--   For a finite graph, the bundle indexes its actual three-cliques and takes each point column from a 44-coordinate matrix Π. IsPointFrame records ΠᵀΠ=27J−9A+I, ΠΠᵀ=63I, Π1=0, and ΠA=−4Π. Each triangle vector is the average of its three point columns; incidence is literal membership, and HasTriangleTightness states that the sum of triangle-vector outer products is 21I.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-operators/CubicOperators.lean#L282, 287-288, 290-292, 299-305, 310-312, 383-385, 387-389, 716-720; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 0f2d54b12bf30488083869062fdc457d5bd73e24c80b6af357d7341c3ad96fed. Canonical generated Definition: Definitions/Def_CubicOperators.lean; generated SHA-256 0929b0ffcf14aae67d9fc5c21c7ad3b97d46be61dfeee511a8b7c228ed0ae31f; Lab Git revision 34ff1647fb2157ca1da38776c83bc9b5a4a0fd8c, path fixtures/generated-project-definitions/Definitions/Def_CubicOperators.lean.

import Mathlib

set_option autoImplicit false

/-! Algebraic contraction lemmas for the graph-owned triangle cubic. The
incidence identities in the hypotheses are the explicit graph bridge. -/

namespace Conway99Formal.CubicOperators

open Finset

variable {T I : Type*} [Fintype T] [Fintype I]





























































end Conway99Formal.CubicOperators

namespace Conway99Formal.CubicOperators.Graph

open Finset

abbrev Coord := Fin 44

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle of the given graph, with its original vertex labels. -/
abbrev Triangle := {T : Finset V // T ∈ G.cliqueFinset 3}

/-- A column of the real point frame of this graph. -/
def pointColumn (Pi : Matrix Coord V ℝ) (u : V) : Coord → ℝ :=
  fun i => Pi i u



/-- The four source equations that make `Pi` the actual `(-4)` point frame. -/
structure IsPointFrame (Pi : Matrix Coord V ℝ) : Prop where
  gram : Pi.transpose * Pi =
    27 • (1 : Matrix V V ℝ) - 9 • G.adjMatrix ℝ + Matrix.of 1
  tight : Pi * Pi.transpose = 63 • (1 : Matrix Coord Coord ℝ)
  zero_sum : Pi.mulVec (fun _ => (1 : ℝ)) = 0
  adjacency : Pi * G.adjMatrix ℝ = -(4 • Pi)



/-- The triangle vector formed from the same frame and graph. -/
noncomputable def triangleVector (Pi : Matrix Coord V ℝ) (T : Triangle G) : Coord → ℝ :=
  fun i => (∑ u ∈ T.1, Pi i u) / 3





/-- Point-triangle incidence in the original graph. -/
def incidence (u : V) (T : Triangle G) : ℝ :=
  if u ∈ T.1 then 1 else 0

/-- Real vertex-triangle incidence matrix of the same graph. -/
def realIncidenceMatrix : Matrix V (Triangle G) ℝ :=
  fun u T => if u ∈ T.1 then 1 else 0

















































/-- The source's `V Vᵀ=21I` in the fixed frame coordinates. -/
def HasTriangleTightness (Pi : Matrix Coord V ℝ) : Prop :=
  ∀ i j : Coord, (∑ T : Triangle G,
    triangleVector G Pi T i * triangleVector G Pi T j) =
      21 * (if i = j then (1 : ℝ) else 0)












end Conway99Formal.CubicOperators.Graph


