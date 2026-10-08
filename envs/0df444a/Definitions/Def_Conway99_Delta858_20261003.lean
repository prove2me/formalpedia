-- Prove2me | Definitions.Def_Conway99_Delta858_20261003
-- name    : Conway99_Delta858_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T05:56:00.827975+00:00
-- url     : https://prove2.me/theorems/05680ca8-3a0b-4cc6-96c3-be52aa5e8c9c
-- title:
--   Graph-owned triangle and prism census quantities
-- statement:
--   For one finite simple graph, define its actual three-cliques, triangle incidence matrices, and unordered disjoint triangle-pair counts. The quantities delta and prismCount count triangle pairs joined by two and three edges respectively. These definitions impose no census identity or graph existence assumption.
-- source:
--   blob/9c021a134a299e87dfebf9caadaa8163847f0215/research/claude/03-delta858/Delta858/Census.lean; exact frozen GraphCounts.lean and TriangleIncidence.lean Definition closure; independent Lab run-90d19280bc45, body SHA-256 3ee63c43046e067ae71cc7a3a4d44daf2aad8c1a0fafa0b9b12ae775d63fa8a4

import Mathlib
set_option autoImplicit false


set_option autoImplicit false

/-! Literal graph counts for the universal triangle and prism claim. -/

namespace Conway99Formal.TriangleBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual triangles of the given graph, with no chosen labels. -/
def triangles : Finset (Finset V) := G.cliqueFinset 3

/-- Number of edges joining two vertex sets in the given graph. -/
def crossEdgeCount (t u : Finset V) : ℕ := (G.interedges t u).card

/-- Unordered disjoint pairs of triangles joined by `j` edges. -/
noncomputable def disjointTrianglePairCount (j : ℕ) : ℕ := by
  classical
  exact (((triangles G).powersetCard 2).filter
    (fun p => ∃ t u, t ∈ p ∧ u ∈ p ∧ t ≠ u ∧
      Disjoint t u ∧ crossEdgeCount G t u = j)).card

/-- The local number of disjoint triangle partners joined by `j` edges. -/
noncomputable def disjointTrianglePartnerCount (j : ℕ) (t : Finset V) : ℕ := by
  classical
  exact ((triangles G).filter fun u =>
    t ≠ u ∧ Disjoint t u ∧ crossEdgeCount G t u = j).card

/-- The source's `δ`: disjoint triangle pairs with two joining edges. -/
noncomputable def delta : ℕ := disjointTrianglePairCount G 2

/-- The source's `q`: unordered triangular-prism triangle pairs. -/
noncomputable def prismCount : ℕ := disjointTrianglePairCount G 3

end Conway99Formal.TriangleBound


/-!
Graph-owned triangle incidence for the Conway parameter set.

The source statements are `Conway99/Conway99/Core.lean` (Line and Obligation
namespaces) and `proofs/FOUNDATIONS.md` in the September proof library. All
objects below use one literal finite graph. The SRG hypothesis forces its vertex count to 99.
-/

namespace Conway99Formal.TriangleIncidence

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual three-cliques of the graph. -/
abbrev Triangle := {T : Finset V // T ∈ G.cliqueFinset 3}

/-- The point by triangle incidence matrix. -/
def Ninc : Matrix V (Triangle G) ℤ :=
  fun v T => if v ∈ T.1 then 1 else 0

/-- The same literal incidence matrix over the reals. -/
def NincReal : Matrix V (Triangle G) ℝ :=
  fun v T => if v ∈ T.1 then 1 else 0

/-- The overlap matrix derived from this graph's actual triangle incidence. -/
def Bblk : Matrix (Triangle G) (Triangle G) ℤ :=
  (Ninc G)ᵀ * Ninc G - 3 • 1

/-- The actual triangles containing both indicated points. -/
def edgeTriangles (x y : V) : Finset (Triangle G) :=
  Finset.univ.filter fun T => x ∈ T.1 ∧ y ∈ T.1

/-- Other triangles through one point of a fixed triangle. -/
def triangleStar (T : Triangle G) (v : V) : Finset (Triangle G) :=
  Finset.univ.filter fun S => S ≠ T ∧ v ∈ S.1

/-- The source's triangle Gram matrix on the actual triangle carrier. -/
def Gtri : Matrix (Triangle G) (Triangle G) ℤ :=
  21 • 1 + 4 • Bblk G - (Bblk G) ^ 2 + of 1

/-- The same graph-owned triangle Gram over characteristic zero. -/
def GtriRat : Matrix (Triangle G) (Triangle G) ℚ :=
  (Gtri G).map (Int.castRingHom ℚ)

end Conway99Formal.TriangleIncidence


