-- Prove2me | Definitions.Def_Hypercube
-- name    : Hypercube
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-23T04:00:13.004394+00:00
-- url     : https://prove2.me/theorems/f9149c19-cc44-485f-921a-80b77ce1287b
-- statement:
--   The n-dimensional Boolean hypercube Q_n (vertices = Fin n → Bool) with adjacency (differ in exactly one coordinate) and the degree of a vertex within a subset. See Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# The n-dimensional hypercube

Basic combinatorial definitions for the n-dimensional Boolean hypercube `Qₙ`, with
vertices `Fin n → Bool`. We define adjacency (differing in exactly one coordinate) and
the degree of a vertex within a subset.
-/

namespace Hypercube

/-- Two vertices of the n-dimensional hypercube `Qₙ` (functions `Fin n → Bool`) are
    adjacent iff they differ in exactly one coordinate. -/
def Adj (n : ℕ) (u v : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => u i ≠ v i).card = 1

instance Adj.decidable (n : ℕ) (u v : Fin n → Bool) : Decidable (Adj n u v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The degree of a vertex `v` within a subset `S` of the hypercube: the number of
    vertices in `S` adjacent to `v`. -/
def degreeIn (n : ℕ) (S : Finset (Fin n → Bool)) (v : Fin n → Bool) : ℕ :=
  (S.filter fun u => Adj n u v).card

end Hypercube


