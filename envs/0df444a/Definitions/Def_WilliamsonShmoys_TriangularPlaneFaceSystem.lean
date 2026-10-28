-- Prove2me | Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
-- name    : WilliamsonShmoys_TriangularPlaneFaceSystem
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-26T06:41:14.677776+00:00
-- url     : https://prove2.me/theorems/559e26e0-5bd5-4b35-b703-c4bb9bf70df2
-- title:
--   Triangular plane face system
-- statement:
--   A finite multiset of triangular vertex sets in which each face’s distinct vertices are adjacent, each graph edge belongs to exactly two faces, and the vertex-face and edge counts satisfy Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
namespace WilliamsonShmoys

def HasTriangularPlaneFaceSystem {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  exists faces : Multiset (Finset V),
    (forall f, f ∈ faces -> f.card = 3) ∧
    (forall f, f ∈ faces -> forall u, u ∈ f -> forall v, v ∈ f -> u ≠ v -> G.Adj u v) ∧
    (forall u v, G.Adj u v -> (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) ∧
    Fintype.card V + faces.card = G.edgeSet.ncard + 2

end WilliamsonShmoys


