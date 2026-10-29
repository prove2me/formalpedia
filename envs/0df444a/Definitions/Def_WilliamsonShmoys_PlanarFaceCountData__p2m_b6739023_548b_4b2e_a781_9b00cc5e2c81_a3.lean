-- Prove2me | Definitions.Def_WilliamsonShmoys_PlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
-- name    : WilliamsonShmoys_PlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-28T22:51:55.342365+00:00
-- url     : https://prove2.me/theorems/89b5f9bb-3f30-4017-ae6f-bd1c589097c5
-- title:
--   Finite face-count certificate
-- statement:
--   There are q faces with natural-number boundary lengths, each at least three; their total length is twice the edge count, and the vertex count plus q equals the edge count plus two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

def HasPlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (q : ℕ) (length : Fin q → ℕ),
    (∀ f, 3 ≤ length f) ∧
    (∑ f, length f = 2 * G.edgeSet.ncard) ∧
    (Fintype.card V + q = G.edgeSet.ncard + 2)

end WilliamsonShmoys


