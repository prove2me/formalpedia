-- Prove2me | Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate
-- name    : WilliamsonShmoys_MaximalPlanarEulerCertificate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T03:09:14.521141+00:00
-- url     : https://prove2.me/theorems/70f6f63f-5e83-43cc-8c08-6d087f8e8364
-- title:
--   Euler and triangular-incidence certificate for a planar graph
-- statement:
--   A graph has this certificate when some natural face count satisfies Euler’s equation and triangular face-edge incidence, with vertex and edge counts interpreted as integers.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

def HasMaximalPlanarEulerCertificate {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) : Prop :=
  ∃ f : ℕ,
    (Fintype.card V : ℤ) - (W.edgeSet.ncard : ℤ) + (f : ℤ) = 2 ∧
    (3 : ℤ) * (f : ℤ) = 2 * (W.edgeSet.ncard : ℤ)

end WilliamsonShmoys


