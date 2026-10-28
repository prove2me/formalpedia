-- Prove2me | Definitions.Def_WilliamsonShmoys_TriangularEulerCertificate
-- name    : WilliamsonShmoys_TriangularEulerCertificate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T13:55:05.200891+00:00
-- url     : https://prove2.me/theorems/cd06df05-9bec-4e9b-9582-ad4efa89b218
-- title:
--   Triangular Euler certificate
-- statement:
--   There is a finite family of face boundaries, each consisting of three graph edges, every graph edge occurs in exactly two boundaries, and the numbers of vertices, boundaries, and edges satisfy Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

def HasTriangularEulerCertificate {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (boundary : Fin m → Finset U.edgeSet),
    (∀ f, (boundary f).card = 3) ∧
    (∀ e : U.edgeSet, (∑ f : Fin m, (if e ∈ boundary f then 1 else 0)) = 2) ∧
    Fintype.card V + m = U.edgeSet.ncard + 2

end WilliamsonShmoys


