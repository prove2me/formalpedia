-- Prove2me | Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
-- name    : WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-27T05:59:38.054527+00:00
-- url     : https://prove2.me/theorems/baaffca9-a968-431e-8a96-334cdf230a55
-- title:
--   Maximal planar supergraph on a fixed vertex type
-- statement:
--   `W` has a planar drawing, contains every edge of `U`, and every planar graph on the same vertex type containing `W` is equal to `W`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

def IsPlanarMaximalSupergraphForEdgeCountCompletion
    {V : Type} [Fintype V] [LinearOrder V]
    (U W : SimpleGraph V) : Prop :=
  HasPlanarDrawingOn W ∧
    (∀ u v, U.Adj u v → W.Adj u v) ∧
    (∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) → X = W)

end WilliamsonShmoys


