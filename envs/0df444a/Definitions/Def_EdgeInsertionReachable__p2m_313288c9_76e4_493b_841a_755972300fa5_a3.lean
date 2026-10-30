-- Prove2me | Definitions.Def_EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
-- name    : EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:49.400281+00:00
-- url     : https://prove2.me/theorems/a44463f7-d602-47fc-8ad2-60a0a6171dca
-- title:
--   Finite edge-insertion reachability
-- statement:
--   This relation records a finite sequence from `⊥` to a graph built by inserting edges. Every inserted edge belongs to `G` and was absent from the current graph; endpoints need not be ordered in the relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations

inductive EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3 {V : Type} (G : SimpleGraph V) : SimpleGraph V → Prop where
  | empty : EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3 G ⊥
  | insert {K : SimpleGraph V} {u v : V}
      (reachable : EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3 G K)
      (subgraph : K ≤ G) (ambientEdge : G.Adj u v)
      (absent : ¬ K.Adj u v) :
      EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3 G
        (K ⊔ SimpleGraph.edge u v)


