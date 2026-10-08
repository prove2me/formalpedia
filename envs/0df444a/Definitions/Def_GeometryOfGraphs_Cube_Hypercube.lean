-- Prove2me | Definitions.Def_GeometryOfGraphs_Cube_Hypercube
-- name    : GeometryOfGraphs_Cube_Hypercube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:52.844775+00:00
-- url     : https://prove2.me/theorems/866c1673-962a-4713-b282-1bc3075a7756
-- title:
--   The m-dimensional cube graph
-- statement:
--   The $m$-cube has the binary strings of length $m$ as vertices. Two strings are adjacent exactly when they differ in one coordinate:
--
--   $$
--   x\sim y\quad\Longleftrightarrow\quad |\{k:x_k\ne y_k\}|=1.
--   $$
--
--   Its graph distance is the Hamming distance. This graph is the subject of Corollary 5.12.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, Corollary 5.12 and proof; https://doi.org/10.1007/BF01200757

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- The graph on binary strings of length `m`, with edges at Hamming distance one. -/
def hypercube (m : ℕ) : SimpleGraph (Fin m → Bool) where
  Adj x y := hammingDist x y = 1
  symm := ⟨by
    intro x y h
    simpa only [hammingDist_comm] using h⟩
  loopless := ⟨by
    intro x h
    simp only [hammingDist_self] at h
    omega⟩

end GeometryOfGraphs.Cube


