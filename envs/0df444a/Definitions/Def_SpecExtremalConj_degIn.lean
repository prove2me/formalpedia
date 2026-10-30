-- Prove2me | Definitions.Def_SpecExtremalConj_degIn
-- name    : SpecExtremalConj_degIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:03.542669+00:00
-- url     : https://prove2.me/theorems/8473b5d3-5b33-4edf-9f73-17bbf3e41692
-- title:
--   Degree into a set: $d_S(v)=|N(v)\cap S|$
-- statement:
--   For a graph $G$, a vertex $v$ and a set $S$ of vertices, the **degree of $v$ into $S$** is
--
--   $$d_S(v)=|N_S(v)|=|N_G(v)\cap S|,$$
--
--   the number of neighbours of $v$ that lie in $S$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §2, p. 2 ("For S ⊆ V(G) and v ∈ V(G), let d_S(v) = |N_S(v)| = |N_G(v) ∩ S|")

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **d_S(v), the degree of v into S.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §2, p. 2 (unnumbered): "For S ⊆ V(G) and v ∈ V(G),
let d_S(v) = |N_S(v)| = |N_G(v) ∩ S|."

`degIn G S v` is the number of neighbours of `v` in `G` that lie in `S`. -/
def degIn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : ℕ :=
  #(G.neighborFinset v ∩ S)

end SpecExtremalConj


