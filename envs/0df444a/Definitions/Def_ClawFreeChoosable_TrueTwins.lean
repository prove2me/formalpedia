-- Prove2me | Definitions.Def_ClawFreeChoosable_TrueTwins
-- name    : ClawFreeChoosable_TrueTwins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:41.761373+00:00
-- url     : https://prove2.me/theorems/9fe31bb3-31f3-4908-b90c-5befed4e2c0d
-- title:
--   True twins
-- statement:
--   Two vertices $x, y$ of a graph $G$ are **true twins** if they are adjacent and have equal closed neighbourhoods $N_G[x] = N_G[y]$, where $N_G[v] = N_G(v) \cup \{v\}$.
--
--   True twins appear in the definition of rich clique cutsets and in Lemma 7.3, where the vertices of a clique of simplicial vertices are shown to be pairwise true twins.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §7.1 p.9, "true twins"

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **True twins** (arXiv:2611.01068v1, §7.1 p.9): two adjacent vertices `x, y` with equal closed
neighbourhoods `N[x] = N[y]`, where `N[v] = N(v) ∪ {v}`. -/
def TrueTwins {V : Type} (G : SimpleGraph V) (x y : V) : Prop :=
  G.Adj x y ∧ insert x (G.neighborSet x) = insert y (G.neighborSet y)

end ClawFreeChoosable


