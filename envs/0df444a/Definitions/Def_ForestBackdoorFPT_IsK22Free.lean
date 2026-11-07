-- Prove2me | Definitions.Def_ForestBackdoorFPT_IsK22Free
-- name    : ForestBackdoorFPT_IsK22Free
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:22.796749+00:00
-- url     : https://prove2.me/theorems/da7e068a-df44-4ca8-8ecd-bcb687da18b3
-- title:
--   $K_{2,2}$-free graphs
-- statement:
--   A graph is **$K_{2,2}$-free** if it contains no copy of $K_{2,2}$, that is, no two distinct vertices $a,b$ and two distinct vertices $c,e$ such that all four edges $ac,ae,bc,be$ are present. In a bipartite incidence graph such a copy is a four-cycle through two variables and two clauses.
--
--   $K_{2,2}$-freeness is the hypothesis under which strong forest backdoors are characterized by cycle killers (Lemma 4.4); Lemmas 4.9 and 4.10 find and eliminate copies of $K_{2,2}$.
--
--   **Formalization Note** The copy need not be induced. Because a simple graph has no loops, the four vertices of such a configuration are automatically pairwise distinct.
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §4.1, pp.13–14 (PDF pp.14–15); Lemma 4.9, p.20 (PDF p.21)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- A graph is **`K_{2,2}`-free** (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to Forests is FPT*,
STOC 2027 submission (manuscript sha256 7fd1a7a8…), §4.1, pp.13–14 and Lemma 4.9, p.20) if it
contains no copy of `K_{2,2}`, i.e. no two distinct vertices `a, b` and two distinct vertices
`c, e` with all four edges `ac, ae, bc, be`.

**Formalization Note** Since a simple graph has no loops, the four vertices of such a configuration
are automatically pairwise distinct (`a ≠ c` etc. follow from adjacency, `a ≠ b` and `c ≠ e` are
required). A copy of `K_{2,2}` is a (not necessarily induced) four-cycle `a, c, b, e`; in the
bipartite incidence graph it is two variables and two clauses (p.21, PDF p.22: "a cycle on 4
vertices"). -/
def IsK22Free {W : Type*} (G : SimpleGraph W) : Prop :=
  ¬ ∃ a b c e : W, a ≠ b ∧ c ≠ e ∧ G.Adj a c ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b e

end ForestBackdoorFPT


