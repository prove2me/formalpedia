-- Prove2me | Definitions.Def_GeometricDL_WL_WLColor
-- name    : GeometricDL_WL_WLColor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:05.811992+00:00
-- url     : https://prove2.me/theorems/d61e9bd4-4c89-47b7-a4f8-faebaad470f6
-- title:
--   Canonical Weisfeiler–Lehman colour type after $t$ rounds
-- statement:
--   Fix a type $F$ of node features. The **WL colours after $t$ rounds** form the type $\mathcal C_t$ defined by
--
--   $$\mathcal C_0=F,\qquad \mathcal C_{t+1}=\mathcal C_t\times\mathrm{Multiset}(\mathcal C_t).$$
--
--   A colour after $t+1$ rounds is a pair: a colour after $t$ rounds (the node's own) and a finite multiset of colours after $t$ rounds (its neighbours').
--
--   This type is the codomain of Weisfeiler–Lehman colour refinement. Since a colour is literally the pair being "hashed", the relabelling step is injective and the same for every graph, so colours of two different graphs can be compared directly.
--
--   **Formalization Note** This is the canonical form of the injective relabelling $\varphi(x_u,X_{N_u})$ of p. 34 ("When $\varphi$ is injective, it is equivalent to one step of the Weisfeiler-Lehman graph isomorphism test"). Rounds are 0-based.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §4.1, printed p. 34 (PDF p. 38) (one WL step = injective φ(x_u, X_{N_u})); Ch. 7, 'The Weisfeiler-Lehman formalism', printed pp. 119–120 (PDF pp. 123–124)

import Mathlib

universe u

namespace GeometricDL.WL

/-- **The canonical colour type of the Weisfeiler–Lehman test after `t` rounds.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §4.1,
printed p. 34 (PDF p. 38): "When φ is injective, it is equivalent to one step of the
Weisfeiler-Lehman graph isomorphism test, a classical algorithm in graph theory providing a
necessary condition for two graphs to be isomorphic by an iterative color refinement
procedure."; Ch. 7, printed pp. 119–120 (PDF pp. 123–124): the WL test "generates a graph
representation by iteratively passing node features along the edges of the graph, then randomly
hashing their sums across neighbourhoods."

`WLColor F 0 = F` (the node features) and `WLColor F (t + 1) = WLColor F t × Multiset (WLColor F t)`:
a colour after `t + 1` rounds is the pair (own colour after `t` rounds, multiset of neighbour colours
after `t` rounds).

**Formalization Note.** This is the injective relabelling `φ(x_u, X_{N_u})` of p. 34 in canonical
form: a colour *is* the pair it hashes, so the relabelling is injective and shared by every graph,
and colours of two different graphs are directly comparable. Rounds are 0-based. -/
def WLColor (F : Type u) : ℕ → Type u
  | 0 => F
  | t + 1 => WLColor F t × Multiset (WLColor F t)

end GeometricDL.WL


