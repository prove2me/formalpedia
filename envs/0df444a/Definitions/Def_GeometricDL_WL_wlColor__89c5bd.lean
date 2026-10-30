-- Prove2me | Definitions.Def_GeometricDL_WL_wlColor__89c5bd
-- name    : GeometricDL_WL_wlColor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:44.879382+00:00
-- url     : https://prove2.me/theorems/89c5bd04-ed49-4878-b56c-30473f8230ae
-- title:
--   Weisfeiler–Lehman colour refinement $c^{(t)}_u$
-- statement:
--   Let $G=(V,E)$ be a finite graph with node features $x_u\in F$. **Weisfeiler–Lehman colour refinement** assigns to every node $u$ and every round $t\ge 0$ a colour $c^{(t)}_u\in\mathcal C_t$:
--
--   $$c^{(0)}_u=x_u,\qquad c^{(t+1)}_u=\Big(c^{(t)}_u,\ \{\!\{\,c^{(t)}_v:\ v\in N_u\,\}\!\}\Big),$$
--
--   where $N_u$ is the neighbourhood (11) and $\{\!\{\cdots\}\!\}$ is a multiset (12): a neighbour colour that occurs several times is counted with its multiplicity.
--
--   This is the iterative colour refinement procedure of the Weisfeiler–Lehman graph isomorphism test, in which each round applies an injective relabelling to a node's own colour and the multiset of its neighbours' colours.
--
--   **Formalization Note** The relabelling is the canonical injective one (the colour is the pair itself, see `WLColor`). Neighbour colours form a multiset, never a set. Rounds are 0-based: round 0 is the input features.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §4.1, eqs. (11)–(12) and the WL remark, printed p. 34 (PDF p. 38); Ch. 7, 'The Weisfeiler-Lehman formalism', printed pp. 119–120 (PDF pp. 123–124)

import Mathlib
import Definitions.Def_GeometricDL_WL_nbhd
import Definitions.Def_GeometricDL_WL_WLColor

universe u

namespace GeometricDL.WL

/-- **Weisfeiler–Lehman colour refinement: the colour of each node after `t` rounds.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §4.1,
eqs. (11)–(12), printed p. 34 (PDF p. 38): "When φ is injective, it is equivalent to one step of
the Weisfeiler-Lehman graph isomorphism test, a classical algorithm in graph theory providing a
necessary condition for two graphs to be isomorphic by an iterative color refinement procedure";
Ch. 7, printed pp. 119–120 (PDF pp. 123–124).

For a finite graph `(V, E)` with node features `x : V → F`:
`wlColor E x 0 u = x u`, and
`wlColor E x (t + 1) u = (wlColor E x t u, {{ wlColor E x t v : v ∈ N_u }})`,
where `N_u = nbhd E u` is the neighbourhood (11) and `{{…}}` is a multiset (12).

**Formalization Note.** The refinement step is the canonical injective one (`WLColor`); the
neighbour colours form a multiset (`Multiset.map` over `N_u`), never a set, so repeated neighbour
colours are counted. Rounds are 0-based: round 0 is the input features. -/
def wlColor {V : Type*} [Fintype V] {F : Type u} (E : V → V → Prop) [DecidableRel E]
    (x : V → F) : (t : ℕ) → V → WLColor F t
  | 0 => x
  | t + 1 => fun u =>
      ((wlColor E x t u, (nbhd E u).val.map (wlColor E x t)) :
        WLColor F t × Multiset (WLColor F t))

end GeometricDL.WL


