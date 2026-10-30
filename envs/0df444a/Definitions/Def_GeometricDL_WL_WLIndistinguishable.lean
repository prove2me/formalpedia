-- Prove2me | Definitions.Def_GeometricDL_WL_WLIndistinguishable
-- name    : GeometricDL_WL_WLIndistinguishable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:21.278129+00:00
-- url     : https://prove2.me/theorems/e22cbdec-99a9-456b-a548-fa4afc3dc764
-- title:
--   Graphs the Weisfeiler–Lehman test does not distinguish
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be finite graphs with node features $x^{(1)}:V_1\to F$ and $x^{(2)}:V_2\to F$ in the same feature type $F$. The **Weisfeiler–Lehman test does not distinguish** them when, at every round $t\ge 0$, the two graphs have the same multiset (histogram) of colours:
--
--   $$\{\!\{\,c^{(t)}_u(G_1):\ u\in V_1\,\}\!\}=\{\!\{\,c^{(t)}_u(G_2):\ u\in V_2\,\}\!\}\qquad\text{for all } t\ge 0.$$
--
--   The WL test distinguishes two graphs exactly when their colour histograms differ at some round. For example, the WL test cannot distinguish a 6-cycle from two disjoint triangles.
--
--   **Formalization Note** The two graphs may have different node types; no bijection between them is assumed.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, Ch. 7, 'The Weisfeiler-Lehman formalism', printed pp. 119–120 (PDF pp. 123–124), including the side note "the WL test cannot distinguish a 6-cycle from two triangles"

import Mathlib
import Definitions.Def_GeometricDL_WL_wlColor__89c5bd

universe u

namespace GeometricDL.WL

/-- **Two node-featured graphs that the Weisfeiler–Lehman test does not distinguish.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, Ch. 7,
'The Weisfeiler-Lehman formalism', printed pp. 119–120 (PDF pp. 123–124): the WL test "generates a
graph representation by iteratively passing node features along the edges of the graph, then
randomly hashing their sums across neighbourhoods"; side note p. 120: "the WL test cannot
distinguish a 6-cycle from two triangles."

`WLIndistinguishable E₁ x₁ E₂ x₂` holds when, at **every** round `t`, the multiset (histogram) of
WL colours of the nodes of `(V₁, E₁, x₁)` equals that of `(V₂, E₂, x₂)`:
`{{ wlColor E₁ x₁ t u : u ∈ V₁ }} = {{ wlColor E₂ x₂ t u : u ∈ V₂ }}` for all `t`.

**Formalization Note.** The two graphs may have different node types; no bijection between them
is assumed. Features of both graphs lie in the same type `F`, so their colours are comparable. -/
def WLIndistinguishable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] {F : Type u}
    (E₁ : V₁ → V₁ → Prop) [DecidableRel E₁] (x₁ : V₁ → F)
    (E₂ : V₂ → V₂ → Prop) [DecidableRel E₂] (x₂ : V₂ → F) : Prop :=
  ∀ t : ℕ, (Finset.univ : Finset V₁).val.map (wlColor E₁ x₁ t) =
    (Finset.univ : Finset V₂).val.map (wlColor E₂ x₂ t)

end GeometricDL.WL


