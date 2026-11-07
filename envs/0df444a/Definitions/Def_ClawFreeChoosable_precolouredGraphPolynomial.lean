-- Prove2me | Definitions.Def_ClawFreeChoosable_precolouredGraphPolynomial
-- name    : ClawFreeChoosable_precolouredGraphPolynomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:57.673318+00:00
-- url     : https://prove2.me/theorems/40b8c6d9-bfad-4537-94ec-c787dffa12f9
-- title:
--   Graph polynomial $P_{G,\phi}$ relative to a precoloured set
-- statement:
--   Fix a linear order on $V(G)$, a set $Z \subseteq V(G)$ and real colours $\phi(z)$ on $Z$. The polynomial in the variables $x_v$, $v \in V(G) \setminus Z$, is
--   $$P_{G,\phi} = \prod_{\substack{uv \in E(G - Z)\\ u < v}} (x_v - x_u) \prod_{\substack{vz \in E(G)\\ v \notin Z,\ z \in Z}} (x_v - \phi(z)).$$
--   Each edge of $G - Z$ contributes one factor; each edge between $V(G) \setminus Z$ and $Z$ contributes one factor.
--
--   A nonzero coefficient of a suitable monomial of $P_{G,\phi}$ certifies, through the Combinatorial Nullstellensatz, that $\phi$ extends from lists (Corollary 7.7).
--
--   **Formalization Note** Colours are real numbers, as the paper identifies colours injectively with reals whenever graph polynomials are used (p.12).
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Corollary 7.7, p.12, and §7.5 p.12 (graph polynomial)

import Mathlib

set_option autoImplicit false

open Classical

noncomputable section

namespace ClawFreeChoosable

/-- **Graph polynomial relative to a precoloured set** (arXiv:2611.01068v1, Corollary 7.7, p.12,
and §7.5): for a linear order on `V(G)`, `Z ⊆ V(G)` and real colours `ϕ` on `Z`,
`P_{G,ϕ} = ∏_{uv ∈ E(G − Z), u < v} (x_v − x_u) · ∏_{vz ∈ E(G), v ∉ Z, z ∈ Z} (x_v − ϕ(z))`,
a polynomial in the variables `x_v`, `v ∈ V(G) \ Z`.

**Formalization Note.** Colours are real numbers, as the paper identifies them injectively with
reals whenever graph polynomials are used (p.12). The first product runs over ordered pairs
`(u, v)` of vertices outside `Z` with `u < v` and `uv ∈ E(G)`, so each edge of `G − Z` contributes
exactly one factor; the second runs over pairs `(v, z)` with `v ∉ Z`, `z ∈ Z`, `vz ∈ E(G)`. -/
def precolouredGraphPolynomial {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (Z : Set V) (ϕ : V → ℝ) : MvPolynomial {v // v ∉ Z} ℝ :=
  (∏ p ∈ (Finset.univ : Finset ({v // v ∉ Z} × {v // v ∉ Z})).filter
      (fun p => p.1.1 < p.2.1 ∧ G.Adj p.1.1 p.2.1),
      (MvPolynomial.X p.2 - MvPolynomial.X p.1)) *
  (∏ p ∈ (Finset.univ : Finset ({v // v ∉ Z} × V)).filter
      (fun p => p.2 ∈ Z ∧ G.Adj p.1.1 p.2),
      (MvPolynomial.X p.1 - MvPolynomial.C (ϕ p.2)))

end ClawFreeChoosable


