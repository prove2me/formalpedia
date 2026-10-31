-- Prove2me | Definitions.Def_SteinerCutDominants_IsFacetInducing
-- name    : SteinerCutDominants_IsFacetInducing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:03.753009+00:00
-- url     : https://prove2.me/theorems/f099cb64-6114-483a-9d00-6164f2a68fc7
-- title:
--   Facet inducing Steiner graph with facet weights $c$
-- statement:
--   A Steiner graph $(G,T)$ is **facet inducing with facet weights $c$** if $c$ is all-positive (so that $G_c=G$), $c$ is in minimum integer form (its components are nonnegative integers with greatest common divisor one), and $c$ has a **root basis**, a basis of $\mathbb R^{E(G)}$ consisting of roots of $c$.
--
--   These are the graphs and weights from which the facets of Steiner cut dominants are built: by Remark 1 they are the facets with full support.
--
--   **Formalization Note** The paper's definition reads "$cx\ge\gamma$ in minimum integer form defines a facet of $\mathrm{CUT}_+(G,T)$ with $G_c=G$ and $\gamma>0$", followed by "Due to Remark 1, a vector $c$ provides facet weights for $(G,T)$ if and only if $c$ has minimum integer form and there is a root basis of $c$". This definition takes the second form, and the theorem `facetInducing_iff_definesFacet` proves it equivalent to the first. A root basis exists iff the roots span $\mathbb R^{E(G)}$. The unweighted "$(G,T)$ is facet inducing" is the existence of such a $c$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wR
import Definitions.Def_SteinerCutDominants_rootCuts

namespace SteinerCutDominants

/-- `(G, T)` is a facet inducing Steiner graph with facet weights `c` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4): `c` is all-positive (so `G_c = G`), in
minimum integer form, and has a root basis.

**Formalization Note** The page defines this by "`cx ≥ γ` in minimum integer form defines a facet of
`CUT₊(G, T)` with `G_c = G` and `γ > 0`" and continues "Due to Remark 1, a vector `c` provides facet
weights for `(G, T)` if and only if `c` has minimum integer form and there is a root basis of `c`".
This definition takes the second form; the equivalence with the first is the theorem
`facetInducing_iff_definesFacet`. A root basis exists exactly when the roots span `ℝ^{E(G)}`. The
page's unweighted "`(G, T)` is facet inducing" is `∃ c`. -/
def IsFacetInducing (H : WSG) : Prop :=
  (∀ e, 0 < H.c e) ∧ (Finset.univ : Finset H.G.edgeSet).gcd H.c = 1 ∧
    Submodule.span ℝ (rootCuts H.G H.T H.wR) = ⊤

end SteinerCutDominants


