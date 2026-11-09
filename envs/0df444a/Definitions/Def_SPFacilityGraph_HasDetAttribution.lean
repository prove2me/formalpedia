-- Prove2me | Definitions.Def_SPFacilityGraph_HasDetAttribution
-- name    : SPFacilityGraph_HasDetAttribution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:02:22.637889+00:00
-- url     : https://prove2.me/theorems/b8c2c4af-805b-4e25-bb48-705bf165152e
-- title:
--   Deterministic PL $(\Pi(W), \mathcal T)$-attribution of a deterministic mechanism
-- statement:
--   Let $K$ be a triangulation of $G^n$ and $W \subseteq G$ finite. A deterministic mechanism $M : G^n \to G$ **admits a deterministic $(\Pi(W), \mathcal T)$-attribution** on the maximal simplices $\mathcal T$ of $K$ if one selector $f_T \in \Pi(W)$ can be chosen for each maximal simplex $T$ so that
--   $$
--   M(\boldsymbol x) = f_T(\boldsymbol x) \qquad \text{for all } T \in \mathcal T \text{ and } \boldsymbol x \in T .
--   $$
--   On every region the mechanism either follows one agent's report or is constant at a point of $W$. Together with the region requirement on $K$ this is a deterministic PL attribution in the sense of Definitions 3.3, 3.5 and 7.1.
--
--   **Formalization Note** In a deterministic attribution the mixing weights are $1$ on $f_T$ and $0$ on the other selectors. Constant weights are affine, lie in $[0,1]$ and sum to $1$, so the attribution identity (3.2) becomes $M(\boldsymbol x) = f_T(\boldsymbol x)$ on $T$, a point identified with its point mass. Report selectors and constants are PL maps, so the component requirement of Definition 3.5 holds automatically. Regions are closed simplices.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 3.3, (3.2), p.7; Definition 3.5, p.8; Definition 7.1, p.16

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_embed
import Definitions.Def_SPFacilityGraph_Selector_eval

set_option autoImplicit false

namespace SPFacilityGraph

/-- A deterministic mechanism `M : Gⁿ → G` admits a deterministic PL `(Π(W), T)`-attribution
with regions `T` the maximal simplices of the triangulation `K` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 3.3, (3.2),
p.7; Definition 3.5, p.8; Definition 7.1, p.16): there is a choice of one selector `f_T ∈ Π(W)`
for every maximal simplex `T` of `K` such that `M(𝒙) = f_T(𝒙)` for every profile `𝒙` in the
closed simplex `T`.

**Formalization Note** In a deterministic attribution the mixing weights are `1` on `f_T` and
`0` on every other selector; constant weights are affine on `T`, lie in `[0, 1]` and sum to
`1`, so (3.2) reduces to `M(𝒙) = f_T(𝒙)` on `T` (a point identified with its point mass).
Selectors of `Π(W)` are coordinate projections and constants, hence PL, and `Π(W)` is finite and
nonempty. The region requirement on `K` is `IsEdgeTriangulation`, stated separately. -/
def HasDetAttribution {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt) (W : Finset G.Pt)
    (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))) : Prop :=
  ∃ sel : K.facets → Selector G n W, ∀ (s : K.facets) (x : Profile G n),
    G.embed x ∈ convexHull ℝ (s.1 : Set (Fin n → EuclideanSpace ℝ (Fin k))) →
      M x = (sel s).eval x

end SPFacilityGraph


