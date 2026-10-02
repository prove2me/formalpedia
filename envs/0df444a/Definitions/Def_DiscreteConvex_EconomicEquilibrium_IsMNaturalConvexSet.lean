-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsMNaturalConvexSet
-- name    : DiscreteConvex_EconomicEquilibrium_IsMNaturalConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:50:08.899093+00:00
-- url     : https://prove2.me/theorems/73cff677-8b67-4725-a364-d42ce1f2f92c
-- title:
--   M$^\natural$-convex set, via projection (Eq. 4.35)
-- statement:
--   $Q \subseteq \mathbb Z^K$ is an **M$^\natural$-convex set** (Eq. (4.35)) if it is the projection, along the new coordinate $0$, of some M-convex set $B \subseteq \mathbb Z^{\{0\}\cup K}$ (represented as `Option K → ℤ`, `none` standing for the new element $0$): $Q = \{x \in \mathbb Z^K \mid \exists x_0 \in \mathbb Z,\ (x_0,x) \in B\}$.
--
--   **Formalization Note.** Reuses chunk 04's `DiscreteConvex.MConvexSets.ExchangeAxiomB` (p.101, axiom (B-EXC[Z])) for "$B$ is M-convex".
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.117, Eq. (4.35).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.117, Eq. (4.35)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.117, Eq. (4.35): the definition of an
M♮-convex set by projection of an M-convex set on the extended ground set, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `Q ⊆ Zᴷ` is an **M♮-convex set** (Eq. (4.35)) if it is the projection, along the new
coordinate `0`, of some M-convex set `B ⊆ Z^({0}∪K)` (represented as `Option K → ℤ`, `none`
standing for the new element `0`): `Q = {x ∈ Zᴷ | ∃ x₀ ∈ ℤ, (x₀, x) ∈ B}`, reusing
`DiscreteConvex.MConvexSets.ExchangeAxiomB` (p.101, axiom (B-EXC[Z])) for "`B` is M-convex". -/
def IsMNaturalConvexSet {K : Type*} [Fintype K] [DecidableEq K] (Q : Set (K → ℤ)) : Prop :=
  ∃ B : Set (Option K → ℤ), DiscreteConvex.MConvexSets.ExchangeAxiomB B ∧
    Q = {x : K → ℤ | ∃ x0 : ℤ, (fun w : Option K => w.elim x0 x) ∈ B}

end DiscreteConvex.EconomicEquilibrium


