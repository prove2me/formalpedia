-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_RankOfFamily
-- name    : DiscreteConvex_Combinatorial_RankOfFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:39.023382+00:00
-- url     : https://prove2.me/theorems/460c7795-7997-4439-b451-029833307a62
-- title:
--   Rank function induced by a base family (Eq. 2.71)
-- statement:
--   Given a family $\mathcal B$ of subsets of $V$, its **induced rank function** is $$\rho(X) = \max\{|X \cap J| : J \in \mathcal B\} \qquad (X \subseteq V),$$ Eq. (2.71). When $\mathcal B$ is the base family of a matroid, $\rho$ is exactly that matroid's rank function.
--
--   **Formalization Note.** Represented with `Finset.sup` over $\mathbb N$ so the map is total on every $\mathcal B : \mathrm{Finset}(\mathrm{Finset}\ V)$; the junk value at $\mathcal B = \emptyset$ is $0$ and is never relied upon, since every use site supplies $\mathcal B$ nonempty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Eq. (2.71).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Eq. (2.71)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, Eq. (2.71): the rank function induced
by a base family, `ρ(X) = max{|X ∩ J| : J ∈ 𝓑}`. One half of the correspondence of
Theorem 2.29 in `DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- The rank function `ρ(X) = max\{|X ∩ J| : J ∈ 𝓑\}` induced by a family `𝓑` of subsets of
`V` (Eq. (2.71)). Uses `Finset.sup` over `ℕ` (with the junk value `0` when `𝓑` is empty) so
that the map is total; every use site supplies `𝓑.Nonempty`. -/
def RankOfFamily {V : Type*} [DecidableEq V] (𝓑 : Finset (Finset V)) (X : Finset V) : ℤ :=
  (𝓑.sup (fun J => (X ∩ J).card) : ℕ)

end DiscreteConvex.Combinatorial


