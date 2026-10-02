-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet
-- name    : DiscreteConvex_EconomicEquilibrium_BoundedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:20.222598+00:00
-- url     : https://prove2.me/theorems/9a4992d0-8068-47ae-9a9d-007052b009bf
-- title:
--   Boundedness of a subset of the integer lattice
-- statement:
--   A set $S \subseteq \mathbb Z^K$ is bounded: there is a single integer bound $N$ with $|x(k)| \le N$ for every $x \in S$ and $k \in K$. This is the boundedness assumption carried on every consumer's and producer's domain throughout the chapter (e.g. the "bounded nonempty effective domain" hypothesis of Theorem 11.7, p.332, and Proposition 11.10, p.335).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325 (the boundedness assumption on `dom Cl`,
carried throughout chapter 11, e.g. Proposition 11.10, p.335, and pp.331-332's "bounded nonempty
effective domain"): boundedness of a subset of the integer lattice `Zᴷ`, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- A set `S ⊆ Zᴷ` is bounded: there is a single integer bound `N` with `|x(k)| ≤ N` for every
`x ∈ S` and `k ∈ K`. -/
def BoundedSet {K : Type*} (S : Set (K → ℤ)) : Prop :=
  ∃ N : ℤ, ∀ x ∈ S, ∀ k : K, |x k| ≤ N

end DiscreteConvex.EconomicEquilibrium


