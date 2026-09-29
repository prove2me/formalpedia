-- Prove2me | Definitions.Def_Supermodularity_Matching_IsTightMatching
-- name    : Supermodularity_Matching_IsTightMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:37.887983+00:00
-- url     : https://prove2.me/theorems/869259a0-9e6c-40e6-aafb-9ab48f43422c
-- title:
--   A matching feasible in a tight labor market (§3.2)
-- statement:
--   The labor market for worker type $i$ is **tight** if there are exactly $m$ workers of that
--   type available, i.e. $|X_i| = m$ (Topkis, p. 96). In a tight labor market every worker is
--   hired by some firm, so a feasible matching is a *bijective* assignment of the $m$ workers of
--   each type to the $m$ firms: `IsTightMatching x` says that for every worker type $i$, the map
--   sending a firm $j$ to the quality $x^j_i$ of the type-$i$ worker it hires,
--   $$j \longmapsto x^j_i, \qquad j \in \{1,\dots,m\},$$
--   is a bijection from firms onto $X_i$ (assuming $|X_i| = m$, so such a bijection can exist).
--
--   Topkis (p. 96): "The labor market is tight if there are exactly $m$ workers of each type;
--   that is, if $|X_i| = m$ for each $i$. In a tight labor market, each matching has each worker
--   in the labor market being hired by some firm."
--
--   **Formalization Note.** `IsTightMatching` is a per-matching feasibility predicate (every
--   type-$i$ worker in $X_i$ is hired exactly once); the market-wide precondition $|X_i| = m$ for
--   every $i$ that makes such a bijection possible in the first place is supplied separately, as
--   an explicit `Fintype.card (X i) = m` hypothesis, wherever a tight-market result needs it.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 96, Section 3.2

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 96, Section 3.2 (the labor market is tight if there are exactly `m` workers of each type,
so a feasible matching partitions that fixed supply among the `m` firms).
-/

namespace Supermodularity.Matching

/-- `IsTightMatching x` says the matching `x : Fin m → ∀ i, X i` is feasible in a *tight*
labor market, in which the supply of each worker type `i` is exactly the `m` elements of
`X i` (one per firm, no worker left unhired and no worker hired twice): for each type `i`,
the map `j ↦ x j i` sending firms to the quality of the type-`i` worker they hire is a
bijection onto `X i`. -/
def IsTightMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  ∀ i, Function.Bijective (fun j : Fin m => x j i)

end Supermodularity.Matching


