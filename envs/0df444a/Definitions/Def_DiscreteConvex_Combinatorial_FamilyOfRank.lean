-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_FamilyOfRank
-- name    : DiscreteConvex_Combinatorial_FamilyOfRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:46.226278+00:00
-- url     : https://prove2.me/theorems/787f32d1-130b-4818-87c1-6ba6ea6d1086
-- title:
--   Base family recovered from a rank function (Eq. 2.72)
-- statement:
--   Given a set function $\rho$ on the subsets of $V$, the family recovered from it is $$\mathcal B = \{J \subseteq V : \rho(J) = |J| = \rho(V)\},$$ Eq. (2.72): the maximum-rank sets whose own cardinality equals their rank.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Eq. (2.72).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Eq. (2.72)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, Eq. (2.72): the base family recovered
from a rank function, `𝓑 = {J ⊆ V : ρ(J) = |J| = ρ(V)}`. The other half of the
correspondence of Theorem 2.29 in `DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- The family `𝓑 = \{J ⊆ V : ρ(J) = |J| = ρ(V)\}` recovered from a rank function `ρ`
(Eq. (2.72)). -/
def FamilyOfRank {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → ℤ) : Finset (Finset V) :=
  Finset.univ.filter (fun J => ρ J = (J.card : ℤ) ∧ (J.card : ℤ) = ρ (Finset.univ : Finset V))

end DiscreteConvex.Combinatorial


