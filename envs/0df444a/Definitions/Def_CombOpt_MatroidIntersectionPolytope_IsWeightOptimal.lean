-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsWeightOptimal
-- name    : CombOpt_MatroidIntersectionPolytope_IsWeightOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:37.504394+00:00
-- url     : https://prove2.me/theorems/567b32a0-a8c3-4b0b-a123-9339b91c747d
-- title:
--   $J$ is $c$-optimal in $\mathcal I$
-- statement:
--   For a matroid $M=(S,\mathcal I)$ and weights $c\in\mathbb R^S$, a set $J$ is **$c$-optimal in $\mathcal I$** if $J\in\mathcal I$ and
--
--   $$
--   c(J)=\sum_{e\in J}c_e\ \ge\ c(J')\quad\text{for every } J'\in\mathcal I.
--   $$
--
--   This is the notion used in the weight-splitting form of the matroid intersection optimality conditions.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 274 (PDF p. 281); §8.5, p. 299 (PDF p. 306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid

namespace CombOpt.MatroidIntersectionPolytope

/-- **`J` is `c`-optimal in `I`**: `J` is an independent set of maximum weight
`c(J) = Σ_{e∈J} c_e` among the independent sets of `M`.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 274 (PDF p. 281) (an "optimal independent set" for weights `c`), and §8.5,
p. 299 (PDF p. 306) ("J is cⁱ-optimal in Iᵢ"). -/
def IsWeightOptimal {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S) (c : S → ℝ)
    (J : Finset S) : Prop :=
  M.Indep J ∧ ∀ J' : Finset S, M.Indep J' → ∑ e ∈ J', c e ≤ ∑ e ∈ J, c e

end CombOpt.MatroidIntersectionPolytope


