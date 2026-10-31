-- Prove2me | Definitions.Def_MixedManna_IsAdmissibleDelta
-- name    : MixedManna_IsAdmissibleDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:51.77477+00:00
-- url     : https://prove2.me/theorems/d2bc29d9-d97a-44ee-afe4-11b3ea3f0035
-- title:
--   Admissible coefficients $\delta_j\in(1,1+1/m)$
-- statement:
--   The coefficients of $z$ in the goods' constraints (14c) are $\delta_j=1+\epsilon_j$ with $\epsilon_j\in(0,1/m)$, $m=|M|$. A vector $\delta$ is **admissible** when $1<\delta_j<1+1/m$ for every good $j$; values on bads are not used.
--
--   **Formalization Note** The paper draws $\epsilon_j$ uniformly at random; here every value of the interval is allowed.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.2, p.21 (δ_j = 1 + ϵ_j)

import Mathlib
import Definitions.Def_MixedManna_Instance

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **Admissible coefficients `δ`** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation
of a Mixed Manna*, arXiv:2008.02753v1, p.21): "we use a coefficient `δ_j = 1 + ϵ_j`, where `ϵ_j`
is a uniform random number from `(0, 1/m)`", `m = |M|`. Here: `1 < δ_j < 1 + 1/m` for every good
`j`; the values of `δ` on bads are not used.

**Formalization Note** Every value in the interval is allowed, not a random draw. -/
def IsAdmissibleDelta (I : Instance N M) (δ : M → ℝ) : Prop :=
  ∀ j, IsGood I j → 1 < δ j ∧ δ j < 1 + 1 / (Fintype.card M : ℝ)

end MixedManna


