-- Prove2me | Definitions.Def_MixedManna_IsCompetitiveEquilibrium
-- name    : MixedManna_IsCompetitiveEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:42.889338+00:00
-- url     : https://prove2.me/theorems/94efd12a-8aba-4b06-8049-89c3fc5393dc
-- title:
--   Competitive equilibrium (budget equality, market clearing)
-- statement:
--   Prices $p=(p_j)_{j\in M}$ and an allocation $(x_i)_{i\in N}$ form a **competitive equilibrium** when
--
--   1. (optimal bundle) every $x_i\ge 0$ maximizes $u_i$ over the budget set: $\sum_j x_{ij}p_j=\sum_j W_{ij}p_j$ and $u_i(y)\le u_i(x_i)$ for every $y\ge 0$ with $\sum_j y_jp_j=\sum_j W_{ij}p_j$;
--   2. (market clearing) $\sum_{i}x_{ij}=\sum_i W_{ij}$ for every $j\in M$.
--
--   Bads carry negative prices at equilibrium, so an agent earns money by taking chores. This is the object Algorithm 1 is shown to compute.
--
--   **Formalization Note** The budget constraint is an equality, as printed on p.5, and the utilities are the true SPLC utilities with an infinite last segment. No sign or normalization is imposed on prices.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §2.1, p.5 (conditions 1–2)

import Mathlib
import Definitions.Def_MixedManna_Instance

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **Competitive equilibrium** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a
Mixed Manna*, arXiv:2008.02753v1, §2.1, p.5): prices `p = (p_j)_{j ∈ M}` and allocation
`(x_i)_{i ∈ N}` such that
1. (optimal bundle) `x_i ∈ argmax u_i(y)` s.t. `Σ_j y_j p_j = Σ_j W_ij p_j`, `y_j ≥ 0`;
2. (market clearing) `Σ_i x_ij = Σ_i W_ij` for every `j ∈ M`.

**Formalization Note** The budget is an equality, as printed on p.5. The utilities are the true
SPLC utilities with an infinite last segment. Prices carry no sign or normalization constraint
(equilibrium prices are scale invariant, p.5). With an equality budget the signs asserted on p.14
do not follow: `(−p, x)` is an equilibrium whenever `(p, x)` is. Statements that need the signs
(Lemma 7) take them as hypotheses. -/
def IsCompetitiveEquilibrium (I : Instance N M) (p : M → ℝ) (x : N → M → ℝ) : Prop :=
  (∀ i, (∀ j, 0 ≤ x i j) ∧ ∑ j, x i j * p j = ∑ j, I.W i j * p j ∧
      ∀ y : M → ℝ, (∀ j, 0 ≤ y j) → ∑ j, y j * p j = ∑ j, I.W i j * p j →
        utility I i y ≤ utility I i (x i)) ∧
  ∀ j, ∑ i, x i j = ∑ i, I.W i j

end MixedManna


