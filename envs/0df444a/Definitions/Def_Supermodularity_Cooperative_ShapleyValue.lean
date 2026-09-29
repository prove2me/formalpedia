-- Prove2me | Definitions.Def_Supermodularity_Cooperative_ShapleyValue
-- name    : Supermodularity_Cooperative_ShapleyValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:25.011978+00:00
-- url     : https://prove2.me/theorems/b8edee48-a8f4-4fe5-8d9f-6e9980a0528f
-- title:
--   Section 5.1 - the Shapley value
-- statement:
--   The **Shapley value** of a cooperative game $(N,f)$ assigns each player $i$ the payoff (p.
--   209-210)
--   $$\sum_{S \subseteq N \setminus \{i\}} \frac{|S|!\,(n-|S|-1)!}{n!}\big(f(S \cup \{i\}) - f(S)\big),$$
--   the average, over all coalitions $S$ not containing $i$, of the marginal value of adding $i$ to
--   $S$, weighted by $|S|!(n-|S|-1)!/n!$ — equivalently the average of $y^\pi_i$ over all $n!$
--   permutations $\pi$.
--
--   **Formalization note.** The weight is stated exactly as the rational number
--   `S.card.factorial * (n - S.card - 1).factorial / n.factorial` cast to `ℝ`, not replaced by a
--   generic normalizing constant, since Theorem 5.2.1(c) is a precise identity.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 209-210, Section 5.1

import Mathlib

namespace Supermodularity.Cooperative

/-- `ShapleyValue f i` is the Shapley value's payoff to player `i` (Topkis p. 210):
the average, over all coalitions `S ⊆ Fin n \ {i}`, of the marginal value
`f (insert i S) - f S` of adding `i` to `S`, weighted by
`|S|! (n - |S| - 1)! / n!`. -/
noncomputable def ShapleyValue {n : ℕ} (f : Finset (Fin n) → ℝ) : Fin n → ℝ :=
  fun i => ∑ S ∈ (Finset.univ.erase i).powerset,
    (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
      (f (insert i S) - f S)

end Supermodularity.Cooperative


