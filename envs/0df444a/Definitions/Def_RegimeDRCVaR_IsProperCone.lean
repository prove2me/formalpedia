-- Prove2me | Definitions.Def_RegimeDRCVaR_IsProperCone
-- name    : RegimeDRCVaR_IsProperCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:39.586033+00:00
-- url     : https://prove2.me/theorems/399ba603-371b-4c9a-b063-010862773ab3
-- title:
--   Proper cone in $\mathbb R^{I+1}$
-- statement:
--   A set $\bar K\subseteq\mathbb R^{I+1}$ is a **proper cone** (Boyd and Vandenberghe 2004, §2.4.1) if
--
--   1. it is a cone: $cz\in\bar K$ for $z\in\bar K$ and $c\ge0$;
--   2. it is convex;
--   3. it is closed;
--   4. it is solid: its interior is nonempty;
--   5. it is pointed: $z\in\bar K$ and $-z\in\bar K$ imply $z=0$.
--
--   Lemma EC.2 is stated for proper cones.
--
--   **Formalization Note** $\mathbb R^{I+1}$ is $\mathbb R^I\times\mathbb R$ with its product (Euclidean) topology. Mathlib's `ProperCone` is not used, since it does not require solidity or pointedness in this sense.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Lemma EC.2, p.ec2 (from Boyd and Vandenberghe (2004))

import Mathlib

namespace RegimeDRCVaR

/-- **Proper cone** `K̄ ⊆ ℝ^{I+1}` (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930,
Lemma EC.2, p.ec2, which takes the notion from Boyd and Vandenberghe (2004), §2.4.1): a cone
(closed under multiplication by nonnegative scalars) that is convex, closed, solid (nonempty
interior) and pointed (contains no line: `z ∈ K̄` and `−z ∈ K̄` imply `z = 0`).

**Formalization Note** `ℝ^{I+1}` is `(Fin I → ℝ) × ℝ` with the product topology, which is the
Euclidean topology. Mathlib's `ProperCone` is not used: it means a closed pointed cone in the sense
"contains 0", without salience or solidity. -/
def IsProperCone {I : ℕ} (K : Set ((Fin I → ℝ) × ℝ)) : Prop :=
  (∀ z ∈ K, ∀ c : ℝ, 0 ≤ c → c • z ∈ K) ∧ Convex ℝ K ∧ IsClosed K ∧
    (interior K).Nonempty ∧ ∀ z, z ∈ K → -z ∈ K → z = 0

end RegimeDRCVaR


