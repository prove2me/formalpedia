-- Prove2me | Definitions.Def_DetCCHard_DeletionBounds
-- name    : DetCCHard_DeletionBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:41.095841+00:00
-- url     : https://prove2.me/theorems/d9e0de52-8c8a-438c-9c23-180333efeff0
-- title:
--   Deletion bounds $\mathcal P(F; \rho, d)$
-- statement:
--   Let $F : X \times Y \to \{0,1\}$ have input weights $\mu_X, \mu_Y$, let $\rho$ be a threshold and $d$ an integer. $F$ satisfies the **deletion bounds** $\mathcal P(F; \rho, d)$ if for every $j \in \{0, 1\}$ and all $U \subseteq X$, $V \subseteq Y$,
--   $$
--   \mu_X(U) \ge \rho \ \text{ and } \ \mu_Y(V) \ge \tfrac35\, 2^{-j} \quad\Longrightarrow\quad D(F[U, V]) \ge d - j .
--   $$
--   No matching upper bound is required.
--
--   The deletion bounds are the invariant that every round of the amplifier preserves: a lower bound that survives deleting all but a $\rho$ fraction of rows and $2/5$ (or $7/10$) of the columns.
--
--   **Formalization Note** $d$ is an integer and $d - j \le D(F[U,V])$ is compared in $\mathbb Z$, so nothing truncates. $\rho$ is real and compared with the set weight cast to $\mathbb R$. The paper's range $0 < \rho \le 1$ and the positivity and normalization of the weights are hypotheses of the statements that use the predicate.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 5.1, p.16

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight

namespace DetCCHard

/-- The **deletion bounds** `P(F; ρ, d)` (Gaspers–He–Mackenzie, arXiv:2508.05597, held version
sha256 ad552d13…a4a03, Definition 5.1, p.16): for every `j ∈ {0, 1}` and all `U ⊆ X`, `V ⊆ Y`,
`μX(U) ≥ ρ` and `μY(V) ≥ (3/5)·2^{-j}` imply `D(F[U, V]) ≥ d − j`.

**Formalization Note** `d` is an integer, as printed, and the comparison `d − j ≤ D(F[U, V])` is
made in `ℤ`, so it never truncates. The threshold `ρ` is real and compared with the (rational) set
weight cast to `ℝ`. The range `0 < ρ ≤ 1` and the positivity and normalization of the weights are
hypotheses of the statements that use the predicate, as in the paper's definition. -/
def DeletionBounds {X Y : Type} [Fintype X] [Fintype Y] (F : X → Y → Bool) (μX : X → ℚ)
    (μY : Y → ℚ) (ρ : ℝ) (d : ℤ) : Prop :=
  ∀ j : ℕ, j ≤ 1 → ∀ (U : Set X) (V : Set Y),
    ρ ≤ (wt μX U : ℝ) → (3 / 5 : ℚ) * (1 / 2) ^ j ≤ wt μY V → d - j ≤ (commCost F U V : ℤ)

end DetCCHard


