-- Prove2me | Definitions.Def_DetCCHard_IsWeight
-- name    : DetCCHard_IsWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:07.871209+00:00
-- url     : https://prove2.me/theorems/662f73a3-684f-4a21-b15b-4bf8204ece2b
-- title:
--   Positive normalized rational weights, set weights and conditioning
-- statement:
--   Labels of a finite input set $X$ carry **positive normalized rational weights** $\mu : X \to \mathbb Q$: $\mu(x) > 0$ for every $x$ and $\sum_{x} \mu(x) = 1$. **Normalized weights** only require $\mu(x) \ge 0$ and $\sum_x \mu(x) = 1$. The **weight of a set** $A \subseteq X$ is
--   $$
--   \mu(A) = \sum_{x \in A} \mu(x),
--   $$
--   and **conditioning** on a set $A$ of positive weight renormalizes:
--   $$
--   (\mu \mid A)(B) = \frac{\mu(A \cap B)}{\mu(A)}.
--   $$
--
--   The weights are auxiliary data of the construction and its lower-bound proof; communication cost depends only on the table.
--
--   **Formalization Note** Lean's division returns $0$ when $\mu(A) = 0$; every statement using the conditional weight assumes $\mu(A) > 0$.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), §4.2, p.14

import Mathlib

namespace DetCCHard

/-- **Positive normalized rational weights** on a finite label set (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, §4.2, p.14: "we assign the labels in each
input set positive rational weights summing to one"): every label has positive weight and the
weights sum to one. -/
def IsWeight {X : Type} [Fintype X] (μ : X → ℚ) : Prop :=
  (∀ x, 0 < μ x) ∧ ∑ x, μ x = 1

/-- **Normalized rational weights** (nonnegative, summing to one), the input of the list
construction of Lemma 7.1, p.33. -/
def IsNormWeight {X : Type} [Fintype X] (μ : X → ℚ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The **weight of a set** of labels, `μ(A) = ∑_{x ∈ A} μ(x)` (§4.2, p.14). -/
noncomputable def wt {X : Type} [Fintype X] (μ : X → ℚ) (A : Set X) : ℚ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (· ∈ A), μ x

/-- The **conditional weight** `(μ | A)(B) = μ(A ∩ B) / μ(A)` (§4.2, p.14: conditioning on a
retained set `A` of positive weight means renormalizing).

**Formalization Note** Lean's division gives `0` when `μ(A) = 0`; every statement that uses this
quantity assumes `μ(A) > 0`. -/
noncomputable def condWt {X : Type} [Fintype X] (μ : X → ℚ) (A B : Set X) : ℚ :=
  wt μ (A ∩ B) / wt μ A

end DetCCHard


