-- Prove2me | Definitions.Def_SmoothedNash_PassesTest
-- name    : SmoothedNash_PassesTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:46.507846+00:00
-- url     : https://prove2.me/theorems/6b1e64c6-0ed3-4f0c-9984-cacb81171e0c
-- title:
--   Survival test and relaxed region $E_A(\tau)$
-- statement:
--   Let $u$ be a game, $A$ a support profile and $\tau \in \mathbb R$. A profile $x$ **passes the test with tolerance $\tau$** if for every player $i$ there is an anchor action $\alpha_i \in A_i$ such that
--   $$
--   U_{i,\alpha_i}(x) \le U_{i,a}(x) \le U_{i,\alpha_i}(x) + \tau \quad \text{for all } a \in A_i, \qquad
--   U_{i,b}(x) \le U_{i,\alpha_i}(x) + \tau \quad \text{for all } b \notin A_i .
--   $$
--   The level-$t$ test (1)–(2) of Algorithm 2 is this test with $\tau = 2\rho_t$. For $\tau \ge 0$ the relaxed survival region is $E_A(\tau) = \{x \in K_A : x \text{ passes the test with tolerance } \tau\}$.
--
--   **Formalization Note** Membership in $K_A$ is not part of the predicate; theorems state it separately.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.2, (1)–(2), p.14, and §2.1.4, p.18

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_devPayoff
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- The survival test with tolerance `τ` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.2, (1)–(2), p.14, and the region `E_A(τ)` of
§2.1.4, p.18): for every player `i` there is an anchor action `α_i ∈ A_i` such that, at the profile
`x`,
`U_{i,α_i}(x) ≤ U_{i,a}(x) ≤ U_{i,α_i}(x) + τ` for all `a ∈ A_i`, and
`U_{i,b}(x) ≤ U_{i,α_i}(x) + τ` for all `b ∉ A_i`.

**Formalization Note** The level-`t` test is `PassesTest u A (2 * rho m t)`. The relaxed region is
`E_A(τ) = {x | InK A x ∧ PassesTest u A τ x}`; membership in `K_A` is stated separately. -/
def PassesTest {m n : ℕ} (u : Game m n) (A : SupportProfile m n) (τ : ℝ)
    (x : Fin m → Fin n → ℝ) : Prop :=
  ∀ i, ∃ α ∈ A.1 i,
    (∀ a ∈ A.1 i, devPayoff u x i α ≤ devPayoff u x i a ∧ devPayoff u x i a ≤ devPayoff u x i α + τ) ∧
    ∀ b, b ∉ A.1 i → devPayoff u x i b ≤ devPayoff u x i α + τ

end SmoothedNash


