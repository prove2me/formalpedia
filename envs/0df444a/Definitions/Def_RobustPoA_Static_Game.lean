-- Prove2me | Definitions.Def_RobustPoA_Static_Game
-- name    : RobustPoA_Static_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:00.19538+00:00
-- url     : https://prove2.me/theorems/49c546c0-27f1-4fa9-9fa5-dcc426bb8342
-- title:
--   §1, §2.1, §4.1, pp. 2, 4, 15 — cost-minimization games, the joint cost C(s) = Σ_i C_i(s), pure Nash (1) and ε-Nash (26) equilibria
-- statement:
--   A **cost-minimization game** has finitely many players $i \in \iota$ (the paper's players $1, \dots, k$). Player $i$ chooses a strategy $s_i$ from a set $S_i$; the sets $S_i$ are arbitrary (no finiteness is assumed). A vector $s = (s_i)_i$ of chosen strategies is an **outcome**, and each player incurs a real cost $C_i(s)$ that depends on the whole outcome. For an outcome $s$, a player $i$ and a strategy $s_i' \in S_i$, write $(s_i', s_{-i})$ for the outcome in which player $i$ switches to $s_i'$ and every other player keeps its strategy. The **joint cost objective** is
--
--   $$C(s) = \sum_{i} C_i(s).$$
--
--   An outcome $s$ is a **pure Nash equilibrium** if no player can decrease its cost by a unilateral deviation,
--
--   $$C_i(s) \le C_i(s_i', s_{-i}) \quad \text{for every player } i \text{ and every } s_i' \in S_i, \tag{1}$$
--
--   and, for $\epsilon \in \mathbb{R}$, an **$\epsilon$-Nash equilibrium** if no unilateral deviation decreases a player's cost by more than a $(1+\epsilon)$ factor,
--
--   $$C_i(s) \le (1+\epsilon)\, C_i(s_i', s_{-i}) \quad \text{for every player } i \text{ and every } s_i' \in S_i. \tag{26}$$
--
--   These are the basic objects of the smoothness framework: the price-of-anarchy bounds of the mission compare the joint cost of equilibria with the joint cost of an arbitrary or optimal outcome.
--
--   **Formalization Note** Players form a `Fintype` with decidable equality; strategy sets are a family of arbitrary types `S i`, and outcomes are dependent functions. The deviation $(s_i', s_{-i})$ is `Function.update s i s'ᵢ`. The paper's standing assumption that the objective is nonnegative is not built into the definitions; theorems that need it state it.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §1 (1), p. 2; §2.1, p. 4; §4.1 (26), p. 15

import Mathlib

namespace RobustPoA.Static

/-- §2.1, p. 4: the joint cost objective `C(s) = ∑ᵢ Cᵢ(s)` of a cost-minimization game with a
finite set of players `ι`, strategy sets `S i` (arbitrary types) and player costs `C i`. -/
def cost {ι : Type*} [Fintype ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : ℝ :=
  ∑ i, C i s

/-- §1, (1), p. 2: `s` is a pure Nash equilibrium if no player lowers its cost by a unilateral
deviation `(s'ᵢ, s₋ᵢ) = Function.update s i s'ᵢ`. -/
def IsPureNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ (i : ι) (t : S i), C i s ≤ C i (Function.update s i t)

/-- §4.1, (26), p. 15: `s` is an `ε`-Nash equilibrium if no unilateral deviation lowers a
player's cost by more than a `(1 + ε)` factor. -/
def IsEpsNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (ε : ℝ) (s : ∀ i, S i) : Prop :=
  ∀ (i : ι) (t : S i), C i s ≤ (1 + ε) * C i (Function.update s i t)

end RobustPoA.Static


