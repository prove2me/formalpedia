-- Prove2me | Definitions.Def_RoughgardenPOA_objective
-- name    : RoughgardenPOA_objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:14.992064+00:00
-- url     : https://prove2.me/theorems/6d69c0ce-2728-4648-bdb6-7e86df25b5fc
-- title:
--   Joint cost objective $C(\mathbf s)=\sum_{i=1}^k C_i(\mathbf s)$
-- statement:
--   A **cost-minimization game** has players $i = 1, \dots, k$, a strategy set $S_i$ for each player, and a cost function $C_i$ for each player. An **outcome** (strategy profile) is a vector $\mathbf s = (s_1, \dots, s_k)$ with $s_i \in S_i$, and the cost $C_i(\mathbf s) \in \mathbb R$ of player $i$ depends on the whole outcome. The **joint cost objective** of the game is
--
--   $$C(\mathbf s) = \sum_{i=1}^k C_i(\mathbf s).$$
--
--   This is the objective whose equilibrium value the price of anarchy compares with the value of other outcomes; every later definition of the mission (smoothness, robust price of anarchy) is phrased through it.
--
--   **Formalization Note** The players form an arbitrary finite type $\iota$ (the paper's $\{1, \dots, k\}$ is $\mathtt{Fin}\ k$), outcomes are dependent functions $\mathbf s : \forall i, S_i$, and costs are real numbers with no sign condition.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, §2.1, p. 4 (unnumbered definition of a cost-minimization game and its joint cost objective); §1, p. 2 (players, strategy sets, outcomes)

import Mathlib

namespace RoughgardenPOA

/-- **The joint cost objective `C(s) = Σ_{i=1}^k Cᵢ(s)` of a cost-minimization game.**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, §2.1, p. 4 (unnumbered): "By a cost-minimization game, we mean a game —
players, strategies, and cost functions — together with the joint cost objective function
C(s) = Σ_{i=1}^k Ci(s)." (§1, p. 2: "Each player i selects a strategy si from a set Si … The
cost Ci(s) incurred by a player i in a game is a function of the entire vector s of players'
chosen strategies, which is called a strategy profile or outcome.")

A cost-minimization game is given by a finite set of players `ι`, a strategy set `S i` for each
player, and a cost function `C i : (∀ i, S i) → ℝ` for each player, defined on outcomes
(strategy profiles) `s : ∀ i, S i`. `objective C s` is the sum `∑ i, C i s`.

**Formalization Note.** The paper's players `1, …, k` are an arbitrary finite type `ι`
(`Fin k` is an instance). Costs are real-valued, with no sign condition on an individual
`C i`. -/
def objective {ι : Type*} [Fintype ι] {S : ι → Type*} (C : ι → (∀ i, S i) → ℝ)
    (s : ∀ i, S i) : ℝ :=
  ∑ i, C i s

end RoughgardenPOA


