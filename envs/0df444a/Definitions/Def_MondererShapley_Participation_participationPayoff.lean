-- Prove2me | Definitions.Def_MondererShapley_Participation_participationPayoff
-- name    : MondererShapley_Participation_participationPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:14.946816+00:00
-- url     : https://prove2.me/theorems/66a87c7e-3f93-4898-83e0-fd89feb25a50
-- title:
--   The participation game Γ(ψ, c, v) (Monderer–Shapley, p. 137)
-- statement:
--   Let $\psi$ be a solution, $c \in \mathbb R^N$ and $v \in G(N)$. The **participation game** $\Gamma(\psi, c, v)$ is the game in strategic form with player set $N$ and strategy sets $Y^i = \{0, 1\}$: player $i$ either stays out (strategy 0) and receives $c^i$, or participates (strategy 1). If $S(\varepsilon) = \{i : \varepsilon^i = 1\}$ is the set of participants at the profile $\varepsilon$, each participant receives what the solution $\psi$ assigns to it in the restriction $v_{S(\varepsilon)}$ of $v$ to the subsets of $S(\varepsilon)$:
--
--   $$u^i(\varepsilon) = \begin{cases} c^i, & \text{if } \varepsilon^i = 0,\\ \psi(v_{S(\varepsilon)})(i), & \text{if } \varepsilon^i = 1. \end{cases}$$
--
--   Section 6 characterises the Shapley value through the strategic property that these games are potential games.
--
--   **Formalization Note** `participationPayoff ψ c v i ε` is $u^i(\varepsilon)$; $\{0, 1\}$ is `Bool` (`true` = 1), and $\psi(v_{S(\varepsilon)})$ is `ψ (joiners ε) v` (see the convention of `Solution`). No hypothesis is placed on $\psi$, $c$ or $v$ in the definition.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), definition of the participation games Γ(ψ, c, v)

import Mathlib
import Definitions.Def_MondererShapley_Participation_Solution
import Definitions.Def_MondererShapley_Participation_joiners

namespace MondererShapley.Participation

variable {ι : Type*} [Fintype ι]

/-- The payoff functions of the participation game `Γ(ψ, c, v)` (p. 137): player `i` gets `cⁱ`
if `εⁱ = 0` (`false`) and `ψ(v_{S(ε)})(i)` if `εⁱ = 1` (`true`). -/
def participationPayoff (ψ : Solution ι) (c : ι → ℝ) (v : Finset ι → ℝ) :
    ι → (ι → Bool) → ℝ :=
  fun i ε => if ε i = true then ψ (joiners ε) v i else c i

end MondererShapley.Participation


