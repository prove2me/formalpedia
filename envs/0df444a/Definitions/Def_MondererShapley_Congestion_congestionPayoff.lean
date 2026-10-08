-- Prove2me | Definitions.Def_MondererShapley_Congestion_congestionPayoff
-- name    : MondererShapley_Congestion_congestionPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:54.355756+00:00
-- url     : https://prove2.me/theorems/f2c4b151-b319-48b7-aaca-f2139cbfdd76
-- title:
--   The congestion game of a congestion model, as a game in strategic form (Monderer–Shapley, (3.1), pp. 132–133)
-- statement:
--   A **congestion model** $C(N, M, (\Sigma^i)_{i\in N}, (c_j)_{j\in M})$ consists of a finite set of players $N$, a finite set of facilities $M$, for every player $i$ a set $\Sigma^i$ of strategies, each strategy $A^i \in \Sigma^i$ being a subset of facilities, and for every facility $j$ a vector $c_j$ of payoffs, where $c_j(k)$ is the payoff (e.g. the cost) to each user of facility $j$ if there are exactly $k$ users.
--
--   The associated **congestion game** has players $N$, strategy sets $\Sigma^i$, and, on $\Sigma = \times_{i\in N}\Sigma^i$, the payoff functions
--
--   $$v^i(A) = \sum_{j \in A^i} c_j\big(\sigma_j(A)\big), \qquad \sigma_j(A) = \#\{i \in N : j \in A^i\}, \qquad A = (A^1, \dots, A^n) \in \Sigma. \tag{3.1}$$
--
--   This definition presents the congestion game as a game in strategic form, so that it can be compared with arbitrary games (isomorphism, potentials).
--
--   **Formalization Note.** The congestion model is the published `CongestionPoA.AsymSum.CongestionGame ι M`: `strategies i` is the finite family $\Sigma^i$ of finite facility sets and `latency j k` is $c_j(k)$, an arbitrary real number (the published names "latency" and "cost" are only names; no sign change is made). The strategy set of player $i$ is the subtype of members of `strategies i`; `load` is $\sigma_j$ and `cost` is the sum (3.1). The values `latency j 0` and `latency j k` for $k > n$ never enter (3.1). Nonemptiness of the strategies is not part of the published structure; statements that need it state it separately.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 132–133 (PDF pp. 9–10), congestion model and (3.1)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

open CongestionPoA.AsymSum

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), pp. 132–133, (3.1): the congestion game associated with the
congestion model `C(N, M, (Σⁱ)_{i∈N}, (c_j)_{j∈M})`, as a game in strategic form. The players are `ι`,
the strategy set of player `i` is `Σⁱ` (the subtype of the finite family `G.strategies i` of facility
sets), and the payoff of player `i` at `A = (A¹, …, Aⁿ) ∈ Σ` is
`vⁱ(A) = Σ_{j∈Aⁱ} c_j(σ_j(A))`, where `σ_j(A) = #{i : j ∈ Aⁱ}`.

**Formalization Note.** The congestion model is the published `CongestionPoA.AsymSum.CongestionGame`:
`G.latency j k` is the paper's `c_j(k)` (an arbitrary real number, a payoff; the published name
"latency" is only a name), `load` is `σ_j` and `cost G A i` is the sum (3.1). -/
noncomputable def congestionPayoff {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M]
    [DecidableEq M] (G : CongestionGame ι M) : ι → (∀ i, ↥(G.strategies i)) → ℝ :=
  fun i A => cost G (fun j => (A j : Finset M)) i

end MondererShapley.Congestion


