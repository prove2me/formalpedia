-- Prove2me | Definitions.Def_DGPNash_Gadget_EpsNash
-- name    : DGPNash_Gadget_EpsNash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:08:26.680415+00:00
-- url     : https://prove2.me/theorems/79647707-8a9c-4934-b3b4-49ac59453ec6
-- title:
--   ε-Nash (ε-approximately well-supported Nash) equilibrium, Eq. (2)
-- statement:
--   Let $\mathcal G$ be a finite game in normal form: a finite set of players, for each player $p$ a finite set $S_p$ of pure strategies, and payoffs $u^p_s$ for every pure strategy profile $s$. A mixed strategy profile $x = \{x^p_j\}$ assigns to each player $p$ a probability distribution $(x^p_j)_{j \in S_p}$ on $S_p$; for a profile $s$ of the players other than $p$, $x_s$ is the product of the probabilities the other players give to their components of $s$.
--
--   For a pure strategy $j \in S_p$, the **expected payoff of $j$** against $x$ is
--   $$\sum_{s \in S_{-p}} u^p_{js}\, x_s,$$
--   the expected payoff of $p$ when $p$ plays $j$ and every other player plays its mixed strategy in $x$.
--
--   Given $\epsilon$, the profile $x$ satisfies the **$\epsilon$-well-supported condition at player $p$** if
--   $$\forall j, j' \in S_p:\quad \sum_{s \in S_{-p}} u^p_{js}x_s > \sum_{s \in S_{-p}} u^p_{j's}x_s + \epsilon \implies x^p_{j'} = 0,$$
--   that is, $p$ puts no weight on a pure strategy that some other pure strategy beats by more than $\epsilon$. The profile $x$ is an **$\epsilon$-Nash equilibrium** (an $\epsilon$-approximately well-supported Nash equilibrium) if this holds at every player. For $\epsilon = 0$ this is the standard characterization (1) of a Nash equilibrium.
--
--   This is the notion of approximate equilibrium used throughout the paper, and the one under which all game gadgets of this mission are analysed. The per-player form lets one speak of the condition at a subset of the players.
--
--   **Formalization Note** Games, mixed profiles and expected payoffs are those of the referenced `agt_games` bundle (`AGT.IsMixedProfile`, `AGT.expectedPayoff`). The expected payoff of the pure strategy $j$ is `AGT.expectedPayoff` of the profile in which $p$'s mixed strategy is replaced by the point mass at $j$ (`purePayoff`). `IsEpsNash` requires the profile to be a genuine mixed profile (each coordinate a probability distribution).
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 199, §2.1, Eqs. (1)–(2)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.Gadget

open AGT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The degenerate lottery on a finite type that puts all weight on `j`. -/
def pureLottery {α : Type*} [DecidableEq α] (j : α) : α → ℝ :=
  fun k => if k = j then 1 else 0

/-- The ε-approximately well-supported Nash condition, Eq. (2), at the single player `p`:
whenever pure strategy `j` beats pure strategy `j'` by more than `ε` against the others' mixed
strategies, `p` puts probability `0` on `j'`. -/
def IsEpsWellSupportedAt (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (σ : ∀ i, S i → ℝ) (p : ι) : Prop :=
  ∀ j j' : S p, DGPNash.NashMap.purePayoff u σ p j > DGPNash.NashMap.purePayoff u σ p j' + ε → σ p j' = 0

/-- An **ε-Nash equilibrium** in the sense of the paper (an ε-approximately well-supported Nash
equilibrium, Eq. (2), p. 199): a mixed-strategy profile satisfying the condition of Eq. (2) at
every player. For `ε = 0` this is condition (1), i.e. a Nash equilibrium. -/
def IsEpsNash (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  IsMixedProfile σ ∧ ∀ p, IsEpsWellSupportedAt u ε σ p

end DGPNash.Gadget


