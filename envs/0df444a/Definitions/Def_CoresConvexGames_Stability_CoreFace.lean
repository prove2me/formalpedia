-- Prove2me | Definitions.Def_CoresConvexGames_Stability_CoreFace
-- name    : CoresConvexGames_Stability_CoreFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:46:28.985045+00:00
-- url     : https://prove2.me/theorems/6144877a-7bb5-464f-bd95-a6dc1c7f6d41
-- title:
--   Face $C_S$ of the core: core points with $a(S) = v(S)$, and $C_O = C$
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The **core** $C$ is the set of feasible $a$ with $a(S)\ge v(S)$ for all $S\subseteq N$; equivalently $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S$. Let $H_S$ be the hyperplane $a(S)=v(S)$. For every coalition $S$ the **face** $C_S$ of the core is
--
--   $$
--   C_S=\begin{cases} C\cap H_S, & \emptyset\ne S\subseteq N,\\ C, & S=\emptyset.\end{cases}
--   $$
--
--   In particular $C_N=C$. The family $\{C_S\}_{S\subseteq N}$ is the **core configuration** of $v$; its facial structure is the object of study of §3 of the paper.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The convention $C_\emptyset=C$ is encoded literally: the condition $a(S)=v(S)$ is imposed only when $S$ is nonempty.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 16, §3, second paragraph (definition of C_S, and C_O = C)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 16, §3: the face `C_S = C ∩ H_S` of the core `C` for `O ⊂ S ⊆ N`,
where `H_S` is the hyperplane `a(S) = v(S)`; and `C_O = C` by the page's convention.
For `S = ∅` the membership condition reduces to `a ∈ C`. -/
def CoreFace {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {a | a ∈ Core Finset.univ f ∧ (S.Nonempty → ∑ i ∈ S, a i = f S)}

end CoresConvexGames.Stability


