-- Prove2me | Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration
-- name    : CoresConvexGames_Stability_IsRegularConfiguration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:47:40.650332+00:00
-- url     : https://prove2.me/theorems/39cc177d-45d9-4cc0-90c2-b900fe57f069
-- title:
--   Regular core configuration: $C_N \ne O$ and $C_S \cap C_T \subseteq C_{S\cup T} \cap C_{S\cap T}$
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. The core configuration $\{C_S\}$ is **regular** if $C_N\ne\emptyset$ and
--
--   $$
--   C_S\cap C_T\subseteq C_{S\cup T}\cap C_{S\cap T}\qquad\text{for all } S,T\subseteq N .
--   $$
--
--   Equivalently, the core is nonempty and for every payoff vector $a$ the family of coalitions whose faces contain $a$ is closed under union and intersection. Shapley proves that a game is convex exactly when its core configuration is regular; the geometric results on faces and vertices of the core are stated for regular configurations.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The clause $C_N\ne\emptyset$ is part of the definition, as on the page; without it every game with an empty core would be regular.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 18, §3.1, condition (13) and the sentence before it

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 18, §3.1: the core configuration `{C_S}` is *regular* if `C_N ≠ O`
and `C_S ∩ C_T ⊆ C_{S ∪ T} ∩ C_{S ∩ T}` for all `S, T ⊆ N` (condition (13)). -/
def IsRegularConfiguration {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  (CoreFace f Finset.univ).Nonempty ∧
    ∀ S T : Finset (Fin n),
      CoreFace f S ∩ CoreFace f T ⊆ CoreFace f (S ∪ T) ∩ CoreFace f (S ∩ T)

end CoresConvexGames.Stability


