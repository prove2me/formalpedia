-- Prove2me | Definitions.Def_CoresConvexGames_Stability_IsCompleteConfiguration
-- name    : CoresConvexGames_Stability_IsCompleteConfiguration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:47:10.330234+00:00
-- url     : https://prove2.me/theorems/6527d6be-2154-4f6e-bc3e-722b572a7b92
-- title:
--   Complete core configuration: every face $C_S$ is nonempty
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. The core configuration $\{C_S\}$ is **complete** if none of the faces is empty:
--
--   $$
--   C_S\ne\emptyset\quad\text{for all } S\subseteq N.
--   $$
--
--   Completeness is the property of the faces that the external-stability argument for convex games uses: it guarantees a core point on the hyperplane of any prescribed coalition.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 16, §3, second paragraph (definition of complete)

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 16, §3: the core configuration `{C_S}` is *complete* if none of the
faces `C_S`, `S ⊆ N`, is empty. -/
def IsCompleteConfiguration {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), (CoreFace f S).Nonempty

end CoresConvexGames.Stability


