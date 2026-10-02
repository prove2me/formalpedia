-- Prove2me | Definitions.Def_TheoryOfGames_Decomposition_Splitting
-- name    : TheoryOfGames_Decomposition_Splitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:10:38.375532+00:00
-- url     : https://prove2.me/theorems/d0faef69-fcfe-479c-a28c-b61f3d2b7d66
-- title:
--   Splitting sets, minimal splitting sets, indecomposability and the decomposition partition Π_Γ (43.1, 43.3)
-- statement:
--   Let $I$ be a finite set of players and $v$ a real function on the subsets of $I$ (the characteristic function of a game $\Gamma$).
--
--   1. **Splitting set** (43.1). A set $J \subseteq I$ is a *splitting set* of $\Gamma$ if $\Gamma$ is decomposable with respect to $J$ and $K = I - J$, i.e. by (41:6)
--   $$v(S \cup T) = v(S) + v(T) \quad \text{for } S \subseteq J,\ T \subseteq I - J.$$
--   2. **Indecomposable game** (43.3.1). $\Gamma$ is *indecomposable* if $\ominus$ and $I$ are its only splitting sets.
--   3. **Minimal splitting set** (43.3.2). A splitting set $J \neq \ominus$ is *minimal* if no proper subset $J' \neq \ominus$ of $J$ is a splitting set.
--   4. **Decomposition partition** (43.3.3). $\Pi_\Gamma$ is the system of all minimal splitting sets.
--
--   A splitting set is a self-contained group of players, who neither influence nor are influenced by the others as far as the rules of the game are concerned (43.1). The book calls $\Pi_\Gamma$ the decomposition partition after (43:F), (43:G) show that the minimal splitting sets form a partition of $I$.
--
--   **Formalization Note** The definitions are stated for an arbitrary $v$; the theorems of the mission add the hypothesis (42:6:a)–(42:6:c). The complement $I - J$ is `Jᶜ`, the complement in the finite player type. $\Pi_\Gamma$ (`decompositionPartition v`) is a `Set (Finset ι)` defined as the set of minimal splitting sets; that it is a partition is not built into the definition but is proved in (43:F), (43:G).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 353, 43.1; p. 354, 43.3.1; p. 355, 43.3.2; p. 356, 43.3.3

import Mathlib

namespace TheoryOfGames.Decomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A *splitting set* `J ⊆ I` of the game with characteristic function `v` (43.1): the game is
decomposable with respect to `J` and `K = I - J = Jᶜ`, which by (42:G) is the condition (41:6):
`v(S ∪ T) = v(S) + v(T)` for all `S ⊆ J`, `T ⊆ K`. -/
def IsSplitting (v : Finset ι → ℝ) (J : Finset ι) : Prop :=
  ∀ S T : Finset ι, S ⊆ J → T ⊆ Jᶜ → v (S ∪ T) = v S + v T

/-- The game is *indecomposable* (43.3.1): `⊖` and `I` are its only splitting sets. -/
def IsIndecomposable (v : Finset ι → ℝ) : Prop :=
  ∀ J : Finset ι, IsSplitting v J → J = ∅ ∨ J = Finset.univ

/-- A *minimal splitting set* (43.3.2): a splitting set `J ≠ ⊖` such that no proper subset
`J' ≠ ⊖` of `J` is a splitting set. -/
def IsMinimalSplitting (v : Finset ι → ℝ) (J : Finset ι) : Prop :=
  IsSplitting v J ∧ J.Nonempty ∧
    ∀ J' : Finset ι, IsSplitting v J' → J'.Nonempty → J' ⊆ J → J' = J

/-- The *decomposition partition* `Π_Γ` (43.3.3): the system of all minimal splitting sets. (That
it is a partition of `I` is the content of (43:F), (43:G); it is not assumed here.) -/
def decompositionPartition (v : Finset ι → ℝ) : Set (Finset ι) :=
  {J | IsMinimalSplitting v J}

end TheoryOfGames.Decomposition


