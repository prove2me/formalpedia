-- Prove2me | Definitions.Def_NonmonotoneSubmod_Shared_Submodular
-- name    : NonmonotoneSubmod_Shared_Submodular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:56:53.265987+00:00
-- url     : https://prove2.me/theorems/4a2ce664-df57-4fb0-b790-6149e0f66993
-- title:
--   Definition 1.1 — submodular set function
-- statement:
--   Let $X$ be a finite ground set. A set function $f : 2^X \to \mathbb{R}$ is **submodular** if for all $S, T \subseteq X$,
--
--   $$f(S \cup T) + f(S \cap T) \le f(S) + f(T).$$
--
--   Submodularity is the discrete analogue of concavity and is equivalent to decreasing marginal values: $f(B \cup \{x\}) - f(B) \le f(A \cup \{x\}) - f(A)$ whenever $A \subseteq B \subseteq X$ and $x \in X \setminus B$. Examples include cut functions of graphs and digraphs, rank functions of matroids, and coverage functions. No monotonicity and no sign is assumed.
--
--   Used by all five missions of this paper, each citing Definition 1.1 on p. 1133: 01-random-set (§2.1, Theorem 2.1), 02-nonadaptive (§2.2, Theorem 2.6), 03-local-search (§3.1, Theorem 3.4), 04-smooth-local-search (§3.2, Theorem 3.6) and 05-query-lower-bound (§4.2, Theorem 4.5).
--
--   **Formalization Note** Subsets of $X$ are `Finset X` for a type `X` with `[Fintype X] [DecidableEq X]`, and $f$ is real valued. The definition is the lattice inequality of Definition 1.1 itself, not the decreasing-marginals characterization.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1133, Definition 1.1

import Mathlib

namespace NonmonotoneSubmod.Shared

/-- Definition 1.1 (Feige–Mirrokni–Vondrák 2011, p. 1133): a set function `f : 2^X → ℝ` on a
finite ground set `X` is submodular if `f (S ∪ T) + f (S ∩ T) ≤ f S + f T` for all `S, T ⊆ X`. -/
def Submodular {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ S T : Finset X, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

end NonmonotoneSubmod.Shared


