-- Prove2me | Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
-- name    : NonmonotoneSubmod_Shared_SymmetricSetFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:57:14.203038+00:00
-- url     : https://prove2.me/theorems/891a33d4-515d-4bdb-9147-0b7eeb24c811
-- title:
--   Symmetric set function: $f(X \setminus S) = f(S)$
-- statement:
--   Let $X$ be a finite ground set. A set function $f : 2^X \to \mathbb{R}$ is **symmetric** if
--
--   $$f(X \setminus S) = f(S) \quad \text{for every } S \subseteq X.$$
--
--   The cut function of an undirected graph is the standard example: the edges leaving $S$ are exactly the edges leaving its complement. For symmetric submodular functions the random-set guarantee of Theorem 2.1 improves from $\tfrac14$ to $\tfrac12$.
--
--   Used by three missions of this paper, each citing the definition in Theorem 2.1 on p. 1137: 01-random-set (Theorem 2.1, symmetric case), 03-local-search (Theorem 3.4, symmetric case, p. 1141) and 05-query-lower-bound (the symmetric hard instance of Theorem 4.5, pp. 1149–1150).
--
--   **Formalization Note** The complement $X \setminus S$ is `Sᶜ = Finset.univ \ S`. The property is required of every subset, not only of an optimal one.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Theorem 2.1 (parenthetical definition of symmetric)

import Mathlib

namespace NonmonotoneSubmod.Shared

/-- Symmetric set function (Feige–Mirrokni–Vondrák 2011, Theorem 2.1, p. 1137):
`f (X \ S) = f S` for every `S ⊆ X`; here `Sᶜ = Finset.univ \ S`. -/
def SymmetricSetFun {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ S : Finset X, f Sᶜ = f S

end NonmonotoneSubmod.Shared


