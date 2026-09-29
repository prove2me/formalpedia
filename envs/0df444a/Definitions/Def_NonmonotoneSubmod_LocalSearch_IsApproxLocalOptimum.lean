-- Prove2me | Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum
-- name    : NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:00:03.497722+00:00
-- url     : https://prove2.me/theorems/0ddc8400-3adf-4da7-8c52-9970ebc1fc7f
-- title:
--   Definition 3.2 — $(1+\alpha)$-approximate local optimum
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a set function on a finite ground set $X$ and let $\alpha \in \mathbb{R}$. A set $S \subseteq X$ is a **$(1+\alpha)$-approximate local optimum** of $f$ if
--
--   $$(1+\alpha) f(S) \ge f(S \setminus \{v\}) \ \text{ for every } v \in S \qquad\text{and}\qquad (1+\alpha) f(S) \ge f(S \cup \{v\}) \ \text{ for every } v \notin S.$$
--
--   For $\alpha = 0$ this is a local optimum. The relaxation is what a local search that accepts only improvements by a factor larger than $1+\alpha$ can guarantee at termination.
--
--   **Formalization Note** $\alpha$ is an arbitrary real number here, as in the definition; the results using it add $\alpha \ge 0$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, Definition 3.2

import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- Definition 3.2 (Feige–Mirrokni–Vondrák 2011, p. 1141): a set `S` is a `(1 + α)`-approximate
local optimum of `f` if `(1 + α) f(S) ≥ f(S \ {v})` for every `v ∈ S` and
`(1 + α) f(S) ≥ f(S ∪ {v})` for every `v ∉ S`. -/
def IsApproxLocalOptimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (α : ℝ)
    (S : Finset X) : Prop :=
  (∀ v, v ∈ S → f (S.erase v) ≤ (1 + α) * f S) ∧
    (∀ v, v ∉ S → f (insert v S) ≤ (1 + α) * f S)

end NonmonotoneSubmod.LocalSearch


