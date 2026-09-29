-- Prove2me | Definitions.Def_Supermodularity_Cooperative_IsConvexGame
-- name    : Supermodularity_Cooperative_IsConvexGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:09.640916+00:00
-- url     : https://prove2.me/theorems/14a43429-4199-4fab-8db1-4390d81d4153
-- title:
--   Section 5.1 - a convex game (supermodular characteristic function)
-- statement:
--   A cooperative game $(N,f)$ is a **convex game** (p. 208-209) if $f(\emptyset) = 0$ and $f$ is
--   supermodular on the Boolean lattice $2^N$ of coalitions:
--   $$f(S) + f(S') \le f(S \cup S') + f(S \cap S') \quad \text{for all } S, S' \subseteq N.$$
--   `IsConvexGame f` reuses `Supermodularity.Monotonicity.SupermodularOn f Set.univ` (the ambient
--   `Lattice` structure on `Finset (Fin n)` gives $\cup = \sqcup$, $\cap = \sqcap$) together with
--   $f(\emptyset) = 0$.
--
--   **Formalization note.** "Convex game" is the literature's term for a game with a *supermodular*
--   characteristic function; it has no relation to convex sets or convex functions on $\mathbb{R}^n$
--   (the book itself flags this terminological collision on p. 208-209). Because a supermodular $f$
--   with $f(\emptyset) = 0$ is automatically superadditive (p. 209), `IsConvexGame` already carries
--   the book's standing "cooperative game" hypotheses ($f(\emptyset)=0$ and superadditivity) without
--   restating superadditivity separately.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 208-209, Section 5.1

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace Supermodularity.Cooperative

/-- `IsConvexGame f` says the cooperative game with player set `Fin n` and
characteristic function `f` is a convex game (Topkis p. 207-208): `f ∅ = 0` and `f`
is supermodular on the Boolean lattice of subsets of the player set (`⊔ = ∪`,
`⊓ = ∩`). Since a supermodular `f` with `f ∅ = 0` is automatically superadditive
(Topkis p. 209), this already carries the book's standing "cooperative game"
hypotheses. -/
def IsConvexGame {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  f ∅ = 0 ∧ Supermodularity.Monotonicity.SupermodularOn f Set.univ

end Supermodularity.Cooperative


