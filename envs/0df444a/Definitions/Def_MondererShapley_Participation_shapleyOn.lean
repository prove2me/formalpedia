-- Prove2me | Definitions.Def_MondererShapley_Participation_shapleyOn
-- name    : MondererShapley_Participation_shapleyOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:05.429681+00:00
-- url     : https://prove2.me/theorems/09d50ec1-51c8-441f-b189-f1e4fb47ce60
-- title:
--   Shapley value of a TU game on the player set S
-- statement:
--   Let $S$ be a finite set of players, $w$ a TU game on $S$ (a real function on the subsets of $S$) and $i \in S$. The **Shapley value** of player $i$ in $w$ is
--
--   $$\varphi_i(w) = \sum_{T \subseteq S \setminus \{i\}} \frac{|T|!\,(|S| - |T| - 1)!}{|S|!}\,\bigl(w(T \cup \{i\}) - w(T)\bigr),$$
--
--   the expected marginal contribution of $i$ to the players preceding it in a uniformly random ordering of $S$.
--
--   Monderer and Shapley use the Shapley value on p. 137 ("$\psi$ is the Shapley value on $\{v_S : S \in 2^N\}$") without defining it; this is Shapley's (1953) value, which the paper invokes through Hart and Mas-Colell (1989). Applied to the restriction $v_S$ of a game $v$ on $N$, the weights use $|S|$, not $n$, and only subsets of $S$ enter.
--
--   **Formalization Note** The formula is supplied, since the paper does not state it. `shapleyOn S w i` is meaningful only for $i \in S$; the natural-number subtraction $|S| - |T| - 1$ is exact there because $|T| \le |S| - 1$. The published `Supermodularity_Cooperative_ShapleyValue` has the same weights but is the value of a game on all players of `Fin n`, so it cannot be applied to the subgames $v_S$ without an extension convention; it is related, not reused.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), used in Theorems 6.1, 6.2 (not defined in the paper; Shapley's value, cited through Hart and Mas-Colell 1989)

import Mathlib

namespace MondererShapley.Participation

variable {ι : Type*} [DecidableEq ι]

/-- The Shapley value of player `i` in the TU game `w` restricted to the player set `S`:
`∑_{T ⊆ S \ {i}} |T|! (|S| - |T| - 1)! / |S|! · (w(T ∪ {i}) - w(T))`. Meaningful for `i ∈ S`. -/
noncomputable def shapleyOn (S : Finset ι) (w : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ T ∈ (S.erase i).powerset,
    ((T.card.factorial * (S.card - T.card - 1).factorial : ℕ) / (S.card.factorial : ℝ)) *
      (w (insert i T) - w T)

end MondererShapley.Participation


