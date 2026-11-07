-- Prove2me | Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost
-- name    : CutwidthCircuitLB_CubicCutwidthAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:51.817149+00:00
-- url     : https://prove2.me/theorems/8aee91c3-83b6-4f78-831b-e2d458740955
-- title:
--   The cubic cutwidth constant is at most $a$
-- statement:
--   The **cubic cutwidth constant** $\alpha$ is the infimum of all $\beta > 0$ for which there is a function $r(N) = o(N)$ such that every connected loopless subcubic multigraph with $N$ vertices and $M$ edges has
--   $$
--   \mathrm{cw}(G) \le \beta (M - N) + r(N).
--   $$
--   This definition is the statement $\alpha \le a$: for every $\beta > a$ there is such a function $r$ (depending on $\beta$ only).
--
--   Upper bounds on $\alpha$ give circuit lower bounds (Theorem 4.3): $\alpha \le a$ implies that $B_2$-circuits for Li's function need more than $(1 + 1/a - \varepsilon) n$ gates.
--
--   **Formalization Note** Multigraphs are the published `CombOpt.MatchingPolytope.Graph` with $N$ vertices and $M$ edges; "loopless" is its published predicate `Graph.IsLoopless`. "$\alpha \le a$" is written as "every $\beta > a$ is admissible". The set of admissible $\beta$ is upward closed, because a connected multigraph has $M - N \ge -1$, so raising $\beta$ costs at most an additive constant that $r$ absorbs; hence the two readings agree. The constant is never formed as an infimum of a possibly empty set. The paper's "$r(N) < o(N)$" is read as $r = o(N)$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.1, p.2

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CutwidthCircuitLB_IsSubcubic
import Definitions.Def_CutwidthCircuitLB_IsConnected
import Definitions.Def_CutwidthCircuitLB_edgeMultiset
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE

namespace CutwidthCircuitLB

/-- **The cubic cutwidth constant is at most `a`** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.1, p.2): the cubic cutwidth constant `α`
is the infimum of all `β > 0` for which there is a function `r(N) = o(N)` such that every connected
loopless subcubic multigraph with `N` vertices and `M` edges has cutwidth at most
`β(M − N) + r(N)`; this predicate says `α ≤ a`.

**Formalization Note** Multigraphs are the published `CombOpt.MatchingPolytope.Graph` on
`Fin N` vertices and `Fin M` edges, and "loopless" is its published `Graph.IsLoopless`.
`α ≤ a` is written as: every `β > a` is admissible. The admissible set is
upward closed (a connected graph has `M − N ≥ −1`, so raising `β` costs an additive constant, which
`r` absorbs), so this is equivalent to the infimum being at most `a`. `α` is never formed as an
`sInf`, whose value on an empty set would be `0`. "`r(N) < o(N)`" is read as `r = o(N)`. -/
def CubicCutwidthAtMost (a : ℝ) : Prop :=
  ∀ β : ℝ, a < β → ∃ r : ℕ → ℝ, r =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) ∧
    ∀ (N M : ℕ) (G : CombOpt.MatchingPolytope.Graph (Fin N) (Fin M)),
      IsConnected G → G.IsLoopless → IsSubcubic G →
        CutwidthLE (edgeMultiset G) (β * ((M : ℝ) - N) + r N)

end CutwidthCircuitLB


