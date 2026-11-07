-- Prove2me | Definitions.Def_MCPoise_IsPartialSolution
-- name    : MCPoise_IsPartialSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:41.060179+00:00
-- url     : https://prove2.me/theorems/1dd28b84-a2cd-4198-a7d9-31f93ab828cf
-- title:
--   $(\alpha, \beta)$-approximate partial solution
-- statement:
--   A subgraph $H \subseteq G$ is an **$(\alpha, \beta)$-approximate partial solution** covering $D' \subseteq D$ when
--
--   1. for every $(s_i, t_i) \in D'$, the graph $H$ contains an $s_i$-$t_i$ path of length at most $\beta L$;
--   2. $\max_{v} \deg_H(v) \le \alpha L$.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 3, p.7

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_maxDeg

namespace MCPoise

/-- **`(α, β)`-approximate partial solution covering `D′`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 3, p.7: "A subgraph H ⊆ G is an (α, β)-approximate partial solution to the MC poise covering
demand pairs D′ ⊆ D if (1) for all (s_i, t_i) ∈ D′, H contains a s_i-t_i path of length at most β · L, and (2)
max_{v∈V} deg_H(v) ≤ α · L."

**Formalization Note.** `D′` is a set of demand indices. A walk of `H` of length at most `β L` contains a path
of that length. -/
structure IsPartialSolution (I : Inst) (L α β : ℝ) (H : SimpleGraph (Fin I.n))
    (D' : Finset (Fin I.k)) : Prop where
  le_graph : H ≤ I.graph
  path : ∀ i ∈ D', ∃ p : H.Walk (I.s i) (I.t i), (p.length : ℝ) ≤ β * L
  degree : (maxDeg H : ℝ) ≤ α * L

end MCPoise


