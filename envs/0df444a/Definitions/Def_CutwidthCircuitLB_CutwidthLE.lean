-- Prove2me | Definitions.Def_CutwidthCircuitLB_CutwidthLE
-- name    : CutwidthCircuitLB_CutwidthLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:39.676283+00:00
-- url     : https://prove2.me/theorems/b82b1ed2-0fa8-4f84-9a1d-6c99552e2ff4
-- title:
--   Cutwidth at most $w$: $\mathrm{cw}(G) \le w$
-- statement:
--   The **cutwidth** $\mathrm{cw}(G)$ of a multigraph $G$ on vertices $v_1, \dots, v_N$ is the minimum $w$ for which there exists an ordering $\pi$ of the vertices such that for every $i \in [N]$ the number of edges across the cut $(\{v_{\pi(1)}, \dots, v_{\pi(i-1)}\}, \{v_{\pi(i)}, \dots, v_{\pi(N)}\})$ is at most $w$. This definition is the statement $\mathrm{cw}(G) \le w$: some ordering has all its prefix cuts of size at most $w$.
--
--   **Formalization Note** Every statement of the mission bounds the cutwidth from above, so only the predicate $\mathrm{cw}(G) \le w$ is defined (no minimum is formed). The prefixes range over $0, \dots, N$ vertices (the extra prefix of all $N$ vertices has an empty cut). A simple graph is passed by its edge set.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.4, p.8

import Mathlib
import Definitions.Def_CutwidthCircuitLB_cutSize

namespace CutwidthCircuitLB

/-- `cw(G) ≤ w`: the multigraph with edge multiset `E` on the vertices `Fin N` **has cutwidth at most
`w`** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.4, p.8): there is an ordering `π` of the vertices such that every cut
`({v_π(1), …, v_π(i−1)}, {v_π(i), …, v_π(N)})` has at most `w` crossing edges.

**Formalization Note** The cutwidth is the minimum such `w`; every statement of the mission only
bounds it from above, so only the predicate `cw ≤ w` is defined. The prefixes have `i = 0, …, N`
vertices (the paper's `i − 1 = 0, …, N − 1`, plus the empty cut `i = N`). A simple graph `H` uses
`H.edgeFinset.val`. -/
def CutwidthLE {N : ℕ} (E : Multiset (Sym2 (Fin N))) (w : ℝ) : Prop :=
  ∃ π : Equiv.Perm (Fin N), ∀ i : ℕ, i ≤ N → (cutSize E π i : ℝ) ≤ w

end CutwidthCircuitLB


