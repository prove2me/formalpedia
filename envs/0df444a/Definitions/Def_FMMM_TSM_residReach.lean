-- Prove2me | Definitions.Def_FMMM_TSM_residReach
-- name    : FMMM_TSM_residReach
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:31.068802+00:00
-- url     : https://prove2.me/theorems/e4d9f6ff-069b-4073-a549-a96b64c3b869
-- title:
--   Reachability from the source in the residual graph of $G_f$
-- statement:
--   Let $F$ be an integral flow of the boosted flow graph $G_f$, given by its unit-flow edges. In the residual graph, the source $s$ has an arc to every ad with fewer than two edges of $F$; an ad $a$ has an arc to an impression type $j$ when $(a, j) \in E \setminus F$; and $j$ has an arc back to $a$ when $(a, j) \in F$. A vertex is **reachable from $s$** if a directed path of residual arcs leads to it from $s$.
--
--   The reachable vertices form the source side of the canonical "reachability" minimum $s$–$t$ cut, which the analysis uses to bound $\mathrm{OPT}$.
--
--   **Formalization Note** Arcs through the sink are omitted: when $F$ is a maximum flow the sink is not reachable from $s$, so no residual path from $s$ passes through it.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 7 (canonical reachability min s−t cut)

import Mathlib

namespace FMMM.TSM

/-- **Reachability from the source in the residual graph of `G_f`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 7: "First start with the canonical "reachability" min s−t cut of the
flow graph G_f, where S is defined as the set of nodes reachable from s in the residual graph G_f
left after finding the max-flow E_f."

For the integral flow with support `F` (capacities 2, 1, 2), the residual arcs among ads and
impressions are `a → j` for `(a, j) ∈ E \ F` and `j → a` for `(a, j) ∈ F`; the source reaches
directly the ads `a` with fewer than two `F`-edges. `residReach E F v` says that the vertex `v` of
`A ⊕ J` is reachable from `s`: some ad `a` with `F`-degree `< 2` reaches `v` along residual arcs.

**Formalization Note.** Arcs through the sink are omitted: when `F` is a maximum flow the sink is
not reachable from `s`, so no residual path from `s` passes through it. -/
def residReach {A J : Type} [DecidableEq A] [DecidableEq J] (E F : Finset (A × J))
    (v : A ⊕ J) : Prop :=
  ∃ a : A, (F.filter (fun e => e.1 = a)).card < 2 ∧
    Relation.ReflTransGen
      (fun u w : A ⊕ J => match u, w with
        | Sum.inl a, Sum.inr j => (a, j) ∈ E ∧ (a, j) ∉ F
        | Sum.inr j, Sum.inl a => (a, j) ∈ F
        | _, _ => False)
      (Sum.inl a) v

end FMMM.TSM


