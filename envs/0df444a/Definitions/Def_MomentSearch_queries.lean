-- Prove2me | Definitions.Def_MomentSearch_queries
-- name    : MomentSearch_queries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:33.734207+00:00
-- url     : https://prove2.me/theorems/c6c4a949-fccc-4f78-b7b7-7e56ef5db0b1
-- title:
--   Number of queries $q(S,t)$ a strategy uses to identify a target
-- statement:
--   For a strategy $S$ and a target $t\in[n]_0$, $q(S,t)$ denotes the **number of queries** performed by $S$ before identifying $t$. Following the tree from the root: at a leaf (singleton interval) the target is identified with no further query; at a node labelled $v$ one query is made, the search ends if $t=v$, and otherwise it continues in the subtree of the side containing $t$. Thus $q(S,t)$ is the depth of the node querying $t$ plus one, or the depth of the leaf $\{t\}$.
--
--   The query counts are the per-target costs from which the expected cost $\mathrm{cost}_p(S)$ is formed.
--
--   **Formalization Note** The recursion is defined for every natural number $t$; its value is meaningful only for $t$ in the tree's interval, and all statements evaluate it only at targets $t\in[n]_0$ of a strategy on $[n]_0$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_MomentSearch_SearchTree

namespace MomentSearch

/-- `queries S t = q(S, t)`: the number of queries a search tree `S` performs before identifying
the target `t` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)).

At a leaf (singleton interval) the target is identified with no query. At a node labelled `v`
one query is made; it terminates if `t = v` and otherwise the strategy continues in the subtree
of the side containing `t`.

**Formalization Note.** The value is only meaningful for targets `t` in the tree's interval
`{a, …, b}`; for `t` outside it the recursion returns an unused value (every statement only
evaluates `queries S t` at `t : Fin n` for `S : Strategy n`, whose interval is `{0, …, n − 1}`). -/
def queries : {a b : ℕ} → SearchTree a b → ℕ → ℕ
  | _, _, .leaf _, _ => 0
  | a, b, .node v _ _ _ l r, t =>
      if t = v then 1
      else if t < v then
        (if hl : a < v then 1 + queries (l hl) t else 1)
      else
        (if hr : v < b then 1 + queries (r hr) t else 1)

end MomentSearch


